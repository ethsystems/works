//! Chain events folded into a durable Merkle accumulator.
//!
//! chainfold owns the total order, dedup, and fork recovery. rotortree owns the
//! append-only accumulator behind a WAL. One invariant joins them: the accumulator only
//! ever receives leaves at or below the engine's durable point, the oldest retained
//! checkpoint, so no rollback the engine can survive ever needs to un-append a leaf.
//! Survivable reorg depth is therefore the retained checkpoint window.
//!
//! ```sh
//! cargo run --release -p examples --example merkle_log
//! ```

use std::path::Path;

use chainfold::{
    Driver,
    DriverConfig,
    Engine,
    EngineConfig,
    Fold,
    FoldError,
    Persist,
    Position,
    Tick,
    storage::{
        Flusher,
        RealVfs,
        SnapshotStore,
        StoreConfig,
    },
    test_util::ScriptedChain,
};
use rotortree::{
    Blake3Hasher,
    CheckpointPolicy,
    FlushPolicy,
    Hash,
    RotorTree,
    RotorTreeConfig,
    TieringConfig,
};

/// Accumulator branching factor and depth ceiling.
const N: usize = 4;
const MAX_DEPTH: usize = 12;
/// Observed-block ring window.
const RING_CAPACITY: usize = 32;
/// Retained checkpoint slots; with the interval below, the survivable reorg depth.
const CHECKPOINT_SLOTS: usize = 4;
/// Blocks between checkpoints and between snapshot offers.
const CHECKPOINT_INTERVAL: u64 = 4;
/// Snapshot jobs the flusher admits before an offer blocks on the queue.
const QUEUE_DEPTH: usize = 4;
/// Bytes of the persisted base offset, then of one persisted leaf.
const BASE_LEN: usize = 8;
const LEAF_LEN: usize = 32;

/// Fold recording one leaf commitment per event, in position order.
///
/// Retains only the leaves the accumulator has not fsynced, so what `checkpoint` clones
/// is bounded by the finality window rather than the chain's whole history.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct MerkleLog {
    /// Leaves dropped from the front, durable in the accumulator; the suffix's origin.
    base: usize,
    /// Leaf commitments still retained, ascending.
    leaves: Vec<Hash>,
}

impl MerkleLog {
    /// Leaves folded since genesis; also the accumulator index the next one lands at.
    fn folded(&self) -> usize {
        self.base + self.leaves.len()
    }

    /// Drops the retained leaves below `durable`, an absolute index the accumulator has
    /// fsynced. Pruning to its in-memory size instead would open a gap: a crash losing
    /// unflushed WAL writes would leave leaves neither side still holds.
    fn prune(&mut self, durable: usize) {
        let drop = durable.saturating_sub(self.base).min(self.leaves.len());
        self.leaves.drain(..drop);
        self.base += drop;
    }
}

impl Fold for MerkleLog {
    type Event = u64;
    type Error = core::convert::Infallible;

    fn apply(
        &mut self,
        pos: Position,
        event: &u64,
    ) -> Result<(), FoldError<Self::Error>> {
        self.leaves.push(leaf(pos, *event));
        Ok(())
    }
}

impl Persist for MerkleLog {
    const STATE_TAG: &'static str = "example.merkle-log.v1";
    type PersistError = ();

    fn encode_state(&self, out: &mut Vec<u8>) {
        out.reserve(BASE_LEN + self.leaves.len() * LEAF_LEN);
        out.extend_from_slice(&(self.base as u64).to_le_bytes());
        out.extend(self.leaves.iter().flatten());
    }

    fn decode_state(bytes: &[u8]) -> Result<Self, Self::PersistError> {
        let (base, leaves) = bytes.split_at_checked(BASE_LEN).ok_or(())?;
        if !leaves.len().is_multiple_of(LEAF_LEN) {
            return Err(());
        }
        Ok(Self {
            base: usize::try_from(u64::from_le_bytes(base.try_into().map_err(|_| ())?))
                .map_err(|_| ())?,
            leaves: leaves
                .chunks_exact(LEAF_LEN)
                .map(|leaf| leaf.try_into().map_err(|_| ()))
                .collect::<Result<_, _>>()?,
        })
    }
}

/// Canonical 32-byte leaf: block, log index, event, reserved. A verifier holding the
/// event rebuilds the leaf itself and checks it against the accumulator root.
fn leaf(pos: Position, event: u64) -> Hash {
    let mut bytes = [0u8; 32];
    bytes[..8].copy_from_slice(&pos.block.to_le_bytes());
    bytes[8..16].copy_from_slice(&pos.log_index.to_le_bytes());
    bytes[16..24].copy_from_slice(&event.to_le_bytes());
    bytes
}

/// Chain indexer over one home directory: chainfold folds the log, rotortree commits
/// the finalized prefix, and both recover from that same directory on the next open.
struct Indexer {
    driver: Driver<MerkleLog, ScriptedChain, Flusher<RealVfs>>,
    tree: RotorTree<Blake3Hasher, N, MAX_DEPTH>,
    /// Newest accumulator write, with the size it brought the accumulator to.
    pending: Option<(rotortree::DurabilityToken, usize)>,
}

impl Indexer {
    /// Opens both durability domains, resuming whatever they hold: the WAL replays the
    /// accumulator, the snapshot replays the cursor. A fresh directory starts at genesis.
    fn open(home: &Path, chain: ScriptedChain) -> Self {
        let tree = RotorTree::open(
            Blake3Hasher,
            RotorTreeConfig {
                path: home.join("accumulator"),
                flush_policy: FlushPolicy::default(),
                checkpoint_policy: CheckpointPolicy::OnClose,
                tiering: TieringConfig::default(),
                verify_checkpoint: true,
            },
        )
        .expect("accumulator opens cleanly");

        let store = StoreConfig {
            dir: home.join("cursor"),
            retain: 1,
        };
        let (store, recovered) =
            SnapshotStore::open(store, RealVfs).expect("store opens cleanly");
        let sink = Flusher::spawn(store, QUEUE_DEPTH);

        let engine = EngineConfig {
            ring_capacity: RING_CAPACITY,
            checkpoint_slots: CHECKPOINT_SLOTS,
        };
        let config = DriverConfig {
            checkpoint_interval: Some(CHECKPOINT_INTERVAL),
            snapshot_interval: Some(CHECKPOINT_INTERVAL),
            ..DriverConfig::default()
        };
        let driver = match recovered {
            Some(recovered) => Driver::resume_with_sink(
                Engine::decode_snapshot(&recovered.snapshot, engine)
                    .expect("snapshot decodes cleanly"),
                chain,
                sink,
                MerkleLog::default(),
                config,
            ),
            None => Driver::with_sink(MerkleLog::default(), chain, sink, engine, config),
        }
        .expect("driver configuration is valid");

        Self {
            driver,
            tree,
            pending: None,
        }
    }

    /// Ticks to completion, committing newly finalized leaves after each step and
    /// dropping from the fold whatever the accumulator has since fsynced.
    fn sync(&mut self) {
        loop {
            let tick = self.driver.tick();
            self.pending = self.commit().or(self.pending.take());
            self.prune();
            match tick {
                Tick::Idle => {
                    // at the tip there is time to fsync, and that is what lets the
                    // fold drop leaves; mid-catch-up it rides the flush interval
                    self.tree.flush().expect("accumulator flushes cleanly");
                    self.prune();
                    return;
                }
                Tick::RolledBack { to } => println!("  rolled back to {to:?}"),
                Tick::Progressed(_) | Tick::SourceError | Tick::DurabilityLost => {}
                // the scripted reorg stays inside the checkpoint window, so neither a
                // resync nor a terminal status is reachable here
                lost => panic!("engine cannot serve the fork: {lost:?}"),
            }
        }
    }

    /// Appends the leaves at or below the engine's durable point the accumulator lacks.
    ///
    /// Both watermarks are absolute leaf counts, so their gap is the whole
    /// reconciliation. An open can land with the accumulator ahead of the fold, because
    /// the snapshot is an older checkpoint, or behind it, because the last WAL writes
    /// were never fsynced; this one skip covers both, so neither domain has to persist
    /// a cursor into the other.
    fn commit(&self) -> Option<(rotortree::DurabilityToken, usize)> {
        let finalized = self.driver.engine().durable_fold()?.folded();
        let committed = self.size();
        if finalized <= committed {
            return None;
        }
        let log = self.driver.engine().fold();
        let (_root, token) = self
            .tree
            .insert_many(&log.leaves[committed - log.base..finalized - log.base])
            .expect("the accumulator accepts finalized leaves");
        Some((token, finalized))
    }

    /// Drops the fold's leaves the accumulator has fsynced, bounding what a checkpoint
    /// clones to the events still inside the finality window.
    fn prune(&mut self) {
        let Some((token, durable)) = &self.pending else {
            return;
        };
        if !token.is_durable() {
            return;
        }
        let durable = *durable;
        self.driver.engine_mut().fold_mut().prune(durable);
    }

    /// Leaves committed to the accumulator.
    fn size(&self) -> usize {
        usize::try_from(self.tree.size()).expect("accumulator size fits in usize")
    }

    /// Accumulator root over the finalized prefix.
    fn root(&self) -> Hash {
        self.tree.root().expect("the accumulator is non-empty")
    }

    /// The accumulator holds exactly a prefix of the fold's leaves, and only grew since
    /// (`size`, `root`): nothing at or below a durable point is ever rewritten, whatever
    /// the reorg and restart history. Both sides prune, so only their overlap is
    /// checkable, and the base guard proves nothing was dropped below it.
    fn assert_committed_prefix(&self, size: usize, root: Hash) {
        let log = self.driver.engine().fold();
        let snapshot = self.tree.snapshot();
        assert!(
            log.base <= self.size(),
            "the fold pruned past the accumulator"
        );
        for (offset, leaf) in log.leaves[..(self.size() - log.base).min(log.leaves.len())]
            .iter()
            .enumerate()
        {
            let index = log.base + offset;
            let committed = snapshot.get_node(0, index).expect("leaf index is in range");
            assert_eq!(committed, *leaf, "leaf {index} was rewritten");
        }
        assert!(
            snapshot
                .generate_consistency_proof(size as u64, root)
                .expect("the accumulator extends its committed prefix")
                .verify_transition(&Blake3Hasher, root)
                .expect("consistency proof is well formed")
        );
    }

    /// Closes both domains, fsyncing the accumulator before the flusher drains its
    /// queue, and hands the source back. A real source reconnects instead.
    fn close(mut self) -> ScriptedChain {
        if let Some((token, _)) = self.pending {
            token.wait();
        }
        self.tree.close().expect("accumulator closes cleanly");
        let chain = self.driver.source_mut().clone();
        self.driver
            .into_sink()
            .join()
            .expect("the flusher drains its queue cleanly");
        chain
    }
}

/// Pushes `blocks` blocks, two events on every second one.
fn extend(chain: &mut ScriptedChain, blocks: u64, tag: u64) {
    for block in 0..blocks {
        if block % 2 == 0 {
            chain.push_block(&[tag + block * 10, tag + block * 10 + 1]);
        } else {
            chain.push_block(&[]);
        }
    }
}

fn main() {
    let home = tempfile::tempdir().expect("temp directory is available");

    let mut chain = ScriptedChain::new(1);
    extend(&mut chain, 40, 0);
    // one event-bearing block per poll, so the checkpoint interval has room to act
    chain.set_window(1);

    let mut indexer = Indexer::open(home.path(), chain);
    indexer.sync();
    let (size, root) = (indexer.size(), indexer.root());
    indexer.assert_committed_prefix(size, root);
    println!(
        "caught up at {:?}: {} events folded, {size} committed",
        indexer.driver.engine().cursor(),
        indexer.driver.engine().fold().folded(),
    );

    // a reorg shallower than the checkpoint window, then the chain moves on
    let chain = indexer.driver.source_mut();
    chain.reorg(3, &[&[9_000, 9_001], &[], &[9_010]]);
    extend(chain, 16, 9_100);
    indexer.sync();
    indexer.assert_committed_prefix(size, root);
    println!(
        "reorg absorbed: {size} -> {} leaves committed, consistency proven",
        indexer.size(),
    );

    // restart: both domains recover from the same home directory
    let view = indexer.driver.engine().fold().folded();
    let (size, root) = (indexer.size(), indexer.root());
    let chain = indexer.close();

    let mut indexer = Indexer::open(home.path(), chain);
    assert_eq!((indexer.size(), indexer.root()), (size, root));
    println!("reopened: {size} leaves recovered from the WAL");

    // the fold converged, and replaying it committed nothing the accumulator held
    indexer.sync();
    assert_eq!(indexer.driver.engine().fold().folded(), view);
    indexer.assert_committed_prefix(size, root);
    println!(
        "converged: {} leaves committed, {} retained by the fold",
        indexer.size(),
        indexer.driver.engine().fold().leaves.len(),
    );
    indexer.close();
}
