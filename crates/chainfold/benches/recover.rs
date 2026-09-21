//! Fork recovery cost: the tick that detects a reorg, bisects, and rolls back, then the
//! refold that brings the cursor back to the tip.
//!
//! Engine and driver settings are the ones one of our settlement PoCs runs: a 1024
//! block ring, four checkpoint slots, a checkpoint every 64 blocks. The chain is long
//! enough that the ring has wrapped, so bisection searches a full window.

use std::hint::black_box;

use chainfold::{
    BlockRef,
    Driver,
    DriverConfig,
    EngineConfig,
    ReplayHorizon,
    Source,
    Tick,
    test_util::{
        PollFailure,
        RecordingFold,
        ScriptedChain,
    },
};
use criterion::{
    BatchSize,
    Criterion,
    Throughput,
};

/// Observed-block ring window.
const RING_CAPACITY: usize = 1024;
/// Retained rollback points.
const CHECKPOINT_SLOTS: usize = 4;
/// Blocks of cursor progress between checkpoints, and blocks per poll while catching
/// up, so a checkpoint lands on every catch-up tick.
const CHECKPOINT_INTERVAL: u64 = 64;
/// Blocks folded before the reorg: past a full ring, with the cursor 32 blocks after
/// the last checkpoint rather than on it.
const BLOCKS: u64 = RING_CAPACITY as u64 + 5 * CHECKPOINT_INTERVAL + 32;
/// Events per block in the end-to-end recovery matrix.
const EVENTS_PER_BLOCK: u64 = 4;
/// Reorg depths: the common one-block case, the seven-block mainnet reorg of May 2022,
/// one checkpoint interval, and one deep inside the retained window.
const DEPTHS: [usize; 4] = [1, 7, 64, 200];
/// Events per block in the rollback matrix; the fold clone at rollback scales with the
/// entries the fold holds, which is blocks times events per block.
const FOLD_DENSITIES: [u64; 2] = [1, 64];

/// Scripted chain that counts `header_at` calls, the reads a recovery spends on a node.
struct Probed {
    inner: ScriptedChain,
    probes: u64,
}

impl Source for Probed {
    type Error = PollFailure;
    type Event = u64;

    fn head(&mut self) -> Result<u64, PollFailure> {
        self.inner.head()
    }

    fn header_at(&mut self, number: u64) -> Result<Option<BlockRef>, PollFailure> {
        self.probes += 1;
        self.inner.header_at(number)
    }

    fn events_in(
        &mut self,
        from: u64,
        to: u64,
        out: &mut Vec<(BlockRef, u32, u64)>,
    ) -> Result<(), PollFailure> {
        self.inner.events_in(from, to, out)
    }

    fn horizon(&self) -> ReplayHorizon {
        self.inner.horizon()
    }

    fn window(&self) -> u64 {
        self.inner.window()
    }
}

type Indexer = Driver<RecordingFold, Probed>;

fn events(block: u64, per_block: u64) -> Vec<u64> {
    (0..per_block).map(|i| block * per_block + i).collect()
}

/// Folds `BLOCKS` blocks to the tip, then reorgs the last `depth` of them for `depth + 1`
/// replacements, so the head also advances by one.
fn reorged(depth: usize, per_block: u64) -> Indexer {
    let mut chain = ScriptedChain::new(1);
    for block in 1..=BLOCKS {
        chain.push_block(&events(block, per_block));
    }
    chain.set_window(CHECKPOINT_INTERVAL);
    let mut driver = Driver::new(
        RecordingFold::default(),
        Probed {
            inner: chain,
            probes: 0,
        },
        EngineConfig {
            ring_capacity: RING_CAPACITY,
            checkpoint_slots: CHECKPOINT_SLOTS,
        },
        DriverConfig {
            checkpoint_interval: Some(CHECKPOINT_INTERVAL),
            snapshot_interval: None,
            ..DriverConfig::from_block(1)
        },
    )
    .expect("driver configuration is valid");
    while driver.tick() != Tick::Idle {}
    assert_eq!(driver.engine().checkpoint_count(), CHECKPOINT_SLOTS);

    let depth_u64 = u64::try_from(depth).expect("depth fits in u64");
    let replacements: Vec<Vec<u64>> = (0..=depth_u64)
        .map(|i| events(BLOCKS + 1 + i, per_block))
        .collect();
    let slices: Vec<&[u64]> = replacements.iter().map(Vec::as_slice).collect();
    let source = driver.source_mut();
    source.inner.reorg(depth, &slices);
    source.probes = 0;
    driver
}

/// One tick: boundary mismatch, bisection, rollback to a retained checkpoint.
fn roll_back(driver: &mut Indexer) {
    assert!(matches!(driver.tick(), Tick::RolledBack { .. }));
}

/// Rollback, then refold to the new tip. Returns the events the fold re-applied.
fn recover(driver: &mut Indexer) -> u64 {
    roll_back(driver);
    let mut replayed = 0;
    loop {
        match driver.tick() {
            Tick::Progressed(summary) => replayed += summary.applied,
            Tick::Idle => return replayed,
            other => panic!("recovery took an unexpected path: {other:?}"),
        }
    }
}

fn bench_recover(c: &mut Criterion) {
    let mut group = c.benchmark_group("chainfold::recover");
    for depth in DEPTHS {
        let mut probe = reorged(depth, EVENTS_PER_BLOCK);
        let replayed = recover(&mut probe);
        group.throughput(Throughput::Elements(replayed));
        group.bench_function(format!("depth={depth} replayed={replayed}"), |b| {
            b.iter_batched(
                || reorged(depth, EVENTS_PER_BLOCK),
                |mut driver| black_box(recover(&mut driver)),
                BatchSize::PerIteration,
            );
        });
    }
    group.finish();
}

fn bench_rollback(c: &mut Criterion) {
    let mut group = c.benchmark_group("chainfold::rollback");
    for per_block in FOLD_DENSITIES {
        let entries = BLOCKS * per_block;
        group.bench_function(format!("depth=1 fold_entries={entries}"), |b| {
            b.iter_batched(
                || reorged(1, per_block),
                |mut driver| roll_back(black_box(&mut driver)),
                BatchSize::PerIteration,
            );
        });
    }
    group.finish();
}

fn main() {
    // Node reads per recovery, independent of timing: one boundary header, then the
    // bisection over the observed ring.
    for depth in DEPTHS {
        let mut driver = reorged(depth, EVENTS_PER_BLOCK);
        roll_back(&mut driver);
        let probes = driver.source_mut().probes;
        println!(
            "ring={RING_CAPACITY} depth={depth}: {probes} header_at calls to roll back"
        );
    }

    let mut criterion = Criterion::default().configure_from_args();
    bench_recover(&mut criterion);
    bench_rollback(&mut criterion);
    criterion.final_summary();
}
