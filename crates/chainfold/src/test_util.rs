//! Test helpers: scripted folds and a scripted chain source for the engine and driver.

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::vec::Vec;

use core::fmt;

use crate::{
    batch::Batch,
    engine::Engine,
    error::{
        DurabilityLost,
        FoldError,
    },
    fold::Fold,
    position::{
        BlockRef,
        Position,
    },
    sink::SnapshotSink,
    source::{
        EventSource,
        ProbeSource,
        ReplayHorizon,
    },
};

/// Fold that records every applied event and can fail on a scripted position.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct RecordingFold {
    /// Every position the fold accepted, with its event.
    pub applied: Vec<(Position, u64)>,
    /// Position the fold fails at, and how.
    pub fail_at: Option<(Position, FailKind)>,
}

/// Scripted failure the recording fold raises at its `fail_at` position.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FailKind {
    /// Declares the event not mine.
    Skip,
    /// Refuses the event with clean state below it.
    Halt,
    /// Records the event, then refuses it.
    Poison,
}

impl Fold for RecordingFold {
    type Event = u64;
    type View = Vec<(Position, u64)>;
    type Error = FailKind;

    fn apply(
        &mut self,
        pos: Position,
        event: &Self::Event,
    ) -> Result<(), FoldError<FailKind>> {
        if let Some((scripted_pos, kind)) = self.fail_at
            && scripted_pos == pos
        {
            return match kind {
                FailKind::Skip => Err(FoldError::Skip(kind)),
                FailKind::Halt => Err(FoldError::Halt(kind)),
                FailKind::Poison => {
                    self.applied.push((pos, *event));
                    Err(FoldError::Poison(kind))
                }
            };
        }
        self.applied.push((pos, *event));
        Ok(())
    }

    fn view(&self) -> Self::View {
        self.applied.clone()
    }
}

#[cfg(feature = "wincode")]
#[cfg_attr(docsrs, doc(cfg(feature = "wincode")))]
impl crate::snapshot::Persist for RecordingFold {
    const STATE_TAG: &'static str = "chainfold.test.recording";
    type PersistError = ();

    fn encode_state(&self, out: &mut Vec<u8>) {
        let count =
            u64::try_from(self.applied.len()).expect("recorded entry count fits in u64");
        out.reserve(8 + 24 * self.applied.len());
        out.extend_from_slice(&count.to_le_bytes());
        for (pos, event) in &self.applied {
            out.extend_from_slice(&pos.block.to_le_bytes());
            out.extend_from_slice(&pos.log_index.to_le_bytes());
            out.extend_from_slice(&event.to_le_bytes());
        }
    }

    fn decode_state(bytes: &[u8]) -> Result<Self, Self::PersistError> {
        const ENTRY_LEN: usize = 24;
        let (count, entries) = bytes.split_first_chunk::<8>().ok_or(())?;
        let count = usize::try_from(u64::from_le_bytes(*count)).map_err(|_| ())?;
        if entries.len() != count.checked_mul(ENTRY_LEN).ok_or(())? {
            return Err(());
        }
        // The length check above makes every chunk exactly three 8-byte lanes.
        let lane = |e: &[u8], i: usize| {
            u64::from_le_bytes(e[i * 8..][..8].try_into().expect("three lanes"))
        };
        let entry = |e: &[u8]| (Position::new(lane(e, 0), lane(e, 1)), lane(e, 2));
        Ok(Self {
            applied: entries.chunks_exact(ENTRY_LEN).map(entry).collect(),
            fail_at: None,
        })
    }
}

/// Zero-state fold for overhead and allocation measurements.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct NoopFold;

impl Fold for NoopFold {
    type Event = u64;
    type View = ();
    type Error = core::convert::Infallible;

    fn apply(
        &mut self,
        _pos: Position,
        _event: &Self::Event,
    ) -> Result<(), FoldError<Self::Error>> {
        Ok(())
    }

    fn view(&self) -> Self::View {}
}

/// Sink recording each accepted offer's durable point; fails scripted offers.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct WatermarkSink {
    /// Durable point of every accepted offer, in offer order.
    pub offered: Vec<Position>,
    /// Offers still scripted to fail before the sink accepts again.
    pub fail_next_offers: u32,
}

impl<F: Fold> SnapshotSink<F> for WatermarkSink {
    fn offer(&mut self, engine: &Engine<F>) -> Result<(), DurabilityLost> {
        if self.fail_next_offers > 0 {
            self.fail_next_offers -= 1;
            return Err(DurabilityLost);
        }
        if let Some(point) = engine.durable_point() {
            self.offered.push(point);
        }
        Ok(())
    }

    fn durable_cursor(&self) -> Option<Position> {
        self.offered.last().copied()
    }
}

/// Number of splitmix64 lanes composing a block hash.
const HASH_LANES: usize = 4;
/// Byte width of one hash lane.
const LANE_BYTES: usize = 8;
/// Sentinel batch_blocks value meaning no cap on event-bearing blocks per poll.
const UNBOUNDED_BATCH_BLOCKS: usize = usize::MAX;

/// One splitmix64 mixing step, the building block of the ancestry-committing hash.
fn splitmix64(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9e3779b97f4a7c15);
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94d049bb133111eb);
    x ^ (x >> 31)
}

/// Derives a block hash from its parent hash, number, and salt across four lanes.
fn block_hash(parent_hash: [u8; 32], number: u64, salt: u64) -> [u8; 32] {
    let mut hash = [0u8; 32];
    for lane in 0..HASH_LANES {
        let lane_index = u64::try_from(lane).expect("lane index fits in u64");
        let offset = lane * LANE_BYTES;
        let parent_lane = u64::from_le_bytes(
            parent_hash[offset..offset + LANE_BYTES]
                .try_into()
                .expect("lane slice is exactly 8 bytes"),
        );
        let value = splitmix64(parent_lane ^ number ^ salt ^ lane_index);
        hash[offset..offset + LANE_BYTES].copy_from_slice(&value.to_le_bytes());
    }
    hash
}

/// One recorded block: identity, ancestry-committing hash, and its event payload.
#[derive(Debug, Clone)]
struct ScriptedBlock {
    number: u64,
    hash: [u8; 32],
    events: Vec<u64>,
}

/// In-memory chain with deterministic ancestry-committing hashes and reorg injection.
#[derive(Debug, Clone)]
pub struct ScriptedChain {
    first_block: u64,
    blocks: Vec<ScriptedBlock>,
    next_salt: u64,
    horizon: ReplayHorizon,
    batch_blocks: usize,
    pending_failures: u32,
}

/// Error returned by a scripted poll that consumed its injected failure budget.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PollFailure;

impl fmt::Display for PollFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "scripted chain poll failed")
    }
}

impl core::error::Error for PollFailure {}

impl ScriptedChain {
    /// Builds an empty chain whose first pushed block is numbered `first_block`.
    pub fn new(first_block: u64) -> Self {
        Self {
            first_block,
            blocks: Vec::new(),
            next_salt: 0,
            horizon: ReplayHorizon::Genesis,
            batch_blocks: UNBOUNDED_BATCH_BLOCKS,
            pending_failures: 0,
        }
    }

    /// Appends a block carrying the given events, hashed from the tip and a fresh salt.
    pub fn push_block(&mut self, events: &[u64]) {
        let pushed = u64::try_from(self.blocks.len()).expect("block count fits in u64");
        let number = self
            .first_block
            .checked_add(pushed)
            .expect("block number overflow");
        let parent_hash = self.blocks.last().map_or([0u8; 32], |block| block.hash);
        let salt = self.next_salt;
        self.next_salt = self
            .next_salt
            .checked_add(1)
            .expect("salt counter overflow");
        let hash = block_hash(parent_hash, number, salt);
        self.blocks.push(ScriptedBlock {
            number,
            hash,
            events: events.to_vec(),
        });
    }

    /// Replaces the last depth blocks; hashes of all replacements change.
    pub fn reorg(&mut self, depth: usize, replacements: &[&[u64]]) {
        let keep = self.blocks.len().saturating_sub(depth);
        self.blocks.truncate(keep);
        for events in replacements {
            self.push_block(events);
        }
    }

    /// Current tip header, or None for an empty chain.
    pub fn tip(&self) -> Option<BlockRef> {
        self.blocks.last().map(|block| BlockRef {
            number: block.number,
            hash: block.hash,
        })
    }

    /// Header for an exact block number if it exists on the current chain.
    pub fn header(&self, number: u64) -> Option<BlockRef> {
        let offset = number.checked_sub(self.first_block)?;
        let index = usize::try_from(offset).ok()?;
        self.blocks.get(index).map(|block| BlockRef {
            number: block.number,
            hash: block.hash,
        })
    }

    /// Sets the horizon the chain reports through `EventSource::horizon`.
    pub fn set_horizon(&mut self, horizon: ReplayHorizon) {
        self.horizon = horizon;
    }

    /// Caps the event-bearing blocks served per poll.
    pub fn set_batch_blocks(&mut self, blocks: usize) {
        self.batch_blocks = blocks;
    }

    /// The next n polls return PollFailure.
    pub fn fail_next_polls(&mut self, n: u32) {
        self.pending_failures = n;
    }
}

impl EventSource for ScriptedChain {
    type Event = u64;
    type Error = PollFailure;

    fn next_batch(
        &mut self,
        cursor: Option<Position>,
        out: &mut Batch<Self::Event>,
    ) -> Result<(), Self::Error> {
        if self.pending_failures > 0 {
            self.pending_failures -= 1;
            return Err(PollFailure);
        }
        out.clear();
        let start_number = match cursor {
            Some(pos) => {
                out.boundary = self.header(pos.block);
                pos.block.checked_add(1).expect("cursor block at u64::MAX")
            }
            None => self.first_block,
        };
        let mut served = 0usize;
        for block in &self.blocks {
            if block.number < start_number || block.events.is_empty() {
                continue;
            }
            if served >= self.batch_blocks {
                break;
            }
            out.push_block(
                BlockRef {
                    number: block.number,
                    hash: block.hash,
                },
                block.events.iter().enumerate().map(|(index, event)| {
                    (u32::try_from(index).expect("log index fits in u32"), *event)
                }),
            );
            served += 1;
        }
        Ok(())
    }

    fn horizon(&self) -> ReplayHorizon {
        self.horizon
    }
}

impl ProbeSource for ScriptedChain {
    fn header_at(&mut self, number: u64) -> Result<Option<BlockRef>, Self::Error> {
        if self.pending_failures > 0 {
            self.pending_failures -= 1;
            return Err(PollFailure);
        }
        Ok(self.header(number))
    }
}

#[cfg(feature = "storage")]
use std::{
    collections::BTreeMap,
    io,
    path::{
        Path,
        PathBuf,
    },
};

#[cfg(feature = "storage")]
use crate::storage::Vfs;

/// One file's content, split into what a crash discards and what fsync kept.
#[cfg(feature = "storage")]
#[derive(Debug, Clone, Default)]
struct CrashFileBytes {
    durable: Vec<u8>,
    volatile: Vec<u8>,
}

/// In-memory Vfs with fsync-accurate durability and crash injection.
#[cfg(feature = "storage")]
#[cfg_attr(docsrs, doc(cfg(feature = "storage")))]
#[derive(Debug, Default)]
pub struct CrashVfs {
    files: BTreeMap<u64, CrashFileBytes>,
    durable_names: BTreeMap<PathBuf, u64>,
    volatile_names: BTreeMap<PathBuf, u64>,
    next_inode: u64,
    budget: Option<u32>,
    torn_len: usize,
    op_count: u32,
}

#[cfg(feature = "storage")]
fn crash_budget_error() -> io::Error {
    io::Error::other("crash budget exhausted")
}

#[cfg(feature = "storage")]
fn crash_not_found_error() -> io::Error {
    io::Error::new(io::ErrorKind::NotFound, "path not found")
}

#[cfg(feature = "storage")]
#[cfg_attr(docsrs, doc(cfg(feature = "storage")))]
impl CrashVfs {
    /// Builds a fresh, empty CrashVfs that never crashes.
    pub fn new() -> Self {
        Self::default()
    }

    /// Mutating ops error with ErrorKind::Other once the budget is spent; the
    /// crashing write persists only torn_len bytes of its volatile effect.
    pub fn with_crash_budget(ops: u32, torn_len: usize) -> Self {
        Self {
            budget: Some(ops),
            torn_len,
            ..Self::default()
        }
    }

    /// Discards all volatile state, keeping only what fsync made durable.
    pub fn crash(&mut self) {
        self.volatile_names.clone_from(&self.durable_names);
        for file in self.files.values_mut() {
            file.volatile.clone_from(&file.durable);
        }
    }

    /// Number of mutating op attempts made so far, crashing or not.
    pub fn op_count(&self) -> u32 {
        self.op_count
    }

    /// Consumes one unit of crash budget; true means this call is the crashing one.
    fn consume_budget(&mut self) -> bool {
        self.op_count = self.op_count.wrapping_add(1);
        match &mut self.budget {
            None => false,
            Some(0) => true,
            Some(remaining) => {
                *remaining -= 1;
                false
            }
        }
    }

    /// Consumes budget and reports how much of a `len`-byte effect this call keeps.
    fn torn_write(&mut self, len: usize) -> (bool, usize) {
        let crashing = self.consume_budget();
        (
            crashing,
            if crashing {
                len.min(self.torn_len)
            } else {
                len
            },
        )
    }

    /// Maps a crash flag onto the io result every mutating op returns.
    fn outcome(crashing: bool) -> io::Result<()> {
        if crashing {
            Err(crash_budget_error())
        } else {
            Ok(())
        }
    }

    /// Resolves the inode a write targets, allocating a fresh one for a new name.
    fn inode_for_write(&mut self, path: &Path) -> u64 {
        if let Some(&inode) = self.volatile_names.get(path) {
            inode
        } else {
            let inode = self.next_inode;
            self.next_inode += 1;
            self.files.insert(inode, CrashFileBytes::default());
            self.volatile_names.insert(path.to_path_buf(), inode);
            inode
        }
    }
}

#[cfg(feature = "storage")]
#[cfg_attr(docsrs, doc(cfg(feature = "storage")))]
impl Vfs for CrashVfs {
    fn create_dir_all(&mut self, _path: &Path) -> io::Result<()> {
        Ok(())
    }

    fn read(&mut self, path: &Path) -> io::Result<Vec<u8>> {
        let inode = *self
            .volatile_names
            .get(path)
            .ok_or_else(crash_not_found_error)?;
        Ok(self.files[&inode].volatile.clone())
    }

    fn write(&mut self, path: &Path, bytes: &[u8]) -> io::Result<()> {
        let inode = self.inode_for_write(path);
        let (crashing, keep) = self.torn_write(bytes.len());
        self.files
            .get_mut(&inode)
            .expect("write always registers its inode first")
            .volatile = bytes[..keep].to_vec();
        Self::outcome(crashing)
    }

    fn write_at(&mut self, path: &Path, offset: u64, bytes: &[u8]) -> io::Result<()> {
        let inode = self.inode_for_write(path);
        let (crashing, keep) = self.torn_write(bytes.len());
        let offset =
            usize::try_from(offset).expect("offset fits in memory on this platform");
        let file = self
            .files
            .get_mut(&inode)
            .expect("write_at always registers its inode first");
        let needed = offset + keep;
        if file.volatile.len() < needed {
            file.volatile.resize(needed, 0);
        }
        file.volatile[offset..needed].copy_from_slice(&bytes[..keep]);
        Self::outcome(crashing)
    }

    fn fsync_file(&mut self, path: &Path) -> io::Result<()> {
        let inode = *self
            .volatile_names
            .get(path)
            .ok_or_else(crash_not_found_error)?;
        let target_len = self.files[&inode].volatile.len();
        let (crashing, keep) = self.torn_write(target_len);
        let file = self
            .files
            .get_mut(&inode)
            .expect("fsync_file always resolves a registered inode");
        if file.durable.len() < target_len {
            file.durable.resize(target_len, 0);
        }
        file.durable[..keep].copy_from_slice(&file.volatile[..keep]);
        Self::outcome(crashing)
    }

    fn rename(&mut self, from: &Path, to: &Path) -> io::Result<()> {
        let inode = self
            .volatile_names
            .remove(from)
            .ok_or_else(crash_not_found_error)?;
        let crashing = self.consume_budget();
        let name = if crashing { from } else { to };
        self.volatile_names.insert(name.to_path_buf(), inode);
        Self::outcome(crashing)
    }

    fn remove(&mut self, path: &Path) -> io::Result<()> {
        let inode = self
            .volatile_names
            .remove(path)
            .ok_or_else(crash_not_found_error)?;
        let crashing = self.consume_budget();
        if crashing {
            self.volatile_names.insert(path.to_path_buf(), inode);
        }
        Self::outcome(crashing)
    }

    fn list(&mut self, dir: &Path) -> io::Result<Vec<PathBuf>> {
        Ok(self
            .volatile_names
            .keys()
            .filter(|path| path.parent() == Some(dir))
            .cloned()
            .collect())
    }

    fn fsync_dir(&mut self, path: &Path) -> io::Result<()> {
        let crashing = self.consume_budget();
        if crashing {
            return Err(crash_budget_error());
        }
        self.durable_names
            .retain(|name, _| name.parent() != Some(path));
        for (name, inode) in &self.volatile_names {
            if name.parent() == Some(path) {
                self.durable_names.insert(name.clone(), *inode);
            }
        }
        Ok(())
    }

    fn exists(&mut self, path: &Path) -> io::Result<bool> {
        Ok(self.volatile_names.contains_key(path))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        batch::Batch,
        fold::Fold,
        position::{
            BlockRef,
            Position,
        },
        source::{
            EventSource,
            ProbeSource,
        },
    };
    #[cfg(not(feature = "std"))]
    use alloc::vec;
    #[cfg(feature = "std")]
    use std::vec;

    #[test]
    fn recording_fold_records_in_order() {
        // given three applies at ascending positions
        let mut fold = RecordingFold::default();
        let positions = [
            Position::new(1, 0),
            Position::new(1, 1),
            Position::new(2, 0),
        ];
        // when applied
        for (index, pos) in positions.iter().enumerate() {
            fold.apply(*pos, &(index as u64)).unwrap();
        }
        // then entries match in order
        assert_eq!(
            fold.view(),
            vec![(positions[0], 0), (positions[1], 1), (positions[2], 2)]
        );
    }

    #[test]
    fn recording_fold_poison_mutates_before_failing() {
        // given fail_at Poison at block 1 log index 0
        let pos = Position::new(1, 0);
        let mut fold = RecordingFold {
            applied: Vec::new(),
            fail_at: Some((pos, FailKind::Poison)),
        };
        // when applied at that position
        let result = fold.apply(pos, &42);
        // then the error is Poison and the entry was recorded
        assert!(matches!(
            result,
            Err(crate::error::FoldError::Poison(FailKind::Poison))
        ));
        assert_eq!(fold.view(), vec![(pos, 42)]);
    }

    #[test]
    fn noop_fold_never_errors() {
        // given any event applied to a fresh NoopFold
        let mut fold = NoopFold;
        // when applied
        let result = fold.apply(Position::new(1, 0), &7);
        // then Ok and view is unit
        assert_eq!(result, Ok(()));
        assert_eq!(fold.view(), ());
    }

    #[test]
    fn hashes_commit_to_ancestry() {
        // given ten blocks on a scripted chain
        let mut chain = ScriptedChain::new(1);
        for _ in 0..10 {
            chain.push_block(&[]);
        }
        let before: Vec<BlockRef> = (1..=9).map(|n| chain.header(n).unwrap()).collect();
        // when block 4 is replaced by a reorg
        chain.reorg(7, &[&[], &[], &[], &[], &[], &[]]);
        // then headers 4..=9 all change and headers 1..=3 are unchanged
        for n in 1..=3u64 {
            assert_eq!(chain.header(n), Some(before[(n - 1) as usize]));
        }
        for n in 4..=9u64 {
            assert_ne!(chain.header(n).unwrap().hash, before[(n - 1) as usize].hash);
        }
    }

    #[test]
    fn batches_deliver_whole_blocks_after_cursor() {
        // given events on blocks 2, 5, 9 and a cursor at block 5's last event
        let mut chain = ScriptedChain::new(1);
        chain.push_block(&[]);
        chain.push_block(&[10, 11]);
        chain.push_block(&[]);
        chain.push_block(&[]);
        chain.push_block(&[20, 21]);
        chain.push_block(&[]);
        chain.push_block(&[]);
        chain.push_block(&[]);
        chain.push_block(&[30, 31]);
        let cursor = Position::new(5, 1);
        let mut batch = Batch::new();
        // when polled
        chain.next_batch(Some(cursor), &mut batch).unwrap();
        // then one span for block 9 with the complete event set
        assert_eq!(batch.span_count(), 1);
        let span = batch.spans().next().expect("one span");
        assert_eq!(span.number, 9);
        let events: Vec<u64> = span.events.to_vec();
        assert_eq!(events, vec![30, 31]);
    }

    #[test]
    fn boundary_reports_current_header_of_cursor_block() {
        // given a cursor on block 5
        let mut chain = ScriptedChain::new(1);
        for _ in 0..6 {
            chain.push_block(&[1]);
        }
        let cursor = Position::new(5, 0);
        // when the chain reorgs at block 4 and is polled
        chain.reorg(3, &[&[1], &[1], &[1]]);
        let new_header = chain.header(5).unwrap();
        let mut batch = Batch::new();
        chain.next_batch(Some(cursor), &mut batch).unwrap();
        // then boundary is block 5's new header
        assert_eq!(batch.boundary, Some(new_header));
    }

    #[test]
    fn boundary_is_none_when_chain_is_shorter_than_cursor() {
        // given a reorg that shortens the chain below the cursor
        let mut chain = ScriptedChain::new(1);
        for _ in 0..6 {
            chain.push_block(&[1]);
        }
        let cursor = Position::new(5, 0);
        chain.reorg(4, &[&[1]]);
        let mut batch = Batch::new();
        // when polled
        chain.next_batch(Some(cursor), &mut batch).unwrap();
        // then boundary None
        assert_eq!(batch.boundary, None);
    }

    #[test]
    fn batch_blocks_caps_spans_per_poll() {
        // given five event-bearing blocks and batch_blocks 2
        let mut chain = ScriptedChain::new(1);
        for i in 0..5u64 {
            chain.push_block(&[i]);
        }
        chain.set_batch_blocks(2);
        let mut batch = Batch::new();
        // when polled
        chain.next_batch(None, &mut batch).unwrap();
        // then two spans
        assert_eq!(batch.span_count(), 2);
    }

    #[test]
    fn empty_batch_signals_caught_up() {
        // given a cursor at the tip
        let mut chain = ScriptedChain::new(1);
        chain.push_block(&[1]);
        chain.push_block(&[2]);
        let tip = Position::new(2, 0);
        let mut batch = Batch::new();
        // when polled
        chain.next_batch(Some(tip), &mut batch).unwrap();
        // then no spans
        assert!(batch.is_empty());
    }

    #[test]
    fn header_at_beyond_tip_is_none() {
        // given a ten-block chain
        let mut chain = ScriptedChain::new(1);
        for _ in 0..10 {
            chain.push_block(&[]);
        }
        // when probing number 50
        let result = chain.header_at(50);
        // then Ok(None)
        assert_eq!(result, Ok(None));
    }

    #[test]
    fn scripted_failures_surface_then_clear() {
        // given fail_next_polls 2
        let mut chain = ScriptedChain::new(1);
        chain.push_block(&[1]);
        chain.fail_next_polls(2);
        let mut batch = Batch::new();
        // when polling three times
        let first = chain.next_batch(None, &mut batch);
        let second = chain.next_batch(None, &mut batch);
        let third = chain.next_batch(None, &mut batch);
        // then two errors then success
        assert_eq!(first, Err(PollFailure));
        assert_eq!(second, Err(PollFailure));
        assert_eq!(third, Ok(()));
    }
}
