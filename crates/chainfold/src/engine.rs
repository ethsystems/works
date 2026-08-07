use crate::{
    batch::{
        Batch,
        BlockSpan,
        LogEvent,
    },
    checkpoint::{
        CheckpointRing,
        Slot,
    },
    error::{
        ApplyError,
        ConfigError,
        DivergenceCause,
        EngineStatus,
        FoldError,
        RollbackError,
    },
    fold::Fold,
    position::{
        BlockRef,
        Position,
    },
    ring::{
        BlockRing,
        Observed,
    },
};

/// Smallest allowed observed-block ring capacity.
const MIN_RING_CAPACITY: usize = 2;
/// Largest allowed observed-block ring capacity.
const MAX_RING_CAPACITY: usize = 1 << 20;

/// Fixed engine construction parameters.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EngineConfig {
    /// Observed-block window W; power of two between 2 and 1 << 20.
    pub ring_capacity: usize,
    /// Retained checkpoint slots K; zero disables rollback.
    pub checkpoint_slots: usize,
}

impl EngineConfig {
    /// Accepts a power-of-two ring capacity within the allowed range.
    pub(crate) fn validate(&self) -> Result<(), ConfigError> {
        if !self.ring_capacity.is_power_of_two() {
            return Err(ConfigError::RingCapacityNotPowerOfTwo {
                got: self.ring_capacity,
            });
        }
        if !(MIN_RING_CAPACITY..=MAX_RING_CAPACITY).contains(&self.ring_capacity) {
            return Err(ConfigError::RingCapacityOutOfRange {
                got: self.ring_capacity,
            });
        }
        Ok(())
    }
}

/// Per-batch counts of applied, deduped, and skipped events.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct ApplySummary {
    /// Events the fold accepted.
    pub applied: u64,
    /// Events at or below the cursor, dropped as already applied.
    pub deduped: u64,
    /// Events the fold declared not its own.
    pub skipped: u64,
}

/// Single-writer fold engine: ordering, dedup, fork detection, rollback, snapshots.
///
/// When the cursor is set, the ring's newest entry is the cursor block.
#[derive(Debug)]
pub struct Engine<F> {
    fold: F,
    cursor: Option<Position>,
    ring: BlockRing,
    checkpoints: CheckpointRing<F>,
    status: EngineStatus,
    last_verified: Option<BlockRef>,
    skips: u64,
}

impl<F: Fold> Engine<F> {
    /// Builds an engine with an empty ring and no retained checkpoints.
    pub fn new(fold: F, config: EngineConfig) -> Result<Self, ConfigError> {
        config.validate()?;
        Ok(Self {
            ring: BlockRing::with_capacity(config.ring_capacity),
            checkpoints: CheckpointRing::new(config.checkpoint_slots),
            fold,
            cursor: None,
            status: EngineStatus::Active,
            last_verified: None,
            skips: 0,
        })
    }

    /// Returns the coarse engine status.
    pub fn status(&self) -> EngineStatus {
        self.status
    }

    /// Returns the most recently applied position, if any.
    pub fn cursor(&self) -> Option<Position> {
        self.cursor
    }

    /// Most recent block whose hash the source confirmed; None until first confirmation.
    pub fn last_verified(&self) -> Option<BlockRef> {
        self.last_verified
    }

    /// Count of events the fold declared not its own.
    pub fn skip_count(&self) -> u64 {
        self.skips
    }

    /// Count of checkpoints currently retained.
    pub fn checkpoint_count(&self) -> usize {
        self.checkpoints.count()
    }

    /// Cursor of the oldest retained checkpoint; the reorg-safe durable point.
    /// None without checkpoints or when the oldest slot predates any applied event.
    pub fn durable_point(&self) -> Option<Position> {
        self.checkpoints.oldest().and_then(|slot| slot.cursor)
    }

    /// Oldest retained checkpoint slot, for the snapshot codec.
    #[cfg(feature = "wincode")]
    pub(crate) fn oldest_checkpoint(&self) -> Option<&Slot<F>> {
        self.checkpoints.oldest()
    }

    /// Borrows the fold state.
    pub fn fold(&self) -> &F {
        &self.fold
    }

    /// Reads the fold's current view.
    pub fn view(&self) -> F::View {
        self.fold.view()
    }

    /// Iterates observed blocks oldest first.
    pub fn observed(&self) -> Observed<'_> {
        self.ring.iter()
    }

    /// Applies one poll's batch: total order, dedup, boundary recheck, fork detection.
    pub fn apply_batch(
        &mut self,
        batch: &Batch<F::Event>,
    ) -> Result<ApplySummary, ApplyError<F::Error>> {
        if !self.status.is_active() {
            return Err(ApplyError::NotActive {
                status: self.status,
            });
        }
        batch.validate().map_err(ApplyError::Shape)?;

        if let Some(cursor) = self.cursor {
            let boundary = batch.boundary.ok_or(ApplyError::MissingBoundary)?;
            if boundary.number != cursor.block {
                return Err(ApplyError::BoundaryNumberMismatch {
                    expected: cursor.block,
                    got: boundary.number,
                });
            }
            let observed_hash = self.ring.hash_at(cursor.block).ok_or(
                ApplyError::CursorBlockUnobserved {
                    block: cursor.block,
                },
            )?;
            if observed_hash != boundary.hash {
                return Err(fork_suspected(cursor.block, observed_hash, boundary));
            }
            self.last_verified = Some(boundary);
        }

        let mut summary = ApplySummary::default();
        for span in &batch.spans {
            let redelivered = self
                .cursor
                .is_some_and(|cursor| span.block.number <= cursor.block);
            if redelivered
                && let Some(observed_hash) = self.ring.hash_at(span.block.number)
                && observed_hash != span.block.hash
            {
                return Err(fork_suspected(span.block.number, observed_hash, span.block));
            }
            self.apply_span(span, batch, &mut summary)?;
        }

        Ok(summary)
    }

    /// Stores a checkpoint of the current fold, cursor, and ring.
    ///
    /// A no-op with zero slots or a non-Active status, so every stored slot holds
    /// state the engine still trusts.
    pub fn checkpoint(&mut self)
    where
        F: Clone,
    {
        if !self.status.is_active() {
            return;
        }
        self.checkpoints.store(Slot {
            fold: self.fold.clone(),
            cursor: self.cursor,
            ring: self.ring.clone(),
        });
    }

    /// Restores the newest checkpoint whose cursor block is at or below the argument.
    /// Clears Halted and Poisoned; drops checkpoints above the argument, the fork
    /// boundary, so checkpoints between it and the restored cursor stay valid.
    /// Freshness resets to None, since the restored cursor is unverified until the
    /// next boundary check confirms it.
    #[cold]
    pub fn rollback_at_or_below(
        &mut self,
        block: u64,
    ) -> Result<Option<Position>, RollbackError>
    where
        F: Clone,
    {
        if let EngineStatus::Unrecoverable { cause } = self.status {
            return Err(RollbackError::Unrecoverable { cause });
        }
        let slot = self
            .checkpoints
            .best_at_or_below(block)
            .ok_or(RollbackError::NoCheckpointAtOrBelow { block })?;
        self.fold = slot.fold.clone();
        self.cursor = slot.cursor;
        self.ring = slot.ring.clone();
        self.status = EngineStatus::Active;
        self.last_verified = None;
        self.checkpoints.drop_above(block);
        Ok(self.cursor)
    }

    /// Full restart with a fresh fold: clears cursor, ring, checkpoints, counters.
    pub fn reset(&mut self, fold: F) {
        self.ring.clear();
        self.checkpoints.clear();
        self.fold = fold;
        self.cursor = None;
        self.status = EngineStatus::Active;
        self.last_verified = None;
        self.skips = 0;
    }

    /// Terminal for automated paths; only reset leaves this state.
    #[cold]
    pub fn mark_unrecoverable(&mut self, cause: DivergenceCause) {
        self.status = EngineStatus::Unrecoverable { cause };
    }

    /// Overwrites cursor and ring with decoded snapshot data; used by snapshot decode.
    #[cfg(any(feature = "wincode", test))]
    pub(crate) fn restore_cursor_and_ring(
        &mut self,
        cursor: Option<Position>,
        ring: BlockRing,
    ) {
        self.cursor = cursor;
        self.ring = ring;
    }

    /// Applies every event of one span, deduping positions at or below the cursor.
    fn apply_span(
        &mut self,
        span: &BlockSpan,
        batch: &Batch<F::Event>,
        summary: &mut ApplySummary,
    ) -> Result<(), ApplyError<F::Error>> {
        let events = &batch.events[span.start as usize..span.end as usize];
        let pos = |entry: &LogEvent<F::Event>| {
            Position::new(span.block.number, entry.log_index)
        };
        // Log indices ascend within a span, so the deduped set is a prefix.
        let deduped = self.cursor.map_or(0, |cursor| {
            events.partition_point(|entry| pos(entry) <= cursor)
        });
        summary.deduped += deduped as u64;
        let fresh = &events[deduped..];
        let Some(last) = fresh.last() else {
            return Ok(());
        };

        for (index, entry) in fresh.iter().enumerate() {
            let at = pos(entry);
            match self.fold.apply(at, &entry.event) {
                Ok(()) => summary.applied += 1,
                Err(FoldError::Skip(_)) => {
                    self.skips += 1;
                    summary.skipped += 1;
                }
                Err(FoldError::Halt(error)) => {
                    self.consumed_through(span.block, fresh, &pos, index);
                    return Err(self.halt(at, error));
                }
                Err(FoldError::Poison(error)) => {
                    self.consumed_through(span.block, fresh, &pos, index);
                    return Err(self.poison(at, error));
                }
            }
        }
        self.advance(span.block, pos(last));
        Ok(())
    }

    /// Places the cursor at the predecessor of `fresh[index]`; a no-op at index 0, since
    /// nothing in this span was consumed yet.
    #[cold]
    fn consumed_through(
        &mut self,
        block: BlockRef,
        fresh: &[LogEvent<F::Event>],
        pos: &impl Fn(&LogEvent<F::Event>) -> Position,
        index: usize,
    ) {
        if let Some(entry) = index.checked_sub(1).and_then(|i| fresh.get(i)) {
            self.advance(block, pos(entry));
        }
    }

    /// Moves the cursor to `pos`, recording the block the first time the cursor enters it.
    ///
    /// Ring and cursor move together, so the ring's newest entry is the cursor block
    /// at every point a batch can return from.
    #[inline]
    fn advance(&mut self, block: BlockRef, pos: Position) {
        if self
            .ring
            .newest()
            .is_none_or(|newest| newest.number < block.number)
        {
            self.ring.push(block);
            self.last_verified = Some(block);
        }
        self.cursor = Some(pos);
    }

    #[cold]
    fn halt(&mut self, at: Position, error: F::Error) -> ApplyError<F::Error> {
        self.status = EngineStatus::Halted { at };
        ApplyError::Halted { at, error }
    }

    #[cold]
    fn poison(&mut self, at: Position, error: F::Error) -> ApplyError<F::Error> {
        self.status = EngineStatus::Poisoned { at };
        ApplyError::Poisoned { at, error }
    }
}

/// Builds the fork report comparing the hash the ring observed for a block against
/// the refetched header for that same block.
#[cold]
fn fork_suspected<E>(
    number: u64,
    observed_hash: [u8; 32],
    refetched: BlockRef,
) -> ApplyError<E> {
    ApplyError::ForkSuspected {
        observed: BlockRef {
            number,
            hash: observed_hash,
        },
        refetched,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        batch::{
            BatchShapeError,
            LogEvent,
        },
        test_util::{
            FailKind,
            RecordingFold,
        },
    };
    #[cfg(not(feature = "std"))]
    use alloc::{
        vec,
        vec::Vec,
    };
    #[cfg(feature = "std")]
    use std::{
        vec,
        vec::Vec,
    };

    fn block(number: u64, salt: u8) -> BlockRef {
        let mut hash = [0u8; 32];
        hash[..8].copy_from_slice(&number.to_le_bytes());
        hash[8] = salt;
        BlockRef { number, hash }
    }

    fn batch_of(
        boundary: Option<BlockRef>,
        spans: Vec<(BlockRef, Vec<u64>)>,
    ) -> Batch<u64> {
        let mut events = Vec::new();
        let mut built_spans = Vec::new();
        for (block, log_indices) in spans {
            let start = events.len() as u32;
            for log_index in log_indices {
                events.push(LogEvent {
                    log_index,
                    event: log_index,
                });
            }
            let end = events.len() as u32;
            built_spans.push(BlockSpan { block, start, end });
        }
        Batch {
            boundary,
            spans: built_spans,
            events,
        }
    }

    fn new_engine() -> Engine<RecordingFold> {
        Engine::new(
            RecordingFold::default(),
            EngineConfig {
                ring_capacity: 8,
                checkpoint_slots: 0,
            },
        )
        .unwrap()
    }

    fn engine_with_checkpoints(slots: usize) -> Engine<RecordingFold> {
        Engine::new(
            RecordingFold::default(),
            EngineConfig {
                ring_capacity: 8,
                checkpoint_slots: slots,
            },
        )
        .unwrap()
    }

    fn scripted_engine(fail_at: Position, kind: FailKind) -> Engine<RecordingFold> {
        Engine::new(
            RecordingFold {
                applied: Vec::new(),
                fail_at: Some((fail_at, kind)),
            },
            EngineConfig {
                ring_capacity: 8,
                checkpoint_slots: 0,
            },
        )
        .unwrap()
    }

    #[test]
    fn first_batch_applies_without_boundary() {
        // given a fresh engine and a two-span batch with no boundary
        let mut engine = new_engine();
        let batch = batch_of(
            None,
            vec![(block(1, 0), vec![0, 1]), (block(2, 0), vec![0])],
        );
        // when applied
        let summary = engine.apply_batch(&batch).unwrap();
        // then all events applied and cursor is the last position
        assert_eq!(
            summary,
            ApplySummary {
                applied: 3,
                deduped: 0,
                skipped: 0,
            }
        );
        assert_eq!(engine.cursor(), Some(Position::new(2, 0)));
    }

    #[test]
    fn matching_boundary_updates_freshness() {
        // given an engine at block 5
        let mut engine = new_engine();
        let first = batch_of(None, vec![(block(5, 0), vec![0])]);
        engine.apply_batch(&first).unwrap();
        // when a batch with the correct boundary hash applies
        let next = batch_of(Some(block(5, 0)), vec![]);
        engine.apply_batch(&next).unwrap();
        // then last_verified is the boundary
        assert_eq!(engine.last_verified(), Some(block(5, 0)));
    }

    #[test]
    fn mismatched_boundary_reports_fork() {
        // given an engine at block 5
        let mut engine = new_engine();
        let first = batch_of(None, vec![(block(5, 0), vec![0])]);
        engine.apply_batch(&first).unwrap();
        let view_before = engine.view();
        // when the boundary carries a different hash
        let next = batch_of(Some(block(5, 1)), vec![]);
        let result = engine.apply_batch(&next);
        // then ForkSuspected and the fold state is untouched
        assert_eq!(
            result,
            Err(ApplyError::ForkSuspected {
                observed: block(5, 0),
                refetched: block(5, 1),
            })
        );
        assert_eq!(engine.view(), view_before);
    }

    #[test]
    fn wrong_boundary_number_is_rejected() {
        // given cursor block 5 and boundary number 4
        let mut engine = new_engine();
        let first = batch_of(None, vec![(block(5, 0), vec![0])]);
        engine.apply_batch(&first).unwrap();
        // when applied
        let next = batch_of(Some(block(4, 0)), vec![]);
        let result = engine.apply_batch(&next);
        // then BoundaryNumberMismatch
        assert_eq!(
            result,
            Err(ApplyError::BoundaryNumberMismatch {
                expected: 5,
                got: 4,
            })
        );
    }

    #[test]
    fn missing_boundary_with_cursor_is_rejected() {
        // given a cursor
        let mut engine = new_engine();
        let first = batch_of(None, vec![(block(5, 0), vec![0])]);
        engine.apply_batch(&first).unwrap();
        // when the batch has no boundary
        let next = batch_of(None, vec![]);
        let result = engine.apply_batch(&next);
        // then MissingBoundary
        assert_eq!(result, Err(ApplyError::MissingBoundary));
    }

    #[test]
    fn redelivered_span_with_same_hash_dedupes() {
        // given an applied block
        let mut engine = new_engine();
        let first = batch_of(None, vec![(block(5, 0), vec![0, 1])]);
        engine.apply_batch(&first).unwrap();
        // when the same span is redelivered with its boundary
        let next = batch_of(Some(block(5, 0)), vec![(block(5, 0), vec![0, 1])]);
        let summary = engine.apply_batch(&next).unwrap();
        // then summary counts deduped and applies nothing
        assert_eq!(
            summary,
            ApplySummary {
                applied: 0,
                deduped: 2,
                skipped: 0,
            }
        );
    }

    #[test]
    fn redelivered_span_with_different_hash_reports_fork() {
        // given an applied block
        let mut engine = new_engine();
        let first = batch_of(None, vec![(block(5, 0), vec![0])]);
        engine.apply_batch(&first).unwrap();
        // when a span at that number returns a different hash
        let next = batch_of(Some(block(5, 0)), vec![(block(5, 1), vec![0])]);
        let result = engine.apply_batch(&next);
        // then ForkSuspected
        assert_eq!(
            result,
            Err(ApplyError::ForkSuspected {
                observed: block(5, 0),
                refetched: block(5, 1),
            })
        );
    }

    #[test]
    fn skip_advances_cursor_and_counter() {
        // given fail_at Skip at block 1 log index 0
        let mut engine = scripted_engine(Position::new(1, 0), FailKind::Skip);
        let batch = batch_of(None, vec![(block(1, 0), vec![0, 1])]);
        // when applied
        let summary = engine.apply_batch(&batch).unwrap();
        // then Ok summary with one skipped, cursor past the position, skip_count 1
        assert_eq!(
            summary,
            ApplySummary {
                applied: 1,
                deduped: 0,
                skipped: 1,
            }
        );
        assert_eq!(engine.cursor(), Some(Position::new(1, 1)));
        assert_eq!(engine.skip_count(), 1);
    }

    #[test]
    fn a_lone_skip_consumes_its_position_and_observes_the_block() {
        // given a fold skipping the only event of block 1, so no later apply masks it
        let mut engine = scripted_engine(Position::new(1, 0), FailKind::Skip);
        let batch = batch_of(None, vec![(block(1, 0), vec![0])]);
        // when applied
        let summary = engine.apply_batch(&batch).unwrap();
        // then the position is consumed and the block still entered the ring
        assert_eq!(
            summary,
            ApplySummary {
                applied: 0,
                deduped: 0,
                skipped: 1,
            }
        );
        assert_eq!(engine.cursor(), Some(Position::new(1, 0)));
        assert_eq!(engine.observed().collect::<Vec<_>>(), vec![block(1, 0)]);
        assert_eq!(engine.last_verified(), Some(block(1, 0)));
    }

    #[test]
    fn halt_stops_at_declared_position() {
        // given fail_at Halt at the third event
        let halt_pos = Position::new(1, 2);
        let mut engine = scripted_engine(halt_pos, FailKind::Halt);
        let batch = batch_of(None, vec![(block(1, 0), vec![0, 1, 2])]);
        // when applied
        let result = engine.apply_batch(&batch);
        // then Halted at that position, cursor at the second event, status Halted
        assert_eq!(
            result,
            Err(ApplyError::Halted {
                at: halt_pos,
                error: FailKind::Halt,
            })
        );
        assert_eq!(engine.cursor(), Some(Position::new(1, 1)));
        assert_eq!(engine.status(), EngineStatus::Halted { at: halt_pos });
        let next = batch_of(None, vec![(block(2, 0), vec![0])]);
        let next_result = engine.apply_batch(&next);
        assert_eq!(
            next_result,
            Err(ApplyError::NotActive {
                status: EngineStatus::Halted { at: halt_pos },
            })
        );
    }

    #[test]
    fn halt_mid_span_leaves_the_ring_on_the_cursor_block() {
        // given a fold halting at the second event of a three-event first block
        let halt_pos = Position::new(1, 1);
        let mut engine = Engine::new(
            RecordingFold {
                applied: Vec::new(),
                fail_at: Some((halt_pos, FailKind::Halt)),
            },
            EngineConfig {
                ring_capacity: 8,
                checkpoint_slots: 2,
            },
        )
        .unwrap();
        // when the batch halts mid span
        let halted =
            engine.apply_batch(&batch_of(None, vec![(block(1, 0), vec![0, 1, 2])]));
        // then the cursor rests on block 1 and the ring's newest entry is that block
        assert!(matches!(halted, Err(ApplyError::Halted { .. })));
        assert_eq!(engine.cursor(), Some(Position::new(1, 0)));
        assert_eq!(engine.observed().collect::<Vec<_>>(), vec![block(1, 0)]);
    }

    #[test]
    fn halt_before_a_block_leaves_it_out_of_the_ring() {
        // given a fold halting at the first event of block 2
        let halt_pos = Position::new(2, 0);
        let mut engine = Engine::new(
            RecordingFold {
                applied: Vec::new(),
                fail_at: Some((halt_pos, FailKind::Halt)),
            },
            EngineConfig {
                ring_capacity: 8,
                checkpoint_slots: 2,
            },
        )
        .unwrap();
        engine
            .apply_batch(&batch_of(None, vec![(block(1, 0), vec![0])]))
            .unwrap();
        // when the next batch halts on the first event of block 2
        let halted = engine
            .apply_batch(&batch_of(Some(block(1, 0)), vec![(block(2, 0), vec![0])]));
        // then block 2 never entered the ring and the cursor still rests on block 1
        assert!(matches!(halted, Err(ApplyError::Halted { .. })));
        assert_eq!(engine.cursor(), Some(Position::new(1, 0)));
        assert_eq!(engine.observed().collect::<Vec<_>>(), vec![block(1, 0)]);
    }

    #[test]
    fn checkpoint_after_a_halt_is_refused() {
        // given a Halted engine that had one checkpoint before the halt
        let halt_pos = Position::new(1, 1);
        let mut engine = Engine::new(
            RecordingFold {
                applied: Vec::new(),
                fail_at: Some((halt_pos, FailKind::Halt)),
            },
            EngineConfig {
                ring_capacity: 8,
                checkpoint_slots: 4,
            },
        )
        .unwrap();
        engine
            .apply_batch(&batch_of(None, vec![(block(1, 0), vec![0])]))
            .unwrap();
        engine.checkpoint();
        let halted = engine
            .apply_batch(&batch_of(Some(block(1, 0)), vec![(block(1, 0), vec![1])]));
        assert!(matches!(halted, Err(ApplyError::Halted { .. })));
        // when checkpointing while halted, then rolling back
        engine.checkpoint();
        let restored = engine.rollback_at_or_below(1).unwrap();
        // then only the pre-halt slot exists and the rollback restores Active state
        assert_eq!(engine.checkpoint_count(), 1);
        assert_eq!(restored, Some(Position::new(1, 0)));
        assert_eq!(engine.status(), EngineStatus::Active);
        let resumed = engine
            .apply_batch(&batch_of(Some(block(1, 0)), vec![(block(2, 0), vec![0])]));
        assert!(resumed.is_ok());
    }

    #[test]
    fn rollback_clears_freshness() {
        // given a checkpointed engine whose boundary was verified at block 2
        let mut engine = engine_with_checkpoints(4);
        engine
            .apply_batch(&batch_of(None, vec![(block(1, 0), vec![0])]))
            .unwrap();
        engine.checkpoint();
        engine
            .apply_batch(&batch_of(Some(block(1, 0)), vec![(block(2, 0), vec![0])]))
            .unwrap();
        assert_eq!(engine.last_verified(), Some(block(2, 0)));
        // when rolling back to block 1
        engine.rollback_at_or_below(1).unwrap();
        // then freshness resets, never naming a block above the restored cursor
        assert_eq!(engine.last_verified(), None);
    }

    #[test]
    fn unobserved_cursor_block_is_typed() {
        // given a cursor restored without its ring entry
        let mut engine = new_engine();
        engine.restore_cursor_and_ring(
            Some(Position::new(5, 0)),
            BlockRing::with_capacity(8),
        );
        // when a batch arrives with the boundary for that cursor block
        let result = engine.apply_batch(&batch_of(Some(block(5, 0)), vec![]));
        // then CursorBlockUnobserved, never a panic
        assert_eq!(result, Err(ApplyError::CursorBlockUnobserved { block: 5 }));
    }

    #[test]
    fn poison_marks_state_untrusted() {
        // given fail_at Poison
        let poison_pos = Position::new(1, 0);
        let mut engine = scripted_engine(poison_pos, FailKind::Poison);
        let batch = batch_of(None, vec![(block(1, 0), vec![0])]);
        // when applied
        let result = engine.apply_batch(&batch);
        // then Poisoned status and the partial mutation is visible in the view
        assert_eq!(
            result,
            Err(ApplyError::Poisoned {
                at: poison_pos,
                error: FailKind::Poison,
            })
        );
        assert_eq!(engine.status(), EngineStatus::Poisoned { at: poison_pos });
        assert_eq!(engine.view(), vec![(poison_pos, 0)]);
    }

    #[test]
    fn ring_records_each_observed_block_once() {
        // given two batches over four blocks
        let mut engine = new_engine();
        let first = batch_of(None, vec![(block(1, 0), vec![0]), (block(2, 0), vec![0])]);
        engine.apply_batch(&first).unwrap();
        let second = batch_of(
            Some(block(2, 0)),
            vec![(block(3, 0), vec![0]), (block(4, 0), vec![0])],
        );
        // when applied
        engine.apply_batch(&second).unwrap();
        // then observed yields the four blocks ascending
        let observed: Vec<BlockRef> = engine.observed().collect();
        assert_eq!(
            observed,
            vec![block(1, 0), block(2, 0), block(3, 0), block(4, 0)]
        );
    }

    #[test]
    fn invalid_shape_is_rejected_before_fold_runs() {
        // given a gap batch
        let mut engine = new_engine();
        let batch = Batch {
            boundary: None,
            spans: vec![
                BlockSpan {
                    block: block(1, 0),
                    start: 0,
                    end: 1,
                },
                BlockSpan {
                    block: block(2, 0),
                    start: 2,
                    end: 3,
                },
            ],
            events: vec![
                LogEvent {
                    log_index: 0,
                    event: 0u64,
                },
                LogEvent {
                    log_index: 0,
                    event: 0u64,
                },
                LogEvent {
                    log_index: 0,
                    event: 0u64,
                },
            ],
        };
        // when applied
        let result = engine.apply_batch(&batch);
        // then Shape and the fold recorded nothing
        assert_eq!(
            result,
            Err(ApplyError::Shape(BatchShapeError::SpansNotContiguous {
                span: 1
            }))
        );
        assert_eq!(engine.view(), Vec::<(Position, u64)>::new());
    }

    #[test]
    fn config_rejects_non_power_of_two_ring() {
        // given capacity 12
        let config = EngineConfig {
            ring_capacity: 12,
            checkpoint_slots: 0,
        };
        // when constructing
        let result = Engine::new(RecordingFold::default(), config);
        // then RingCapacityNotPowerOfTwo
        assert_eq!(
            result.err(),
            Some(ConfigError::RingCapacityNotPowerOfTwo { got: 12 })
        );
    }

    #[test]
    fn checkpoint_then_rollback_restores_view() {
        // given a checkpoint at block 3 and applies through block 6
        let mut engine = engine_with_checkpoints(4);
        engine
            .apply_batch(&batch_of(None, vec![(block(3, 0), vec![0])]))
            .unwrap();
        engine.checkpoint();
        let checkpoint_view = engine.view();
        let checkpoint_cursor = engine.cursor();
        let rest = batch_of(
            Some(block(3, 0)),
            vec![
                (block(4, 0), vec![0]),
                (block(5, 0), vec![0]),
                (block(6, 0), vec![0]),
            ],
        );
        engine.apply_batch(&rest).unwrap();
        // when rolling back at or below 4
        let restored = engine.rollback_at_or_below(4).unwrap();
        // then the view equals the checkpoint view and cursor is the checkpoint cursor
        assert_eq!(engine.view(), checkpoint_view);
        assert_eq!(restored, checkpoint_cursor);
        assert_eq!(engine.cursor(), checkpoint_cursor);
    }

    #[test]
    fn rollback_prefers_newest_eligible_checkpoint() {
        // given checkpoints at blocks 2 and 4
        let mut engine = engine_with_checkpoints(4);
        engine
            .apply_batch(&batch_of(None, vec![(block(2, 0), vec![0])]))
            .unwrap();
        engine.checkpoint();
        engine
            .apply_batch(&batch_of(Some(block(2, 0)), vec![(block(4, 0), vec![0])]))
            .unwrap();
        engine.checkpoint();
        engine
            .apply_batch(&batch_of(Some(block(4, 0)), vec![(block(6, 0), vec![0])]))
            .unwrap();
        // when rolling back at or below 5
        let restored = engine.rollback_at_or_below(5).unwrap();
        // then block 4 restores
        assert_eq!(restored, Some(Position::new(4, 0)));
    }

    #[test]
    fn rollback_without_eligible_checkpoint_is_typed() {
        // given only a checkpoint at block 6
        let mut engine = engine_with_checkpoints(4);
        engine
            .apply_batch(&batch_of(None, vec![(block(6, 0), vec![0])]))
            .unwrap();
        engine.checkpoint();
        // when rolling back at or below 4
        let result = engine.rollback_at_or_below(4);
        // then NoCheckpointAtOrBelow { block: 4 }
        assert_eq!(
            result,
            Err(RollbackError::NoCheckpointAtOrBelow { block: 4 })
        );
    }

    #[test]
    fn zero_slots_never_checkpoints() {
        // given checkpoint_slots 0
        let mut engine = new_engine();
        engine
            .apply_batch(&batch_of(None, vec![(block(1, 0), vec![0])]))
            .unwrap();
        // when checkpointing and rolling back
        engine.checkpoint();
        let result = engine.rollback_at_or_below(1);
        // then count stays 0 and rollback errors
        assert_eq!(engine.checkpoint_count(), 0);
        assert_eq!(
            result,
            Err(RollbackError::NoCheckpointAtOrBelow { block: 1 })
        );
    }

    #[test]
    fn slot_ring_overwrites_oldest() {
        // given 2 slots and 3 checkpoints
        let mut engine = engine_with_checkpoints(2);
        engine
            .apply_batch(&batch_of(None, vec![(block(1, 0), vec![0])]))
            .unwrap();
        engine.checkpoint();
        engine
            .apply_batch(&batch_of(Some(block(1, 0)), vec![(block(2, 0), vec![0])]))
            .unwrap();
        engine.checkpoint();
        engine
            .apply_batch(&batch_of(Some(block(2, 0)), vec![(block(3, 0), vec![0])]))
            .unwrap();
        engine.checkpoint();
        // when rolling back to the earliest
        let result = engine.rollback_at_or_below(1);
        // then it is gone and the call errors
        assert_eq!(
            result,
            Err(RollbackError::NoCheckpointAtOrBelow { block: 1 })
        );
    }

    #[test]
    fn rollback_clears_halted_state() {
        // given a Halted engine with an earlier checkpoint
        let halt_pos = Position::new(2, 0);
        let mut engine = Engine::new(
            RecordingFold {
                applied: Vec::new(),
                fail_at: Some((halt_pos, FailKind::Halt)),
            },
            EngineConfig {
                ring_capacity: 8,
                checkpoint_slots: 2,
            },
        )
        .unwrap();
        engine
            .apply_batch(&batch_of(None, vec![(block(1, 0), vec![0])]))
            .unwrap();
        engine.checkpoint();
        let checkpoint_cursor = engine.cursor();
        let halted = engine
            .apply_batch(&batch_of(Some(block(1, 0)), vec![(block(2, 0), vec![0])]));
        assert_eq!(
            halted,
            Err(ApplyError::Halted {
                at: halt_pos,
                error: FailKind::Halt,
            })
        );
        // when rolled back
        let restored = engine.rollback_at_or_below(1).unwrap();
        // then status Active and applying resumes
        assert_eq!(engine.status(), EngineStatus::Active);
        assert_eq!(restored, checkpoint_cursor);
        let resumed = engine
            .apply_batch(&batch_of(Some(block(1, 0)), vec![(block(3, 0), vec![0])]));
        assert!(resumed.is_ok());
        assert_eq!(engine.cursor(), Some(Position::new(3, 0)));
    }

    #[test]
    fn rollback_restores_poisoned_state() {
        // given a Poisoned engine
        let poison_pos = Position::new(2, 0);
        let mut engine = Engine::new(
            RecordingFold {
                applied: Vec::new(),
                fail_at: Some((poison_pos, FailKind::Poison)),
            },
            EngineConfig {
                ring_capacity: 8,
                checkpoint_slots: 2,
            },
        )
        .unwrap();
        engine
            .apply_batch(&batch_of(None, vec![(block(1, 0), vec![0])]))
            .unwrap();
        engine.checkpoint();
        let checkpoint_view = engine.view();
        let poisoned = engine
            .apply_batch(&batch_of(Some(block(1, 0)), vec![(block(2, 0), vec![0])]));
        assert!(matches!(poisoned, Err(ApplyError::Poisoned { .. })));
        assert_ne!(engine.view(), checkpoint_view);
        // when rolled back
        engine.rollback_at_or_below(1).unwrap();
        // then the view has no trace of the partial mutation
        assert_eq!(engine.view(), checkpoint_view);
        assert_eq!(engine.status(), EngineStatus::Active);
    }

    #[test]
    fn rollback_drops_checkpoints_above_restore_point() {
        // given checkpoints at 2 and 5
        let mut engine = engine_with_checkpoints(4);
        engine
            .apply_batch(&batch_of(None, vec![(block(2, 0), vec![0])]))
            .unwrap();
        engine.checkpoint();
        engine
            .apply_batch(&batch_of(Some(block(2, 0)), vec![(block(5, 0), vec![0])]))
            .unwrap();
        engine.checkpoint();
        // when rolling back at or below 3
        engine.rollback_at_or_below(3).unwrap();
        // then only the block 2 checkpoint remains
        assert_eq!(engine.checkpoint_count(), 1);
    }

    #[test]
    fn rollback_truncates_observed_ring() {
        // given a checkpoint at block 2 and applies through block 4
        let mut engine = engine_with_checkpoints(4);
        engine
            .apply_batch(&batch_of(
                None,
                vec![(block(1, 0), vec![0]), (block(2, 0), vec![0])],
            ))
            .unwrap();
        engine.checkpoint();
        engine
            .apply_batch(&batch_of(
                Some(block(2, 0)),
                vec![(block(3, 0), vec![0]), (block(4, 0), vec![0])],
            ))
            .unwrap();
        // when rolling back at or below block 2
        engine.rollback_at_or_below(2).unwrap();
        // then observed ends at block 2 and a fresh batch from block 3 applies cleanly
        let observed: Vec<BlockRef> = engine.observed().collect();
        assert_eq!(observed, vec![block(1, 0), block(2, 0)]);
        let result = engine
            .apply_batch(&batch_of(Some(block(2, 0)), vec![(block(3, 0), vec![0])]));
        assert!(result.is_ok());
    }

    #[test]
    fn reset_returns_engine_to_genesis() {
        // given an advanced engine
        let mut engine = new_engine();
        engine
            .apply_batch(&batch_of(None, vec![(block(1, 0), vec![0])]))
            .unwrap();
        // when reset with a fresh fold
        engine.reset(RecordingFold::default());
        // then cursor None, empty ring, zero checkpoints, Active
        assert_eq!(engine.cursor(), None);
        assert_eq!(engine.observed().len(), 0);
        assert_eq!(engine.checkpoint_count(), 0);
        assert_eq!(engine.status(), EngineStatus::Active);
    }

    #[test]
    fn unrecoverable_refuses_apply_and_rollback() {
        // given mark_unrecoverable
        let mut engine = new_engine();
        engine.mark_unrecoverable(DivergenceCause::ForkBeyondWindow);
        // when applying or rolling back
        let apply_result =
            engine.apply_batch(&batch_of(None, vec![(block(1, 0), vec![0])]));
        let rollback_result = engine.rollback_at_or_below(0);
        // then NotActive and Unrecoverable errors carry the cause
        assert_eq!(
            apply_result,
            Err(ApplyError::NotActive {
                status: EngineStatus::Unrecoverable {
                    cause: DivergenceCause::ForkBeyondWindow
                },
            })
        );
        assert_eq!(
            rollback_result,
            Err(RollbackError::Unrecoverable {
                cause: DivergenceCause::ForkBeyondWindow,
            })
        );
    }

    #[test]
    fn durable_point_is_the_oldest_retained_checkpoint_cursor() {
        // given 3 slots checkpointed at blocks 1, 3, 5, 7, 9, and 11
        let mut engine = engine_with_checkpoints(3);
        let mut boundary = None;
        for number in [1u64, 3, 5, 7, 9, 11] {
            engine
                .apply_batch(&batch_of(boundary, vec![(block(number, 0), vec![0])]))
                .unwrap();
            engine.checkpoint();
            boundary = Some(block(number, 0));
        }
        // when reading durable_point
        let point = engine.durable_point();
        // then it is block 7, the oldest slot the wraparound left behind
        assert_eq!(point, Some(Position::new(7, 0)));
    }

    #[test]
    fn durable_point_is_none_without_checkpoints() {
        // given a fresh engine with no retained slots
        let engine = new_engine();
        // when reading durable_point
        let point = engine.durable_point();
        // then None
        assert_eq!(point, None);
    }

    #[test]
    fn durable_point_follows_rollback_dropping_newer_slots() {
        // given checkpoints at blocks 2 and 5
        let mut engine = engine_with_checkpoints(4);
        engine
            .apply_batch(&batch_of(None, vec![(block(2, 0), vec![0])]))
            .unwrap();
        engine.checkpoint();
        engine
            .apply_batch(&batch_of(Some(block(2, 0)), vec![(block(5, 0), vec![0])]))
            .unwrap();
        engine.checkpoint();
        // when rolling back at or below block 3
        engine.rollback_at_or_below(3).unwrap();
        // then durable_point is the block 2 cursor
        assert_eq!(engine.durable_point(), Some(Position::new(2, 0)));
    }

    #[test]
    fn cursorless_oldest_slot_yields_no_durable_point() {
        // given a checkpoint taken before any apply and a later one at block 1
        let mut engine = engine_with_checkpoints(3);
        engine.checkpoint();
        engine
            .apply_batch(&batch_of(None, vec![(block(1, 0), vec![0])]))
            .unwrap();
        engine.checkpoint();
        // when reading durable_point
        let point = engine.durable_point();
        // then None while the cursor-less slot is the oldest
        assert_eq!(point, None);
    }

    #[test]
    fn repeated_rollback_to_same_checkpoint_succeeds() {
        // given one checkpoint
        let mut engine = engine_with_checkpoints(4);
        engine
            .apply_batch(&batch_of(None, vec![(block(1, 0), vec![0])]))
            .unwrap();
        engine.checkpoint();
        let checkpoint_view = engine.view();
        let checkpoint_cursor = engine.cursor();
        engine
            .apply_batch(&batch_of(Some(block(1, 0)), vec![(block(2, 0), vec![0])]))
            .unwrap();
        // when rolled back twice with applies between
        let first_restore = engine.rollback_at_or_below(1).unwrap();
        engine
            .apply_batch(&batch_of(Some(block(1, 0)), vec![(block(3, 0), vec![9])]))
            .unwrap();
        let second_restore = engine.rollback_at_or_below(1).unwrap();
        // then both restores match
        assert_eq!(first_restore, checkpoint_cursor);
        assert_eq!(second_restore, checkpoint_cursor);
        assert_eq!(engine.view(), checkpoint_view);
    }

    #[test]
    fn cursor_does_not_regress_when_the_stop_span_is_partially_deduped() {
        // given cursor at block 5 log index 3 and a fold halting at log index 5
        let halt_pos = Position::new(5, 5);
        let mut engine = scripted_engine(halt_pos, FailKind::Halt);
        let first = batch_of(None, vec![(block(5, 0), vec![0, 1, 2, 3])]);
        engine.apply_batch(&first).unwrap();
        // when block 5 is redelivered as [0, 1, 5], dropping 2 and 3 as deduped
        let next = batch_of(Some(block(5, 0)), vec![(block(5, 0), vec![0, 1, 5])]);
        let result = engine.apply_batch(&next);
        // then Halted at (5, 5) and the cursor is still (5, 3), not lower
        assert_eq!(
            result,
            Err(ApplyError::Halted {
                at: halt_pos,
                error: FailKind::Halt,
            })
        );
        assert_eq!(engine.cursor(), Some(Position::new(5, 3)));
    }
}
