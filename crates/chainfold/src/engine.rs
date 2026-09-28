use crate::{
    batch::{
        Batch,
        SpanView,
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
        is_power_of_two,
    },
};
#[cfg(verus_keep_ghost)]
use {
    crate::verus::{
        model::{
            EngineView,
            SlotView,
            fview,
            lemma_opt_lt_order,
            lemma_upto,
            lemma_upto_upto,
            live_count,
            lt,
            lt_sorted,
            opt_le,
            opt_lt,
            prefix_at_or_below,
            qualifies,
            upto,
        },
        tcb::axiom_clone_preserves_fview,
    },
    vstd::prelude::*,
};

/// Smallest allowed observed-block ring capacity.
const MIN_RING_CAPACITY: usize = 2;
/// Largest allowed observed-block ring capacity.
const MAX_RING_CAPACITY: usize = 1 << 20;

/// Fixed engine construction parameters.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EngineConfig {
    /// Observed-block window W; power of two between 2 and 1 << 20.
    pub ring_capacity: usize,
    /// Retained checkpoint slots K; zero disables rollback.
    pub checkpoint_slots: usize,
}

impl Default for EngineConfig {
    fn default() -> Self {
        Self {
            ring_capacity: 1024,
            checkpoint_slots: 4,
        }
    }
}

impl EngineConfig {
    /// Accepts a power-of-two ring capacity within the allowed range.
    pub(crate) fn validate(&self) -> Result<(), ConfigError> {
        if !is_power_of_two(self.ring_capacity) {
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
#[cfg_attr(verus_keep_ghost, verus_verify)]
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
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug)]
pub struct Engine<F> {
    fold: F,
    cursor: Option<Position>,
    ring: BlockRing,
    checkpoints: CheckpointRing<F>,
    status: EngineStatus,
    last_verified: Option<BlockRef>,
    skips: u64,
    resets: u64,
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
            resets: 0,
        })
    }

    /// Returns the coarse engine status.
    #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == self@.status))]
    pub fn status(&self) -> EngineStatus {
        self.status
    }

    /// Returns the most recently applied position, if any.
    #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == self@.cursor))]
    pub fn cursor(&self) -> Option<Position> {
        self.cursor
    }

    /// Most recent block whose hash the source confirmed; None until first confirmation.
    #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == self@.last_verified))]
    pub fn last_verified(&self) -> Option<BlockRef> {
        self.last_verified
    }

    /// Count of events the fold declared not its own.
    #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == self@.skips))]
    pub fn skip_count(&self) -> u64 {
        self.skips
    }

    /// Count of resets since construction, wrapping; the driver's reset epoch.
    #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == self@.resets))]
    pub(crate) fn resets(&self) -> u64 {
        self.resets
    }

    /// Count of checkpoints the ring can still serve; expired slots are not counted.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
        ensures
            r == live_count(self@.slots, self@.ring, self@.slots.len() as int),
    ))]
    pub fn checkpoint_count(&self) -> usize {
        self.checkpoints.count(&self.ring)
    }

    /// Cursor of the oldest live checkpoint; the reorg-safe durable point.
    ///
    /// None without checkpoints, when the oldest live slot predates any applied event, or
    /// once every slot's cursor block has left the observed window.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
        ensures
            r == self@.durable_point(),
    ))]
    pub fn durable_point(&self) -> Option<Position> {
        #[cfg(verus_keep_ghost)]
        proof! {
            self.lemma_oldest_bridge();
        }
        // `match`, not `and_then`: a closure's result has no spec in attribute mode.
        match self.checkpoints.oldest(&self.ring) {
            Some(slot) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    slot.lemma_view();
                }
                slot.cursor
            }
            None => None,
        }
    }

    /// The fold as of the durable point, if there is one.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
        ensures
            match self@.oldest_live_from(0) {
                Some(k) => r matches Some(f) && fview::<F>(f) == self@.slots[k].unwrap().fold,
                None => r is None,
            },
    ))]
    pub fn durable_fold(&self) -> Option<&F> {
        #[cfg(verus_keep_ghost)]
        proof! {
            self.lemma_oldest_bridge();
        }
        match self.checkpoints.oldest(&self.ring) {
            Some(slot) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    slot.lemma_view();
                }
                Some(&slot.fold)
            }
            None => None,
        }
    }

    /// Oldest live checkpoint slot, for the snapshot codec.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
        ensures
            match self@.oldest_live_from(0) {
                Some(k) => r matches Some(s) && self@.slots[k] == Some(s@),
                None => r is None,
            },
    ))]
    #[cfg(feature = "wincode")]
    pub(crate) fn oldest_checkpoint(&self) -> Option<&Slot<F>> {
        #[cfg(verus_keep_ghost)]
        proof! {
            self.lemma_oldest_bridge();
        }
        self.checkpoints.oldest(&self.ring)
    }

    /// Borrows the fold state.
    #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures fview::<F>(r) == self@.fold))]
    pub fn fold(&self) -> &F {
        &self.fold
    }

    /// Mutable access to the live fold, for state the fold has externalized.
    pub fn fold_mut(&mut self) -> &mut F {
        &mut self.fold
    }

    /// Iterates observed blocks oldest first.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
        ensures
            r@ == self@.ring,
    ))]
    pub fn observed(&self) -> Observed<'_> {
        self.ring.iter()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
        ensures
            r.wf(),
            r@ == self@.ring,
    ))]
    pub(crate) fn ring(&self) -> &BlockRing {
        &self.ring
    }

    /// Iterates observed blocks at or below a number, oldest first; a checkpoint's window.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
        ensures
            prefix_at_or_below(self@.ring, number, r@.len() as int),
            r@ == self@.ring.subrange(0, r@.len() as int),
    ))]
    #[cfg(feature = "wincode")]
    pub(crate) fn observed_at_or_below(&self, number: u64) -> Observed<'_> {
        self.ring.iter_at_or_below(number)
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
        let mut start = 0usize;
        for i in 0..batch.span_count() {
            let span = batch.span(i, start);
            start += span.events.len();
            let redelivered = match self.cursor {
                Some(cursor) => span.number <= cursor.block,
                None => false,
            };
            if redelivered {
                match self.ring.hash_at(span.number) {
                    Some(observed_hash) if &observed_hash != span.hash => {
                        return Err(fork_suspected(
                            span.number,
                            observed_hash,
                            span.block(),
                        ));
                    }
                    _ => {}
                }
            }
            self.apply_span(&span, &mut summary)?;
        }

        Ok(summary)
    }

    /// Stores a checkpoint of the current fold and cursor.
    ///
    /// A slot carries no block history of its own; its window is the engine's ring
    /// truncated to its cursor, so rollback depth is bounded by ring_capacity and a slot
    /// expires once its cursor block leaves the window.
    ///
    /// A no-op with zero slots or a non-Active status, so every stored slot holds
    /// state the engine still trusts.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self)@ == if old(self)@.status is Active && old(self)@.slots.len() > 0 {
                EngineView {
                    slots: old(self)@.slots.drop_first().push(
                        Some(SlotView { fold: old(self)@.fold, cursor: old(self)@.cursor }),
                    ),
                    ..old(self)@
                }
            } else {
                old(self)@
            },
            forall|init: int, log: Seq<(Position, F::Event)>|
                #[trigger] old(self)@.inv::<F, F::Event, F::Error>(init, log) ==> final(self)@.inv::<F, F::Event, F::Error>(init, log),
            forall|a: Seq<Option<BlockRef>>|
                #[trigger] old(self)@.anchored(a) ==> final(self)@.anchored(
                    old(self)@.stored_anchors(a),
                ),
    ))]
    pub fn checkpoint(&mut self)
    where
        F: Clone,
    {
        if !self.status.is_active() {
            return;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            // `cloned` is open, so the trigger is the clone call's ensures itself.
            assert forall|b: F| #[trigger] call_ensures(F::clone, (&self.fold,), b) implies fview::<F>(
                &b,
            ) == fview::<F>(&self.fold) by {
                axiom_clone_preserves_fview::<F>(self.fold, b);
            }
        }
        self.checkpoints.store(Slot {
            fold: self.fold.clone(),
            cursor: self.cursor,
        });
        #[cfg(verus_keep_ghost)]
        proof! {
            let pre = old(self)@;
            if pre.slots.len() > 0 {
                assert(self@ == EngineView {
                    slots: pre.slots.drop_first().push(
                        Some(SlotView { fold: pre.fold, cursor: pre.cursor }),
                    ),
                    ..pre
                });
                lemma_checkpoint_view::<F>(pre, self@);
            } else {
                assert(self@ == pre);
            }
        }
    }

    /// Restores the newest live checkpoint whose cursor block is at or below the argument,
    /// truncating the ring to that cursor.
    ///
    /// Clears Halted and Poisoned and drops checkpoints newer than the restored cursor,
    /// expired ones included, so no slot outlives the history it was folded from.
    /// Freshness resets to None, since the restored cursor is unverified until the
    /// next boundary check confirms it. Slots whose cursor block has left the observed
    /// window are expired, so NoCheckpointAtOrBelow also names an exhausted window.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            r is Err ==> *final(self) == *old(self),
            r matches Err(RollbackError::NoCheckpointAtOrBelow { .. }) ==> forall|j: int|
                !(#[trigger] old(self)@.live_at(j) && qualifies(old(self)@.slots[j].unwrap(), block)),
            r matches Err(RollbackError::Unrecoverable { .. }) ==> old(self)@.status is Unrecoverable,
            // T5b: the target is the newest stored qualifying live slot, whose cursor is the
            // maximum over them; T5c: the post-state.
            r matches Ok(t) ==> exists|k: int|
                #[trigger] old(self)@.rollback_target(block, k) && {
                    let (pre, post) = (old(self)@, final(self)@);
                    &&& t == pre.slots[k].unwrap().cursor
                    &&& post.fold == pre.slots[k].unwrap().fold
                    &&& post.cursor == t
                    &&& t is None ==> post.ring.len() == 0
                    &&& t matches Some(c) ==> prefix_at_or_below(pre.ring, c.block, post.ring.len() as int)
                        && post.ring == pre.ring.subrange(0, post.ring.len() as int)
                    &&& post.slots.len() == pre.slots.len()
                    &&& forall|j: int|
                        0 <= j < pre.slots.len() ==> #[trigger] post.slots[j] == if pre.slots[j] is Some
                            && opt_lt(t, pre.slots[j].unwrap().cursor) {
                            None
                        } else {
                            pre.slots[j]
                        }
                    &&& post.status is Active
                    &&& post.last_verified is None
                    &&& post.skips == pre.skips && post.resets == pre.resets
                },
            r matches Ok(t) ==> forall|j: int|
                #[trigger] old(self)@.live_at(j) && qualifies(old(self)@.slots[j].unwrap(), block)
                    ==> opt_le(old(self)@.slots[j].unwrap().cursor, t),
            // T5d: `Inv` holds over the log truncated at the restored cursor.
            r is Ok ==> forall|init: int, log: Seq<(Position, F::Event)>|
                #[trigger] old(self)@.inv::<F, F::Event, F::Error>(init, log) ==> final(self)@.inv::<F, F::Event, F::Error>(init, upto::<F::Event>(log, final(self)@.cursor)),
            forall|a: Seq<Option<BlockRef>>|
                #[trigger] old(self)@.anchored(a) ==> final(self)@.anchored(a),
    ))]
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
        #[cfg(verus_keep_ghost)]
        proof! {
            self.lemma_live_bridge();
        }
        let slot = self
            .checkpoints
            .best_at_or_below(block, &self.ring)
            .ok_or(RollbackError::NoCheckpointAtOrBelow { block })?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost sv = slot@;
            let ghost k = choose|k: int|
                0 <= k < self.checkpoints@.len() && self.checkpoints@[k] == Some(sv)
                    && self.checkpoints.live_view(self.ring@, k) && qualifies(sv, block)
                    && forall|j: int|
                    k < j < self.checkpoints@.len() ==> !(#[trigger] self.checkpoints.live_view(
                        self.ring@,
                        j,
                    ) && qualifies(self.checkpoints@[j].unwrap(), block));
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            slot.lemma_view();
            // `cloned` is open, so the trigger is the clone call's ensures itself.
            assert forall|b: F| #[trigger] call_ensures(F::clone, (&slot.fold,), b) implies fview::<F>(
                &b,
            ) == fview::<F>(&slot.fold) by {
                axiom_clone_preserves_fview::<F>(slot.fold, b);
            }
        }
        self.fold = slot.fold.clone();
        self.cursor = slot.cursor;
        match self.cursor {
            Some(cursor) => self.ring.truncate_above(cursor.block),
            None => self.ring.clear(),
        }
        self.status = EngineStatus::Active;
        self.last_verified = None;
        self.checkpoints.drop_newer(self.cursor);
        #[cfg(verus_keep_ghost)]
        proof! {
            self.ring.lemma_wf();
            let pre = old(self)@;
            assert(pre.rollback_target(block, k));
            lemma_rollback_view::<F>(pre, self@, block, k);
        }
        Ok(self.cursor)
    }

    /// Full restart with a fresh fold: clears cursor, ring, checkpoints, counters.
    ///
    /// A driver over this engine resets its sink before the next tick or status read,
    /// so no durable cursor from before the reset is reported.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self)@.fold == fview::<F>(&fold),
            final(self)@.cursor is None,
            final(self)@.ring.len() == 0,
            final(self)@.slots.len() == old(self)@.slots.len(),
            forall|k: int| 0 <= k < final(self)@.slots.len() ==> #[trigger] final(self)@.slots[k] is None,
            final(self)@.status is Active,
            final(self)@.last_verified is None,
            final(self)@.skips == 0,
            final(self)@.resets == old(self)@.resets.wrapping_add(1),
            final(self)@.inv::<F, F::Event, F::Error>(fview::<F>(&fold), Seq::empty()),
            forall|a: Seq<Option<BlockRef>>|
                a.len() == final(self)@.slots.len() ==> #[trigger] final(self)@.anchored(a),
    ))]
    pub fn reset(&mut self, fold: F) {
        self.ring.clear();
        self.checkpoints.clear();
        self.fold = fold;
        self.cursor = None;
        self.status = EngineStatus::Active;
        self.last_verified = None;
        self.skips = 0;
        self.resets = self.resets.wrapping_add(1);
    }

    /// Terminal for automated paths; only reset leaves this state.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self)@ == (EngineView { status: EngineStatus::Unrecoverable { cause }, ..old(self)@ }),
            forall|init: int, log: Seq<(Position, F::Event)>|
                #[trigger] old(self)@.inv::<F, F::Event, F::Error>(init, log) ==> final(self)@.inv::<F, F::Event, F::Error>(init, log),
            forall|a: Seq<Option<BlockRef>>|
                #[trigger] old(self)@.anchored(a) ==> final(self)@.anchored(a),
    ))]
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
        span: &SpanView<'_, F::Event>,
        summary: &mut ApplySummary,
    ) -> Result<(), ApplyError<F::Error>> {
        let number = span.number;
        let deduped = match self.cursor {
            Some(cursor) if number > cursor.block => 0,
            Some(cursor) if number < cursor.block => span.log_indices.len(),
            Some(cursor) => count_at_or_below(span.log_indices, cursor.log_index),
            None => 0,
        };
        summary.deduped += deduped as u64;
        let (indices, events) = if deduped == 0 {
            (span.log_indices, span.events)
        } else {
            (
                span.log_indices.split_at(deduped).1,
                span.events.split_at(deduped).1,
            )
        };
        let len = indices.len();
        if len == 0 {
            return Ok(());
        }
        // lanes are equal length by construction, so the paired walk drops no event
        let paired = if len < events.len() {
            len
        } else {
            events.len()
        };

        for offset in 0..paired {
            let at = span_pos(number, indices[offset]);
            match self.fold.apply(at, &events[offset]) {
                Ok(()) => summary.applied += 1,
                Err(FoldError::Skip(_)) => {
                    self.skips = self.skips.saturating_add(1);
                    summary.skipped += 1;
                }
                Err(FoldError::Halt(error)) => {
                    self.consumed_through(span, indices, offset);
                    return Err(self.halt(at, error));
                }
                Err(FoldError::Poison(error)) => {
                    self.consumed_through(span, indices, offset);
                    return Err(self.poison(at, error));
                }
            }
        }
        self.advance(span.number, span.hash, span_pos(number, indices[len - 1]));
        Ok(())
    }

    /// Places the cursor at the predecessor of `indices[offset]`; a no-op at offset 0,
    /// since nothing in this span was consumed yet.
    #[cold]
    fn consumed_through(
        &mut self,
        span: &SpanView<'_, F::Event>,
        indices: &[u32],
        offset: usize,
    ) {
        if let Some(log_index) = offset.checked_sub(1).and_then(|i| indices.get(i)) {
            let pos = Position::new(span.number, u64::from(*log_index));
            self.advance(span.number, span.hash, pos);
        }
    }

    /// Moves the cursor to `pos`, recording the block the first time the cursor enters it.
    ///
    /// Ring and cursor move together, so the ring's newest entry is the cursor block
    /// at every point a batch can return from.
    fn advance(&mut self, number: u64, hash: &[u8; 32], pos: Position) {
        let entered = match self.ring.newest_number() {
            Some(newest) => newest < number,
            None => true,
        };
        if entered {
            let block = BlockRef {
                number,
                hash: *hash,
            };
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

/// Position of a span event.
fn span_pos(number: u64, log_index: u32) -> Position {
    Position::new(number, u64::from(log_index))
}

/// Count of the leading log indices at or below `bound`; the lane is strictly ascending.
fn count_at_or_below(log_indices: &[u32], bound: u64) -> usize {
    let mut base = 0usize;
    let mut rest = log_indices;
    while rest.len() > 1 {
        // both candidate windows keep len - half entries, as in std's binary search
        let half = rest.len() / 2;
        let high = rest.split_at(half).1;
        let low = rest.split_at(high.len()).0;
        if u64::from(rest[half]) <= bound {
            base += half;
            rest = high;
        } else {
            rest = low;
        }
    }
    if rest.len() == 1 && u64::from(rest[0]) <= bound {
        base + 1
    } else {
        base
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
        batch::BatchShapeError,
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
        spans: Vec<(BlockRef, Vec<u32>)>,
    ) -> Batch<u64> {
        let mut batch = Batch::new();
        batch.boundary = boundary;
        for (block, log_indices) in spans {
            batch.push_block(
                block,
                log_indices
                    .into_iter()
                    .map(|index| (index, u64::from(index))),
            );
        }
        batch
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
        let view_before = engine.fold().applied.clone();
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
        assert_eq!(engine.fold().applied, view_before);
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
        assert_eq!(engine.fold().applied, vec![(poison_pos, 0)]);
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
        // given a batch whose second span moves the block number backwards
        let mut engine = new_engine();
        let batch = batch_of(None, vec![(block(2, 0), vec![0]), (block(1, 0), vec![0])]);
        // when applied
        let result = engine.apply_batch(&batch);
        // then Shape and the fold recorded nothing
        assert_eq!(
            result,
            Err(ApplyError::Shape(BatchShapeError::BlocksNotAscending {
                span: 1
            }))
        );
        assert_eq!(engine.fold().applied, Vec::<(Position, u64)>::new());
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
        let checkpoint_view = engine.fold().applied.clone();
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
        assert_eq!(engine.fold().applied, checkpoint_view);
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
        let checkpoint_view = engine.fold().applied.clone();
        let poisoned = engine
            .apply_batch(&batch_of(Some(block(1, 0)), vec![(block(2, 0), vec![0])]));
        assert!(matches!(poisoned, Err(ApplyError::Poisoned { .. })));
        assert_ne!(engine.fold().applied, checkpoint_view);
        // when rolled back
        engine.rollback_at_or_below(1).unwrap();
        // then the view has no trace of the partial mutation
        assert_eq!(engine.fold().applied, checkpoint_view);
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
    fn durable_fold_reads_the_oldest_live_checkpoint() {
        // given an engine checkpointed once, then advanced past it
        let mut engine = engine_with_checkpoints(2);
        engine
            .apply_batch(&batch_of(None, vec![(block(1, 0), vec![0])]))
            .unwrap();
        engine.checkpoint();
        let durable = engine.fold().applied.clone();
        engine
            .apply_batch(&batch_of(Some(block(1, 0)), vec![(block(2, 0), vec![1])]))
            .unwrap();
        // then the live fold has moved on but the durable one has not
        assert_ne!(engine.fold().applied, durable);
        assert_eq!(
            engine.durable_fold().map(|f| f.applied.clone()),
            Some(durable)
        );
        // and without checkpoints there is no durable fold at all
        assert!(new_engine().durable_fold().is_none());
    }

    #[test]
    fn fold_mut_edits_live_state_and_leaves_checkpoints_whole() {
        // given a checkpointed engine
        let mut engine = engine_with_checkpoints(2);
        engine
            .apply_batch(&batch_of(None, vec![(block(1, 0), vec![0, 1])]))
            .unwrap();
        engine.checkpoint();
        let checkpointed = engine.fold().applied.clone();
        // when the live fold drops state it has externalized
        engine.fold_mut().applied.clear();
        assert_eq!(engine.fold().applied, Vec::new());
        // then the retained checkpoint still holds it, and rollback restores it
        engine.rollback_at_or_below(1).unwrap();
        assert_eq!(engine.fold().applied, checkpointed);
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
    fn rollback_refuses_a_checkpoint_whose_block_left_the_ring() {
        // given a checkpoint at block 1, then twelve blocks through a ring holding 8
        let mut engine = engine_with_checkpoints(2);
        engine
            .apply_batch(&batch_of(None, vec![(block(1, 0), vec![0])]))
            .unwrap();
        engine.checkpoint();
        for number in 2..=12u64 {
            engine
                .apply_batch(&batch_of(
                    Some(block(number - 1, 0)),
                    vec![(block(number, 0), vec![0])],
                ))
                .unwrap();
        }
        // when rolling back to the expired checkpoint's block
        let result = engine.rollback_at_or_below(1);
        // then it is refused rather than restored against a window that cannot serve it
        assert_eq!(
            result,
            Err(RollbackError::NoCheckpointAtOrBelow { block: 1 })
        );
        assert_eq!(engine.checkpoint_count(), 0);
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
    fn checkpoint_scans_follow_store_order_across_the_wrap() {
        // given 3 slots checkpointed at blocks 1, 2, 3, and 4, so block 4 overwrote
        // block 1 and the oldest slot sits after the write position
        let mut engine = engine_with_checkpoints(3);
        let mut boundary = None;
        for number in 1u64..=4 {
            engine
                .apply_batch(&batch_of(boundary, vec![(block(number, 0), vec![0])]))
                .unwrap();
            engine.checkpoint();
            boundary = Some(block(number, 0));
        }
        // when reading the slot scans
        // then count, oldest, and newest-at-or-below all follow store order
        assert_eq!(engine.checkpoint_count(), 3);
        assert_eq!(engine.durable_point(), Some(Position::new(2, 0)));
        assert_eq!(
            engine.rollback_at_or_below(3),
            Ok(Some(Position::new(3, 0)))
        );
    }

    #[test]
    fn count_at_or_below_matches_partition_point() {
        // given strictly ascending lanes of every length up to 9
        for len in 0u32..=9 {
            let lane: Vec<u32> = (0..len).map(|i| 2 * i + 1).collect();
            // when counting at every bound from below the first to past the last
            for bound in 0..=u64::from(2 * len + 1) {
                // then the count agrees with std's partition point
                let expected = lane.partition_point(|index| u64::from(*index) <= bound);
                assert_eq!(
                    count_at_or_below(&lane, bound),
                    expected,
                    "{lane:?} {bound}"
                );
            }
        }
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
    fn expired_slot_stays_dead_after_rollback_to_a_cursorless_slot() {
        // given a ring of 2, a cursorless slot, and a slot at (1, 1) that expired once
        // blocks 2 and 3 pushed block 1 out of the ring
        let mut engine = Engine::new(
            RecordingFold::default(),
            EngineConfig {
                ring_capacity: 2,
                checkpoint_slots: 2,
            },
        )
        .unwrap();
        engine.checkpoint();
        engine
            .apply_batch(&batch_of(None, vec![(block(1, 0), vec![0, 1])]))
            .unwrap();
        engine.checkpoint();
        engine
            .apply_batch(&batch_of(Some(block(1, 0)), vec![(block(2, 0), vec![0])]))
            .unwrap();
        engine
            .apply_batch(&batch_of(Some(block(2, 0)), vec![(block(3, 0), vec![0])]))
            .unwrap();
        // when rolling back to the cursorless slot, then folding a replacement block 1
        let to = engine.rollback_at_or_below(2).unwrap();
        engine
            .apply_batch(&batch_of(None, vec![(block(1, 1), vec![0])]))
            .unwrap();
        engine.checkpoint();
        // then the expired slot stays dead: the durable point is the new checkpoint,
        // which holds only the replacement block's event
        assert_eq!(to, None);
        assert_eq!(engine.cursor(), Some(Position::new(1, 0)));
        assert_eq!(engine.durable_point(), engine.cursor());
        assert_eq!(
            engine.durable_fold().map(|fold| fold.applied.clone()),
            Some(vec![(Position::new(1, 0), 0)])
        );
    }

    #[test]
    fn repeated_rollback_to_same_checkpoint_succeeds() {
        // given one checkpoint
        let mut engine = engine_with_checkpoints(4);
        engine
            .apply_batch(&batch_of(None, vec![(block(1, 0), vec![0])]))
            .unwrap();
        engine.checkpoint();
        let checkpoint_view = engine.fold().applied.clone();
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
        assert_eq!(engine.fold().applied, checkpoint_view);
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

#[cfg(verus_keep_ghost)]
verus! {
impl<F> View for Engine<F> {
    type V = EngineView;

    closed spec fn view(&self) -> EngineView {
        EngineView {
            fold: fview::<F>(&self.fold),
            cursor: self.cursor,
            ring: self.ring@,
            slots: self.checkpoints@,
            status: self.status,
            last_verified: self.last_verified,
            skips: self.skips,
            resets: self.resets,
        }
    }
}

impl<F> Engine<F> {
    /// Plan `wf(Engine)`: ring and slot representation plus the view-level clauses.
    pub closed spec fn wf(&self) -> bool {
        &&& self.ring.wf()
        &&& self.checkpoints.wf()
        &&& self@.wf()
    }

    /// The view-level clauses of `wf`, for modules that cannot see its body.
    pub(crate) proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            self@.wf(),
            self@.ring.len() <= 0x10_0000,
    {
        self.ring.lemma_wf();
    }
}

impl<F> Engine<F> {
    /// `EngineView::live_at` is the checkpoint ring's `live_view` over the engine ring.
    proof fn lemma_live_bridge(&self)
        ensures
            forall|j: int| #[trigger] self@.live_at(j) == self.checkpoints.live_view(self.ring@, j),
    {
        assert forall|j: int| #[trigger] self@.live_at(j) == self.checkpoints.live_view(
            self.ring@,
            j,
        ) by {
            self.checkpoints.lemma_live_view(self.ring@, j);
        }
    }

    /// What `CheckpointRing::oldest` finds is `EngineView::oldest_live_from(0)`.
    proof fn lemma_oldest_bridge(&self)
        ensures
            forall|k: int|
                0 <= k < self.checkpoints@.len() && #[trigger] self.checkpoints.live_view(self.ring@, k)
                    && (forall|j: int| 0 <= j < k ==> !#[trigger] self.checkpoints.live_view(self.ring@, j))
                    ==> self@.oldest_live_from(0) == Some(k),
            (forall|j: int|
                0 <= j < self.checkpoints@.len() ==> !#[trigger] self.checkpoints.live_view(self.ring@, j))
                ==> self@.oldest_live_from(0) is None,
    {
        self.lemma_live_bridge();
        assert forall|k: int|
            0 <= k < self.checkpoints@.len() && #[trigger] self.checkpoints.live_view(self.ring@, k)
                && (forall|j: int| 0 <= j < k ==> !#[trigger] self.checkpoints.live_view(self.ring@, j))
                implies self@.oldest_live_from(0) == Some(k) by {
            assert forall|j: int| 0 <= j < k implies !#[trigger] self@.live_at(j) by {
                assert(!self.checkpoints.live_view(self.ring@, j));
            }
            self@.lemma_oldest_live(0, k);
        }
        if forall|j: int|
            0 <= j < self.checkpoints@.len() ==> !#[trigger] self.checkpoints.live_view(self.ring@, j) {
            assert forall|j: int| 0 <= j < self@.slots.len() implies !#[trigger] self@.live_at(j) by {
                assert(!self.checkpoints.live_view(self.ring@, j));
            }
            self@.lemma_no_live(0);
        }
    }
}

/// Entry `k` of `slots` after `drop_newer(t)`.
spec fn dropped(s: Option<SlotView>, t: Option<Position>) -> Option<SlotView> {
    if s is Some && opt_lt(t, s.unwrap().cursor) {
        None
    } else {
        s
    }
}

/// T5a and T5d for `checkpoint`: storing the cursor keeps `wf`, `Inv` over the same log,
/// and the anchors with the new slot anchored at the ring tip.
proof fn lemma_checkpoint_view<F: Fold>(pre: EngineView, post: EngineView)
    requires
        pre.wf(),
        pre.status is Active,
        pre.slots.len() > 0,
        post == (EngineView {
            slots: pre.slots.drop_first().push(Some(SlotView { fold: pre.fold, cursor: pre.cursor })),
            ..pre
        }),
    ensures
        post.wf(),
        forall|init: int, log: Seq<(Position, F::Event)>|
            #[trigger] pre.inv::<F, F::Event, F::Error>(init, log) ==> post.inv::<
                F,
                F::Event,
                F::Error,
            >(init, log),
        forall|a: Seq<Option<BlockRef>>|
            #[trigger] pre.anchored(a) ==> post.anchored(pre.stored_anchors(a)),
{
    let n = pre.slots.len() as int;
    assert forall|j: int| 0 <= j < n - 1 implies #[trigger] post.slots[j] == pre.slots[j + 1] by {}
    assert(post.slots[n - 1] == Some(SlotView { fold: pre.fold, cursor: pre.cursor }));
    // wf: every stored cursor is at or below the cursor, so the new newest keeps the order.
    assert forall|i: int, j: int|
        0 <= i < j < n && post.slots[i] is Some && post.slots[j] is Some implies opt_le(
        #[trigger] post.slots[i].unwrap().cursor,
        #[trigger] post.slots[j].unwrap().cursor,
    ) by {
        if j < n - 1 {
            assert(pre.slots[i + 1] == post.slots[i] && pre.slots[j + 1] == post.slots[j]);
        } else {
            assert(pre.slots[i + 1] == post.slots[i]);
        }
    }
    assert forall|i: int| 0 <= i < n && #[trigger] post.slots[i] is Some implies opt_le(
        post.slots[i].unwrap().cursor,
        post.cursor,
    ) by {
        if i < n - 1 {
            assert(pre.slots[i + 1] == post.slots[i]);
        }
    }
    assert forall|init: int, log: Seq<(Position, F::Event)>|
        #[trigger] pre.inv::<F, F::Event, F::Error>(init, log) implies post.inv::<
        F,
        F::Event,
        F::Error,
    >(init, log) by {
        // All of the log is at or below the cursor, so the new slot folded all of it.
        if log.len() > 0 {
            assert(opt_le(Some(log[log.len() - 1].0), pre.cursor));
        }
        assert(upto::<F::Event>(log, pre.cursor) == log);
        assert forall|j: int| 0 <= j < n && #[trigger] post.slots[j] is Some implies crate::verus::model::run::<
            F,
            F::Event,
            F::Error,
        >((init, false), upto::<F::Event>(log, post.slots[j].unwrap().cursor)) == (
            post.slots[j].unwrap().fold,
            false,
        ) by {
            if j < n - 1 {
                assert(pre.slots[j + 1] == post.slots[j]);
            }
        }
    }
    assert forall|a: Seq<Option<BlockRef>>| #[trigger] pre.anchored(a) implies post.anchored(
        pre.stored_anchors(a),
    ) by {
        let b = pre.stored_anchors(a);
        assert forall|k: int|
            #[trigger] post.slots[k] is Some && post.live_at(k) && post.slots[k].unwrap().cursor is Some implies {
            &&& b[k] is Some
            &&& b[k].unwrap().number == post.slots[k].unwrap().cursor.unwrap().block
            &&& post.ring.contains(b[k].unwrap())
        } by {
            if k < n - 1 {
                assert(pre.slots[k + 1] == post.slots[k]);
                assert(pre.live_at(k + 1));
                assert(b[k] == a[k + 1]);
            } else {
                assert(post.ring[post.ring.len() - 1] == post.ring.last());
            }
        }
    }
}

/// T5a, T5b and T5d for `rollback_at_or_below`, over the views.
proof fn lemma_rollback_view<F: Fold>(pre: EngineView, post: EngineView, block: u64, k: int)
    requires
        pre.wf(),
        pre.rollback_target(block, k),
        ({
            let t = pre.slots[k].unwrap().cursor;
            &&& post.fold == pre.slots[k].unwrap().fold
            &&& post.cursor == t
            &&& t is None ==> post.ring.len() == 0
            &&& t matches Some(c) ==> prefix_at_or_below(pre.ring, c.block, post.ring.len() as int)
                && post.ring == pre.ring.subrange(0, post.ring.len() as int)
            &&& post.slots.len() == pre.slots.len()
            &&& forall|j: int|
                0 <= j < pre.slots.len() ==> #[trigger] post.slots[j] == dropped(pre.slots[j], t)
            &&& post.status is Active
            &&& post.last_verified is None
            &&& post.skips == pre.skips && post.resets == pre.resets
        }),
        crate::verus::model::ring_ascending(post.ring),
    ensures
        post.wf(),
        forall|j: int|
            #[trigger] pre.live_at(j) && qualifies(pre.slots[j].unwrap(), block) ==> opt_le(
                pre.slots[j].unwrap().cursor,
                post.cursor,
            ),
        forall|init: int, log: Seq<(Position, F::Event)>|
            #[trigger] pre.inv::<F, F::Event, F::Error>(init, log) ==> post.inv::<
                F,
                F::Event,
                F::Error,
            >(init, upto::<F::Event>(log, post.cursor)),
        forall|a: Seq<Option<BlockRef>>| #[trigger] pre.anchored(a) ==> post.anchored(a),
{
    let t = post.cursor;
    let n = pre.slots.len() as int;
    // Kept slots are at or below t.
    assert forall|j: int| 0 <= j < n && #[trigger] post.slots[j] is Some implies post.slots[j]
        == pre.slots[j] && opt_le(post.slots[j].unwrap().cursor, t) by {
        lemma_opt_lt_order(t, pre.slots[j].unwrap().cursor, None);
    }
    // T5b max: newer qualifying slots are excluded, older ones are ordered below slot k.
    assert forall|j: int| #[trigger] pre.live_at(j) && qualifies(pre.slots[j].unwrap(), block) implies opt_le(
        pre.slots[j].unwrap().cursor,
        t,
    ) by {
        if j < k {
            assert(opt_le(pre.slots[j].unwrap().cursor, pre.slots[k].unwrap().cursor));
        }
    }
    // The cursor block is the truncated ring's tip.
    match t {
        Some(c) => {
            let i = choose|i: int| 0 <= i < pre.ring.len() && #[trigger] pre.ring[i].number == c.block;
            assert(pre.ring[i].number == c.block);
            let m = post.ring.len() as int;
            assert(i < m);
            assert(post.ring[m - 1] == pre.ring[m - 1]);
            if i < m - 1 {
                assert(pre.ring[i].number < pre.ring[m - 1].number);
            }
            assert(post.ring.last().number == c.block);
        },
        None => {},
    }
    assert(post.wf()) by {
        assert forall|i: int, j: int|
            0 <= i < j < post.slots.len() && post.slots[i] is Some && post.slots[j] is Some implies opt_le(
            #[trigger] post.slots[i].unwrap().cursor,
            #[trigger] post.slots[j].unwrap().cursor,
        ) by {
            assert(post.slots[i] == pre.slots[i] && post.slots[j] == pre.slots[j]);
        }
    }
    assert forall|init: int, log: Seq<(Position, F::Event)>|
        #[trigger] pre.inv::<F, F::Event, F::Error>(init, log) implies post.inv::<
        F,
        F::Event,
        F::Error,
    >(init, upto::<F::Event>(log, t)) by {
        let l2 = upto::<F::Event>(log, t);
        lemma_upto::<F::Event>(log, t);
        assert(lt_sorted(l2)) by {
            assert forall|i: int, j: int| 0 <= i < j < l2.len() implies lt(
                #[trigger] l2[i].0,
                #[trigger] l2[j].0,
            ) by {
                assert(l2[i] == log[i] && l2[j] == log[j]);
            }
        }
        assert forall|i: int| 0 <= i < l2.len() implies opt_le(Some(#[trigger] l2[i].0), t) by {
            assert(l2[i] == log[i]);
        }
        assert forall|j: int| 0 <= j < n && #[trigger] post.slots[j] is Some implies crate::verus::model::run::<
            F,
            F::Event,
            F::Error,
        >((init, false), upto::<F::Event>(l2, post.slots[j].unwrap().cursor)) == (
            post.slots[j].unwrap().fold,
            false,
        ) by {
            lemma_upto_upto::<F::Event>(log, post.slots[j].unwrap().cursor, t);
        }
    }
    assert forall|a: Seq<Option<BlockRef>>| #[trigger] pre.anchored(a) implies post.anchored(a) by {
        assert forall|j: int|
            #[trigger] post.slots[j] is Some && post.live_at(j) && post.slots[j].unwrap().cursor is Some implies {
            &&& a[j] is Some
            &&& a[j].unwrap().number == post.slots[j].unwrap().cursor.unwrap().block
            &&& post.ring.contains(a[j].unwrap())
        } by {
            let c = post.slots[j].unwrap().cursor.unwrap();
            let tc = t.unwrap();
            let m = post.ring.len() as int;
            let i = choose|i: int| 0 <= i < m && #[trigger] post.ring[i].number == c.block;
            assert(pre.ring[i] == post.ring[i]);
            assert(pre.live_at(j));
            let i0 = choose|i0: int| 0 <= i0 < pre.ring.len() && pre.ring[i0] == a[j].unwrap();
            assert(c.block <= tc.block);
            if i0 >= m {
                assert(pre.ring[i0].number > tc.block);
            }
            assert(post.ring[i0] == a[j].unwrap());
        }
    }
}
} // verus!
