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
    crate::batch::{
        lemma_end_bounds,
        lemma_flat_upto,
    },
    crate::verus::{
        model::{
            BatchView,
            EngineView,
            SlotView,
            accepted,
            applied,
            calls,
            checked_freshness,
            count_le,
            cursor_after,
            fold,
            forked,
            fview,
            lemma_applied_all,
            lemma_applied_concat,
            lemma_applied_extend,
            lemma_applied_prefix,
            lemma_applied_stop,
            lemma_count_le,
            lemma_flat_prefix,
            lemma_newer_add,
            lemma_newer_sorted,
            lemma_newer_split,
            lemma_opt_lt_order,
            lemma_ring_ext_from,
            lemma_ring_ext_push,
            lemma_run_concat,
            lemma_run_push,
            lemma_skips_concat,
            lemma_upto,
            lemma_upto_append,
            lemma_upto_upto,
            live_count,
            lt,
            lt_sorted,
            newer,
            ok_calls,
            opt_le,
            opt_lt,
            prefix_at_or_below,
            qualifies,
            ring_after,
            ring_ext,
            ring_push,
            run,
            sat_add,
            skips,
            span_refs,
            split_at_tip,
            stopped,
            upto,
        },

        tcb::axiom_clone_preserves_fview,
    },
    vstd::prelude::*,
};

/// Smallest allowed observed-block ring capacity.
#[cfg_attr(verus_keep_ghost, verus_verify)]
const MIN_RING_CAPACITY: usize = 2;
/// Largest allowed observed-block ring capacity.
#[cfg_attr(verus_keep_ghost, verus_verify)]
const MAX_RING_CAPACITY: usize = 1 << 20;
/// Largest allowed checkpoint slot count.
#[cfg_attr(verus_keep_ghost, verus_verify)]
const MAX_CHECKPOINT_SLOTS: usize = 1 << 16;

/// Fixed engine construction parameters.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EngineConfig {
    /// Observed-block window W; power of two between 2 and 1 << 20.
    pub ring_capacity: usize,
    /// Retained checkpoint slots K, at most 1 << 16; zero disables rollback.
    pub checkpoint_slots: usize,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Default for EngineConfig {
    fn default() -> Self {
        Self {
            ring_capacity: 1024,
            checkpoint_slots: 4,
        }
    }
}

impl EngineConfig {
    /// Accepts a power-of-two ring capacity and a slot count within the allowed ranges.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            r is Ok <==> self.valid(),
    ))]
    pub(crate) fn validate(&self) -> Result<(), ConfigError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(MIN_RING_CAPACITY == 2);
            assert(MAX_RING_CAPACITY == 0x10_0000) by (compute);
            assert(MAX_CHECKPOINT_SLOTS == 0x1_0000) by (compute);
        }
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
        if self.checkpoint_slots > MAX_CHECKPOINT_SLOTS {
            return Err(ConfigError::CheckpointSlotsOutOfRange {
                got: self.checkpoint_slots,
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

#[cfg_attr(verus_keep_ghost, cfg_eval, verus_verify)]
impl<F: Fold> Engine<F> {
    /// Builds an engine with an empty ring and no retained checkpoints.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            r is Ok <==> config.valid(),
            r matches Ok(e) ==> e.wf() && e@ == Self::fresh(fview::<F>(&fold), config),
    ))]
    pub fn new(fold: F, config: EngineConfig) -> Result<Self, ConfigError> {
        config.validate()?;
        let engine = Self {
            ring: BlockRing::with_capacity(config.ring_capacity),
            checkpoints: CheckpointRing::new(config.checkpoint_slots),
            fold,
            cursor: None,
            status: EngineStatus::Active,
            last_verified: None,
            skips: 0,
            resets: 0,
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(engine@.ring =~= Seq::empty());
        }
        Ok(engine)
    }
}

impl<F: Fold> Engine<F> {
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

    /// Applies one poll's batch: total order, dedup, boundary recheck, fork detection.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
            batch@.wf(),
        ensures
            final(self).wf(),
            final(self).window() == old(self).window(),
            // A rejection changes nothing but the checked freshness.
            r matches Err(e) && !(e is Halted || e is Poisoned) ==> !accepted(old(self)@, batch@)
                && final(self)@ == (EngineView {
                last_verified: checked_freshness(old(self)@, batch@),
                ..old(self)@
            }),
            // Unreachable under wf.
            !(r matches Err(ApplyError::CursorBlockUnobserved { .. })),
            r matches Err(ApplyError::Shape(_)) ==> !batch@.shaped(),
            r matches Err(ApplyError::BoundaryNumberMismatch { .. }) ==> old(self)@.cursor is Some
                && batch@.boundary is Some && batch@.boundary.unwrap().number != old(self)@.cursor.unwrap().block,
            r matches Err(ApplyError::NotActive { .. }) ==> !(old(self)@.status is Active),
            r is Ok ==> accepted(old(self)@, batch@) && final(self)@.status == old(self)@.status,
            accepted(old(self)@, batch@) ==> (r is Ok <==> !stopped::<F, F::Event, F::Error>(
                old(self)@,
                batch@,
            )),
            r matches Err(e) ==> ((e is Halted || e is Poisoned) ==> accepted(old(self)@, batch@)
                && stopped::<F, F::Event, F::Error>(old(self)@, batch@) && stops_at(
                e,
                final(self)@.status,
                calls::<F, F::Event, F::Error>(old(self)@, batch@).last().0,
            )),
            // The fold ran on `calls`, and the counts split the batch.
            final(self)@.fold == fold::<F, F::Event, F::Error>(
                old(self)@.fold,
                calls::<F, F::Event, F::Error>(old(self)@, batch@),
            ),
            r matches Ok(s) ==> s.deduped == batch@.flat().len() - newer(
                old(self)@.cursor,
                batch@.flat(),
            ).len() && s.applied + s.skipped == newer(old(self)@.cursor, batch@.flat()).len(),
            r matches Ok(s) ==> s.skipped == skips::<F, F::Event, F::Error>(
                (old(self)@.fold, false),
                calls::<F, F::Event, F::Error>(old(self)@, batch@),
            ) && final(self)@.skips == sat_add(old(self)@.skips, s.skipped as int),
            // Cursor and ring.
            final(self)@.cursor == cursor_after(
                old(self)@.cursor,
                ok_calls::<F, F::Event, F::Error>(old(self)@, batch@),
            ),
            accepted(old(self)@, batch@) ==> ring_after(
                old(self)@,
                final(self)@,
                batch@,
                old(self).window(),
            ),
            final(self)@.slots == old(self)@.slots,
            final(self)@.resets == old(self)@.resets,
            old(self)@.status is Unrecoverable ==> final(self)@.status == old(self)@.status,
            // After Ok nothing of the batch is newer than the cursor.
            r is Ok ==> newer(final(self)@.cursor, batch@.flat()).len() == 0,
            // `Inv` and the slot anchors carry over.
            forall|init: int, log: Seq<(Position, F::Event)>|
                #[trigger] old(self)@.inv::<F, F::Event, F::Error>(init, log) ==> final(self)@.inv::<F, F::Event, F::Error>(init, log + calls::<F, F::Event, F::Error>(old(self)@, batch@)),
            forall|a: Seq<Option<BlockRef>>|
                #[trigger] old(self)@.anchored(a) ==> final(self)@.anchored(a),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verifier::rlimit(200))]
    pub fn apply_batch(
        &mut self,
        batch: &Batch<F::Event>,
    ) -> Result<ApplySummary, ApplyError<F::Error>> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost v0 = self@;
            let ghost bv = batch@;
            let ghost w = self.window();
            let ghost i0: int = match v0.cursor {
                None => 0,
                Some(c) => count_le(bv.blocks, c.block),
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            self.lemma_wf();
            self.ring.lemma_wf();
            lemma_rejected::<F>(v0, v0, bv);
        }
        if !self.status.is_active() {
            return Err(ApplyError::NotActive {
                status: self.status,
            });
        }
        if let Err(shape) = batch.validate() {
            return Err(ApplyError::Shape(shape));
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            lemma_count_le(bv.blocks, match v0.cursor { None => 0, Some(c) => c.block });
            assert(split_at_tip(bv, v0.cursor, i0));
        }

        let mut from = Position::new(0, 0);
        if let Some(cursor) = self.cursor {
            from = cursor;
            let boundary = batch.boundary.ok_or(ApplyError::MissingBoundary)?;
            if boundary.number != cursor.block {
                return Err(ApplyError::BoundaryNumberMismatch {
                    expected: cursor.block,
                    got: boundary.number,
                });
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(self@.ring[self@.ring.len() - 1].number == cursor.block);
            }
            let observed_hash = self.ring.hash_at(cursor.block).ok_or(
                ApplyError::CursorBlockUnobserved {
                    block: cursor.block,
                },
            )?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(observed_hash == self@.ring[self@.ring.len() - 1].hash);
            }
            if observed_hash != boundary.hash {
                return Err(fork_suspected(cursor.block, observed_hash, boundary));
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                broadcast use vstd::array::group_array_axioms;
                assert(observed_hash == boundary.hash);
                assert(boundary.number == v0.ring.last().number);
                assert(boundary.hash == v0.ring.last().hash);
                assert(boundary == v0.ring.last());
            }
            self.last_verified = Some(boundary);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(self@ == (EngineView { last_verified: checked_freshness(v0, bv), ..v0 }));
            lemma_rejected::<F>(v0, self@, bv);
            assert(bv.flat_upto(0).len() == 0);
            assert(newer(v0.cursor, bv.flat_upto(0)).len() == 0) by {
                reveal(Seq::filter);
            }
            assert(ring_ext(v0.ring, w, span_refs(bv).subrange(i0, i0)) == v0.ring);
            assert(setup(v0, bv, w, i0)) by {
                reveal(setup);
            }
            assert(loop_state::<F>(v0, bv, w, i0, self@, 0)) by {
                reveal(loop_state);
                reveal(tip_state);
            }
        }

        let mut summary = ApplySummary {
            applied: 0,
            deduped: 0,
            skipped: 0,
        };
        let mut start = 0usize;
        // A panic out of `Fold::apply` unwinds past the cursor update with the fold
        // partly mutated, so the spans run under Poisoned at the starting cursor and a
        // caught panic never leaves an engine that the next batch trusts. The loop proof
        // reads the engine with its batch-start status.
        let mark = EngineStatus::Poisoned { at: from };
        self.status = mark;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                self.wf(),
                self.window() == w,
                w == old(self).window(),
                batch@ == bv,
                v0 == old(self)@,
                bv.wf(),
                setup(v0, bv, w, i0),
                v0.cursor is Some ==> bv.boundary == Some(v0.ring.last()),
                self@.status == mark,
                loop_state::<F>(v0, bv, w, i0, EngineView { status: v0.status, ..self@ }, i as int),
                start == bv.start(i as int),
                forall|k: int, j: int|
                    #![trigger bv.blocks[k], v0.ring[j]]
                    0 <= k < i && k < i0 && 0 <= j < v0.ring.len() && v0.ring[j].number
                        == bv.blocks[k] ==> v0.ring[j].hash == bv.hashes[k],
                summary.deduped == bv.flat_upto(i as int).len() - newer(
                    v0.cursor,
                    bv.flat_upto(i as int),
                ).len(),
                summary.applied + summary.skipped == newer(v0.cursor, bv.flat_upto(i as int)).len(),
                summary.skipped == skips::<F, F::Event, F::Error>(
                    (v0.fold, false),
                    newer(v0.cursor, bv.flat_upto(i as int)),
                ),
                self@.skips == sat_add(v0.skips, summary.skipped as int),
                bv.flat_upto(i as int).len() == start,
        ))]
        for i in 0..batch.span_count() {
            #[cfg(verus_keep_ghost)]
            proof! {
                self.lemma_wf();
                lemma_end_bounds(bv, i as int);
                lemma_flat_upto(bv, i as int);
                lemma_flat_upto(bv, i as int + 1);
            }
            let span = batch.span(i, start);
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost pre = EngineView { status: v0.status, ..self@ };
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(span_seq(span) =~= bv.span_events(i as int));
                lemma_span_redelivered::<F>(v0, bv, w, i0, pre, i as int);
            }
            start += span.events.len();
            let redelivered = match self.cursor {
                Some(cursor) => span.number <= cursor.block,
                None => false,
            };
            if redelivered {
                match self.ring.hash_at(span.number) {
                    Some(observed_hash) if &observed_hash != span.hash => {
                        self.status = EngineStatus::Active;
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            assert(self@ == pre);
                            let j = choose|j: int|
                                0 <= j < v0.ring.len() && #[trigger] v0.ring[j].number == bv.blocks[i as int];
                            assert(v0.ring[j].hash != bv.hashes[i as int]);
                            assert(forked(v0, bv));
                            lemma_rejected::<F>(v0, self@, bv);
                        }
                        return Err(fork_suspected(
                            span.number,
                            observed_hash,
                            span.block(),
                        ));
                    }
                    _ => {
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            broadcast use vstd::array::group_array_axioms;
                            assert forall|j: int|
                                0 <= j < v0.ring.len() && #[trigger] v0.ring[j].number == bv.blocks[i as int]
                                    implies v0.ring[j].hash == bv.hashes[i as int] by {
                                assert(self.ring@[j].number == span.number);
                            }
                        }
                    }
                }
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                lemma_span_indices(v0, bv, w, i0, i as int, span.log_indices@);
            }
            let applied = self.apply_span(&span, &mut summary);
            #[cfg(verus_keep_ghost)]
            proof! {
                lemma_span_newer::<F>(v0, bv, w, i0, pre, i as int);
                let sq = bv.span_events(i as int);
                let blk = bv.block(i as int);
                if applied is Ok {
                    lemma_span_skips::<F>(v0, bv, w, i0, pre, i as int);
                    let post = EngineView { status: v0.status, ..self@ };
                    assert(span_post::<F>(pre, post, w, sq, blk, true));
                    lemma_span_ok::<F>(v0, bv, w, i0, pre, post, i as int);
                } else {
                    assert(span_post::<F>(pre, self@, w, sq, blk, false));
                    lemma_span_stop::<F>(v0, bv, w, i0, pre, self@, i as int);
                }
            }
            match applied {
                Ok(()) => {}
                Err(e) => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        reveal(setup);
                        reveal(stop_state);
                        let k = if tip_state(v0, bv, w, i0, self@, i as int) { i as int } else { i as int + 1 };
                        lemma_not_forked(v0, bv, w, i0, i as int + 1);
                        lemma_apply_post::<F>(v0, bv, w, i0, self@, k);
                    }
                    return Err(e);
                }
            }
        }
        self.status = EngineStatus::Active;
        #[cfg(verus_keep_ghost)]
        proof! {
            let n = bv.ends.len() as int;
            reveal(setup);
            lemma_not_forked(v0, bv, w, i0, n);
            lemma_loop_done::<F>(v0, bv, w, i0, self@);
            lemma_apply_post::<F>(v0, bv, w, i0, self@, n);
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
            // Unrecoverable is left only by `reset`: rollback refuses it.
            old(self)@.status is Unrecoverable ==> r is Err,
            // The target is the newest stored qualifying live slot, whose cursor is the
            // maximum over them, and the post-state.
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
            // `Inv` holds over the log truncated at the restored cursor.
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
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            old(self).wf(),
            ring.wf(),
            (EngineView { cursor, ring: ring@, ..old(self)@ }).wf(),
        ensures
            final(self).wf(),
            final(self)@ == (EngineView { cursor, ring: ring@, ..old(self)@ }),
    ))]
    pub(crate) fn restore_cursor_and_ring(
        &mut self,
        cursor: Option<Position>,
        ring: BlockRing,
    ) {
        self.cursor = cursor;
        self.ring = ring;
    }

    /// Applies every event of one span, deduping positions at or below the cursor.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
            span.log_indices@.len() == span.events@.len(),
            forall|j: int, k: int|
                0 <= j < k < span.log_indices@.len() ==> span.log_indices@[j] < span.log_indices@[k],
            old(summary).deduped + old(summary).applied + old(summary).skipped + span.events@.len()
                <= usize::MAX,
        ensures
            final(self).wf(),
            final(self).window() == old(self).window(),
            span_post::<F>(
                old(self)@,
                final(self)@,
                old(self).window(),
                span_seq(*span),
                BlockRef { number: span.number, hash: *span.hash },
                r is Ok,
            ),
            r matches Err(e) ==> stops_at(
                e,
                final(self)@.status,
                applied::<F, F::Event, F::Error>(
                    old(self)@.fold,
                    newer(old(self)@.cursor, span_seq(*span)),
                ).last().0,
            ),
            r is Ok ==> final(summary).deduped == old(summary).deduped + span.events@.len() - newer(
                old(self)@.cursor,
                span_seq(*span),
            ).len(),
            r is Ok ==> final(summary).applied + final(summary).skipped == old(summary).applied
                + old(summary).skipped + newer(old(self)@.cursor, span_seq(*span)).len(),
            r is Ok ==> final(summary).skipped == old(summary).skipped + skips::<F, F::Event, F::Error>(
                (old(self)@.fold, false),
                newer(old(self)@.cursor, span_seq(*span)),
            ),
            r is Ok ==> final(summary).skipped >= old(summary).skipped && final(self)@.skips == sat_add(
                old(self)@.skips,
                final(summary).skipped - old(summary).skipped,
            ),
    ))]
    fn apply_span(
        &mut self,
        span: &SpanView<'_, F::Event>,
        summary: &mut ApplySummary,
    ) -> Result<(), ApplyError<F::Error>> {
        let number = span.number;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost pre = self@;
            let ghost sq = span_seq(*span);
            let ghost p = newer(pre.cursor, sq);
        }
        let deduped = match self.cursor {
            Some(cursor) if number > cursor.block => 0,
            Some(cursor) if number < cursor.block => span.log_indices.len(),
            Some(cursor) => count_at_or_below(span.log_indices, cursor.log_index),
            None => 0,
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|k: int| 0 <= k < deduped implies !opt_lt(pre.cursor, Some(#[trigger] sq[k].0)) by {
                assert(sq[k].0.log_index == span.log_indices@[k] as u64);
            }
            assert forall|k: int| deduped <= k < sq.len() implies opt_lt(pre.cursor, Some(#[trigger] sq[k].0)) by {
                assert(sq[k].0.log_index == span.log_indices@[k] as u64);
            }
            lemma_newer_split(pre.cursor, sq, deduped as int);
        }
        summary.deduped += deduped as u64;
        let (indices, events) = if deduped == 0 {
            (span.log_indices, span.events)
        } else {
            (
                span.log_indices.split_at(deduped).1,
                span.events.split_at(deduped).1,
            )
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(indices@ =~= span.log_indices@.subrange(deduped as int, sq.len() as int));
            assert(events@ =~= span.events@.subrange(deduped as int, sq.len() as int));
            assert forall|k: int| 0 <= k < p.len() implies #[trigger] p[k] == (
                Position { block: number, log_index: indices@[k] as u64 },
                events@[k],
            ) && opt_lt(pre.cursor, Some(p[k].0)) by {
                assert(p[k] == sq[deduped + k]);
            }
        }
        let len = indices.len();
        if len == 0 {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(p.len() == 0);
                assert(self@ == pre);
            }
            return Ok(());
        }
        // lanes are equal length by construction, so the paired walk drops no event
        let paired = if len < events.len() {
            len
        } else {
            events.len()
        };

        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                self.wf(),
                self.window() == old(self).window(),
                pre == old(self)@,
                self@ == (EngineView { fold: self@.fold, skips: self@.skips, ..pre }),
                paired == len,
                len == indices@.len(),
                len == events@.len(),
                len == p.len(),
                p == newer(pre.cursor, span_seq(*span)),
                forall|k: int|
                    0 <= k < p.len() ==> #[trigger] p[k] == (
                        Position { block: number, log_index: indices@[k] as u64 },
                        events@[k],
                    ) && opt_lt(pre.cursor, Some(p[k].0)),
                run::<F, F::Event, F::Error>((pre.fold, false), p.subrange(0, offset as int))
                    == (self@.fold, false),
                number == span.number,
                deduped + len == span.events@.len(),
                summary.deduped == old(summary).deduped + deduped,
                summary.applied + summary.skipped == old(summary).applied + old(summary).skipped
                    + offset,
                summary.skipped == old(summary).skipped + skips::<F, F::Event, F::Error>(
                    (pre.fold, false),
                    p.subrange(0, offset as int),
                ),
                summary.skipped >= old(summary).skipped,
                self@.skips == sat_add(pre.skips, summary.skipped - old(summary).skipped),
                old(summary).deduped + old(summary).applied + old(summary).skipped
                    + span.events@.len() <= usize::MAX,
        ))]
        for offset in 0..paired {
            let at = span_pos(number, indices[offset]);
            #[cfg(verus_keep_ghost)]
            proof! {
                let head = p.subrange(0, offset as int);
                assert(p.subrange(0, offset + 1) =~= head.push(p[offset as int]));
                assert(head.push(p[offset as int]).drop_last() =~= head);
                lemma_run_push::<F, F::Event, F::Error>((pre.fold, false), head, p[offset as int]);
            }
            match self.fold.apply(at, &events[offset]) {
                Ok(()) => summary.applied += 1,
                Err(FoldError::Skip(_)) => {
                    self.skips = self.skips.saturating_add(1);
                    summary.skipped += 1;
                }
                Err(FoldError::Halt(error)) => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        lemma_applied_stop::<F, F::Event, F::Error>(pre.fold, p, offset as int);
                    }
                    self.consumed_through(span, indices, offset);
                    return Err(self.halt(at, error));
                }
                Err(FoldError::Poison(error)) => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        lemma_applied_stop::<F, F::Event, F::Error>(pre.fold, p, offset as int);
                    }
                    self.consumed_through(span, indices, offset);
                    return Err(self.poison(at, error));
                }
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(p.subrange(0, len as int) =~= p);
            lemma_applied_all::<F, F::Event, F::Error>(pre.fold, p);
        }
        self.advance(span.number, span.hash, span_pos(number, indices[len - 1]));
        Ok(())
    }

    /// Places the cursor at the predecessor of `indices[offset]`; a no-op at offset 0,
    /// since nothing in this span was consumed yet.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            old(self).wf(),
            0 < offset <= indices@.len() ==> opt_le(
                old(self)@.cursor,
                Some(Position { block: span.number, log_index: indices@[offset - 1] as u64 }),
            ),
        ensures
            final(self).wf(),
            final(self).window() == old(self).window(),
            final(self)@ == if 0 < offset <= indices@.len() {
                advanced(
                    old(self)@,
                    old(self).window(),
                    BlockRef { number: span.number, hash: *span.hash },
                    Position { block: span.number, log_index: indices@[offset - 1] as u64 },
                )
            } else {
                old(self)@
            },
    ))]
    #[cold]
    fn consumed_through(
        &mut self,
        span: &SpanView<'_, F::Event>,
        indices: &[u32],
        offset: usize,
    ) {
        let Some(i) = offset.checked_sub(1) else {
            return;
        };
        if let Some(log_index) = indices.get(i) {
            let pos = Position::new(span.number, u64::from(*log_index));
            self.advance(span.number, span.hash, pos);
        }
    }

    /// Moves the cursor to `pos`, recording the block the first time the cursor enters it.
    ///
    /// Ring and cursor move together, so the ring's newest entry is the cursor block
    /// at every point a batch can return from.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            old(self).wf(),
            pos.block == number,
            opt_le(old(self)@.cursor, Some(pos)),
        ensures
            final(self).wf(),
            final(self).window() == old(self).window(),
            final(self)@ == advanced(old(self)@, old(self).window(), BlockRef { number, hash: *hash }, pos),
    ))]
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
        #[cfg(verus_keep_ghost)]
        proof! {
            self.ring.lemma_wf();
            let (pre, post) = (old(self)@, self@);
            if pre.cursor is Some {
                lemma_opt_lt_order(pre.cursor, pre.cursor, Some(pos));
            }
            assert forall|i: int|
                0 <= i < post.slots.len() && #[trigger] post.slots[i] is Some implies opt_le(
                post.slots[i].unwrap().cursor,
                post.cursor,
            ) by {
                lemma_opt_lt_order(post.slots[i].unwrap().cursor, pre.cursor, Some(pos));
            }
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).window() == old(self).window(),
            final(self)@ == (EngineView { status: EngineStatus::Halted { at }, ..old(self)@ }),
            r == (ApplyError::Halted { at, error }),
    ))]
    #[cold]
    fn halt(&mut self, at: Position, error: F::Error) -> ApplyError<F::Error> {
        self.status = EngineStatus::Halted { at };
        ApplyError::Halted { at, error }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).window() == old(self).window(),
            final(self)@ == (EngineView { status: EngineStatus::Poisoned { at }, ..old(self)@ }),
            r == (ApplyError::Poisoned { at, error }),
    ))]
    #[cold]
    fn poison(&mut self, at: Position, error: F::Error) -> ApplyError<F::Error> {
        self.status = EngineStatus::Poisoned { at };
        ApplyError::Poisoned { at, error }
    }
}

/// Position of a span event.
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == (Position { block: number, log_index: log_index as u64 }),
))]
fn span_pos(number: u64, log_index: u32) -> Position {
    Position::new(number, u64::from(log_index))
}

/// Count of the leading log indices at or below `bound`; the lane is strictly ascending.
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        log_indices@.len() <= usize::MAX,
        forall|i: int, j: int|
            0 <= i < j < log_indices@.len() ==> log_indices@[i] < log_indices@[j],
    ensures
        r <= log_indices@.len(),
        forall|k: int| 0 <= k < r ==> #[trigger] log_indices@[k] as u64 <= bound,
        forall|k: int| r <= k < log_indices@.len() ==> #[trigger] log_indices@[k] as u64 > bound,
))]
fn count_at_or_below(log_indices: &[u32], bound: u64) -> usize {
    let mut base = 0usize;
    let mut rest = log_indices;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            log_indices@.len() <= usize::MAX,
            forall|i: int, j: int|
                0 <= i < j < log_indices@.len() ==> log_indices@[i] < log_indices@[j],
            base + rest@.len() <= log_indices@.len(),
            rest@ == log_indices@.subrange(base as int, base + rest@.len()),
            forall|k: int| 0 <= k < base ==> #[trigger] log_indices@[k] as u64 <= bound,
            forall|k: int|
                base + rest@.len() <= k < log_indices@.len() ==> #[trigger] log_indices@[k] as u64 > bound,
        decreases rest@.len(),
    ))]
    while rest.len() > 1 {
        // both candidate windows keep len - half entries, as in std's binary search
        let half = rest.len() / 2;
        let high = rest.split_at(half).1;
        let low = rest.split_at(high.len()).0;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(rest@[half as int] == log_indices@[base + half]);
        }
        if u64::from(rest[half]) <= bound {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|k: int| 0 <= k < base + half implies #[trigger] log_indices@[k] as u64 <= bound by {
                    if k >= base {
                        assert(log_indices@[k] <= log_indices@[base + half]);
                    }
                }
            }
            base += half;
            rest = high;
        } else {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|k: int|
                    base + low@.len() <= k < log_indices@.len() implies #[trigger] log_indices@[k] as u64 > bound by {
                    if k < base + rest@.len() {
                        assert(log_indices@[base + half] <= log_indices@[k]);
                    }
                }
            }
            rest = low;
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        if rest@.len() == 1 {
            assert(rest@[0] == log_indices@[base as int]);
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
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == (ApplyError::<E>::ForkSuspected {
            observed: BlockRef { number, hash: observed_hash },
            refetched,
        }),
))]
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

    /// Counts applied events and panics on the event at `panic_at`.
    #[cfg(feature = "std")]
    struct PanicFold {
        applied: u32,
        panic_at: Position,
    }

    #[cfg(feature = "std")]
    impl Fold for PanicFold {
        type Event = u64;
        type Error = core::convert::Infallible;

        fn apply(
            &mut self,
            pos: Position,
            _event: &Self::Event,
        ) -> Result<(), FoldError<Self::Error>> {
            self.applied += 1;
            assert_ne!(pos, self.panic_at, "scripted fold panic");
            Ok(())
        }
    }

    #[cfg(feature = "std")]
    #[test]
    fn panic_in_fold_leaves_the_engine_poisoned() {
        // given a fold that counts the second event of a three-event span, then panics
        let fold = PanicFold {
            applied: 0,
            panic_at: Position::new(1, 1),
        };
        let config = EngineConfig {
            ring_capacity: 8,
            checkpoint_slots: 0,
        };
        let mut engine = Engine::new(fold, config).unwrap();
        let batch = batch_of(None, vec![(block(1, 0), vec![0, 1, 2])]);
        // when the panic is caught
        let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            engine.apply_batch(&batch)
        }));
        assert!(caught.is_err());
        // then the engine is Poisoned from where the batch started
        let poisoned = EngineStatus::Poisoned {
            at: Position::new(0, 0),
        };
        assert_eq!(engine.status(), poisoned);
        assert_eq!(engine.cursor(), None);
        // and applying the batch again is refused, never folding its events twice
        assert_eq!(
            engine.apply_batch(&batch),
            Err(ApplyError::NotActive { status: poisoned })
        );
        assert_eq!(engine.fold().applied, 2);
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
    fn config_rejects_slot_counts_past_the_bound() {
        for slots in [(1 << 16) + 1, 1 << 60, usize::MAX] {
            // given a slot count whose vector would overflow or exhaust the allocator
            let config = EngineConfig {
                ring_capacity: 8,
                checkpoint_slots: slots,
            };
            // when constructing
            let result = Engine::new(RecordingFold::default(), config);
            // then CheckpointSlotsOutOfRange, never a capacity-overflow panic
            assert_eq!(
                result.err(),
                Some(ConfigError::CheckpointSlotsOutOfRange { got: slots })
            );
        }
        // and the bound itself is accepted
        let config = EngineConfig {
            ring_capacity: 8,
            checkpoint_slots: 1 << 16,
        };
        assert!(Engine::new(RecordingFold::default(), config).is_ok());
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
        // given mark_unrecoverable with a horizon past the start block
        let cause = DivergenceCause::HorizonExceeded {
            needed: 0,
            horizon: 9,
        };
        let mut engine = new_engine();
        engine.mark_unrecoverable(cause);
        // when applying or rolling back
        let apply_result =
            engine.apply_batch(&batch_of(None, vec![(block(1, 0), vec![0])]));
        let rollback_result = engine.rollback_at_or_below(0);
        // then NotActive and Unrecoverable errors carry the cause
        assert_eq!(
            apply_result,
            Err(ApplyError::NotActive {
                status: EngineStatus::Unrecoverable { cause },
            })
        );
        assert_eq!(rollback_result, Err(RollbackError::Unrecoverable { cause }));
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
broadcast use crate::batch::lemma_batch_view;

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

impl EngineConfig {
    /// What `validate` accepts: a power-of-two ring capacity in `[2, 2^20]` and at most
    /// `2^16` checkpoint slots. Both bound the vectors `Engine::new` allocates, so their
    /// byte size never reaches the capacity-overflow panic that vstd's specs leave out.
    pub open spec fn valid(self) -> bool {
        &&& 2 <= self.ring_capacity <= 0x10_0000
        &&& self.ring_capacity & ((self.ring_capacity - 1) as usize) == 0
        &&& self.checkpoint_slots <= 0x1_0000
    }
}

impl<F> Engine<F> {
    /// The view of `Engine::new(fold, config)`: fold view `fold`, nothing applied, K
    /// empty slots.
    pub open spec fn fresh(fold: int, config: EngineConfig) -> EngineView {
        EngineView {
            fold,
            cursor: None,
            ring: Seq::empty(),
            slots: Seq::new(config.checkpoint_slots as nat, |_i: int| None::<SlotView>),
            status: EngineStatus::Active,
            last_verified: None,
            skips: 0,
            resets: 0,
        }
    }

    /// Capacity of the observed-block ring (`EngineConfig::ring_capacity`).
    pub closed spec fn window(&self) -> int {
        self.ring.cap()
    }

    /// Ring and slot representation plus the view-level clauses.
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
            0 < self.window(),
    {
        self.ring.lemma_wf();
    }

    /// In a `wf` engine the durable point never passes the cursor.
    pub(crate) proof fn lemma_durable_point_le_cursor(&self)
        requires
            self.wf(),
        ensures
            opt_le(self@.durable_point(), self@.cursor),
    {
        crate::verus::model::lemma_durable_point_le_cursor(self@);
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

/// Events of a span with their positions.
spec fn span_seq<'a, E>(s: SpanView<'a, E>) -> Seq<(Position, E)> {
    Seq::new(
        s.events@.len(),
        |k: int| (Position { block: s.number, log_index: s.log_indices@[k] as u64 }, s.events@[k]),
    )
}

/// `apply_span`'s post-state over the span's entries `s` and header `blk`: the fold runs
/// on the entries after the cursor through the first stop, and the cursor and ring
/// follow the entries that consumed their position.
spec fn span_post<F: Fold>(
    pre: EngineView,
    post: EngineView,
    w: int,
    s: Seq<(Position, F::Event)>,
    blk: BlockRef,
    ok: bool,
) -> bool {
    let q = applied::<F, F::Event, F::Error>(pre.fold, newer(pre.cursor, s));
    let st = run::<F, F::Event, F::Error>((pre.fold, false), q);
    let done = if st.1 { q.drop_last() } else { q };
    let entered = done.len() > 0 && (pre.ring.len() == 0 || pre.ring.last().number < blk.number);
    &&& ok == !st.1
    &&& post.fold == st.0
    &&& post.cursor == cursor_after(pre.cursor, done)
    &&& post.ring == if entered { ring_push(pre.ring, w, blk) } else { pre.ring }
    &&& post.last_verified == if entered { Some(blk) } else { pre.last_verified }
    &&& post.slots == pre.slots
    &&& post.resets == pre.resets
    &&& ok ==> post.status == pre.status
    &&& q.len() == 0 ==> post == pre
}

/// The skip count over the batch so far grows by span `i`'s.
proof fn lemma_span_skips<F: Fold>(
    v0: EngineView,
    bv: BatchView<F::Event>,
    w: int,
    i0: int,
    pre: EngineView,
    i: int,
)
    requires
        setup(v0, bv, w, i0),
        0 <= i < bv.ends.len(),
        loop_state::<F>(v0, bv, w, i0, pre, i),
        pre.wf(),
    ensures
        skips::<F, F::Event, F::Error>((v0.fold, false), newer(v0.cursor, bv.flat_upto(i + 1)))
            == skips::<F, F::Event, F::Error>((v0.fold, false), newer(v0.cursor, bv.flat_upto(i)))
            + skips::<F, F::Event, F::Error>((pre.fold, false), newer(pre.cursor, bv.span_events(i))),
{
    reveal(loop_state);
    lemma_span_newer::<F>(v0, bv, w, i0, pre, i);
    let g = newer(v0.cursor, bv.flat_upto(i));
    assert(bv.flat_upto(i + 1) == bv.flat_upto(i) + bv.span_events(i));
    lemma_newer_add(v0.cursor, bv.flat_upto(i), bv.span_events(i));
    lemma_skips_concat::<F, F::Event, F::Error>((v0.fold, false), g, newer(v0.cursor, bv.span_events(i)));
}

/// Facts fixed once `apply_batch` has passed its checks; `i0` spans are at or below the
/// cursor block.
#[verifier::opaque]
spec fn setup<E>(v0: EngineView, bv: BatchView<E>, w: int, i0: int) -> bool {
    &&& v0.wf()
    &&& bv.wf()
    &&& bv.shaped()
    &&& lt_sorted(bv.flat())
    &&& v0.status is Active
    &&& 0 < w
    &&& split_at_tip(bv, v0.cursor, i0)
}

/// Cursor, ring and freshness after `i` spans: past the old tip the cursor sits on
/// span `i - 1` and the ring gained spans `i0..i`; below it nothing moved but the cursor
/// within the tip block.
#[verifier::opaque]
spec fn tip_state<E>(v0: EngineView, bv: BatchView<E>, w: int, i0: int, v: EngineView, i: int) -> bool {
    if i > i0 {
        &&& v.cursor is Some
        &&& v.cursor.unwrap().block == bv.blocks[i - 1]
        &&& v.ring == ring_ext(v0.ring, w, span_refs(bv).subrange(i0, i))
        &&& v.last_verified == Some(v.ring.last())
    } else {
        &&& v.ring == v0.ring
        &&& v.last_verified == checked_freshness(v0, bv)
        &&& match v0.cursor {
            None => v.cursor is None,
            Some(c) => v.cursor is Some && v.cursor.unwrap().block == c.block,
        }
    }
}

/// `apply_batch`'s loop invariant after `i` spans applied without a stop.
#[verifier::opaque]
spec fn loop_state<F: Fold>(
    v0: EngineView,
    bv: BatchView<F::Event>,
    w: int,
    i0: int,
    v: EngineView,
    i: int,
) -> bool {
    let g = newer(v0.cursor, bv.flat_upto(i));
    &&& 0 <= i <= bv.ends.len()
    &&& run::<F, F::Event, F::Error>((v0.fold, false), g) == (v.fold, false)
    &&& v.cursor == cursor_after(v0.cursor, g)
    &&& v.status == v0.status
    &&& v.slots == v0.slots
    &&& v.resets == v0.resets
    &&& g.len() == 0 ==> v == (EngineView { last_verified: v.last_verified, ..v0 })
    &&& i < i0 ==> g.len() == 0
    &&& tip_state(v0, bv, w, i0, v, i)
}

/// The entries `F::apply` runs on when the batch is accepted.
spec fn run_calls<F: Fold>(v0: EngineView, bv: BatchView<F::Event>) -> Seq<(Position, F::Event)> {
    applied::<F, F::Event, F::Error>(v0.fold, newer(v0.cursor, bv.flat()))
}

/// `apply_batch`'s state after span `i` stopped the fold.
#[verifier::opaque]
spec fn stop_state<F: Fold>(
    v0: EngineView,
    bv: BatchView<F::Event>,
    w: int,
    i0: int,
    pre: EngineView,
    post: EngineView,
    i: int,
) -> bool {
    let c = run_calls::<F>(v0, bv);
    let q = applied::<F, F::Event, F::Error>(pre.fold, newer(pre.cursor, bv.span_events(i)));
    &&& c.len() > 0
    &&& run::<F, F::Event, F::Error>((v0.fold, false), c).1
    &&& c.last() == q.last()
    &&& post.fold == run::<F, F::Event, F::Error>((v0.fold, false), c).0
    &&& post.cursor == cursor_after(v0.cursor, c.drop_last())
    &&& i0 <= i + 1
    &&& tip_state(v0, bv, w, i0, post, i) || tip_state(v0, bv, w, i0, post, i + 1)
    &&& post.slots == v0.slots
    &&& post.resets == v0.resets
}

/// A rejected batch calls the fold zero times, so every threaded clause carries over.
proof fn lemma_rejected<F: Fold>(v0: EngineView, post: EngineView, bv: BatchView<F::Event>)
    requires
        post == (EngineView { last_verified: post.last_verified, ..v0 }),
    ensures
        !accepted(v0, bv) ==> {
            &&& calls::<F, F::Event, F::Error>(v0, bv).len() == 0
            &&& post.fold == fold::<F, F::Event, F::Error>(v0.fold, calls::<F, F::Event, F::Error>(v0, bv))
            &&& post.cursor == cursor_after(v0.cursor, ok_calls::<F, F::Event, F::Error>(v0, bv))
            &&& forall|init: int, log: Seq<(Position, F::Event)>|
                #[trigger] v0.inv::<F, F::Event, F::Error>(init, log) ==> post.inv::<F, F::Event, F::Error>(
                    init,
                    log + calls::<F, F::Event, F::Error>(v0, bv),
                )
            &&& forall|a: Seq<Option<BlockRef>>| #[trigger] v0.anchored(a) ==> post.anchored(a)
        },
{
    if !accepted(v0, bv) {
        assert forall|init: int, log: Seq<(Position, F::Event)>|
            #[trigger] v0.inv::<F, F::Event, F::Error>(init, log) implies post.inv::<F, F::Event, F::Error>(
            init,
            log + calls::<F, F::Event, F::Error>(v0, bv),
        ) by {
            assert(log + calls::<F, F::Event, F::Error>(v0, bv) =~= log);
        }
    }
}

/// Span `i` of `b`: non-empty, strictly ascending, every entry on block `i`.
proof fn lemma_span_sorted<E>(bv: BatchView<E>, i: int)
    requires
        bv.wf(),
        bv.shaped(),
        0 <= i < bv.ends.len(),
    ensures
        bv.span_events(i).len() > 0,
        lt_sorted(bv.span_events(i)),
        forall|k: int|
            0 <= k < bv.span_events(i).len() ==> (#[trigger] bv.span_events(i)[k]).0.block == bv.blocks[i],
{
    lemma_end_bounds(bv, i);
    assert(bv.start(i) < bv.ends[i]);
    let sp = bv.span_events(i);
    assert forall|a: int, b: int| #![trigger sp[a], sp[b]] 0 <= a < b < sp.len() implies lt(sp[a].0, sp[b].0) by {
        assert(bv.log_indices[bv.start(i) + a] < bv.log_indices[bv.start(i) + b]);
    }
}

/// The `setup` facts every loop lemma uses; `shaped` stays hidden, since its span-bound
/// clause instantiates itself through `start(i) == ends[i - 1]`.
proof fn lemma_setup<E>(v0: EngineView, bv: BatchView<E>, w: int, i0: int)
    requires
        setup(v0, bv, w, i0),
    ensures
        v0.wf(),
        bv.wf(),
        lt_sorted(bv.flat()),
        v0.status is Active,
        0 < w,
        split_at_tip(bv, v0.cursor, i0),
        forall|i: int, j: int|
            #![trigger bv.blocks[i], bv.blocks[j]]
            0 <= i < j < bv.blocks.len() ==> bv.blocks[i] < bv.blocks[j],
{
    reveal(setup);
}

proof fn lemma_setup_span<E>(v0: EngineView, bv: BatchView<E>, w: int, i0: int, i: int)
    requires
        setup(v0, bv, w, i0),
        0 <= i < bv.ends.len(),
    ensures
        bv.span_events(i).len() > 0,
        lt_sorted(bv.span_events(i)),
        forall|k: int|
            0 <= k < bv.span_events(i).len() ==> (#[trigger] bv.span_events(i)[k]).0.block == bv.blocks[i],
{
    reveal(setup);
    lemma_span_sorted(bv, i);
}

/// No fork once every span at or below the old tip matched the ring.
proof fn lemma_not_forked<E>(v0: EngineView, bv: BatchView<E>, w: int, i0: int, m: int)
    requires
        setup(v0, bv, w, i0),
        i0 <= m,
        forall|k: int, j: int|
            #![trigger bv.blocks[k], v0.ring[j]]
            0 <= k < m && k < i0 && 0 <= j < v0.ring.len() && v0.ring[j].number == bv.blocks[k]
                ==> v0.ring[j].hash == bv.hashes[k],
    ensures
        !forked(v0, bv),
{
    reveal(setup);
    if forked(v0, bv) {
        let (k2, j) = choose|k2: int, j: int|
            #![trigger bv.blocks[k2], v0.ring[j]]
            0 <= k2 < bv.blocks.len() && 0 <= j < v0.ring.len() && bv.blocks[k2] <= v0.cursor.unwrap().block
                && v0.ring[j].number == bv.blocks[k2] && v0.ring[j].hash != bv.hashes[k2];
        assert(span_refs(bv)[k2].number == bv.blocks[k2]);
    }
}

/// The log indices of span `i` ascend strictly.
proof fn lemma_span_indices<E>(v0: EngineView, bv: BatchView<E>, w: int, i0: int, i: int, li: Seq<u32>)
    requires
        setup(v0, bv, w, i0),
        0 <= i < bv.ends.len(),
        li == bv.log_indices.subrange(bv.start(i), bv.ends[i] as int),
    ensures
        forall|j: int, k: int| 0 <= j < k < li.len() ==> li[j] < li[k],
{
    reveal(setup);
    lemma_end_bounds(bv, i);
    assert forall|j: int, k: int| 0 <= j < k < li.len() implies li[j] < li[k] by {
        assert(li[j] == bv.log_indices[bv.start(i) + j]);
        assert(li[k] == bv.log_indices[bv.start(i) + k]);
        assert(bv.start(i) + k < bv.ends[i]);
    }
}

/// At span `i`, the redelivery test holds exactly for the spans at or below the old
/// tip, and there the engine still has its checked pre-state.
proof fn lemma_span_redelivered<F: Fold>(
    v0: EngineView,
    bv: BatchView<F::Event>,
    w: int,
    i0: int,
    pre: EngineView,
    i: int,
)
    requires
        setup(v0, bv, w, i0),
        0 <= i < bv.ends.len(),
        loop_state::<F>(v0, bv, w, i0, pre, i),
    ensures
        (pre.cursor matches Some(c) && bv.blocks[i] <= c.block) <==> i < i0,
        pre.status is Active,
        i < i0 ==> pre == (EngineView { last_verified: checked_freshness(v0, bv), ..v0 }),
{
    lemma_setup(v0, bv, w, i0);
    reveal(tip_state);
    reveal(loop_state);
    let r = span_refs(bv);
    assert(r[i].number == bv.blocks[i]);
    if i > i0 {
        assert(bv.blocks[i - 1] < bv.blocks[i]);
    }
}

/// Span `i` against the old cursor: which of its entries are new, and where the ring
/// stands before it.
proof fn lemma_span_newer<F: Fold>(
    v0: EngineView,
    bv: BatchView<F::Event>,
    w: int,
    i0: int,
    pre: EngineView,
    i: int,
)
    requires
        setup(v0, bv, w, i0),
        0 <= i < bv.ends.len(),
        loop_state::<F>(v0, bv, w, i0, pre, i),
        pre.wf(),
    ensures
        newer(pre.cursor, bv.span_events(i)) == newer(v0.cursor, bv.span_events(i)),
        newer(v0.cursor, bv.flat_upto(i + 1)) == newer(v0.cursor, bv.flat_upto(i)) + newer(
            v0.cursor,
            bv.span_events(i),
        ),
        forall|j: int|
            0 <= j < newer(v0.cursor, bv.span_events(i)).len() ==> (#[trigger] newer(
                v0.cursor,
                bv.span_events(i),
            )[j]).0.block == bv.blocks[i] && opt_lt(
                v0.cursor,
                Some(newer(v0.cursor, bv.span_events(i))[j].0),
            ),
        i >= i0 ==> newer(v0.cursor, bv.span_events(i)) == bv.span_events(i) && bv.span_events(i).len() > 0
            && (pre.ring.len() == 0 || pre.ring.last().number < bv.blocks[i])
            && ring_push(pre.ring, w, bv.block(i)) == ring_ext(v0.ring, w, span_refs(bv).subrange(i0, i + 1))
            && ring_push(pre.ring, w, bv.block(i)).last() == bv.block(i),
        i + 1 < i0 ==> newer(v0.cursor, bv.span_events(i)).len() == 0,
        i < i0 ==> v0.cursor is Some && pre.ring == v0.ring && pre.ring.len() > 0
            && pre.ring.last().number >= bv.blocks[i] && (newer(v0.cursor, bv.span_events(i)).len() > 0
            ==> bv.blocks[i] == v0.cursor.unwrap().block),
{
    lemma_setup(v0, bv, w, i0);
    reveal(tip_state);
    reveal(loop_state);
    let c0 = v0.cursor;
    let sp = bv.span_events(i);
    let fl = bv.flat_upto(i);
    let r = span_refs(bv);
    lemma_setup_span(v0, bv, w, i0, i);
    lemma_newer_add(c0, fl, sp);
    assert(bv.flat_upto(i + 1) == fl + sp);
    lemma_newer_sorted(c0, sp);
    let p = newer(c0, sp);
    assert forall|j: int| 0 <= j < p.len() implies (#[trigger] p[j]).0.block == bv.blocks[i] && opt_lt(
        c0,
        Some(p[j].0),
    ) by {
        assert(p[j] == sp[sp.len() - p.len() + j]);
    }
    assert(r[i].number == bv.blocks[i]);
    assert(r[i] == bv.block(i));
    if i + 1 < bv.ends.len() {
        assert(r[i + 1].number == bv.blocks[i + 1]);
    }
    if i >= i0 {
        if i > i0 {
            assert(bv.blocks[i - 1] < bv.blocks[i]);
        } else {
            assert(r.subrange(i0, i0) =~= Seq::<BlockRef>::empty());
        }
        assert forall|k: int| 0 <= k < sp.len() implies opt_lt(c0, Some(#[trigger] sp[k].0)) && opt_lt(
            pre.cursor,
            Some(sp[k].0),
        ) by {
            assert(sp[k].0.block == bv.blocks[i]);
        }
        lemma_newer_split(c0, sp, 0);
        lemma_newer_split(pre.cursor, sp, 0);
        assert(sp.subrange(0, sp.len() as int) =~= sp);
        assert(r.subrange(i0, i + 1) =~= r.subrange(i0, i).push(r[i]));
        lemma_ring_ext_push(v0.ring, w, r.subrange(i0, i), r[i]);
    } else {
        assert(r[i].number <= c0.unwrap().block);
        if p.len() > 0 {
            assert(p[0].0.block == bv.blocks[i]);
        }
    }
    if i + 1 < i0 {
        assert(bv.blocks[i] < bv.blocks[i + 1]);
        assert forall|k: int| 0 <= k < sp.len() implies !opt_lt(c0, Some(#[trigger] sp[k].0)) by {
            assert(sp[k].0.block == bv.blocks[i]);
        }
        lemma_newer_split(c0, sp, sp.len() as int);
    }
}

/// A span that did not stop keeps the loop invariant.
proof fn lemma_span_ok<F: Fold>(
    v0: EngineView,
    bv: BatchView<F::Event>,
    w: int,
    i0: int,
    pre: EngineView,
    post: EngineView,
    i: int,
)
    requires
        setup(v0, bv, w, i0),
        0 <= i < bv.ends.len(),
        loop_state::<F>(v0, bv, w, i0, pre, i),
        pre.wf(),
        span_post::<F>(pre, post, w, bv.span_events(i), bv.block(i), true),
    ensures
        loop_state::<F>(v0, bv, w, i0, post, i + 1),
{
    lemma_setup(v0, bv, w, i0);
    reveal(tip_state);
    reveal(loop_state);
    lemma_span_newer::<F>(v0, bv, w, i0, pre, i);
    let g = newer(v0.cursor, bv.flat_upto(i));
    let p = newer(v0.cursor, bv.span_events(i));
    lemma_applied_prefix::<F, F::Event, F::Error>(pre.fold, p);
    lemma_run_concat::<F, F::Event, F::Error>((v0.fold, false), g, p);
    if p.len() == 0 {
        assert(g + p =~= g);
    } else {
        assert((g + p).last() == p.last());
        assert(p.last() == p[p.len() - 1]);
    }
}

/// When span `i` stops the fold, the batch's calls end at that stop.
proof fn lemma_calls_split<F: Fold>(v0: EngineView, bv: BatchView<F::Event>, i: int, v: int)
    requires
        bv.wf(),
        0 <= i < bv.ends.len(),
        run::<F, F::Event, F::Error>((v0.fold, false), newer(v0.cursor, bv.flat_upto(i))) == (v, false),
        newer(v0.cursor, bv.flat_upto(i + 1)) == newer(v0.cursor, bv.flat_upto(i)) + newer(
            v0.cursor,
            bv.span_events(i),
        ),
        run::<F, F::Event, F::Error>(
            (v, false),
            applied::<F, F::Event, F::Error>(v, newer(v0.cursor, bv.span_events(i))),
        ).1,
    ensures
        run_calls::<F>(v0, bv) == newer(v0.cursor, bv.flat_upto(i)) + applied::<F, F::Event, F::Error>(
            v,
            newer(v0.cursor, bv.span_events(i)),
        ),
{
    let c0 = v0.cursor;
    let f0 = v0.fold;
    let g = newer(c0, bv.flat_upto(i));
    let p = newer(c0, bv.span_events(i));
    let pre_fold = v;
    let n = bv.ends.len() as int;
    let whole = bv.flat();
    let l = bv.flat_upto(i + 1).len() as int;
    lemma_flat_prefix(bv, i + 1, n);
    let rest = whole.subrange(l, whole.len() as int);
    assert(whole =~= bv.flat_upto(i + 1) + rest);
    lemma_newer_add(c0, bv.flat_upto(i + 1), rest);
    let nr = newer(c0, rest);
    assert(g + p + nr =~= g + (p + nr));
    lemma_applied_concat::<F, F::Event, F::Error>(f0, g, p + nr);
    lemma_applied_extend::<F, F::Event, F::Error>(pre_fold, p, nr);
}

/// A span that stopped the fold: the whole batch's calls end at its stop.
proof fn lemma_span_stop<F: Fold>(
    v0: EngineView,
    bv: BatchView<F::Event>,
    w: int,
    i0: int,
    pre: EngineView,
    post: EngineView,
    i: int,
)
    requires
        setup(v0, bv, w, i0),
        0 <= i < bv.ends.len(),
        loop_state::<F>(v0, bv, w, i0, pre, i),
        pre.wf(),
        span_post::<F>(pre, post, w, bv.span_events(i), bv.block(i), false),
    ensures
        stop_state::<F>(v0, bv, w, i0, pre, post, i),
{
    lemma_setup(v0, bv, w, i0);
    reveal(tip_state);
    reveal(loop_state);
    reveal(stop_state);
    lemma_span_newer::<F>(v0, bv, w, i0, pre, i);
    let c0 = v0.cursor;
    let f0 = v0.fold;
    let g = newer(c0, bv.flat_upto(i));
    let p = newer(c0, bv.span_events(i));
    let q = applied::<F, F::Event, F::Error>(pre.fold, p);
    lemma_applied_prefix::<F, F::Event, F::Error>(pre.fold, p);
    assert(q.len() > 0);
    let done = q.drop_last();
    if done.len() > 0 {
        assert(done.last() == p[done.len() - 1]);
    }
    lemma_calls_split::<F>(v0, bv, i, pre.fold);
    lemma_run_concat::<F, F::Event, F::Error>((f0, false), g, q);
    assert(run_calls::<F>(v0, bv) == g + q);
    assert((g + q).drop_last() =~= g + done);
    assert((g + q).last() == q.last());
    if done.len() == 0 {
        assert(g + done =~= g);
    } else {
        assert((g + done).last() == done.last());
    }
}

/// The loop ran every span without a stop.
proof fn lemma_loop_done<F: Fold>(v0: EngineView, bv: BatchView<F::Event>, w: int, i0: int, post: EngineView)
    requires
        setup(v0, bv, w, i0),
        loop_state::<F>(v0, bv, w, i0, post, bv.ends.len() as int),
    ensures
        run_calls::<F>(v0, bv) == newer(v0.cursor, bv.flat()),
        !run::<F, F::Event, F::Error>((v0.fold, false), run_calls::<F>(v0, bv)).1,
        post.fold == run::<F, F::Event, F::Error>((v0.fold, false), run_calls::<F>(v0, bv)).0,
        post.cursor == cursor_after(v0.cursor, run_calls::<F>(v0, bv)),
        tip_state(v0, bv, w, i0, post, bv.ends.len() as int),
        post.status == v0.status,
        post.slots == v0.slots,
        post.resets == v0.resets,
{
    lemma_setup(v0, bv, w, i0);
    reveal(loop_state);
    lemma_applied_all::<F, F::Event, F::Error>(v0.fold, newer(v0.cursor, bv.flat()));
}

/// The calls of an accepted batch are sorted, after the old cursor, and, without a
/// stop, reach the last entry of the batch.
#[verifier::rlimit(30)]
proof fn lemma_calls_facts<F: Fold>(v0: EngineView, bv: BatchView<F::Event>, w: int, i0: int)
    requires
        setup(v0, bv, w, i0),
    ensures
        lt_sorted(run_calls::<F>(v0, bv)),
        forall|j: int|
            0 <= j < run_calls::<F>(v0, bv).len() ==> opt_lt(v0.cursor, Some(#[trigger] run_calls::<F>(v0, bv)[j].0)),
        !run::<F, F::Event, F::Error>((v0.fold, false), run_calls::<F>(v0, bv)).1 ==> newer(
            cursor_after(v0.cursor, run_calls::<F>(v0, bv)),
            bv.flat(),
        ).len() == 0,
{
    lemma_setup(v0, bv, w, i0);
    let c0 = v0.cursor;
    let f0 = v0.fold;
    let fl = bv.flat();
    let nn = fl.len() as int;
    let sa = newer(c0, fl);
    let c = run_calls::<F>(v0, bv);
    lemma_newer_sorted(c0, fl);
    lemma_applied_prefix::<F, F::Event, F::Error>(f0, sa);
    let m = sa.len() as int;
    assert forall|j: int| 0 <= j < c.len() implies #[trigger] c[j] == fl[nn - m + j] && opt_lt(
        c0,
        Some(c[j].0),
    ) by {
        assert(c[j] == sa[j]);
    }
    assert forall|a: int, b: int| #![trigger c[a], c[b]] 0 <= a < b < c.len() implies lt(c[a].0, c[b].0) by {
        assert(c[a] == fl[nn - m + a] && c[b] == fl[nn - m + b]);
    }
    if !run::<F, F::Event, F::Error>((f0, false), c).1 && c.len() > 0 {
        assert(c == sa);
        let top = fl[nn - 1];
        assert(c[c.len() - 1] == top);
        let pc = cursor_after(c0, c);
        assert forall|j: int| 0 <= j < nn implies !opt_lt(pc, Some(#[trigger] fl[j].0)) by {
            if j < nn - 1 {
                assert(lt(fl[j].0, top.0));
            }
        }
        lemma_newer_split(pc, fl, nn);
    }
}

/// The ring after the loop, for a state at `tip_state(k)`.
proof fn lemma_post_ring<E>(v0: EngineView, bv: BatchView<E>, w: int, i0: int, post: EngineView, k: int)
    requires
        setup(v0, bv, w, i0),
        0 <= k <= bv.ends.len(),
        tip_state(v0, bv, w, i0, post, k),
    ensures
        ring_after(v0, post, bv, w),
        forall|j: int|
            0 <= j < post.ring.len() && v0.cursor is Some && post.ring[j].number <= v0.cursor.unwrap().block
                ==> v0.ring.contains(#[trigger] post.ring[j]),
{
    lemma_setup(v0, bv, w, i0);
    reveal(tip_state);
    let c0 = v0.cursor;
    let r = span_refs(bv);
    let i1 = if k > i0 { k } else { i0 };
    if k > i0 {
        assert forall|j: int| 0 <= j < k implies #[trigger] r[j].number <= post.cursor.unwrap().block by {
            if j < k - 1 {
                assert(bv.blocks[j] < bv.blocks[k - 1]);
            }
        }
        assert forall|j: int| k <= j < r.len() implies #[trigger] r[j].number > post.cursor.unwrap().block by {
            assert(bv.blocks[k - 1] < bv.blocks[j]);
        }
    } else {
        assert(r.subrange(i0, i0) =~= Seq::<BlockRef>::empty());
    }
    assert(split_at_tip(bv, post.cursor, i1));
    assert(split_at_tip(bv, c0, i0));
    assert(post.ring == ring_ext(v0.ring, w, r.subrange(i0, i1)));
    lemma_ring_ext_from(v0.ring, w, r.subrange(i0, i1));
    assert forall|j: int|
        0 <= j < post.ring.len() && c0 is Some && post.ring[j].number <= c0.unwrap().block
            implies v0.ring.contains(#[trigger] post.ring[j]) by {
        if !v0.ring.contains(post.ring[j]) {
            let u = choose|u: int| 0 <= u < r.subrange(i0, i1).len() && r.subrange(i0, i1)[u] == post.ring[j];
            assert(r[i0 + u].number > c0.unwrap().block);
        }
    }
}

/// `Inv` across an apply that ran the fold on `c`.
proof fn lemma_post_inv<F: Fold>(v0: EngineView, post: EngineView, c: Seq<(Position, F::Event)>)
    requires
        v0.wf(),
        v0.status is Active,
        lt_sorted(c),
        forall|j: int| 0 <= j < c.len() ==> opt_lt(v0.cursor, Some(#[trigger] c[j].0)),
        post.fold == run::<F, F::Event, F::Error>((v0.fold, false), c).0,
        post.slots == v0.slots,
        post.status is Active ==> !run::<F, F::Event, F::Error>((v0.fold, false), c).1 && post.cursor
            == cursor_after(v0.cursor, c),
    ensures
        forall|init: int, log: Seq<(Position, F::Event)>|
            #[trigger] v0.inv::<F, F::Event, F::Error>(init, log) ==> post.inv::<F, F::Event, F::Error>(
                init,
                log + c,
            ),
{
    let c0 = v0.cursor;
    assert forall|init: int, log: Seq<(Position, F::Event)>|
        #[trigger] v0.inv::<F, F::Event, F::Error>(init, log) implies post.inv::<F, F::Event, F::Error>(
        init,
        log + c,
    ) by {
        let l2 = log + c;
        assert forall|a: int, b: int| #![trigger l2[a], l2[b]] 0 <= a < b < l2.len() implies lt(l2[a].0, l2[b].0) by {
            if b >= log.len() {
                assert(l2[b] == c[b - log.len()]);
                if a >= log.len() {
                    assert(l2[a] == c[a - log.len()]);
                } else {
                    assert(l2[a] == log[a]);
                    assert(opt_le(Some(log[a].0), c0));
                    lemma_opt_lt_order(Some(log[a].0), c0, Some(c[b - log.len()].0));
                }
            } else {
                assert(l2[a] == log[a] && l2[b] == log[b]);
            }
        }
        lemma_run_concat::<F, F::Event, F::Error>((init, false), log, c);
        if post.status is Active {
            assert forall|j: int| 0 <= j < l2.len() implies opt_le(Some(#[trigger] l2[j].0), post.cursor) by {
                if c.len() > 0 {
                    let top = c[c.len() - 1];
                    if j >= log.len() {
                        assert(l2[j] == c[j - log.len()]);
                    } else {
                        assert(l2[j] == log[j]);
                        assert(opt_le(Some(log[j].0), c0));
                        lemma_opt_lt_order(Some(log[j].0), c0, Some(top.0));
                    }
                } else {
                    assert(l2[j] == log[j]);
                }
            }
        }
        assert forall|q: int|
            0 <= q < post.slots.len() && #[trigger] post.slots[q] is Some implies run::<F, F::Event, F::Error>(
            (init, false),
            upto::<F::Event>(l2, post.slots[q].unwrap().cursor),
        ) == (post.slots[q].unwrap().fold, false) by {
            let sc = post.slots[q].unwrap().cursor;
            assert(v0.slots[q] is Some);
            assert(opt_le(sc, c0));
            assert forall|j: int| 0 <= j < c.len() implies opt_lt(sc, Some(#[trigger] c[j].0)) by {
                lemma_opt_lt_order(sc, c0, Some(c[j].0));
            }
            lemma_upto_append::<F::Event>(log, c, sc);
        }
    }
}

/// Anchors across a ring that only gained entries above the old tip: a slot live after
/// was live before, on the same entry, so a dead slot stays dead.
proof fn lemma_post_anchors(v0: EngineView, post: EngineView)
    requires
        v0.wf(),
        post.slots == v0.slots,
        forall|j: int|
            0 <= j < post.ring.len() && v0.cursor is Some && post.ring[j].number <= v0.cursor.unwrap().block
                ==> v0.ring.contains(#[trigger] post.ring[j]),
    ensures
        forall|a: Seq<Option<BlockRef>>| #[trigger] v0.anchored(a) ==> post.anchored(a),
{
    let c0 = v0.cursor;
    assert forall|a: Seq<Option<BlockRef>>| #[trigger] v0.anchored(a) implies post.anchored(a) by {
        assert forall|q: int|
            #![trigger post.slots[q]]
            post.live_at(q) && post.slots[q].unwrap().cursor is Some implies {
                &&& a[q] is Some
                &&& a[q].unwrap().number == post.slots[q].unwrap().cursor.unwrap().block
                &&& post.ring.contains(a[q].unwrap())
            } by {
            let sc = post.slots[q].unwrap().cursor.unwrap();
            assert(v0.slots[q] is Some);
            assert(opt_le(Some(sc), c0));
            let j = choose|j: int| 0 <= j < post.ring.len() && #[trigger] post.ring[j].number == sc.block;
            assert(v0.ring.contains(post.ring[j]));
            let u = choose|u: int| 0 <= u < v0.ring.len() && v0.ring[u] == post.ring[j];
            assert(v0.live_at(q));
            let u2 = choose|u2: int| 0 <= u2 < v0.ring.len() && v0.ring[u2] == a[q].unwrap();
            assert(u2 == u) by {
                if u2 < u {
                    assert(v0.ring[u2].number < v0.ring[u].number);
                } else if u < u2 {
                    assert(v0.ring[u].number < v0.ring[u2].number);
                }
            }
        }
    }
}

/// The final clauses of an accepted batch: ring, `Inv`, anchors and no entry newer than
/// the cursor.
proof fn lemma_apply_post<F: Fold>(
    v0: EngineView,
    bv: BatchView<F::Event>,
    w: int,
    i0: int,
    post: EngineView,
    k: int,
)
    requires
        setup(v0, bv, w, i0),
        accepted(v0, bv),
        0 <= k <= bv.ends.len(),
        tip_state(v0, bv, w, i0, post, k),
        post.fold == run::<F, F::Event, F::Error>((v0.fold, false), run_calls::<F>(v0, bv)).0,
        post.cursor == cursor_after(
            v0.cursor,
            if run::<F, F::Event, F::Error>((v0.fold, false), run_calls::<F>(v0, bv)).1 {
                run_calls::<F>(v0, bv).drop_last()
            } else {
                run_calls::<F>(v0, bv)
            },
        ),
        post.slots == v0.slots,
        post.status is Active ==> !run::<F, F::Event, F::Error>((v0.fold, false), run_calls::<F>(v0, bv)).1,
    ensures
        ring_after(v0, post, bv, w),
        forall|init: int, log: Seq<(Position, F::Event)>|
            #[trigger] v0.inv::<F, F::Event, F::Error>(init, log) ==> post.inv::<F, F::Event, F::Error>(
                init,
                log + calls::<F, F::Event, F::Error>(v0, bv),
            ),
        forall|a: Seq<Option<BlockRef>>| #[trigger] v0.anchored(a) ==> post.anchored(a),
        !run::<F, F::Event, F::Error>((v0.fold, false), run_calls::<F>(v0, bv)).1 ==> newer(
            post.cursor,
            bv.flat(),
        ).len() == 0,
{
    lemma_setup(v0, bv, w, i0);
    assert(calls::<F, F::Event, F::Error>(v0, bv) == run_calls::<F>(v0, bv));
    lemma_calls_facts::<F>(v0, bv, w, i0);
    lemma_post_ring(v0, bv, w, i0, post, k);
    lemma_post_inv::<F>(v0, post, run_calls::<F>(v0, bv));
    lemma_post_anchors(v0, post);
}

/// `e` is the Halt or Poison stop at `at`, and `status` records it.
pub open spec fn stops_at<Er>(e: ApplyError<Er>, status: EngineStatus, at: Position) -> bool {
    match e {
        ApplyError::Halted { at: a, .. } => a == at && status == (EngineStatus::Halted { at }),
        ApplyError::Poisoned { at: a, .. } => a == at && status == (EngineStatus::Poisoned { at }),
        _ => false,
    }
}

/// `Engine::advance`: the cursor moves to `pos`, and the ring and freshness take `blk`
/// when the cursor enters its block.
spec fn advanced(v: EngineView, w: int, blk: BlockRef, pos: Position) -> EngineView {
    let entered = v.ring.len() == 0 || v.ring.last().number < blk.number;
    EngineView {
        cursor: Some(pos),
        ring: if entered { ring_push(v.ring, w, blk) } else { v.ring },
        last_verified: if entered { Some(blk) } else { v.last_verified },
        ..v
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

/// `checkpoint` over the views: storing the cursor keeps `wf`, `Inv` over the same log,
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

/// `wf`, the rollback target and `Inv` for `rollback_at_or_below`, over the views.
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
    // The target is the maximum: newer qualifying slots are excluded, older ones are
    // ordered below slot k.
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
