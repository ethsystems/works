#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::vec::Vec;

use core::time::Duration;

use crate::{
    batch::Batch,
    engine::{
        ApplySummary,
        Engine,
        EngineConfig,
    },
    error::{
        ApplyError,
        ConfigError,
        DivergenceCause,
        DurabilityLost,
        EngineStatus,
        RollbackError,
    },
    fold::Fold,
    position::{
        BlockRef,
        Position,
        pos_gt,
    },
    sink::{
        NoSink,
        SnapshotSink,
    },
    source::{
        ReplayHorizon,
        Source,
    },
};
#[cfg(verus_keep_ghost)]
use {
    crate::batch::{
        appended_at,
        popped_tail,
        pushed_block,
    },
    crate::verus::model::{
        BatchView,
        ChainView,
        EngineView,
        SlotView,
        a1,
        confirms,
        down_closed,
        fview,
        header,
        opt_le,
        prefix_at_or_below,
        qualifies,
        range_entries,
        ring_chain,
        sink_offered,
        sview_log,
        upto,
    },
    crate::verus::tcb::axiom_clone_preserves_fview,
    vstd::prelude::*,
};

/// Default poll cadence when the source has no error backlog.
const DEFAULT_POLL_INTERVAL: Duration = Duration::from_secs(1);
/// Default first backoff step after a source error.
const DEFAULT_BACKOFF_BASE: Duration = Duration::from_millis(200);
/// Default ceiling on exponential backoff.
const DEFAULT_BACKOFF_MAX: Duration = Duration::from_secs(30);
/// Default blocks between checkpoints.
const DEFAULT_CHECKPOINT_INTERVAL: u64 = 64;

/// True when `block` has reached the next interval step past the last marked block.
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == due_spec(last, block, interval),
))]
fn due(last: Option<u64>, block: u64, interval: u64) -> bool {
    match last {
        Some(last) => block >= last.saturating_add(interval),
        None => true,
    }
}

/// Lowers a cadence mark to a restore point; None when either is None.
#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == clamp_spec(mark, to)))]
fn clamp(mark: Option<u64>, to: Option<Position>) -> Option<u64> {
    match (mark, to) {
        (Some(mark), Some(to)) => Some(mark.min(to.block)),
        _ => None,
    }
}

/// Outcome of one driver tick.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tick {
    /// Batch applied; the summary counts what the fold saw.
    Progressed(ApplySummary),
    /// Poll returned nothing new.
    Idle,
    /// A fork rolled the engine back to a checkpoint.
    RolledBack {
        /// Cursor the rollback restored.
        to: Option<Position>,
    },
    /// Engine reset to genesis; the next poll carries no cursor.
    Resynced,
    /// Source or its contract failed; the next delay backs off.
    SourceError,
    /// Sink refused a snapshot offer; reported once, folding continues unpersisted.
    DurabilityLost,
    /// Engine can make no further automated progress.
    Terminal(EngineStatus),
}

/// Point-in-time snapshot of driver and engine state for external observers.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct DriverStatus {
    /// Most recently applied position.
    pub cursor: Option<Position>,
    /// Most recent block whose hash the source confirmed.
    pub last_verified: Option<BlockRef>,
    /// Engine status behind this driver.
    pub engine: EngineStatus,
    /// True once the most recent poll returned no new blocks.
    pub caught_up: bool,
    /// Events the fold declared not its own.
    pub skips: u64,
    /// Cursor the sink reports a restart would recover; None without a sink, before
    /// a flush, and from an engine reset until an offer made after it commits. It
    /// never leads `cursor`.
    pub durable_cursor: Option<Position>,
    /// True once the sink refused an offer; folding continues unpersisted.
    pub durability_lost: bool,
    /// Increments once per tick; a level signal for wait primitives.
    pub generation: u64,
}

impl DriverStatus {
    /// True once the engine can no longer make automated progress.
    #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == !(self.engine is Active)))]
    pub fn is_terminal(&self) -> bool {
        !self.engine.is_active()
    }
}

/// Poll cadence, backoff, and recovery tuning for a driver.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DriverConfig {
    /// Fold genesis; resync feasibility is judged against this block.
    pub start_block: u64,
    /// Delay between polls while the source is healthy.
    pub poll_interval: Duration,
    /// First backoff step after a source error.
    pub backoff_base: Duration,
    /// Ceiling on the exponential backoff.
    pub backoff_max: Duration,
    /// In-memory rollback points every N blocks of cursor progress; persists
    /// nothing. None means caller-driven only.
    pub checkpoint_interval: Option<u64>,
    /// Blocks of durable-point progress between snapshot offers; None disables
    /// offers.
    pub snapshot_interval: Option<u64>,
}

impl Default for DriverConfig {
    fn default() -> Self {
        Self {
            start_block: 0,
            poll_interval: DEFAULT_POLL_INTERVAL,
            backoff_base: DEFAULT_BACKOFF_BASE,
            backoff_max: DEFAULT_BACKOFF_MAX,
            checkpoint_interval: Some(DEFAULT_CHECKPOINT_INTERVAL),
            snapshot_interval: Some(DEFAULT_CHECKPOINT_INTERVAL),
        }
    }
}

impl DriverConfig {
    /// Defaults, folding from `start_block`.
    pub fn from_block(start_block: u64) -> Self {
        Self {
            start_block,
            ..Self::default()
        }
    }
}

/// Poll loop over one source: owns cadence, backoff, scanning, and fork recovery.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct Driver<F, S, K = NoSink>
where
    F: Fold,
    S: Source<Event = F::Event>,
    K: SnapshotSink<F>,
{
    engine: Engine<F>,
    source: S,
    sink: K,
    config: DriverConfig,
    batch: Batch<F::Event>,
    scratch: Vec<(BlockRef, u32, F::Event)>,
    initial: F,
    consecutive_errors: u32,
    caught_up: bool,
    generation: u64,
    last_checkpoint_block: Option<u64>,
    last_snapshot_block: Option<u64>,
    durability_lost: bool,
    advanced: bool,
    seen_resets: u64,
}

#[cfg_attr(verus_keep_ghost, cfg_eval, verus_verify)]
impl<F, S> Driver<F, S>
where
    F: Fold + Clone,
    S: Source<Event = F::Event>,
{
    /// Builds a driver that persists nothing.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            r matches Ok(d) ==> d.wf() && d.synced() && engine.valid()
                && d.engine_view() == Engine::<F>::fresh(fview::<F>(&fold), engine)
                && d.durable_ok(),
            r matches Err(e) ==> !engine.valid() || horizon_refused(e, config.start_block),
    ))]
    pub fn new(
        fold: F,
        source: S,
        engine: EngineConfig,
        config: DriverConfig,
    ) -> Result<Self, ConfigError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::verus::tcb::axiom_no_sink_offers_nothing(NoSink);
        }
        Self::build(fold, source, NoSink, engine, config)
    }

    /// Resumes from a recovered engine, polling onward from its cursor.
    ///
    /// `genesis` is the fold a resync restarts from, so it is empty state rather than
    /// the recovered state.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            engine.wf(),
        ensures
            r matches Ok(d) ==> d.wf() && d.synced() && d.engine_view() == engine@ && d.durable_ok(),
            r matches Err(e) ==> horizon_refused(e, config.start_block),
    ))]
    pub fn resume(
        engine: Engine<F>,
        source: S,
        genesis: F,
        config: DriverConfig,
    ) -> Result<Self, ConfigError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::verus::tcb::axiom_no_sink_offers_nothing(NoSink);
        }
        Self::around(engine, source, NoSink, genesis, config)
    }
}

#[cfg_attr(verus_keep_ghost, cfg_eval, verus_verify)]
impl<F, S, K> Driver<F, S, K>
where
    F: Fold + Clone,
    S: Source<Event = F::Event>,
    K: SnapshotSink<F>,
{
    /// Builds a driver that offers durable snapshots to the sink.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            r matches Ok(d) ==> d.wf() && d.synced() && engine.valid()
                && d.engine_view() == Engine::<F>::fresh(fview::<F>(&fold), engine)
                && (floor_ok(sink_offered::<K>(&sink), d.engine_view()) ==> d.durable_ok()),
            r matches Err(e) ==> !engine.valid() || horizon_refused(e, config.start_block),
    ))]
    pub fn with_sink(
        fold: F,
        source: S,
        sink: K,
        engine: EngineConfig,
        config: DriverConfig,
    ) -> Result<Self, ConfigError> {
        Self::build(fold, source, sink, engine, config)
    }

    /// Resumes from a recovered engine, offering durable snapshots to the sink.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            engine.wf(),
        ensures
            r matches Ok(d) ==> d.wf() && d.synced() && d.engine_view() == engine@
                && (floor_ok(sink_offered::<K>(&sink), engine@) ==> d.durable_ok()),
            r matches Err(e) ==> horizon_refused(e, config.start_block),
    ))]
    pub fn resume_with_sink(
        engine: Engine<F>,
        source: S,
        sink: K,
        genesis: F,
        config: DriverConfig,
    ) -> Result<Self, ConfigError> {
        Self::around(engine, source, sink, genesis, config)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            r matches Ok(d) ==> d.wf() && d.synced() && engine_config.valid()
                && d.engine@ == Engine::<F>::fresh(fview::<F>(&fold), engine_config)
                && fview::<F>(&d.initial) == fview::<F>(&fold)
                && (floor_ok(sink_offered::<K>(&sink), d.engine@) ==> d.durable_ok()),
            r matches Err(e) ==> !engine_config.valid() || horizon_refused(e, driver_config.start_block),
    ))]
    fn build(
        fold: F,
        source: S,
        sink: K,
        engine_config: EngineConfig,
        driver_config: DriverConfig,
    ) -> Result<Self, ConfigError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|b: F| #[trigger] call_ensures(F::clone, (&fold,), b) implies fview::<F>(&b)
                == fview::<F>(&fold) by {
                axiom_clone_preserves_fview::<F>(fold, b);
            }
        }
        let initial = fold.clone();
        let engine = Engine::new(fold, engine_config)?;
        Self::around(engine, source, sink, initial, driver_config)
    }

    /// Wraps an engine, checking the source horizon against the configured start block.
    ///
    /// A sink whose durable cursor leads the engine, such as a store holding a snapshot
    /// under a fresh engine, is reset so it never reports that stale point.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            engine.wf(),
        ensures
            r matches Ok(d) ==> {
                &&& d.wf()
                &&& d.synced()
                &&& d.engine == engine
                &&& d.source == source
                &&& d.initial == initial
                &&& d.config == driver_config
                &&& d.batch@.ends.len() == 0 && d.batch@.boundary is None
                &&& d.last_checkpoint_block is None && d.last_snapshot_block is None
                &&& !d.durability_lost && !d.caught_up && d.consecutive_errors == 0
                // A4 reading: T6b holds when the sink was reset, else when it offered
                // nothing past the engine's state.
                &&& d.sink == sink || sink_offered::<K>(&d.sink) == Set::<Position>::empty()
                &&& floor_ok(sink_offered::<K>(&sink), engine@) ==> d.durable_ok()
            },
            r matches Err(e) ==> horizon_refused(e, driver_config.start_block),
    ))]
    fn around(
        engine: Engine<F>,
        source: S,
        mut sink: K,
        initial: F,
        driver_config: DriverConfig,
    ) -> Result<Self, ConfigError> {
        match source.horizon() {
            ReplayHorizon::FromBlock(horizon) if horizon > driver_config.start_block => {
                return Err(ConfigError::HorizonExceedsStart {
                    start: driver_config.start_block,
                    horizon,
                });
            }
            _ => {}
        }
        if pos_gt(sink.durable_cursor(), engine.cursor()) {
            sink.reset();
        }
        let seen_resets = engine.resets();
        Ok(Self {
            engine,
            source,
            sink,
            config: driver_config,
            batch: Batch::new(),
            scratch: Vec::new(),
            initial,
            consecutive_errors: 0,
            caught_up: false,
            generation: 0,
            last_checkpoint_block: None,
            last_snapshot_block: None,
            durability_lost: false,
            advanced: false,
            seen_resets,
        })
    }
}

impl<F, S, K> Driver<F, S, K>
where
    F: Fold + Clone,
    S: Source<Event = F::Event>,
    K: SnapshotSink<F>,
{
    /// Borrows the durability sink.
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    pub fn sink(&self) -> &K {
        &self.sink
    }

    /// Consumes the driver, returning the sink for joining or inspection.
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    pub fn into_sink(self) -> K {
        self.sink
    }

    /// Borrows the underlying engine.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            r@ == self.engine_view(),
            self.wf() ==> r.wf(),
    ))]
    pub fn engine(&self) -> &Engine<F> {
        &self.engine
    }

    /// Manual recovery access: rollback out of Halted or Poisoned, then keep ticking.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            r@ == old(self).engine_view(),
            old(self).wf() ==> r.wf(),
            // The driver keeps only its own half of `wf`: the engine's, synced and
            // durable_ok are the caller's to restore; `step` reconciles an unseen reset.
            final(self).engine_view() == final(r)@,
            old(self).wf() && final(r).wf() ==> final(self).wf(),
            old(self).synced() ==> (final(self).synced() <==> final(r)@.resets == r@.resets),
            old(self).durable_ok() && final(r)@ == r@ ==> final(self).durable_ok(),
    ))]
    pub fn engine_mut(&mut self) -> &mut Engine<F> {
        &mut self.engine
    }

    /// Mutable access to the underlying event source.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures
            final(self).engine_view() == old(self).engine_view(),
            old(self).wf() ==> final(self).wf(),
            old(self).synced() ==> final(self).synced(),
            old(self).durable_ok() ==> final(self).durable_ok(),
    ))]
    pub fn source_mut(&mut self) -> &mut S {
        &mut self.source
    }

    /// True once the most recent poll returned no new blocks.
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    pub fn is_caught_up(&self) -> bool {
        self.caught_up
    }

    /// Runs the interval-based checkpoint rule.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            old(self).durable_ok() ==> final(self).durable_ok(),
            if checkpoint_due(*old(self)) {
                checkpoint_ran(*old(self), *final(self))
            } else {
                *final(self) == *old(self)
            },
    ))]
    fn auto_checkpoint(&mut self) {
        let Some(interval) = self.config.checkpoint_interval else {
            return;
        };
        let Some(cursor) = self.engine.cursor() else {
            return;
        };
        if due(self.last_checkpoint_block, cursor.block, interval) {
            self.run_checkpoint();
        }
    }

    /// Stores a checkpoint and records the block it was taken at.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            old(self).durable_ok() ==> final(self).durable_ok(),
            checkpoint_ran(*old(self), *final(self)),
    ))]
    fn run_checkpoint(&mut self) {
        self.engine.checkpoint();
        #[cfg(verus_keep_ghost)]
        proof! {
            let (pre, post) = (old(self).engine@, self.engine@);
            if pre.status is Active && pre.slots.len() > 0 {
                // A live slot below the new one was live one index up before.
                assert forall|k: int| #[trigger] post.live_at(k) && k + 1 < post.slots.len() implies pre.live_at(k + 1) by {
                    assert(post.slots[k] == pre.slots[k + 1]);
                }
            }
        }
        if let Some(cursor) = self.engine.cursor() {
            self.last_checkpoint_block = Some(cursor.block);
        }
    }

    /// Runs the interval-based snapshot rule; returns the overriding tick, if any.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            old(self).durable_ok() ==> final(self).durable_ok(),
            if snapshot_due(*old(self)) {
                let p = old(self).engine@.durable_point().unwrap();
                &&& forall|q: Position|
                    #[trigger] sink_offered::<K>(&final(self).sink).contains(q)
                        ==> sink_offered::<K>(&old(self).sink).contains(q) || q == p
                &&& match r {
                    None => *final(self) == (Driver {
                        sink: final(self).sink,
                        last_snapshot_block: Some(p.block),
                        ..*old(self)
                    }),
                    Some(t) => t == Tick::DurabilityLost && *final(self) == (Driver {
                        sink: final(self).sink,
                        durability_lost: true,
                        ..*old(self)
                    }),
                }
            } else {
                r is None && *final(self) == *old(self)
            },
    ))]
    fn offer_snapshot(&mut self) -> Option<Tick> {
        if self.durability_lost {
            return None;
        }
        let interval = self.config.snapshot_interval?;
        let point = self.engine.durable_point()?;
        if !due(self.last_snapshot_block, point.block, interval) {
            return None;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            // The offered point is the oldest live slot's cursor: at or below the cursor
            // and, by slot monotonicity, every live slot.
            let v = self.engine@;
            self.engine.lemma_wf();
            self.engine.lemma_durable_point_le_cursor();
            crate::verus::model::lemma_oldest_live_from(v, 0);
        }
        match self.sink.offer(&self.engine) {
            Ok(()) => {
                self.last_snapshot_block = Some(point.block);
                None
            }
            Err(DurabilityLost) => Some(self.lose_durability()),
        }
    }

    /// Latches the sink refusal so no further offer runs; folding continues unpersisted.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            r == Tick::DurabilityLost,
            *final(self) == (Driver { durability_lost: true, ..*old(self) }),
    ))]
    #[cold]
    fn lose_durability(&mut self) -> Tick {
        self.durability_lost = true;
        Tick::DurabilityLost
    }

    /// Lowers both cadence marks to the restore point so neither the next checkpoint nor
    /// the next offer is suppressed; a cursorless restore clears them.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures
            *final(self) == (Driver {
                last_checkpoint_block: clamp_spec(old(self).last_checkpoint_block, to),
                last_snapshot_block: clamp_spec(old(self).last_snapshot_block, to),
                ..*old(self)
            }),
    ))]
    #[cold]
    fn clamp_marks(&mut self, to: Option<Position>) {
        self.last_checkpoint_block = clamp(self.last_checkpoint_block, to);
        self.last_snapshot_block = clamp(self.last_snapshot_block, to);
    }

    /// Rolls back to the newest checkpoint at or below the ancestor, else escalates.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
            old(self).synced(),
        ensures
            final(self).wf(),
            final(self).synced(),
            old(self).durable_ok() ==> final(self).durable_ok(),
            r matches Tick::RolledBack { to } ==> rolled_back(*old(self), *final(self), ancestor, to),
            r is Resynced ==> resynced(*old(self), *final(self)),
            r is Terminal ==> *final(self) == (Driver { engine: final(self).engine, ..*old(self) })
                && final(self).engine@ == (EngineView { status: final(self).engine@.status, ..old(self).engine@ }),
            // The ladder: rollback, else resync or HorizonExceeded when no live slot
            // qualifies; an Unrecoverable engine stays so.
            r is RolledBack || old(self).engine@.status is Unrecoverable && r matches Tick::Terminal(
                EngineStatus::Unrecoverable { .. },
            ) || (forall|j: int|
                !(#[trigger] old(self).engine@.live_at(j) && qualifies(old(self).engine@.slots[j].unwrap(), ancestor)))
                && exists|h: ReplayHorizon| #[trigger] ladder_tail(old(self).config.start_block, h, r),
    ))]
    #[cold]
    fn roll_back_to(&mut self, ancestor: u64) -> Tick {
        match self.engine.rollback_at_or_below(ancestor) {
            Ok(to) => {
                self.caught_up = false;
                self.clamp_marks(to);
                #[cfg(verus_keep_ghost)]
                proof! {
                    let (pre, post) = (old(self).engine@, self.engine@);
                    assert forall|j: int| #[trigger] post.live_at(j) implies pre.live_at(j) by {
                        let c = post.slots[j].unwrap().cursor;
                        if let Some(c) = c {
                            let i = choose|i: int| 0 <= i < post.ring.len() && #[trigger] post.ring[i].number == c.block;
                            assert(pre.ring[i] == post.ring[i]);
                        }
                    }
                    assert(*self == (Driver {
                        engine: self.engine,
                        caught_up: false,
                        last_checkpoint_block: clamp_spec(old(self).last_checkpoint_block, to),
                        last_snapshot_block: clamp_spec(old(self).last_snapshot_block, to),
                        ..*old(self)
                    }));
                    assert(exists|k: int| #[trigger] pre.rollback_target(ancestor, k) && to == pre.slots[k].unwrap().cursor);
                    assert(post.cursor == to);
                    assert(post.ring == pre.ring.subrange(0, post.ring.len() as int));
                    assert(forall|init: int, log: Seq<(Position, F::Event)>|
                        #[trigger] pre.inv::<F, F::Event, F::Error>(init, log) ==> post.inv::<F, F::Event, F::Error>(init, upto::<F::Event>(log, to)));
                    assert(rolled_back(*old(self), *self, ancestor, to));
                }
                Tick::RolledBack { to }
            }
            Err(RollbackError::NoCheckpointAtOrBelow { .. }) => self.resync_or_terminal(),
            Err(RollbackError::Unrecoverable { cause }) => {
                Tick::Terminal(EngineStatus::Unrecoverable { cause })
            }
        }
    }

    /// Resyncs from genesis when the source horizon still covers the start block,
    /// otherwise marks the engine unrecoverable with the horizon shortfall.
    // The ladder's last two rungs, over the `horizon()` value `h` read here.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
            old(self).synced(),
        ensures
            final(self).wf(),
            final(self).synced(),
            old(self).durable_ok() ==> final(self).durable_ok(),
            exists|h: ReplayHorizon| #[trigger] ladder_tail(old(self).config.start_block, h, r),
            r is Resynced ==> resynced(*old(self), *final(self)),
            r is Terminal ==> *final(self) == (Driver { engine: final(self).engine, ..*old(self) })
                && final(self).engine@ == (EngineView { status: final(self).engine@.status, ..old(self).engine@ }),
    ))]
    #[cold]
    fn resync_or_terminal(&mut self) -> Tick {
        let horizon = self.source.horizon();
        let tick = match horizon {
            // The same shortfall `around` rejects at construction, reached at runtime.
            ReplayHorizon::FromBlock(horizon) if horizon > self.config.start_block => {
                self.engine
                    .mark_unrecoverable(DivergenceCause::HorizonExceeded {
                        needed: self.config.start_block,
                        horizon,
                    });
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert forall|k: int| #[trigger] self.engine@.live_at(k) implies old(self).engine@.live_at(k) by {}
                }
                Tick::Terminal(self.engine.status())
            }
            _ => self.resync(),
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(ladder_tail(old(self).config.start_block, horizon, tick));
        }
        tick
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
            old(self).synced(),
        ensures
            final(self).wf(),
            final(self).durable_ok(),
            r == Tick::Resynced,
            resynced(*old(self), *final(self)),
    ))]
    #[cold]
    fn resync(&mut self) -> Tick {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|b: F| #[trigger] call_ensures(F::clone, (&self.initial,), b) implies fview::<F>(
                &b,
            ) == fview::<F>(&self.initial) by {
                axiom_clone_preserves_fview::<F>(self.initial, b);
            }
        }
        self.engine.reset(self.initial.clone());
        self.caught_up = false;
        self.consecutive_errors = 0;
        self.reconcile_reset();
        Tick::Resynced
    }

    /// Catches up with an engine reset this driver has not seen: resets the sink so
    /// its durable cursor drops to None, and clears the cadence marks.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures
            final(self).synced(),
            old(self).synced() ==> *final(self) == *old(self),
            !old(self).synced() ==> reconciled(*old(self), *final(self)),
            old(self).durable_ok() ==> final(self).durable_ok(),
            old(self).wf() ==> final(self).wf(),
    ))]
    fn reconcile_reset(&mut self) {
        let resets = self.engine.resets();
        if resets != self.seen_resets {
            self.reconcile_reset_slow(resets);
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures
            *final(self) == (Driver {
                seen_resets: resets,
                sink: final(self).sink,
                last_checkpoint_block: None,
                last_snapshot_block: None,
                ..*old(self)
            }),
            sink_offered::<K>(&final(self).sink) == Set::<Position>::empty(),
    ))]
    #[cold]
    fn reconcile_reset_slow(&mut self, resets: u64) {
        self.seen_resets = resets;
        self.sink.reset();
        self.clamp_marks(None);
    }

    /// Runs one poll-apply step, then records whether the cursor moved forward.
    fn step(&mut self) -> Tick {
        self.reconcile_reset();
        let tick = self.poll_apply();
        // Only forward cursor movement earns an immediate re-poll; a batch the
        // engine fully deduped leaves the loop on its poll interval.
        self.advanced = matches!(
            tick,
            Tick::Progressed(summary) if summary.applied > 0 || summary.skipped > 0
        );
        tick
    }

    /// Scans the source and applies the batch, recovering from a fork by bisection.
    fn poll_apply(&mut self) -> Tick {
        self.generation = self.generation.wrapping_add(1);
        if !self.engine.status().is_active() {
            return Tick::Terminal(self.engine.status());
        }
        if self.scan().is_err() {
            self.consecutive_errors = self.consecutive_errors.saturating_add(1);
            return Tick::SourceError;
        }
        self.consecutive_errors = 0;
        match self.engine.apply_batch(&self.batch) {
            Ok(summary) => {
                self.caught_up = self.batch.is_empty();
                // A snapshot refusal overrides progress; a checkpoint is silent.
                self.auto_checkpoint();
                if let Some(tick) = self.offer_snapshot() {
                    return tick;
                }
                if self.batch.is_empty() {
                    Tick::Idle
                } else {
                    Tick::Progressed(summary)
                }
            }
            Err(
                ApplyError::ForkSuspected { .. }
                | ApplyError::MissingBoundary
                | ApplyError::CursorBlockUnobserved { .. },
            ) => self.recover_via_bisection(),
            Err(ApplyError::Halted { .. } | ApplyError::Poisoned { .. }) => {
                Tick::Terminal(self.engine.status())
            }
            Err(ApplyError::Shape(_) | ApplyError::BoundaryNumberMismatch { .. }) => {
                self.consecutive_errors = self.consecutive_errors.saturating_add(1);
                Tick::SourceError
            }
            Err(ApplyError::NotActive { .. }) => {
                unreachable!(
                    "engine status was checked active before this apply_batch call"
                )
            }
        }
    }

    /// Fills `batch` with the blocks strictly after the cursor, plus the cursor block's
    /// header as the source reports it now.
    // B1: the boundary is read after every window, so its view is the last log entry.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            ({
                let (l0, hist) = (
                    sview_log::<S>(&old(self).source).len() as int,
                    sview_log::<S>(&final(self).source),
                );
                let cursor = old(self).engine@.cursor;
                &&& *final(self) == (Driver {
                    source: final(self).source,
                    batch: final(self).batch,
                    scratch: final(self).scratch,
                    ..*old(self)
                })
                &&& l0 < hist.len()
                &&& hist.subrange(0, l0) == sview_log::<S>(&old(self).source)
                &&& forall|k: int| l0 <= k < hist.len() ==> a1::<S, S::Event>(#[trigger] hist[k])
                &&& r is Ok ==> exists|h: u64, w: u64, wins: Seq<(int, int)>|
                    #[trigger] scanned::<S, S::Event>(
                        hist,
                        l0,
                        scan_first(cursor, old(self).config.start_block),
                        h,
                        w,
                        wins,
                        cursor,
                        final(self).batch@,
                    )
            }),
    ))]
    fn scan(&mut self) -> Result<(), S::Error> {
        self.batch.clear();
        let cursor = self.engine.cursor();
        let head = self.source.head()?;
        // None only for a cursor at u64::MAX, which has no block above it to read.
        let first = match cursor {
            Some(cursor) => cursor.block.checked_add(1),
            None => Some(self.config.start_block),
        };

        let window = self.source.window().max(1);
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost l0 = sview_log::<S>(&old(self).source).len() as int;
            let ghost d1 = *self;
            let ghost mut wins: Seq<(int, int)> = Seq::empty();
            assert(d1.batch@.triples() == Seq::<(BlockRef, u32, F::Event)>::empty());
        }
        if let Some(mut from) = first {
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost f0 = from as int;
            }
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant
                    // Loops do not see the fn's requires: carry wf and d1's link to old.
                    old(self).wf(),
                    d1 == (Driver { source: d1.source, batch: d1.batch, ..*old(self) }),
                    l0 == sview_log::<S>(&old(self).source).len(),
                    sview_log::<S>(&d1.source).len() == l0 + 1,
                    sview_log::<S>(&self.source).subrange(0, l0) == sview_log::<S>(&old(self).source),
                    sview_log::<S>(&d1.source).subrange(0, l0) == sview_log::<S>(&old(self).source),
                    d1.batch@.triples().len() == 0,
                    d1.batch@.ends.len() == 0,
                    *self == (Driver { source: self.source, scratch: self.scratch, batch: self.batch, ..d1 }),
                    self.batch@.wf(),
                    self.batch@.boundary is None,
                    sview_log::<S>(&self.source).len() == l0 + 1 + wins.len(),
                    sview_log::<S>(&self.source).subrange(0, l0 + 1) == sview_log::<S>(&d1.source),
                    forall|k: int| l0 <= k < sview_log::<S>(&self.source).len()
                        ==> a1::<S, S::Event>(#[trigger] sview_log::<S>(&self.source)[k]),
                    window >= 1,
                    scan_windows(wins, f0, window, head),
                invariant_except_break
                    self.batch == d1.batch,
                    forall|i: int| 0 <= i < wins.len() ==> range_entries::<S, S::Event>(
                        sview_log::<S>(&self.source)[l0 + 1 + i],
                        #[trigger] wins[i].0,
                        wins[i].1,
                    ).len() == 0,
                    from as int == if wins.len() == 0 { f0 } else { wins.last().1 + 1 },
                ensures
                    self.batch@.wf(),
                    self.batch@.boundary is None,
                    *self == (Driver { source: self.source, scratch: self.scratch, batch: self.batch, ..d1 }),
                    sview_log::<S>(&self.source).len() == l0 + 1 + wins.len(),
                    sview_log::<S>(&self.source).subrange(0, l0 + 1) == sview_log::<S>(&d1.source),
                    forall|k: int| l0 <= k < sview_log::<S>(&self.source).len()
                        ==> a1::<S, S::Event>(#[trigger] sview_log::<S>(&self.source)[k]),
                    scan_windows(wins, f0, window, head),
                    forall|i: int| 0 <= i < wins.len() - 1 ==> range_entries::<S, S::Event>(
                        sview_log::<S>(&self.source)[l0 + 1 + i],
                        #[trigger] wins[i].0,
                        wins[i].1,
                    ).len() == 0,
                    self.batch@.triples().len() > 0 ==> wins.len() > 0
                        && self.batch@.triples().to_multiset() == range_entries::<S, S::Event>(
                        sview_log::<S>(&self.source)[l0 + wins.len()],
                        wins.last().0,
                        wins.last().1,
                    ).to_multiset(),
                    self.batch@.triples().len() == 0 ==> if wins.len() == 0 {
                        f0 > head
                    } else {
                        wins.last().1 == head && range_entries::<S, S::Event>(
                            sview_log::<S>(&self.source)[l0 + wins.len()],
                            wins.last().0,
                            wins.last().1,
                        ).len() == 0
                    },
                decreases head as int + 1 - from as int,
            ))]
            while from <= head {
                let to = head.min(from.saturating_add(window - 1));
                self.scratch.clear();
                #[cfg(verus_keep_ghost)]
                proof! {
                    wins = wins.push((from as int, to as int));
                }
                self.source.events_in(from, to, &mut self.scratch)?;
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(self.scratch@ == self.scratch@.subrange(0, self.scratch@.len() as int));
                    vstd::seq_lib::to_multiset_len(self.scratch@);
                    vstd::seq_lib::to_multiset_len(range_entries::<S, S::Event>(
                        sview_log::<S>(&self.source).last(),
                        from as int,
                        to as int,
                    ));
                }
                if !self.scratch.is_empty() {
                    group_into(&mut self.batch, &mut self.scratch);
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        vstd::seq_lib::to_multiset_len(self.batch@.triples());
                    }
                    break;
                }
                let Some(next) = to.checked_add(1) else {
                    break;
                };
                from = next;
            }
        }

        // Fetched after the events, so a reorg at or below the cursor that lands during
        // the walk fails the boundary check instead of passing a batch from the new chain.
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost b2 = self.batch;
            let ghost h2 = sview_log::<S>(&self.source);
            let ghost m = wins.len() as int;
            if m > 0 && self.batch@.triples().len() == 0 {
                let last = range_entries::<S, S::Event>(h2[l0 + m], wins[m - 1].0, wins[m - 1].1);
                assert(last =~= self.batch@.triples());
            }
            assert(windows_ok::<S, S::Event>(
                h2,
                l0,
                scan_first(cursor, old(self).config.start_block),
                head,
                window,
                wins,
                b2@.triples(),
            ));
        }
        self.batch.boundary = match cursor {
            Some(cursor) => self.source.header_at(cursor.block)?,
            None => None,
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::batch::lemma_batch_view(b2);
            crate::batch::lemma_batch_view(self.batch);
            lemma_triples_ignore_boundary(self.batch@, b2@, b2@.ends.len() as int);
            let h3 = sview_log::<S>(&self.source);
            assert(h3.subrange(0, h2.len() as int) =~= h2);
            assert forall|k: int| 0 <= k < h2.len() implies #[trigger] h3[k] == h2[k] by {
                assert(h3.subrange(0, h2.len() as int)[k] == h3[k]);
            }
            assert(scanned::<S, S::Event>(
                sview_log::<S>(&self.source),
                l0,
                scan_first(cursor, old(self).config.start_block),
                head,
                window,
                wins,
                cursor,
                self.batch@,
            ));
        }
        Ok(())
    }

    /// Bisects the observed ring for the deepest still-canonical block, then rolls back.
    // T4c: a RolledBack restore sits at or below a ring block some probe's view confirmed.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
            old(self).synced(),
        ensures
            ({
                let (from, hist) = (
                    sview_log::<S>(&old(self).source).len() as int,
                    sview_log::<S>(&final(self).source),
                );
                let mid = Driver { source: final(self).source, ..*old(self) };
                let ring = old(self).engine@.ring;
                &&& final(self).wf()
                &&& final(self).synced()
                &&& old(self).durable_ok() ==> final(self).durable_ok()
                &&& from <= hist.len()
                &&& hist.subrange(0, from) == sview_log::<S>(&old(self).source)
                &&& forall|k: int| from <= k < hist.len() ==> a1::<S, S::Event>(#[trigger] hist[k])
                &&& r matches Tick::RolledBack { to } ==> exists|lo: int, k: int|
                    0 < lo <= ring.len() && from <= k < hist.len() && #[trigger] probe_held(ring, lo, hist[k])
                        && rolled_back(mid, *final(self), ring[lo - 1].number, to)
                &&& r is Resynced ==> resynced(mid, *final(self))
                &&& r is Terminal ==> *final(self) == (Driver { engine: final(self).engine, ..mid })
                    && final(self).engine@ == (EngineView { status: final(self).engine@.status, ..old(self).engine@ })
                &&& r is SourceError ==> *final(self) == (Driver {
                    consecutive_errors: if old(self).consecutive_errors < u32::MAX {
                        (old(self).consecutive_errors + 1) as u32
                    } else {
                        u32::MAX
                    },
                    ..mid
                })
                &&& r is RolledBack || r is Resynced || r is Terminal || r is SourceError
            }),
    ))]
    #[cold]
    fn recover_via_bisection(&mut self) -> Tick {
        let ring = self.engine.ring();
        match ring.canonical_prefix(&mut self.source) {
            Ok(0) => self.resync_or_terminal(),
            Ok(lo) => {
                let ancestor = ring.get(lo - 1).number;
                let tick = self.roll_back_to(ancestor);
                #[cfg(verus_keep_ghost)]
                proof! {
                    let (from, hist) = (
                        sview_log::<S>(&old(self).source).len() as int,
                        sview_log::<S>(&self.source),
                    );
                    let ring = old(self).engine@.ring;
                    if let Tick::RolledBack { to } = tick {
                        let k = choose|k: int| from <= k < hist.len() && #[trigger] confirms(hist[k], ring[lo - 1])
                            && (ring_chain(ring) ==> forall|i: int|
                            0 <= i < lo && hist[k].contains_key(#[trigger] ring[i].number)
                                ==> hist[k][ring[i].number] == ring[i]) && (ring_chain(ring)
                            && down_closed(hist[k]) ==> forall|i: int|
                            0 <= i < lo ==> confirms(hist[k], #[trigger] ring[i]));
                        assert(probe_held(ring, lo as int, hist[k]));
                    }
                }
                tick
            }
            Err(_) => {
                self.consecutive_errors = self.consecutive_errors.saturating_add(1);
                Tick::SourceError
            }
        }
    }

    /// Advances the loop by one poll, apply, and recovery step.
    pub fn tick(&mut self) -> Tick {
        self.step()
    }

    /// Forces a checkpoint now.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).synced() == old(self).synced(),
            old(self).durable_ok() ==> final(self).durable_ok(),
            final(self).engine_view() == checkpointed(old(self).engine_view()),
            forall|init: int, log: Seq<(Position, F::Event)>|
                #[trigger] old(self).engine_view().inv::<F, F::Event, F::Error>(init, log)
                    ==> final(self).engine_view().inv::<F, F::Event, F::Error>(init, log),
    ))]
    pub fn checkpoint(&mut self) {
        self.run_checkpoint();
    }

    /// Snapshots the current driver and engine state.
    // T6b: the reported durable cursor never leads the cursor.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            r.cursor == self.engine_view().cursor,
            self.durable_ok() ==> opt_le(r.durable_cursor, r.cursor),
    ))]
    pub fn status(&self) -> DriverStatus {
        DriverStatus {
            cursor: self.engine.cursor(),
            last_verified: self.engine.last_verified(),
            engine: self.engine.status(),
            caught_up: self.caught_up,
            skips: self.engine.skip_count(),
            // An unseen reset leaves the sink's pre-reset point in place until the
            // next tick reconciles it.
            durable_cursor: if self.seen_resets == self.engine.resets() {
                self.sink.durable_cursor()
            } else {
                None
            },
            durability_lost: self.durability_lost,
            generation: self.generation,
        }
    }

    /// How long to wait before the next tick.
    pub fn next_delay(&self) -> Duration {
        if self.consecutive_errors == 0 {
            // Catch-up polls run back to back; the poll interval paces the tip.
            return if self.advanced {
                Duration::ZERO
            } else {
                self.config.poll_interval
            };
        }
        let factor = 1u32
            .checked_shl(self.consecutive_errors - 1)
            .unwrap_or(u32::MAX);
        self.config
            .backoff_base
            .saturating_mul(factor)
            .min(self.config.backoff_max)
    }
}

/// Moves `entries` into `batch`, one span per run of equal `BlockRef`s, so two hashes
/// at one height become two equal-number spans that `Batch::validate` rejects.
///
/// Sorted by descending position and popped from the tail, the entries leave in
/// ascending order with no intermediate buffer; the sort is in place.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires
        old(batch)@.wf(),
        old(batch)@.ends.len() == 0,
    ensures
        final(batch)@.wf(),
        final(batch)@.boundary == old(batch)@.boundary,
        final(entries)@.len() == 0,
        final(batch)@.triples().to_multiset() == old(entries)@.to_multiset(),
))]
// `loop` + `match`, not `while let`: Verus keeps no facts after a `while let` loop.
#[allow(clippy::while_let_loop)]
fn group_into<E>(batch: &mut Batch<E>, entries: &mut Vec<(BlockRef, u32, E)>) {
    // `MAX - x` reverses each key lane, so the sort is descending without `Reverse`.
    entries.sort_unstable_by_key(|e| (u64::MAX - e.0.number, u32::MAX - e.1));
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost s = entries@;
        assert(batch@.triples() =~= Seq::empty());
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            batch@.wf(),
            batch@.boundary == old(batch)@.boundary,
            entries@.len() <= s.len(),
            entries@ == s.subrange(0, entries@.len() as int),
            batch@.triples().len() == s.len() - entries@.len(),
            forall|j: int|
                0 <= j < s.len() - entries@.len() ==> #[trigger] batch@.triples()[j] == s[s.len() - 1 - j],
        ensures
            batch@.wf(),
            batch@.boundary == old(batch)@.boundary,
            entries@.len() == 0,
            batch@.triples() =~= s.reverse(),
        decreases entries@.len(),
    ))]
    loop {
        match entries.last() {
            Some(&(block, _, _)) => {
                #[cfg(verus_keep_ghost)]
                proof_decl! {
                    let ghost pre = batch@;
                    let ghost before = entries@;
                }
                batch.push_block_from_tail(block, entries);
                #[cfg(verus_keep_ghost)]
                proof! {
                    lemma_push_triples(pre, batch@, before, entries@, block);
                    if entries@.len() == before.len() {
                        assert(entries@[entries@.len() - 1] == before[before.len() - 1]);
                    }
                    assert(entries@ =~= s.subrange(0, entries@.len() as int));
                    let n = pre.triples().len();
                    assert forall|j: int|
                        0 <= j < s.len() - entries@.len() implies #[trigger] batch@.triples()[j]
                            == s[s.len() - 1 - j] by {
                        if j >= n {
                            let k = j - n;
                            assert(batch@.triples()[n + k] == before[before.len() - 1 - k]);
                            assert(before[before.len() - 1 - k] == s[s.len() - 1 - j]);
                        } else {
                            assert(pre.triples()[j] == s[s.len() - 1 - j]);
                        }
                    }
                }
            }
            None => break,
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        s.lemma_reverse_to_multiset();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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

    use crate::test_util::{
        FailKind,
        PollFailure,
        RecordingFold,
        ScriptedChain,
        WatermarkSink,
    };

    /// Wraps a scripted chain, counting probes and optionally failing the next few.
    struct Probe {
        inner: ScriptedChain,
        calls: u32,
        fail_next: u32,
    }

    impl Probe {
        fn new(inner: ScriptedChain) -> Self {
            Self {
                inner,
                calls: 0,
                fail_next: 0,
            }
        }

        fn fail_next_probes(&mut self, n: u32) {
            self.fail_next = n;
        }
    }

    impl Source for Probe {
        type Event = u64;
        type Error = PollFailure;

        fn head(&mut self) -> Result<u64, PollFailure> {
            self.inner.head()
        }

        fn header_at(&mut self, number: u64) -> Result<Option<BlockRef>, PollFailure> {
            self.calls += 1;
            if self.fail_next > 0 {
                self.fail_next -= 1;
                return Err(PollFailure);
            }
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

    /// Source that re-serves the same one-event block whatever range is asked for,
    /// so the engine dedupes every poll after the first.
    struct Stuck {
        block: BlockRef,
    }

    impl Source for Stuck {
        type Event = u64;
        type Error = PollFailure;

        fn head(&mut self) -> Result<u64, PollFailure> {
            // above the block, so the scan keeps querying and keeps being re-served it
            Ok(self.block.number + 1)
        }

        fn header_at(&mut self, _number: u64) -> Result<Option<BlockRef>, PollFailure> {
            Ok(Some(self.block))
        }

        fn events_in(
            &mut self,
            _from: u64,
            _to: u64,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            out.push((self.block, 0, 1));
            Ok(())
        }
    }

    /// Replaces the last `depth` blocks with one block per entry of `events`.
    fn reorg_to(chain: &mut ScriptedChain, depth: usize, events: &[u64]) {
        let blocks: Vec<[u64; 1]> = events.iter().map(|event| [*event]).collect();
        let slices: Vec<&[u64]> = blocks.iter().map(|block| block.as_slice()).collect();
        chain.reorg(depth, &slices);
    }

    /// Scripted chain that misbehaves once, inside a single scan.
    struct Adversary {
        inner: ScriptedChain,
        /// Reorg run by the next `head` call.
        on_head: Option<(usize, Vec<u64>)>,
        /// Reorg run by the first `header_at` call after an `events_in` call.
        after_events: Option<(usize, Vec<u64>)>,
        events_served: bool,
        /// Extra entry served whenever the queried range covers its block.
        rogue: Option<(BlockRef, u32, u64)>,
    }

    impl Adversary {
        fn new(inner: ScriptedChain) -> Self {
            Self {
                inner,
                on_head: None,
                after_events: None,
                events_served: false,
                rogue: None,
            }
        }
    }

    impl Source for Adversary {
        type Event = u64;
        type Error = PollFailure;

        fn head(&mut self) -> Result<u64, PollFailure> {
            if let Some((depth, events)) = self.on_head.take() {
                reorg_to(&mut self.inner, depth, &events);
            }
            self.inner.head()
        }

        fn header_at(&mut self, number: u64) -> Result<Option<BlockRef>, PollFailure> {
            if self.events_served
                && let Some((depth, events)) = self.after_events.take()
            {
                reorg_to(&mut self.inner, depth, &events);
            }
            self.inner.header_at(number)
        }

        fn events_in(
            &mut self,
            from: u64,
            to: u64,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            self.events_served = true;
            if let Some(entry) = self.rogue
                && (from..=to).contains(&entry.0.number)
            {
                out.push(entry);
            }
            self.inner.events_in(from, to, out)
        }

        fn window(&self) -> u64 {
            self.inner.window()
        }
    }

    /// Chain whose only block is number `u64::MAX`; errors on a second `events_in` in
    /// one tick, so a scan that spins fails the tick instead of hanging the test.
    struct Summit {
        event: Option<u64>,
        queries: u32,
    }

    impl Summit {
        const BLOCK: BlockRef = BlockRef {
            number: u64::MAX,
            hash: [9u8; 32],
        };
    }

    impl Source for Summit {
        type Event = u64;
        type Error = PollFailure;

        fn head(&mut self) -> Result<u64, PollFailure> {
            self.queries = 0;
            Ok(u64::MAX)
        }

        fn header_at(&mut self, number: u64) -> Result<Option<BlockRef>, PollFailure> {
            Ok((number == u64::MAX).then_some(Self::BLOCK))
        }

        fn events_in(
            &mut self,
            _from: u64,
            to: u64,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            self.queries += 1;
            if self.queries > 1 {
                return Err(PollFailure);
            }
            if let Some(event) = self.event
                && to == u64::MAX
            {
                out.push((Self::BLOCK, 0, event));
            }
            Ok(())
        }
    }

    fn engine_config(checkpoint_slots: usize) -> EngineConfig {
        EngineConfig {
            ring_capacity: 8,
            checkpoint_slots,
        }
    }

    fn new_driver(
        chain: ScriptedChain,
        engine: EngineConfig,
        config: DriverConfig,
    ) -> Driver<RecordingFold, ScriptedChain> {
        Driver::new(RecordingFold::default(), chain, engine, config).unwrap()
    }

    fn run_to_idle<F, S, K>(driver: &mut Driver<F, S, K>) -> Tick
    where
        F: Fold + Clone,
        S: Source<Event = F::Event>,
        K: SnapshotSink<F>,
    {
        let mut outcome = driver.tick();
        while !matches!(outcome, Tick::Idle) {
            outcome = driver.tick();
        }
        outcome
    }

    fn collect_to_idle<F, S, K>(driver: &mut Driver<F, S, K>) -> Vec<Tick>
    where
        F: Fold + Clone,
        S: Source<Event = F::Event>,
        K: SnapshotSink<F>,
    {
        let mut ticks = vec![driver.tick()];
        while !matches!(ticks.last(), Some(Tick::Idle)) {
            ticks.push(driver.tick());
        }
        ticks
    }

    /// Chain of `blocks` one-event blocks served one event-bearing block per poll.
    fn one_event_chain(blocks: u64) -> ScriptedChain {
        let mut chain = ScriptedChain::new(1);
        for value in 1..=blocks {
            chain.push_block(&[value]);
        }
        chain.set_window(1);
        chain
    }

    fn cadence_config(checkpoint: u64, snapshot: u64) -> DriverConfig {
        DriverConfig {
            checkpoint_interval: Some(checkpoint),
            snapshot_interval: Some(snapshot),
            ..DriverConfig::default()
        }
    }

    /// Recording fold over a scripted chain, offering snapshots to a watermark sink.
    type SinkDriver = Driver<RecordingFold, ScriptedChain, WatermarkSink>;

    fn sink_driver(blocks: u64, slots: usize, config: DriverConfig) -> SinkDriver {
        Driver::with_sink(
            RecordingFold::default(),
            one_event_chain(blocks),
            WatermarkSink::default(),
            engine_config(slots),
            config,
        )
        .unwrap()
    }

    fn probed_sink_driver(blocks: u64, slots: usize, config: DriverConfig) -> SinkDriver {
        Driver::with_sink(
            RecordingFold::default(),
            one_event_chain(blocks),
            WatermarkSink::default(),
            engine_config(slots),
            config,
        )
        .unwrap()
    }

    #[test]
    fn snapshot_interval_offers_on_durable_point_cadence() {
        // given twelve one-event blocks, 3 slots, checkpoints every 2, snapshots every 4
        let mut driver = sink_driver(12, 3, cadence_config(2, 4));
        // when driven to the tip
        run_to_idle(&mut driver);
        // then offers land on durable-point progress, not cursor progress
        assert_eq!(
            driver.sink().offered,
            vec![Position::new(1, 0), Position::new(5, 0)]
        );
    }

    #[test]
    fn no_sink_never_offers_and_reports_no_durable_cursor() {
        // given a NoSink driver over four blocks with both cadences at their tightest
        let mut driver =
            new_driver(one_event_chain(4), engine_config(2), cadence_config(1, 1));
        // when driven to the tip collecting every tick
        let ticks = collect_to_idle(&mut driver);
        // then no tick reports lost durability and the status carries no durable cursor
        assert!(!ticks.contains(&Tick::DurabilityLost));
        assert_eq!(driver.status().durable_cursor, None);
        assert!(!driver.status().durability_lost);
    }

    #[test]
    fn zero_checkpoint_slots_never_offers() {
        // given zero checkpoint slots over four blocks with both cadences at 1
        let mut driver = sink_driver(4, 0, cadence_config(1, 1));
        // when driven to the tip
        run_to_idle(&mut driver);
        // then nothing was ever offered and the durable cursor stays None
        assert!(driver.sink().offered.is_empty());
        assert_eq!(driver.status().durable_cursor, None);
    }

    #[test]
    fn durable_cursor_trails_the_live_cursor_by_checkpoint_coverage() {
        // given twelve blocks, 3 slots, checkpoints every 2, snapshots every block
        let mut driver = sink_driver(12, 3, cadence_config(2, 1));
        // when driven to the tip
        run_to_idle(&mut driver);
        // then the durable cursor trails the live cursor by at least (slots - 1) * interval
        let status = driver.status();
        assert_eq!(status.cursor, Some(Position::new(12, 0)));
        assert_eq!(status.durable_cursor, Some(Position::new(7, 0)));
        assert!(status.cursor.unwrap().block - status.durable_cursor.unwrap().block >= 4);
    }

    #[test]
    fn reorg_across_the_live_cursor_leaves_the_durable_cursor_untouched() {
        // given eight blocks driven to a durable cursor of (5, 0) with 4 slots
        let mut driver = probed_sink_driver(8, 4, cadence_config(1, 1));
        run_to_idle(&mut driver);
        let before = driver.status().durable_cursor;
        assert_eq!(before, Some(Position::new(5, 0)));
        // when a depth-2 reorg rolls the driver back
        driver.source_mut().reorg(2, &[&[70], &[80]]);
        let outcome = driver.tick();
        // then the rollback lands above the durable cursor and leaves it unchanged
        let status = driver.status();
        assert_eq!(
            outcome,
            Tick::RolledBack {
                to: Some(Position::new(6, 0)),
            }
        );
        assert_eq!(status.durable_cursor, before);
        assert!(status.durable_cursor.unwrap() <= Position::new(6, 0));
    }

    #[test]
    fn sink_failure_is_reported_once_then_folding_continues() {
        // given a sink scripted to refuse its first offer, 2 slots, six blocks
        let mut driver = Driver::with_sink(
            RecordingFold::default(),
            one_event_chain(6),
            WatermarkSink {
                offered: Vec::new(),
                fail_next_offers: 1,
            },
            engine_config(2),
            cadence_config(1, 1),
        )
        .unwrap();
        // when driven to the tip collecting every tick
        let ticks = collect_to_idle(&mut driver);
        // then exactly one tick reports the loss and folding still reaches every event
        let lost = ticks
            .iter()
            .filter(|tick| **tick == Tick::DurabilityLost)
            .count();
        assert_eq!(lost, 1);
        assert!(driver.status().durability_lost);
        assert!(driver.sink().offered.is_empty());
        let expected: Vec<(Position, u64)> = (1..=6u64)
            .map(|value| (Position::new(value, 0), value))
            .collect();
        assert_eq!(driver.engine().fold().applied, expected);
    }

    #[test]
    fn rollback_does_not_suppress_the_next_offer() {
        // given eight blocks driven to the tip with 4 slots and both cadences at 1
        let mut driver = probed_sink_driver(8, 4, cadence_config(1, 1));
        run_to_idle(&mut driver);
        // when a depth-3 reorg rolls back and folding resumes to the new tip
        driver.source_mut().reorg(3, &[&[60], &[70], &[80], &[90]]);
        let outcome = driver.tick();
        let Tick::RolledBack { to } = outcome else {
            panic!("expected RolledBack, got {outcome:?}");
        };
        let restore = to.expect("the rollback restores a cursor").block;
        run_to_idle(&mut driver);
        // then offers stayed strictly ascending and resumed above the restore point
        let offered = &driver.sink().offered;
        assert!(offered.windows(2).all(|pair| pair[0].block < pair[1].block));
        assert!(offered.last().expect("offers were made").block > restore);
    }

    #[test]
    fn resync_lowers_the_reported_durable_cursor() {
        // given eight blocks driven to a durable cursor at block 5
        let mut driver = sink_driver(8, 4, cadence_config(1, 1));
        run_to_idle(&mut driver);
        let before = driver.status().durable_cursor.expect("offers were made");
        assert_eq!(before, Position::new(5, 0));
        // when a reorg below the ring forces a resync and folding rebuilds from genesis
        driver.source_mut().reorg(8, &[&[10], &[20], &[30], &[40]]);
        let outcome = driver.tick();
        run_to_idle(&mut driver);
        // then the durable cursor names the rebuilt state, below where it stood
        assert_eq!(outcome, Tick::Resynced);
        let after = driver.status().durable_cursor.expect("offers resumed");
        assert!(after < before);
    }

    #[test]
    fn resync_drops_the_durable_cursor_on_the_resynced_tick() {
        // given eight blocks driven to a durable cursor at block 5
        let mut driver = sink_driver(8, 4, cadence_config(1, 1));
        run_to_idle(&mut driver);
        assert_eq!(driver.status().durable_cursor, Some(Position::new(5, 0)));
        // when a reorg below the ring forces a resync
        driver.source_mut().reorg(8, &[&[10], &[20], &[30], &[40]]);
        let outcome = driver.tick();
        // then the Resynced tick already reports no durable cursor, never one above
        // the applied cursor
        let status = driver.status();
        assert_eq!(outcome, Tick::Resynced);
        assert_eq!(status.cursor, None);
        assert_eq!(status.durable_cursor, None);
        assert_eq!(
            SnapshotSink::<RecordingFold>::durable_cursor(driver.sink()),
            None
        );
    }

    #[test]
    fn manual_engine_reset_drops_the_durable_cursor() {
        // given eight blocks driven to a durable cursor at block 5
        let mut driver = sink_driver(8, 4, cadence_config(1, 1));
        run_to_idle(&mut driver);
        assert_eq!(driver.status().durable_cursor, Some(Position::new(5, 0)));
        // when the engine is reset by hand through engine_mut
        driver.engine_mut().reset(RecordingFold::default());
        let before_tick = driver.status();
        let outcome = driver.tick();
        let after_tick = driver.status();
        // then status reports no durable cursor before the next tick, and after it the
        // durable cursor trails the refolded cursor
        assert_eq!(before_tick.durable_cursor, None);
        assert!(matches!(outcome, Tick::Progressed(_)));
        assert!(after_tick.durable_cursor <= after_tick.cursor);
        assert_eq!(
            after_tick.durable_cursor,
            SnapshotSink::<RecordingFold>::durable_cursor(driver.sink())
        );
    }

    #[test]
    fn driver_folds_to_tip_and_reports_caught_up() {
        // given a ten-block chain with one event per block
        let mut chain = ScriptedChain::new(1);
        for value in 1..=10u64 {
            chain.push_block(&[value]);
        }
        let mut driver = new_driver(chain, engine_config(0), DriverConfig::default());
        // when ticking until Idle
        run_to_idle(&mut driver);
        // then the view holds every event in order and is_caught_up
        let expected: Vec<(Position, u64)> = (1..=10u64)
            .map(|value| (Position::new(value, 0), value))
            .collect();
        assert_eq!(driver.engine().fold().applied, expected);
        assert!(driver.is_caught_up());
    }

    #[test]
    fn empty_poll_is_idle() {
        // given a caught-up driver over a two-block chain
        let mut chain = ScriptedChain::new(1);
        chain.push_block(&[1]);
        chain.push_block(&[2]);
        let mut driver = new_driver(chain, engine_config(0), DriverConfig::default());
        driver.tick();
        // when ticked again
        let outcome = driver.tick();
        // then Idle
        assert_eq!(outcome, Tick::Idle);
    }

    #[test]
    fn source_errors_back_off_exponentially() {
        // given a chain that fails the next three polls
        let mut chain = ScriptedChain::new(1);
        chain.push_block(&[1]);
        chain.fail_next_polls(3);
        let mut driver = new_driver(chain, engine_config(0), DriverConfig::default());
        // when ticking
        let first = driver.tick();
        let first_delay = driver.next_delay();
        let second = driver.tick();
        let second_delay = driver.next_delay();
        let third = driver.tick();
        let third_delay = driver.next_delay();
        let fourth = driver.tick();
        // then three SourceError ticks with next_delay 200ms, 400ms, 800ms, then a
        // progressing tick that clears the backoff
        assert_eq!(first, Tick::SourceError);
        assert_eq!(first_delay, Duration::from_millis(200));
        assert_eq!(second, Tick::SourceError);
        assert_eq!(second_delay, Duration::from_millis(400));
        assert_eq!(third, Tick::SourceError);
        assert_eq!(third_delay, Duration::from_millis(800));
        assert!(matches!(fourth, Tick::Progressed(_)));
        assert_eq!(driver.next_delay(), Duration::ZERO);
    }

    #[test]
    fn backoff_caps_at_max() {
        // given a chain that fails every poll
        let mut chain = ScriptedChain::new(1);
        chain.fail_next_polls(u32::MAX);
        let mut driver = new_driver(chain, engine_config(0), DriverConfig::default());
        // when the doubling passes backoff_max
        for _ in 0..10 {
            driver.tick();
        }
        // then next_delay equals backoff_max
        assert_eq!(driver.next_delay(), Duration::from_secs(30));
    }

    #[test]
    fn catch_up_ticks_ask_for_no_delay_until_the_tip() {
        // given ten one-event blocks served one per poll
        let mut driver = new_driver(
            one_event_chain(10),
            engine_config(0),
            DriverConfig::default(),
        );
        // when one tick folds a block and the rest run to the tip
        driver.tick();
        let while_behind = driver.next_delay();
        run_to_idle(&mut driver);
        let at_tip = driver.next_delay();
        // then the catch-up tick asks for no delay and the tip tick asks for the interval
        assert_eq!(while_behind, Duration::ZERO);
        assert_eq!(at_tip, Duration::from_secs(1));
    }

    #[test]
    fn an_empty_window_does_not_report_caught_up_while_behind_head() {
        // given ten blocks where only the last carries events, read one block per query
        let mut chain = ScriptedChain::new(1);
        for _ in 1..10 {
            chain.push_block(&[]);
        }
        chain.push_block(&[42]);
        chain.set_window(1);
        let mut driver = new_driver(chain, engine_config(0), DriverConfig::from_block(1));
        // when polled once
        let tick = driver.tick();
        // then the scan walked every empty window instead of stopping at the first
        assert!(matches!(tick, Tick::Progressed(_)), "got {tick:?}");
        assert!(!driver.is_caught_up());
        assert_eq!(
            driver.engine().fold().applied,
            vec![(Position::new(10, 0), 42)]
        );
    }

    #[test]
    fn rollback_replays_from_the_restored_cursor_not_the_scan_mark() {
        // given a driver caught up on ten blocks, checkpointing every block
        let mut chain = ScriptedChain::new(1);
        for value in 1..=10u64 {
            chain.push_block(&[value]);
        }
        chain.set_window(1);
        let mut driver = new_driver(
            chain,
            engine_config(4),
            DriverConfig {
                checkpoint_interval: Some(1),
                ..DriverConfig::from_block(1)
            },
        );
        run_to_idle(&mut driver);
        // when the last three blocks are replaced
        driver.source_mut().reorg(3, &[&[80], &[90], &[100]]);
        run_to_idle(&mut driver);
        // then the scan restarted at the restored cursor, so the replacements folded;
        // resuming at the high-water mark instead would have skipped them entirely
        let applied: Vec<u64> = driver
            .engine()
            .fold()
            .applied
            .iter()
            .map(|(_, event)| *event)
            .collect();
        assert_eq!(applied, vec![1, 2, 3, 4, 5, 6, 7, 80, 90, 100]);
    }

    #[test]
    fn a_fully_deduped_batch_keeps_the_poll_interval() {
        // given a source that re-serves the same one-event block on every poll
        let block = BlockRef {
            number: 1,
            hash: [7u8; 32],
        };
        let mut driver = Driver::new(
            RecordingFold::default(),
            Stuck { block },
            engine_config(0),
            DriverConfig::default(),
        )
        .unwrap();
        // when the first tick applies the block and the second dedupes it
        let applying = driver.tick();
        let after_apply = driver.next_delay();
        let deduping = driver.tick();
        let after_dedup = driver.next_delay();
        // then only the applying tick asks for an immediate re-poll
        assert_eq!(
            applying,
            Tick::Progressed(ApplySummary {
                applied: 1,
                deduped: 0,
                skipped: 0,
            })
        );
        assert_eq!(after_apply, Duration::ZERO);
        assert_eq!(
            deduping,
            Tick::Progressed(ApplySummary {
                applied: 0,
                deduped: 1,
                skipped: 0,
            })
        );
        assert_eq!(after_dedup, Duration::from_secs(1));
    }

    #[test]
    fn fork_without_probe_resyncs_from_start() {
        // given a chain of five one-event blocks driven to the tip
        let mut chain = ScriptedChain::new(1);
        for value in 1..=5u64 {
            chain.push_block(&[value]);
        }
        let mut driver = new_driver(chain, engine_config(0), DriverConfig::default());
        driver.tick();
        // when the chain reorgs below the cursor and the boundary mismatch surfaces
        driver.source_mut().reorg(3, &[&[10], &[20], &[30]]);
        let outcome = driver.tick();
        // then the tick reports Resynced
        assert_eq!(outcome, Tick::Resynced);
        // and subsequent ticks rebuild the post-reorg view from scratch
        run_to_idle(&mut driver);
        let expected = vec![
            (Position::new(1, 0), 1),
            (Position::new(2, 0), 2),
            (Position::new(3, 0), 10),
            (Position::new(4, 0), 20),
            (Position::new(5, 0), 30),
        ];
        assert_eq!(driver.engine().fold().applied, expected);
    }

    #[test]
    fn resync_with_moved_horizon_is_terminal() {
        // given a fork and a horizon raised above start_block
        let mut chain = ScriptedChain::new(1);
        for value in 1..=5u64 {
            chain.push_block(&[value]);
        }
        let mut driver = new_driver(chain, engine_config(0), DriverConfig::default());
        driver.tick();
        driver.source_mut().reorg(3, &[&[10], &[20], &[30]]);
        driver.source_mut().set_horizon(ReplayHorizon::FromBlock(1));
        // when the fork surfaces
        let outcome = driver.tick();
        // then Terminal with HorizonExceeded { needed, horizon }
        assert_eq!(
            outcome,
            Tick::Terminal(EngineStatus::Unrecoverable {
                cause: DivergenceCause::HorizonExceeded {
                    needed: 0,
                    horizon: 1,
                },
            })
        );
    }

    #[test]
    fn construction_refuses_horizon_above_start() {
        // given a chain whose horizon starts at block 100 and default start_block 0
        let mut chain = ScriptedChain::new(1);
        chain.set_horizon(ReplayHorizon::FromBlock(100));
        // when constructing
        let result = Driver::new(
            RecordingFold::default(),
            chain,
            engine_config(0),
            DriverConfig::default(),
        );
        // then HorizonExceedsStart
        assert_eq!(
            result.err(),
            Some(ConfigError::HorizonExceedsStart {
                start: 0,
                horizon: 100,
            })
        );
    }

    #[test]
    fn auto_checkpoint_follows_interval() {
        // given checkpoint_interval 4 over twelve one-event blocks polled one at a time
        let mut chain = ScriptedChain::new(1);
        for value in 1..=12u64 {
            chain.push_block(&[value]);
        }
        chain.set_window(1);
        let config = DriverConfig {
            checkpoint_interval: Some(4),
            ..DriverConfig::default()
        };
        let engine = EngineConfig {
            ring_capacity: 16,
            checkpoint_slots: 8,
        };
        let mut driver = new_driver(chain, engine, config);
        // when driven to the tip
        run_to_idle(&mut driver);
        // then checkpoint_count is at least 3
        assert!(driver.engine().checkpoint_count() >= 3);
    }

    #[test]
    fn checkpoints_expire_once_their_block_leaves_the_ring() {
        // given checkpoint_interval 4 over twelve blocks with a ring holding only 8
        let mut chain = ScriptedChain::new(1);
        for value in 1..=12u64 {
            chain.push_block(&[value]);
        }
        chain.set_window(1);
        let config = DriverConfig {
            checkpoint_interval: Some(4),
            ..DriverConfig::default()
        };
        let mut driver = new_driver(chain, engine_config(8), config);
        // when driven to the tip, leaving the block 4 checkpoint outside the window
        run_to_idle(&mut driver);
        // then only the checkpoints the ring still observes are retained
        assert_eq!(driver.engine().checkpoint_count(), 2);
        assert_eq!(driver.engine().durable_point(), Some(Position::new(5, 0)));
    }

    #[test]
    fn halt_is_terminal_and_recoverable_via_engine_mut() {
        // given a fold that halts at block 3 after a checkpoint taken at block 2
        let mut chain = ScriptedChain::new(1);
        chain.push_block(&[1]);
        chain.push_block(&[2]);
        chain.push_block(&[3]);
        chain.push_block(&[4]);
        chain.push_block(&[5]);
        chain.set_window(1);
        let halt_pos = Position::new(3, 0);
        let fold = RecordingFold {
            applied: Vec::new(),
            fail_at: Some((halt_pos, FailKind::Halt)),
        };
        let mut driver =
            Driver::new(fold, chain, engine_config(2), DriverConfig::default()).unwrap();
        driver.tick();
        driver.tick();
        driver.checkpoint();
        // when ticked to Terminal
        let outcome = driver.tick();
        assert_eq!(
            outcome,
            Tick::Terminal(EngineStatus::Halted { at: halt_pos })
        );
        driver.source_mut().reorg(3, &[&[], &[40], &[50]]);
        // then engine_mut rollback restores Active
        let restored = driver.engine_mut().rollback_at_or_below(2).unwrap();
        assert_eq!(restored, Some(Position::new(2, 0)));
        assert_eq!(driver.engine().status(), EngineStatus::Active);
        // and further ticks reach the tip
        run_to_idle(&mut driver);
        assert!(driver.is_caught_up());
        assert_eq!(driver.engine().cursor(), Some(Position::new(5, 0)));
    }

    #[test]
    fn generation_increments_every_tick() {
        // given a driver over an empty chain
        let chain = ScriptedChain::new(1);
        let mut driver = new_driver(chain, engine_config(0), DriverConfig::default());
        let start = driver.status().generation;
        // when three ticks of any outcome run
        driver.tick();
        driver.tick();
        driver.tick();
        // then status generation rose by three
        assert_eq!(driver.status().generation, start + 3);
    }

    #[test]
    fn status_snapshot_reflects_engine() {
        // given a driven driver over a two-block chain
        let mut chain = ScriptedChain::new(1);
        chain.push_block(&[1]);
        chain.push_block(&[2]);
        let mut driver = new_driver(chain, engine_config(0), DriverConfig::default());
        driver.tick();
        // when reading status
        let status = driver.status();
        // then cursor, skips, caught_up, engine status all match the engine accessors
        assert_eq!(status.cursor, driver.engine().cursor());
        assert_eq!(status.last_verified, driver.engine().last_verified());
        assert_eq!(status.engine, driver.engine().status());
        assert_eq!(status.caught_up, driver.is_caught_up());
        assert_eq!(status.skips, driver.engine().skip_count());
    }

    #[test]
    fn reorged_content_produces_typed_fork_then_recovery() {
        // given an applied chain with a checkpoint below the fork
        let mut chain = ScriptedChain::new(1);
        for value in 1..=6u64 {
            chain.push_block(&[value]);
        }
        chain.set_window(1);
        let mut driver = Driver::new(
            RecordingFold::default(),
            chain,
            engine_config(4),
            DriverConfig::default(),
        )
        .unwrap();
        driver.tick();
        driver.tick();
        driver.tick();
        driver.checkpoint();
        driver.tick();
        driver.tick();
        driver.tick();
        // when a reorg redelivers changed content and the tick surfaces the fork
        driver.source_mut().reorg(3, &[&[40], &[50], &[60]]);
        let outcome = driver.tick();
        // then one tick reports RolledBack to the checkpoint, later ticks fold the new branch
        assert_eq!(
            outcome,
            Tick::RolledBack {
                to: Some(Position::new(3, 0)),
            }
        );
        run_to_idle(&mut driver);
        let expected = vec![
            (Position::new(1, 0), 1),
            (Position::new(2, 0), 2),
            (Position::new(3, 0), 3),
            (Position::new(4, 0), 40),
            (Position::new(5, 0), 50),
            (Position::new(6, 0), 60),
        ];
        assert_eq!(driver.engine().fold().applied, expected);
    }

    #[test]
    fn eventless_fork_point_is_still_detected() {
        // given events only on blocks 2 and 7 with cursor at 7
        let mut chain = ScriptedChain::new(1);
        chain.push_block(&[]);
        chain.push_block(&[2]);
        chain.push_block(&[]);
        chain.push_block(&[]);
        chain.push_block(&[]);
        chain.push_block(&[]);
        chain.push_block(&[7]);
        chain.set_window(1);
        let mut driver = Driver::new(
            RecordingFold::default(),
            chain,
            engine_config(2),
            DriverConfig::default(),
        )
        .unwrap();
        driver.tick();
        driver.checkpoint();
        driver.tick();
        // when a reorg replaces eventless block 5 upward and the tick surfaces the fork
        driver.source_mut().reorg(3, &[&[], &[], &[70]]);
        let outcome = driver.tick();
        // then the boundary recheck detects it and recovery lands the correct view
        assert!(matches!(outcome, Tick::RolledBack { .. }));
        run_to_idle(&mut driver);
        let expected = vec![(Position::new(2, 0), 2), (Position::new(7, 0), 70)];
        assert_eq!(driver.engine().fold().applied, expected);
    }

    #[test]
    fn shorter_chain_fork_is_suspected_not_retried() {
        // given a reorg to a chain shorter than the cursor block
        let mut chain = ScriptedChain::new(1);
        for value in 1..=5u64 {
            chain.push_block(&[value]);
        }
        chain.set_window(1);
        let mut driver = Driver::new(
            RecordingFold::default(),
            chain,
            engine_config(2),
            DriverConfig::default(),
        )
        .unwrap();
        driver.tick();
        driver.checkpoint();
        for _ in 0..4 {
            driver.tick();
        }
        // when the chain reorgs to a shorter tip and the tick surfaces the fork
        driver.source_mut().reorg(4, &[&[99]]);
        let outcome = driver.tick();
        // then the fork path runs, never SourceError, and recovery proceeds via bisection
        assert_ne!(outcome, Tick::SourceError);
        assert!(matches!(outcome, Tick::RolledBack { .. }));
        run_to_idle(&mut driver);
        let expected = vec![(Position::new(1, 0), 1), (Position::new(2, 0), 99)];
        assert_eq!(driver.engine().fold().applied, expected);
    }

    #[test]
    fn bisection_finds_deepest_canonical_block() {
        // given a ring of eight observed blocks and a fork at the sixth
        let mut chain = ScriptedChain::new(1);
        for value in 1..=8u64 {
            chain.push_block(&[value]);
        }
        chain.set_window(1);
        let mut driver = Driver::new(
            RecordingFold::default(),
            Probe::new(chain),
            engine_config(2),
            DriverConfig::default(),
        )
        .unwrap();
        driver.tick();
        driver.checkpoint();
        for _ in 0..7 {
            driver.tick();
        }
        // when the chain reorgs at the sixth block and the tick surfaces the fork
        driver.source_mut().inner.reorg(3, &[&[60], &[70], &[80]]);
        // the scan spends one probe per poll on the boundary; count only the bisection
        driver.source_mut().calls = 0;
        let outcome = driver.tick();
        // then rollback lands at or below the fifth and probe count is at most four
        match outcome {
            Tick::RolledBack { to } => {
                let landed = to.map_or(0, |pos| pos.block);
                assert!(landed <= 5);
            }
            other => panic!("expected RolledBack, got {other:?}"),
        }
        assert!(driver.source_mut().calls <= 4);
    }

    #[test]
    fn fork_deeper_than_ring_escalates() {
        // given ring capacity 4 and a reorg replacing every retained block
        fn build(horizon: ReplayHorizon) -> Driver<RecordingFold, ScriptedChain> {
            let mut chain = ScriptedChain::new(1);
            for value in 1..=6u64 {
                chain.push_block(&[value]);
            }
            chain.set_window(1);
            let mut driver = Driver::new(
                RecordingFold::default(),
                chain,
                EngineConfig {
                    ring_capacity: 4,
                    checkpoint_slots: 0,
                },
                DriverConfig::default(),
            )
            .unwrap();
            run_to_idle(&mut driver);
            driver
                .source_mut()
                .reorg(6, &[&[10], &[20], &[30], &[40], &[50], &[60]]);
            driver.source_mut().set_horizon(horizon);
            driver
        }
        // when the fork surfaces, once with a horizon that still covers start_block
        let mut resyncable = build(ReplayHorizon::Genesis);
        let resync_outcome = resyncable.tick();
        let mut terminal = build(ReplayHorizon::FromBlock(1));
        let terminal_outcome = terminal.tick();
        // then the resync-capable case reports Resynced, the moved horizon is Terminal
        assert_eq!(resync_outcome, Tick::Resynced);
        assert_eq!(
            terminal_outcome,
            Tick::Terminal(EngineStatus::Unrecoverable {
                cause: DivergenceCause::HorizonExceeded {
                    needed: 0,
                    horizon: 1,
                },
            })
        );
    }

    #[test]
    fn no_checkpoint_below_ancestor_escalates() {
        // given checkpoints only above the fork ancestor
        fn build(horizon: ReplayHorizon) -> Driver<RecordingFold, ScriptedChain> {
            let mut chain = ScriptedChain::new(1);
            for value in 1..=8u64 {
                chain.push_block(&[value]);
            }
            chain.set_window(1);
            let mut driver = Driver::new(
                RecordingFold::default(),
                chain,
                engine_config(1),
                DriverConfig::default(),
            )
            .unwrap();
            for _ in 0..7 {
                driver.tick();
            }
            driver.checkpoint();
            driver.tick();
            driver.source_mut().reorg(3, &[&[60], &[70], &[80]]);
            driver.source_mut().set_horizon(horizon);
            driver
        }
        // when recovery runs, once with a horizon that still covers start_block
        let mut resyncable = build(ReplayHorizon::Genesis);
        let resync_outcome = resyncable.tick();
        let mut terminal = build(ReplayHorizon::FromBlock(1));
        let terminal_outcome = terminal.tick();
        // then resync, or Terminal with the moved horizon, never a wrong-state continue
        assert_eq!(resync_outcome, Tick::Resynced);
        assert_eq!(
            terminal_outcome,
            Tick::Terminal(EngineStatus::Unrecoverable {
                cause: DivergenceCause::HorizonExceeded {
                    needed: 0,
                    horizon: 1,
                },
            })
        );
    }

    #[test]
    fn probe_failure_retries_without_state_damage() {
        // given header_at failures mid bisection
        let mut chain = ScriptedChain::new(1);
        for value in 1..=6u64 {
            chain.push_block(&[value]);
        }
        chain.set_window(1);
        let mut driver = Driver::new(
            RecordingFold::default(),
            Probe::new(chain),
            engine_config(2),
            DriverConfig::default(),
        )
        .unwrap();
        driver.tick();
        driver.checkpoint();
        for _ in 0..5 {
            driver.tick();
        }
        driver.source_mut().inner.reorg(3, &[&[40], &[50], &[60]]);
        driver.source_mut().fail_next_probes(1);
        // when ticked
        let first = driver.tick();
        // then SourceError, and the following tick completes recovery undisturbed
        assert_eq!(first, Tick::SourceError);
        let second = driver.tick();
        assert!(matches!(second, Tick::RolledBack { .. }));
        run_to_idle(&mut driver);
        let expected = vec![
            (Position::new(1, 0), 1),
            (Position::new(2, 0), 2),
            (Position::new(3, 0), 3),
            (Position::new(4, 0), 40),
            (Position::new(5, 0), 50),
            (Position::new(6, 0), 60),
        ];
        assert_eq!(driver.engine().fold().applied, expected);
    }

    /// Fold a fresh driver computes over `chain`, the reference for a raced driver.
    fn canonical_fold(chain: ScriptedChain) -> Vec<(Position, u64)> {
        let mut driver = new_driver(chain, engine_config(2), DriverConfig::from_block(1));
        run_to_idle(&mut driver);
        driver.engine().fold().applied.clone()
    }

    fn adversary_driver(chain: ScriptedChain) -> Driver<RecordingFold, Adversary> {
        Driver::new(
            RecordingFold::default(),
            Adversary::new(chain),
            engine_config(2),
            DriverConfig {
                checkpoint_interval: Some(1),
                ..DriverConfig::from_block(1)
            },
        )
        .unwrap()
    }

    #[test]
    fn reorg_below_the_cursor_inside_one_scan_is_detected() {
        // given a driver caught up on five blocks
        let mut driver = adversary_driver(one_event_chain(5));
        run_to_idle(&mut driver);
        // when blocks 3..=5 are replaced after the scan starts but before it reads events
        driver.source_mut().on_head = Some((3, vec![30, 40, 50, 60, 70]));
        let outcome = driver.tick();
        run_to_idle(&mut driver);
        // then the tick recovers instead of folding the new chain onto the old one
        assert!(
            matches!(outcome, Tick::RolledBack { .. } | Tick::Resynced),
            "got {outcome:?}"
        );
        let chain = driver.source_mut().inner.clone();
        assert_eq!(driver.engine().fold().applied, canonical_fold(chain));
    }

    #[test]
    fn reorg_above_the_cursor_after_the_events_read_is_caught_next_tick() {
        // given a driver caught up on five blocks, and two more blocks on the chain
        let mut driver = adversary_driver(one_event_chain(5));
        run_to_idle(&mut driver);
        driver.source_mut().inner.push_block(&[6]);
        driver.source_mut().inner.set_window(2);
        driver.source_mut().inner.push_block(&[7]);
        // when blocks 6 and 7 are replaced between the events read and the boundary fetch
        driver.source_mut().events_served = false;
        driver.source_mut().after_events = Some((2, vec![600, 700]));
        let stale = driver.tick();
        let next = driver.tick();
        run_to_idle(&mut driver);
        // then the stale blocks fold, the next boundary check catches them, and the
        // fold converges on the canonical chain
        assert!(matches!(stale, Tick::Progressed(_)), "got {stale:?}");
        assert!(
            matches!(next, Tick::RolledBack { .. } | Tick::Resynced),
            "got {next:?}"
        );
        let chain = driver.source_mut().inner.clone();
        assert_eq!(driver.engine().fold().applied, canonical_fold(chain));
    }

    #[test]
    fn two_hashes_at_one_height_are_a_source_error() {
        // given a driver caught up on five blocks, and a sixth served under two hashes
        let mut driver = adversary_driver(one_event_chain(5));
        run_to_idle(&mut driver);
        driver.source_mut().inner.push_block(&[6]);
        let rogue = BlockRef {
            number: 6,
            hash: [0xAA; 32],
        };
        driver.source_mut().rogue = Some((rogue, 1, 66));
        let before = driver.engine().fold().clone();
        // when polled
        let outcome = driver.tick();
        // then the batch is refused as a source fault and the fold is untouched
        assert_eq!(outcome, Tick::SourceError);
        assert_eq!(driver.engine().fold(), &before);
        assert_eq!(driver.engine().cursor(), Some(Position::new(5, 0)));
    }

    #[test]
    fn scan_returns_when_head_is_u64_max() {
        // given a chain whose only block, number u64::MAX, carries no events
        let mut driver = Driver::new(
            RecordingFold::default(),
            Summit {
                event: None,
                queries: 0,
            },
            engine_config(2),
            DriverConfig::from_block(u64::MAX),
        )
        .unwrap();
        // when polled
        let outcome = driver.tick();
        // then the scan reads the one window and stops
        assert_eq!(outcome, Tick::Idle);
        assert_eq!(driver.source_mut().queries, 1);
    }

    #[test]
    fn scan_past_a_cursor_at_u64_max_is_idle() {
        // given a driver that has folded the one event of block u64::MAX
        let mut driver = Driver::new(
            RecordingFold::default(),
            Summit {
                event: Some(1),
                queries: 0,
            },
            engine_config(2),
            DriverConfig::from_block(u64::MAX),
        )
        .unwrap();
        assert!(matches!(driver.tick(), Tick::Progressed(_)));
        // when polled again
        let outcome = driver.tick();
        // then nothing lies above the cursor, and the boundary still verifies
        assert_eq!(outcome, Tick::Idle);
        assert_eq!(driver.engine().cursor(), Some(Position::new(u64::MAX, 0)));
    }

    #[test]
    fn rollback_lowers_the_checkpoint_cadence_mark() {
        // given twenty blocks checkpointed every 4 from block 1: slots at 1, 5, 9, 13, 17
        let mut driver = new_driver(
            one_event_chain(20),
            EngineConfig {
                ring_capacity: 64,
                checkpoint_slots: 16,
            },
            DriverConfig {
                checkpoint_interval: Some(4),
                snapshot_interval: None,
                ..DriverConfig::from_block(1)
            },
        );
        run_to_idle(&mut driver);
        assert_eq!(driver.engine().checkpoint_count(), 5);
        // when blocks 15..=20 are replaced by 15..=24, rolling back to the slot at 13
        let replacements: Vec<u64> = (1000..1010).collect();
        reorg_to(driver.source_mut(), 6, &replacements);
        let outcome = driver.tick();
        run_to_idle(&mut driver);
        // then the refold checkpoints at 17' and 21', four and eight blocks past 13
        assert_eq!(
            outcome,
            Tick::RolledBack {
                to: Some(Position::new(13, 0)),
            }
        );
        assert_eq!(driver.engine().checkpoint_count(), 6);
        let restored = driver.engine_mut().rollback_at_or_below(18).unwrap();
        assert_eq!(restored, Some(Position::new(17, 0)));
    }
}

#[cfg(verus_keep_ghost)]
verus! {

pub open spec fn clamp_spec(mark: Option<u64>, to: Option<Position>) -> Option<u64> {
    match (mark, to) {
        (Some(m), Some(t)) => Some(if m <= t.block { m } else { t.block }),
        _ => None,
    }
}

/// T6b floor: every offered point is at or below the cursor and every live slot's cursor.
pub open spec fn floor_ok(off: Set<Position>, e: EngineView) -> bool {
    forall|p: Position|
        #[trigger] off.contains(p) ==> opt_le(Some(p), e.cursor) && forall|k: int|
            #[trigger] e.live_at(k) ==> opt_le(Some(p), e.slots[k].unwrap().cursor)
}

/// `resync`'s post-state: a fresh engine on `initial`, a reset sink, cleared marks.
spec fn resynced<F: Fold, S: Source<Event = F::Event>, K: SnapshotSink<F>>(
    pre: Driver<F, S, K>,
    post: Driver<F, S, K>,
) -> bool {
    &&& post == Driver {
        engine: post.engine,
        sink: post.sink,
        caught_up: false,
        consecutive_errors: 0,
        seen_resets: post.engine@.resets,
        last_checkpoint_block: None,
        last_snapshot_block: None,
        ..pre
    }
    &&& post.engine@.fold == fview::<F>(&pre.initial)
    &&& post.engine@.cursor is None
    &&& post.engine@.ring.len() == 0
    &&& post.engine@.status is Active
    &&& post.engine@.inv::<F, F::Event, F::Error>(fview::<F>(&pre.initial), Seq::empty())
    &&& sink_offered::<K>(&post.sink) == Set::<Position>::empty()
}

/// `roll_back_to`'s Ok arm: T5b/T5c/T5d restated for the driver, plus the marks clamped
/// to the restore point `to`.
spec fn rolled_back<F: Fold, S: Source<Event = F::Event>, K: SnapshotSink<F>>(
    pre: Driver<F, S, K>,
    post: Driver<F, S, K>,
    ancestor: u64,
    to: Option<Position>,
) -> bool {
    let (e, f) = (pre.engine@, post.engine@);
    &&& post == Driver {
        engine: post.engine,
        caught_up: false,
        last_checkpoint_block: clamp_spec(pre.last_checkpoint_block, to),
        last_snapshot_block: clamp_spec(pre.last_snapshot_block, to),
        ..pre
    }
    &&& exists|k: int| #[trigger] e.rollback_target(ancestor, k) && to == e.slots[k].unwrap().cursor
    &&& f.cursor == to
    &&& f.ring == e.ring.subrange(0, f.ring.len() as int)
    &&& to is None ==> f.ring.len() == 0
    &&& to matches Some(c) ==> prefix_at_or_below(e.ring, c.block, f.ring.len() as int)
    &&& f.status is Active
    &&& f.resets == e.resets
    &&& forall|init: int, log: Seq<(Position, F::Event)>|
        #[trigger] e.inv::<F, F::Event, F::Error>(init, log) ==> f.inv::<F, F::Event, F::Error>(init, upto::<F::Event>(log, to))
}

pub open spec fn due_spec(last: Option<u64>, block: u64, interval: u64) -> bool {
    match last {
        Some(l) => block >= l.saturating_add(interval),
        None => true,
    }
}

/// `Engine::checkpoint`'s view change: the current state becomes the newest slot.
pub open spec fn checkpointed(pre: EngineView) -> EngineView {
    if pre.status is Active && pre.slots.len() > 0 {
        EngineView {
            slots: pre.slots.drop_first().push(Some(SlotView { fold: pre.fold, cursor: pre.cursor })),
            ..pre
        }
    } else {
        pre
    }
}

/// `scan`'s first block: one past the cursor (None at `u64::MAX`), else the start block.
pub open spec fn scan_first(cursor: Option<Position>, start: u64) -> Option<u64> {
    match cursor {
        Some(c) => if c.block < u64::MAX {
            Some((c.block + 1) as u64)
        } else {
            None
        },
        None => Some(start),
    }
}

/// Windows of `w` blocks from `first`, each starting one past the last, the last cut at
/// head `h`.
pub open spec fn scan_windows(wins: Seq<(int, int)>, first: int, w: u64, h: u64) -> bool {
    &&& wins.len() > 0 ==> wins[0].0 == first
    &&& forall|i: int|
        0 <= i < wins.len() ==> (#[trigger] wins[i]).0 <= h && wins[i].1 == if wins[i].0 + w - 1 < h {
            wins[i].0 + w - 1
        } else {
            h as int
        }
    // Adjacent pairs, so the trigger does not chain (cookbook section 2).
    &&& forall|i: int, j: int|
        #![trigger wins[i], wins[j]]
        0 <= i && j == i + 1 && j < wins.len() ==> wins[j].0 == wins[i].1 + 1
}

/// `scan`'s Ok result over the source log `hist` from `l0`: the head call's view, one view
/// per window, then the boundary view last (B1). Windows before the last are empty; the
/// batch holds the last window's entries, or it is empty and the windows cover `[first, h]`.
pub open spec fn scanned<S, E>(
    hist: Seq<ChainView>,
    l0: int,
    first: Option<u64>,
    h: u64,
    w: u64,
    wins: Seq<(int, int)>,
    cursor: Option<Position>,
    b: BatchView<E>,
) -> bool {
    &&& windows_ok::<S, E>(hist, l0, first, h, w, wins, b.triples())
    &&& hist.len() == l0 + 1 + wins.len() + if cursor is Some {
        1int
    } else {
        0int
    }
    &&& b.boundary == match cursor {
        Some(c) => header(hist[hist.len() - 1], c.block),
        None => None,
    }
}

/// `scan`'s windows over `hist` from `l0` and the entries `t` the batch took from them.
pub open spec fn windows_ok<S, E>(
    hist: Seq<ChainView>,
    l0: int,
    first: Option<u64>,
    h: u64,
    w: u64,
    wins: Seq<(int, int)>,
    t: Seq<(BlockRef, u32, E)>,
) -> bool {
    let m = wins.len() as int;
    &&& w >= 1
    &&& l0 + 1 + m <= hist.len()
    &&& first is None ==> m == 0
    &&& first matches Some(f) ==> scan_windows(wins, f as int, w, h)
    &&& forall|i: int|
        0 <= i < m - 1 ==> range_entries::<S, E>(hist[l0 + 1 + i], #[trigger] wins[i].0, wins[i].1).len() == 0
    &&& m > 0 ==> t.to_multiset() == range_entries::<S, E>(
        hist[l0 + m],
        wins[m - 1].0,
        wins[m - 1].1,
    ).to_multiset()
    &&& m == 0 ==> t.len() == 0
    &&& t.len() == 0 ==> match first {
        None => true,
        Some(f) => if m == 0 {
            f > h
        } else {
            wins[m - 1].1 == h
        },
    }
}

/// The batch's entries do not read its boundary.
proof fn lemma_triples_ignore_boundary<E>(a: BatchView<E>, b: BatchView<E>, n: int)
    requires
        a == (BatchView { boundary: a.boundary, ..b }),
    ensures
        a.triples_upto(n) == b.triples_upto(n),
    decreases n,
{
    if n > 0 {
        lemma_triples_ignore_boundary(a, b, n - 1);
        assert(a.span_triples(n - 1) =~= b.span_triples(n - 1));
    }
}

/// Construction refused: the source horizon is above the start block.
pub open spec fn horizon_refused(e: ConfigError, start_block: u64) -> bool {
    e matches ConfigError::HorizonExceedsStart { start, horizon } && start == start_block && horizon > start
}

/// `offer_snapshot`'s trigger: not latched, an interval is set, there is a durable point,
/// and it is due.
spec fn snapshot_due<F: Fold, S: Source<Event = F::Event>, K: SnapshotSink<F>>(d: Driver<F, S, K>) -> bool {
    &&& !d.durability_lost
    &&& match (d.config.snapshot_interval, d.engine@.durable_point()) {
        (Some(i), Some(p)) => due_spec(d.last_snapshot_block, p.block, i),
        _ => false,
    }
}

/// `auto_checkpoint`'s trigger: an interval is set, there is a cursor, and it is due.
spec fn checkpoint_due<F: Fold, S: Source<Event = F::Event>, K: SnapshotSink<F>>(d: Driver<F, S, K>) -> bool {
    match (d.config.checkpoint_interval, d.engine@.cursor) {
        (Some(i), Some(c)) => due_spec(d.last_checkpoint_block, c.block, i),
        _ => false,
    }
}

/// `run_checkpoint`'s post-state: the engine checkpointed, the mark at the cursor block.
spec fn checkpoint_ran<F: Fold, S: Source<Event = F::Event>, K: SnapshotSink<F>>(
    pre: Driver<F, S, K>,
    post: Driver<F, S, K>,
) -> bool {
    &&& post == Driver {
        engine: post.engine,
        last_checkpoint_block: match post.engine@.cursor {
            Some(c) => Some(c.block),
            None => pre.last_checkpoint_block,
        },
        ..pre
    }
    &&& post.engine@ == checkpointed(pre.engine@)
    &&& forall|init: int, log: Seq<(Position, F::Event)>|
        #[trigger] pre.engine@.inv::<F, F::Event, F::Error>(init, log) ==> post.engine@.inv::<F, F::Event, F::Error>(init, log)
    &&& forall|a: Seq<Option<BlockRef>>|
        #[trigger] pre.engine@.anchored(a) ==> post.engine@.anchored(pre.engine@.stored_anchors(a))
}

/// T4c: view `v` confirmed `ring[lo - 1]`, so under `ring_chain` it holds `ring[..lo]`.
pub open spec fn probe_held(ring: Seq<BlockRef>, lo: int, v: ChainView) -> bool {
    &&& confirms(v, ring[lo - 1])
    &&& ring_chain(ring) ==> forall|i: int|
        0 <= i < lo && v.contains_key(#[trigger] ring[i].number) ==> v[ring[i].number] == ring[i]
    &&& ring_chain(ring) && down_closed(v) ==> forall|i: int| 0 <= i < lo ==> confirms(v, #[trigger] ring[i])
}

/// The ladder below "no qualifying slot": resync iff the horizon `h` covers the start
/// block, else `Unrecoverable { HorizonExceeded }` naming `h`.
pub open spec fn ladder_tail(start: u64, h: ReplayHorizon, r: Tick) -> bool {
    match h {
        ReplayHorizon::FromBlock(hb) => if hb > start {
            r == Tick::Terminal(
                EngineStatus::Unrecoverable {
                    cause: DivergenceCause::HorizonExceeded { needed: start, horizon: hb },
                },
            )
        } else {
            r == Tick::Resynced
        },
        ReplayHorizon::Genesis => r == Tick::Resynced,
    }
}

/// `reconcile_reset` took the slow path: the sink was reset and the marks cleared.
spec fn reconciled<F: Fold, S: Source<Event = F::Event>, K: SnapshotSink<F>>(
    pre: Driver<F, S, K>,
    post: Driver<F, S, K>,
) -> bool {
    &&& post == Driver {
        seen_resets: pre.engine@.resets,
        sink: post.sink,
        last_checkpoint_block: None,
        last_snapshot_block: None,
        ..pre
    }
    &&& sink_offered::<K>(&post.sink) == Set::<Position>::empty()
}

impl<F: Fold, S: Source<Event = F::Event>, K: SnapshotSink<F>> Driver<F, S, K> {
    pub closed spec fn wf(&self) -> bool {
        self.engine.wf() && self.batch@.wf()
    }

    pub closed spec fn engine_view(&self) -> EngineView {
        self.engine@
    }

    /// The driver has seen every engine reset.
    pub closed spec fn synced(&self) -> bool {
        self.seen_resets == self.engine@.resets
    }

    /// T6b, threaded through every method: while synced, the sink offered nothing past
    /// the engine's cursor or any live slot.
    pub closed spec fn durable_ok(&self) -> bool {
        self.synced() ==> floor_ok(sink_offered::<K>(&self.sink), self.engine@)
    }
}

/// Spans below the pushed one keep their entries.
proof fn lemma_triples_upto_kept<E>(pre: BatchView<E>, post: BatchView<E>, block: BlockRef, m: int)
    requires
        pre.wf(),
        pushed_block(pre, post, block),
        0 <= m <= pre.ends.len(),
    ensures
        post.triples_upto(m) == pre.triples_upto(m),
    decreases m,
{
    if m > 0 {
        lemma_triples_upto_kept(pre, post, block, m - 1);
        let i = m - 1;
        let len = pre.events.len() as int;
        assert(pre.ends[i] <= len) by {
            if i < pre.ends.len() - 1 {
                assert(pre.ends[i] <= pre.ends[pre.ends.len() - 1]);
            }
        }
        assert(post.ends[i] == pre.ends[i]);
        if i > 0 {
            assert(post.ends[i - 1] == pre.ends[i - 1]);
        }
        assert forall|x: int| 0 <= x < len implies post.log_indices[x] == pre.log_indices[x]
            && post.events[x] == pre.events[x] by {
            assert(post.log_indices.subrange(0, len)[x] == post.log_indices[x]);
            assert(post.events.subrange(0, len)[x] == post.events[x]);
        }
        assert(post.span_triples(i) =~= pre.span_triples(i));
    }
}

/// One `push_block_from_tail` appends the popped entries, last first, to `triples()`.
proof fn lemma_push_triples<E>(
    pre: BatchView<E>,
    post: BatchView<E>,
    before: Seq<(BlockRef, u32, E)>,
    after: Seq<(BlockRef, u32, E)>,
    block: BlockRef,
)
    requires
        pre.wf(),
        pushed_block(pre, post, block),
        popped_tail(pre, post, before, after, block),
    ensures
        post.triples().len() == pre.triples().len() + (before.len() - after.len()),
        forall|j: int| 0 <= j < pre.triples().len() ==> #[trigger] post.triples()[j] == pre.triples()[j],
        forall|j: int|
            0 <= j < before.len() - after.len() ==> #[trigger] post.triples()[pre.triples().len() + j]
                == before[before.len() - 1 - j],
{
    let n = pre.ends.len() as int;
    lemma_triples_upto_kept(pre, post, block, n);
    assert(post.triples() == post.triples_upto(n) + post.span_triples(n));
    let start = post.start(n);
    assert(start == pre.events.len()) by {
        if n > 0 {
            assert(post.ends[n - 1] == pre.ends[n - 1]);
        }
    }
    assert(pre.triples().len() == pre.events.len()) by {
        lemma_triples_len(pre, n);
    }
    let m = before.len() - after.len();
    assert forall|j: int| 0 <= j < m implies #[trigger] post.span_triples(n)[j] == before[before.len() - 1 - j] by {
        assert(appended_at(pre, post, before, j, block));
    }
}

/// `triples_upto(m)` has `start(m)` entries.
proof fn lemma_triples_len<E>(b: BatchView<E>, m: int)
    requires
        b.wf(),
        0 <= m <= b.ends.len(),
    ensures
        b.triples_upto(m).len() == b.start(m),
    decreases m,
{
    if m > 0 {
        lemma_triples_len(b, m - 1);
        if m >= 2 {
            assert(b.ends[m - 2] <= b.ends[m - 1]);
        }
    }
}

} // verus!
