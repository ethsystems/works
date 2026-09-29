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
    crate::verus::model::*,
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
            r matches Ok(d) ==> d.dinv(Seq::empty(), Map::empty()),
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
        let r = Self::build(fold, source, NoSink, engine, config);
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Ok(d) = &r {
                d.engine.lemma_wf();
                lemma_fresh_dinv::<F, S, F::Event, F::Error>(d.engine@, fview::<F>(&d.initial), d.config.start_block);
            }
        }
        r
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
            r matches Ok(d) ==> d.dinv(Seq::empty(), Map::empty()),
            r matches Err(e) ==> !engine.valid() || horizon_refused(e, config.start_block),
    ))]
    pub fn with_sink(
        fold: F,
        source: S,
        sink: K,
        engine: EngineConfig,
        config: DriverConfig,
    ) -> Result<Self, ConfigError> {
        let r = Self::build(fold, source, sink, engine, config);
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Ok(d) = &r {
                d.engine.lemma_wf();
                lemma_fresh_dinv::<F, S, F::Event, F::Error>(d.engine@, fview::<F>(&d.initial), d.config.start_block);
            }
        }
        r
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
                // `durable_ok` holds when the sink was reset, else when it offered
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
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).synced(),
            old(self).durable_ok() ==> final(self).durable_ok(),
            final(self).init_view() == old(self).init_view(),
            final(self).start_block() == old(self).start_block(),
            forall|init: int, log: Seq<(Position, F::Event)>|
                #[trigger] old(self).engine_view().inv::<F, F::Event, F::Error>(init, log)
                    ==> tick_inv(*old(self), *final(self), r, init, log),
            forall|log: Seq<(Position, F::Event)>, h: ChainView|
                #[trigger] old(self).dinv(log, h) ==> t7_tick(*old(self), *final(self), r, log, h),
    ))]
    fn step(&mut self) -> Tick {
        self.reconcile_reset();
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost mid = *self;
        }
        let tick = self.poll_apply();
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost pa = *self;
        }
        // Only forward cursor movement earns an immediate re-poll; a batch the
        // engine fully deduped leaves the loop on its poll interval.
        self.advanced = matches!(
            tick,
            Tick::Progressed(summary) if summary.applied > 0 || summary.skipped > 0
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(mid.engine_view() == old(self).engine_view());
            assert(mid.source_log() == old(self).source_log());
            assert(pa.engine_view() == self.engine_view() && pa.source_log() == self.source_log()
                && pa.batch_view() == self.batch_view() && pa.init_view() == self.init_view());
            assert forall|log: Seq<(Position, F::Event)>, h: ChainView|
                #[trigger] old(self).dinv(log, h) implies t7_tick(*old(self), *self, tick, log, h) by {
                assert(mid.dinv(log, h));
                assert(t7_tick(mid, pa, tick, log, h));
                if exists|log2: Seq<(Position, F::Event)>, h2: ChainView| #[trigger] pa.dinv(log2, h2) {
                    let (log2, h2) = choose|log2: Seq<(Position, F::Event)>, h2: ChainView| #[trigger] pa.dinv(log2, h2);
                    assert(self.dinv(log2, h2));
                }
            }
        }
        tick
    }

    /// Scans the source and applies the batch, recovering from a fork by bisection.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
            old(self).synced(),
        ensures
            final(self).wf(),
            final(self).synced(),
            old(self).durable_ok() ==> final(self).durable_ok(),
            final(self).init_view() == old(self).init_view(),
            final(self).start_block() == old(self).start_block(),
            forall|init: int, log: Seq<(Position, F::Event)>|
                #[trigger] old(self).engine_view().inv::<F, F::Event, F::Error>(init, log)
                    ==> tick_inv(*old(self), *final(self), r, init, log),
            forall|log: Seq<(Position, F::Event)>, h: ChainView|
                #[trigger] old(self).dinv(log, h) ==> t7_tick(*old(self), *final(self), r, log, h),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verifier::rlimit(20))]
    fn poll_apply(&mut self) -> Tick {
        self.generation = self.generation.wrapping_add(1);
        if !self.engine.status().is_active() {
            let tick = Tick::Terminal(self.engine.status());
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(calls::<F, F::Event, F::Error>(self.engine@, self.batch@) =~= Seq::empty());
                assert forall|init: int, log: Seq<(Position, F::Event)>|
                    #[trigger] old(self).engine_view().inv::<F, F::Event, F::Error>(init, log)
                        implies tick_inv(*old(self), *self, tick, init, log) by {
                    assert(log + Seq::<(Position, F::Event)>::empty() =~= log);
                }
                assert forall|log: Seq<(Position, F::Event)>, h: ChainView|
                    #[trigger] old(self).dinv(log, h) implies t7_tick(*old(self), *self, tick, log, h) by {
                    assert(self.dinv(log, h));
                }
            }
            return tick;
        }
        if self.scan().is_err() {
            self.consecutive_errors = self.consecutive_errors.saturating_add(1);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|log: Seq<(Position, F::Event)>, h: ChainView|
                    #[trigger] old(self).dinv(log, h) implies t7_tick(*old(self), *self, Tick::SourceError, log, h) by {
                    assert(self.dinv(log, h));
                }
            }
            return Tick::SourceError;
        }
        self.consecutive_errors = 0;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost v = self.engine@;
            let ghost bv = self.batch@;
            let ghost w = self.engine.window();
            let ghost off = sink_offered::<K>(&self.sink);
            let ghost (l0, hist) = (sview_log::<S>(&old(self).source).len() as int, sview_log::<S>(&self.source));
            let ghost start = self.config.start_block;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            self.engine.lemma_wf();
        }
        let applied = self.engine.apply_batch(&self.batch);
        #[cfg(verus_keep_ghost)]
        proof! {
            self.engine.lemma_wf();
            if old(self).durable_ok() && self.synced() {
                lemma_apply_floor::<F, F::Event, F::Error>(v, self.engine@, bv, w, off);
            }
        }
        match applied {
            Ok(summary) => {
                #[cfg(verus_keep_ghost)]
                proof_decl! {
                    let ghost post = self.engine@;
                }
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(accepted(v, bv) && !stopped::<F, F::Event, F::Error>(v, bv));
                    let cl = calls::<F, F::Event, F::Error>(v, bv);
                    assert forall|log: Seq<(Position, F::Event)>, h: ChainView|
                        #[trigger] old(self).dinv(log, h) && a2_hyp::<S, F::Event>(hist, l0, v.cursor, start, bv, post.cursor)
                            implies dinv::<F, S, F::Event, F::Error>(
                        post,
                        fview::<F>(&self.initial),
                        start,
                        log + cl,
                        if bv.ends.len() > 0 { t7_view(hist, v.cursor, bv) } else { h },
                    ) && t7_state::<F, S, F::Event, F::Error>(
                        post,
                        fview::<F>(&self.initial),
                        start,
                        t7_view(hist, v.cursor, bv),
                    ) by {
                        let (hw, ww, wins) = choose|hw: u64, ww: u64, wins: Seq<(int, int)>|
                            #[trigger] scanned::<S, F::Event>(hist, l0, scan_first(v.cursor, start), hw, ww, wins, v.cursor, bv);
                        lemma_apply_t7::<F, S, F::Event, F::Error>(
                            v, post, bv, w, fview::<F>(&self.initial), start, log, h, hist, l0, hw, ww, wins,
                        );
                    }
                }
                self.caught_up = self.batch.is_empty();
                // A snapshot refusal overrides progress; a checkpoint is silent.
                self.auto_checkpoint();
                #[cfg(verus_keep_ghost)]
                proof! {
                    let cl = calls::<F, F::Event, F::Error>(v, bv);
                    if self.engine@ != post {
                        assert forall|log: Seq<(Position, F::Event)>, h: ChainView|
                            dinv::<F, S, F::Event, F::Error>(post, fview::<F>(&self.initial), start, log, h)
                                implies #[trigger] dinv::<F, S, F::Event, F::Error>(
                                self.engine@,
                                fview::<F>(&self.initial),
                                start,
                                log,
                                h,
                            ) by {
                            lemma_checkpoint_dinv::<F, S, F::Event, F::Error>(post, fview::<F>(&self.initial), start, log, h);
                        }
                    }
                }
                if let Some(tick) = self.offer_snapshot() {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        let cl = calls::<F, F::Event, F::Error>(v, bv);
                        assert(self.engine@.fold == post.fold && self.engine@.cursor == post.cursor && self.engine@.ring == post.ring);
                        assert forall|init: int, log: Seq<(Position, F::Event)>|
                            #[trigger] old(self).engine_view().inv::<F, F::Event, F::Error>(init, log)
                                implies tick_inv(*old(self), *self, tick, init, log) by {}
                        assert forall|log: Seq<(Position, F::Event)>, h: ChainView|
                            #[trigger] old(self).dinv(log, h) implies t7_tick(*old(self), *self, tick, log, h) by {
                            if a2_hyp::<S, F::Event>(hist, l0, v.cursor, start, bv, post.cursor) {
                                let h2 = if bv.ends.len() > 0 { t7_view(hist, v.cursor, bv) } else { h };
                                assert(dinv::<F, S, F::Event, F::Error>(post, fview::<F>(&self.initial), start, log + cl, h2));
                                assert(self.dinv(log + cl, h2));
                            }
                        }
                    }
                    return tick;
                }
                let tick = if self.batch.is_empty() {
                    Tick::Idle
                } else {
                    Tick::Progressed(summary)
                };
                #[cfg(verus_keep_ghost)]
                proof! {
                    let cl = calls::<F, F::Event, F::Error>(v, bv);
                    assert(self.engine@.fold == post.fold && self.engine@.cursor == post.cursor && self.engine@.ring == post.ring);
                    assert forall|init: int, log: Seq<(Position, F::Event)>|
                        #[trigger] old(self).engine_view().inv::<F, F::Event, F::Error>(init, log)
                            implies tick_inv(*old(self), *self, tick, init, log) by {}
                    assert forall|log: Seq<(Position, F::Event)>, h: ChainView|
                        #[trigger] old(self).dinv(log, h) implies t7_tick(*old(self), *self, tick, log, h) by {
                        if a2_hyp::<S, F::Event>(hist, l0, v.cursor, start, bv, post.cursor) {
                            let h2 = if bv.ends.len() > 0 { t7_view(hist, v.cursor, bv) } else { h };
                            assert(dinv::<F, S, F::Event, F::Error>(post, fview::<F>(&self.initial), start, log + cl, h2));
                            assert(self.dinv(log + cl, h2));
                        }
                    }
                }
                tick
            }
            Err(
                ApplyError::ForkSuspected { .. }
                | ApplyError::MissingBoundary
                | ApplyError::CursorBlockUnobserved { .. },
            ) => {
                #[cfg(verus_keep_ghost)]
                proof_decl! {
                    let ghost pre = *self;
                }
                let tick = self.recover_via_bisection();
                #[cfg(verus_keep_ghost)]
                proof! {
                    lemma_recover_t7(*old(self), pre, *self, tick);
                }
                tick
            }
            Err(ApplyError::Halted { .. } | ApplyError::Poisoned { .. }) => {
                let tick = Tick::Terminal(self.engine.status());
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(!(self.engine@.status is Active));
                    assert forall|log: Seq<(Position, F::Event)>, h: ChainView|
                        #[trigger] old(self).dinv(log, h) implies t7_tick(*old(self), *self, tick, log, h) by {
                        assert(self.dinv(log + calls::<F, F::Event, F::Error>(v, bv), h));
                    }
                }
                tick
            }
            Err(ApplyError::Shape(_) | ApplyError::BoundaryNumberMismatch { .. }) => {
                self.consecutive_errors = self.consecutive_errors.saturating_add(1);
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert forall|log: Seq<(Position, F::Event)>, h: ChainView|
                        #[trigger] old(self).dinv(log, h) implies t7_tick(*old(self), *self, Tick::SourceError, log, h) by {
                        assert(self.dinv(log, h));
                    }
                }
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
    // The boundary is read after every window, so its view is the last log entry.
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
    // A RolledBack restore sits at or below a ring block some probe's view confirmed.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
            old(self).synced(),
        ensures
            recovered(*old(self), *final(self), r),
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
    // Under `t7_tick`'s hypotheses, `dinv` carries over and an Active
    // Progressed/Idle tick leaves the fold at the canonical logs of the tick's view.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).synced(),
            old(self).durable_ok() ==> final(self).durable_ok(),
            final(self).init_view() == old(self).init_view(),
            final(self).start_block() == old(self).start_block(),
            forall|init: int, log: Seq<(Position, F::Event)>|
                #[trigger] old(self).engine_view().inv::<F, F::Event, F::Error>(init, log)
                    ==> tick_inv(*old(self), *final(self), r, init, log),
            forall|log: Seq<(Position, F::Event)>, h: ChainView|
                #[trigger] old(self).dinv(log, h) ==> t7_tick(*old(self), *final(self), r, log, h),
    ))]
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
            forall|log: Seq<(Position, F::Event)>, h: ChainView|
                #[trigger] old(self).dinv(log, h) ==> final(self).dinv(log, h),
    ))]
    pub fn checkpoint(&mut self) {
        self.run_checkpoint();
        #[cfg(verus_keep_ghost)]
        proof! {
            old(self).engine.lemma_wf();
            assert forall|log: Seq<(Position, F::Event)>, h: ChainView|
                #[trigger] old(self).dinv(log, h) implies self.dinv(log, h) by {
                lemma_checkpoint_dinv::<F, S, F::Event, F::Error>(
                    old(self).engine@,
                    fview::<F>(&self.initial),
                    self.config.start_block,
                    log,
                    h,
                );
            }
        }
    }

    /// Snapshots the current driver and engine state.
    // The reported durable cursor never leads the cursor.
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

/// Every offered point is at or below the cursor and every live slot's cursor.
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

/// `recover_via_bisection`'s post-state: a restore below a confirmed ring block for
/// RolledBack, the ladder otherwise.
spec fn recovered<F: Fold, S: Source<Event = F::Event>, K: SnapshotSink<F>>(
    pre: Driver<F, S, K>,
    post: Driver<F, S, K>,
    r: Tick,
) -> bool {
    let (from, hist) = (
        sview_log::<S>(&pre.source).len() as int,
        sview_log::<S>(&post.source),
    );
    let mid = Driver { source: post.source, ..pre };
    let ring = pre.engine@.ring;
    &&& post.wf()
    &&& post.synced()
    &&& pre.durable_ok() ==> post.durable_ok()
    &&& from <= hist.len()
    &&& hist.subrange(0, from) == sview_log::<S>(&pre.source)
    &&& forall|k: int| from <= k < hist.len() ==> a1::<S, S::Event>(#[trigger] hist[k])
    &&& r matches Tick::RolledBack { to } ==> exists|lo: int, k: int|
        0 < lo <= ring.len() && from <= k < hist.len() && #[trigger] probe_held(ring, lo, hist[k])
            && rolled_back(mid, post, ring[lo - 1].number, to)
    &&& r is Resynced ==> resynced(mid, post)
    &&& r is Terminal ==> post == (Driver { engine: post.engine, ..mid })
        && post.engine@ == (EngineView { status: post.engine@.status, ..pre.engine@ })
    &&& r is SourceError ==> post == (Driver {
        consecutive_errors: if pre.consecutive_errors < u32::MAX {
            (pre.consecutive_errors + 1) as u32
        } else {
            u32::MAX
        },
        ..mid
    })
    &&& r is RolledBack || r is Resynced || r is Terminal || r is SourceError
}

/// `roll_back_to`'s Ok arm: the engine rollback's target, post-state and `Inv`
/// restated for the driver, plus the marks clamped to the restore point `to`.
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
    &&& f.slots.len() == e.slots.len()
    &&& forall|j: int| 0 <= j < f.slots.len() && #[trigger] f.slots[j] is Some ==> f.slots[j] == e.slots[j]
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
    // Adjacent pairs, so the trigger does not chain.
    &&& forall|i: int, j: int|
        #![trigger wins[i], wins[j]]
        0 <= i && j == i + 1 && j < wins.len() ==> wins[j].0 == wins[i].1 + 1
}

/// `scan`'s Ok result over the source log `hist` from `l0`: the head call's view, one view
/// per window, then the boundary view last. Windows before the last are empty; the
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

/// View `v` confirmed `ring[lo - 1]`, so under `ring_chain` it holds `ring[..lo]`.
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

    /// Kept by every method: while synced, the sink offered nothing past
    /// the engine's cursor or any live slot.
    pub closed spec fn durable_ok(&self) -> bool {
        self.synced() ==> floor_ok(sink_offered::<K>(&self.sink), self.engine@)
    }
}

impl<F: Fold, S: Source<Event = F::Event>, K: SnapshotSink<F>> Driver<F, S, K> {
    /// View of the fold `resync` restarts from (`dinv`'s `init`).
    pub closed spec fn init_view(&self) -> int {
        fview::<F>(&self.initial)
    }

    pub closed spec fn start_block(&self) -> u64 {
        self.config.start_block
    }

    /// The views that answered the source so far.
    pub closed spec fn source_log(&self) -> Seq<ChainView> {
        sview_log::<S>(&self.source)
    }

    pub closed spec fn batch_view(&self) -> BatchView<F::Event> {
        self.batch@
    }

    /// Ghost invariant over log `log` and chain view `h` (`dinv`).
    pub closed spec fn dinv(&self, log: Seq<(Position, F::Event)>, h: ChainView) -> bool {
        dinv::<F, S, F::Event, F::Error>(self.engine@, self.init_view(), self.start_block(), log, h)
    }
}

/// `Inv` threading through one tick: the log grows by the applied calls, is cut at a
/// rollback target, restarts empty at a resync, and stays on a source error.
pub open spec fn tick_inv<F: Fold, S: Source<Event = F::Event>, K: SnapshotSink<F>>(
    pre: Driver<F, S, K>,
    post: Driver<F, S, K>,
    r: Tick,
    init: int,
    log: Seq<(Position, F::Event)>,
) -> bool {
    let f = post.engine_view();
    match r {
        Tick::RolledBack { to } => f.inv::<F, F::Event, F::Error>(init, upto(log, to)),
        Tick::Resynced => f.inv::<F, F::Event, F::Error>(post.init_view(), Seq::empty()),
        Tick::SourceError => f.inv::<F, F::Event, F::Error>(init, log),
        _ => f.inv::<F, F::Event, F::Error>(
            init,
            log + calls::<F, F::Event, F::Error>(pre.engine_view(), post.batch_view()),
        ),
    }
}

/// `t7_tick`'s hypotheses for a tick that applied batch `b` built by a scan over `hist`
/// from `l0`: `a2_scan` for its windows, and its view holds `[start, c2.block]` for the
/// new cursor.
pub open spec fn a2_hyp<S, E>(
    hist: Seq<ChainView>,
    l0: int,
    c: Option<Position>,
    start: u64,
    b: BatchView<E>,
    c2: Option<Position>,
) -> bool {
    &&& forall|hw: u64, w: u64, wins: Seq<(int, int)>|
        #[trigger] scanned::<S, E>(hist, l0, scan_first(c, start), hw, w, wins, c, b) ==> a2_scan(hist, l0, wins, c)
    &&& c2 matches Some(p) ==> holds(t7_view(hist, c, b), start, p.block)
}

/// The driver's end-to-end claim across one tick from `pre` with `pre.dinv(log, h)`. The
/// hypotheses, for a tick that applied a batch: `a2_scan` for the scan's windows, and the
/// tick's view holding every height from `start_block` to the new cursor. Then the
/// invariant carries over, and after `Progressed`/`Idle` with the engine Active the fold
/// is the fold of the canonical logs of the tick's view (its last `events_in` view, or
/// the boundary view for `Idle`), with the ring a hash chain inside that view. After
/// `RolledBack`, `Inv` holds over the canonical logs of a view that confirmed the probed
/// ring entry, when that view holds `[start_block, entry]`.
pub open spec fn t7_tick<F: Fold, S: Source<Event = F::Event>, K: SnapshotSink<F>>(
    pre: Driver<F, S, K>,
    post: Driver<F, S, K>,
    r: Tick,
    log: Seq<(Position, F::Event)>,
    h: ChainView,
) -> bool {
    let (l0, hist) = (pre.source_log().len() as int, post.source_log());
    let c = pre.engine_view().cursor;
    let start = pre.start_block();
    let v = t7_view(hist, c, post.batch_view());
    let hyp = (r is Progressed || r is Idle || r is DurabilityLost) ==> a2_hyp::<S, F::Event>(
        hist,
        l0,
        c,
        start,
        post.batch_view(),
        post.engine_view().cursor,
    );
    let ring = pre.engine_view().ring;
    &&& hyp ==> exists|log2: Seq<(Position, F::Event)>, h2: ChainView| #[trigger] post.dinv(log2, h2)
    &&& hyp && (r is Progressed || r is Idle) && post.engine_view().status is Active ==> t7_state::<
        F,
        S,
        F::Event,
        F::Error,
    >(post.engine_view(), pre.init_view(), start, v)
    &&& r matches Tick::RolledBack { to } ==> exists|lo: int, k: int|
        0 < lo <= ring.len() && l0 <= k < hist.len() && #[trigger] probe_held(ring, lo, hist[k]) && (holds(
            hist[k],
            start,
            ring[lo - 1].number,
        ) ==> post.engine_view().inv::<F, F::Event, F::Error>(
            pre.init_view(),
            canon::<S, F::Event>(hist[k], before(start), to),
        ))
}

/// Driver invariant: `Inv` over `log`, and while Active `log` is the canonical history of
/// the chain view `h` from `before(start)` to the cursor, which ends its block, with the
/// ring in `h` at heights from `start`, and every stored slot cursor ending its block in
/// `h`.
pub open spec fn dinv<F: ?Sized, S: ?Sized, E, Er>(
    e: EngineView,
    init: int,
    start: u64,
    log: Seq<(Position, E)>,
    h: ChainView,
) -> bool {
    &&& e.inv::<F, E, Er>(init, log)
    &&& e.status is Active ==> {
        &&& a1::<S, E>(h)
        &&& log == canon::<S, E>(h, before(start), e.cursor)
        &&& ring_in(e.ring, h)
        &&& forall|i: int| 0 <= i < e.ring.len() ==> #[trigger] e.ring[i].number >= start
        &&& e.cursor matches Some(c) ==> holds(h, start, c.block) && complete::<S, E>(h, c)
        &&& forall|k: int|
            0 <= k < e.slots.len() && #[trigger] e.slots[k] is Some && e.slots[k].unwrap().cursor is Some
                ==> e.slots[k].unwrap().cursor.unwrap().block >= start && complete::<S, E>(
                h,
                e.slots[k].unwrap().cursor.unwrap(),
            )
    }
}

/// A tick's conclusion for view `v`.
pub open spec fn t7_state<F: ?Sized, S: ?Sized, E, Er>(e: EngineView, init: int, start: u64, v: ChainView) -> bool {
    &&& e.fold == fold::<F, E, Er>(init, canon::<S, E>(v, before(start), e.cursor))
    &&& ring_chain(e.ring)
    &&& ring_in(e.ring, v)
}

/// Scan-view stability for one scan over `hist` from `l0` with windows `wins`: blocks of
/// the earlier (empty) windows are unchanged in the last `events_in` view, and the cursor
/// block there is the one the boundary fetch saw.
pub open spec fn a2_scan(hist: Seq<ChainView>, l0: int, wins: Seq<(int, int)>, cursor: Option<Position>) -> bool {
    let vk = hist[l0 + wins.len()];
    &&& forall|i: int, n: u64|
        0 <= i < wins.len() - 1 && wins[i].0 <= n <= wins[i].1 ==> #[trigger] header(hist[l0 + 1 + i], n)
            == header(vk, n)
    &&& cursor matches Some(c) ==> header(vk, c.block) == header(hist[hist.len() - 1], c.block)
}

/// The view a tick's conclusion names: the last `events_in` view for a non-empty batch,
/// else the boundary view (the last view either way when there is no cursor).
pub open spec fn t7_view<E>(hist: Seq<ChainView>, cursor: Option<Position>, b: BatchView<E>) -> ChainView {
    if b.ends.len() > 0 && cursor is Some {
        hist[hist.len() - 2]
    } else {
        hist[hist.len() - 1]
    }
}

/// `flat` is `triples` with positions.
proof fn lemma_flat_triples<E>(b: BatchView<E>, n: int)
    requires
        0 <= n <= b.ends.len(),
    ensures
        b.flat_upto(n).len() == b.triples_upto(n).len(),
        forall|i: int| 0 <= i < b.flat_upto(n).len() ==> #[trigger] b.flat_upto(n)[i] == tpos(b.triples_upto(n)[i]),
    decreases n,
{
    if n > 0 {
        lemma_flat_triples(b, n - 1);
        let (f0, t0, fs, ts) = (b.flat_upto(n - 1), b.triples_upto(n - 1), b.span_events(n - 1), b.span_triples(n - 1));
        assert(fs.len() == ts.len());
        assert forall|i: int| 0 <= i < b.flat_upto(n).len() implies #[trigger] b.flat_upto(n)[i] == tpos(b.triples_upto(n)[i]) by {
            if i >= f0.len() {
                assert(b.flat_upto(n)[i] == fs[i - f0.len()]);
                assert(b.triples_upto(n)[i] == ts[i - t0.len()]);
            } else {
                assert(b.flat_upto(n)[i] == f0[i]);
                assert(b.triples_upto(n)[i] == t0[i]);
            }
        }
    }
}

/// Span `j`'s first entry is at `start(j)` in `triples_upto(n)`.
proof fn lemma_triples_at<E>(b: BatchView<E>, n: int, j: int)
    requires
        b.wf(),
        0 <= j < n <= b.ends.len(),
        b.start(j) < b.ends[j],
    ensures
        b.start(j) < b.triples_upto(n).len(),
        b.triples_upto(n)[b.start(j)].0 == b.block(j),
    decreases n,
{
    lemma_triples_len(b, n - 1);
    lemma_triples_len(b, n);
    if j == n - 1 {
        assert(b.triples_upto(n)[b.start(j)] == b.span_triples(j)[0]);
    } else {
        lemma_triples_at(b, n - 1, j);
        assert(b.ends[j] <= b.ends[n - 2]);
        assert(b.triples_upto(n)[b.start(j)] == b.triples_upto(n - 1)[b.start(j)]);
    }
}

/// The windows before window `i` hold no entry in the last `events_in` view.
proof fn lemma_windows_empty<S, E>(
    hist: Seq<ChainView>,
    l0: int,
    first: u64,
    hw: u64,
    w: u64,
    wins: Seq<(int, int)>,
    t: Seq<(BlockRef, u32, E)>,
    i: int,
)
    requires
        0 <= l0,
        windows_ok::<S, E>(hist, l0, Some(first), hw, w, wins, t),
        a2_scan(hist, l0, wins, None),
        0 <= i < wins.len(),
    ensures
        first <= wins[i].0 <= wins[i].1 + 1,
        wins[i].1 <= hw,
        range_entries::<S, E>(hist[l0 + wins.len()], first as int, wins[i].0 - 1).len() == 0,
    decreases i,
{
    assert(wins[i].0 <= hw);
    if i > 0 {
        let j = i - 1;
        lemma_windows_empty::<S, E>(hist, l0, first, hw, w, wins, t, j);
        let vk = hist[l0 + wins.len()];
        assert(wins[i].0 == wins[j].1 + 1);
        lemma_re_split::<S, E>(vk, first as int, wins[j].0 - 1, wins[j].1);
        assert forall|n: u64| wins[j].0 <= n <= wins[j].1 implies #[trigger] header(hist[l0 + 1 + j], n) == header(vk, n) by {}
        lemma_re_agree::<S, E>(hist[l0 + 1 + j], vk, wins[j].0, wins[j].1);
        assert(range_entries::<S, E>(hist[l0 + 1 + j], wins[j].0, wins[j].1).len() == 0);
    }
}

/// A scanned, shaped, non-empty batch is exactly the last window's entries in the last
/// `events_in` view, and the windows before it are empty there.
proof fn lemma_batch_window<S, E>(
    b: BatchView<E>,
    hist: Seq<ChainView>,
    l0: int,
    first: Option<u64>,
    hw: u64,
    ww: u64,
    wins: Seq<(int, int)>,
    cursor: Option<Position>,
)
    requires
        b.wf(),
        b.shaped(),
        b.ends.len() > 0,
        0 <= l0,
        scanned::<S, E>(hist, l0, first, hw, ww, wins, cursor, b),
        forall|k: int| l0 <= k < hist.len() ==> a1::<S, E>(#[trigger] hist[k]),
        a2_scan(hist, l0, wins, cursor),
    ensures
        ({
            let m = wins.len() as int;
            let vk = hist[l0 + m];
            let (wlo, whi) = (wins[m - 1].0, wins[m - 1].1);
            &&& m > 0
            &&& first is Some
            &&& first.unwrap() <= wlo <= whi + 1
            &&& whi <= hw
            &&& vk == t7_view(hist, cursor, b)
            &&& a1::<S, E>(vk)
            &&& b.triples() == range_entries::<S, E>(vk, wlo, whi)
            &&& b.flat() == pentries::<S, E>(vk, wlo, whi)
            &&& range_entries::<S, E>(vk, first.unwrap() as int, wlo - 1).len() == 0
        }),
{
    let m = wins.len() as int;
    let n = b.ends.len() as int;
    let vk = hist[l0 + m];
    let t = b.triples();
    let flat = b.flat();
    lemma_triples_len(b, n);
    assert(b.start(n - 1) < b.ends[n - 1]);
    if n >= 2 {
        assert(b.ends[0] <= b.ends[n - 1]);
    }
    assert(t.len() > 0);
    assert(m > 0);
    let first = first.unwrap();
    let (wlo, whi) = (wins[m - 1].0, wins[m - 1].1);
    assert(a1::<S, E>(vk));
    let r = range_entries::<S, E>(vk, wlo, whi);
    assert(t.to_multiset() == r.to_multiset());
    lemma_re_sorted::<S, E>(vk, wlo, whi);
    crate::batch::lemma_shaped_sorted(b);
    lemma_flat_triples(b, n);
    assert forall|i: int, j: int| 0 <= i < j < t.len() implies lt(tpos(#[trigger] t[i]).0, tpos(#[trigger] t[j]).0) by {
        assert(flat[i] == tpos(t[i]) && flat[j] == tpos(t[j]));
        assert(lt(flat[i].0, flat[j].0));
    }
    lemma_sorted_unique(t, r);
    assert(flat =~= pentries::<S, E>(vk, wlo, whi)) by {
        assert forall|i: int| 0 <= i < flat.len() implies flat[i] == pentries::<S, E>(vk, wlo, whi)[i] by {
            assert(flat[i] == tpos(t[i]));
        }
    }
    lemma_windows_empty::<S, E>(hist, l0, first, hw, ww, wins, t, m - 1);
}

/// Every entry of the ring after an accepted non-empty apply is in `vk`, at a height from
/// `start`: an old entry through the agreement with `h`, a gained one through the batch.
proof fn lemma_ring_after_in<E>(
    v: EngineView,
    post: EngineView,
    b: BatchView<E>,
    w: int,
    h: ChainView,
    vk: ChainView,
    start: u64,
    lo: int,
    hi: int,
)
    requires
        v.wf(),
        b.wf(),
        b.shaped(),
        0 < w,
        ring_after(v, post, b, w),
        ring_in(v.ring, h),
        forall|i: int| 0 <= i < v.ring.len() ==> #[trigger] v.ring[i].number >= start,
        v.cursor matches Some(p) ==> forall|n: u64| start <= n <= p.block ==> #[trigger] header(h, n) == header(vk, n),
        forall|j: int|
            0 <= j < b.blocks.len() ==> vk.contains_key(#[trigger] b.blocks[j]) && vk[b.blocks[j]] == b.block(j)
                && b.blocks[j] >= start,
    ensures
        ring_in(post.ring, vk),
        forall|i: int| 0 <= i < post.ring.len() ==> #[trigger] post.ring[i].number >= start,
{
    let (i0, i1) = choose|i0: int, i1: int|
        #![trigger split_at_tip(b, v.cursor, i0), split_at_tip(b, post.cursor, i1)]
        {
            &&& i0 <= i1
            &&& split_at_tip(b, v.cursor, i0)
            &&& split_at_tip(b, post.cursor, i1)
            &&& post.ring == ring_ext(v.ring, w, span_refs(b).subrange(i0, i1))
        };
    let g = span_refs(b).subrange(i0, i1);
    assert(0 <= i0 && i1 <= span_refs(b).len());
    lemma_ring_ext_from(v.ring, w, g);
    assert forall|i: int| 0 <= i < post.ring.len() implies vk.contains_key(#[trigger] post.ring[i].number)
        && vk[post.ring[i].number] == post.ring[i] && post.ring[i].number >= start by {
        let x = post.ring[i];
        if v.ring.contains(x) {
            let j = choose|j: int| 0 <= j < v.ring.len() && v.ring[j] == x;
            let p = v.cursor.unwrap();
            if j < v.ring.len() - 1 {
                assert(v.ring[j].number < v.ring[v.ring.len() - 1].number);
            }
            assert(header(h, x.number) == header(vk, x.number));
        } else {
            let q = choose|q: int| 0 <= q < g.len() && g[q] == x;
            assert(g[q] == b.block(i0 + q));
            assert(b.blocks[i0 + q] == x.number);
        }
    }
}

/// `dinv` and the tick's conclusion for an accepted apply that did not stop, over the
/// scan that built the batch.
proof fn lemma_apply_t7<F: ?Sized, S, E, Er>(
    v: EngineView,
    post: EngineView,
    b: BatchView<E>,
    w: int,
    init: int,
    start: u64,
    log: Seq<(Position, E)>,
    h: ChainView,
    hist: Seq<ChainView>,
    l0: int,
    hw: u64,
    ww: u64,
    wins: Seq<(int, int)>,
)
    requires
        v.wf(),
        post.wf(),
        b.wf(),
        0 < w,
        v.status is Active,
        dinv::<F, S, E, Er>(v, init, start, log, h),
        accepted(v, b),
        !stopped::<F, E, Er>(v, b),
        post.cursor == cursor_after(v.cursor, ok_calls::<F, E, Er>(v, b)),
        ring_after(v, post, b, w),
        post.slots == v.slots,
        post.status == v.status,
        post.inv::<F, E, Er>(init, log + calls::<F, E, Er>(v, b)),
        0 <= l0,
        scanned::<S, E>(hist, l0, scan_first(v.cursor, start), hw, ww, wins, v.cursor, b),
        forall|k: int| l0 <= k < hist.len() ==> a1::<S, E>(#[trigger] hist[k]),
        a2_scan(hist, l0, wins, v.cursor),
        post.cursor matches Some(c2) ==> holds(t7_view(hist, v.cursor, b), start, c2.block),
    ensures
        dinv::<F, S, E, Er>(
            post,
            init,
            start,
            log + calls::<F, E, Er>(v, b),
            if b.ends.len() > 0 {
                t7_view(hist, v.cursor, b)
            } else {
                h
            },
        ),
        t7_state::<F, S, E, Er>(post, init, start, t7_view(hist, v.cursor, b)),
{
    if b.ends.len() == 0 {
        lemma_apply_empty::<F, S, E, Er>(v, post, b, w, init, start, log, h, hist, l0, hw, ww, wins);
    } else {
        lemma_apply_step::<F, S, E, Er>(v, post, b, w, init, start, log, h, hist, l0, hw, ww, wins);
    }
}

/// `lemma_apply_t7` for an empty batch: nothing moves, and the boundary view agrees with
/// `h` up to the cursor.
proof fn lemma_apply_empty<F: ?Sized, S, E, Er>(
    v: EngineView,
    post: EngineView,
    b: BatchView<E>,
    w: int,
    init: int,
    start: u64,
    log: Seq<(Position, E)>,
    h: ChainView,
    hist: Seq<ChainView>,
    l0: int,
    hw: u64,
    ww: u64,
    wins: Seq<(int, int)>,
)
    requires
        v.wf(),
        post.wf(),
        b.wf(),
        0 < w,
        v.status is Active,
        dinv::<F, S, E, Er>(v, init, start, log, h),
        accepted(v, b),
        !stopped::<F, E, Er>(v, b),
        post.cursor == cursor_after(v.cursor, ok_calls::<F, E, Er>(v, b)),
        ring_after(v, post, b, w),
        post.slots == v.slots,
        post.status == v.status,
        post.inv::<F, E, Er>(init, log + calls::<F, E, Er>(v, b)),
        0 <= l0,
        scanned::<S, E>(hist, l0, scan_first(v.cursor, start), hw, ww, wins, v.cursor, b),
        forall|k: int| l0 <= k < hist.len() ==> a1::<S, E>(#[trigger] hist[k]),
        a2_scan(hist, l0, wins, v.cursor),
        post.cursor matches Some(c2) ==> holds(t7_view(hist, v.cursor, b), start, c2.block),
        b.ends.len() == 0,
    ensures
        dinv::<F, S, E, Er>(post, init, start, log + calls::<F, E, Er>(v, b), h),
        t7_state::<F, S, E, Er>(post, init, start, t7_view(hist, v.cursor, b)),
{
    let c = v.cursor;
    let a0 = before(start);
    let flat = b.flat();
    let cl = calls::<F, E, Er>(v, b);
    assert(flat.len() == 0);
    lemma_newer_all(c, flat);
    assert(cl.len() == 0);
    assert(log + cl =~= log);
    let (i0, i1) = choose|i0: int, i1: int|
        #![trigger split_at_tip(b, v.cursor, i0), split_at_tip(b, post.cursor, i1)]
        {
            &&& i0 <= i1
            &&& split_at_tip(b, v.cursor, i0)
            &&& split_at_tip(b, post.cursor, i1)
            &&& post.ring == ring_ext(v.ring, w, span_refs(b).subrange(i0, i1))
        };
    assert(span_refs(b).subrange(i0, i1) =~= Seq::<BlockRef>::empty());
    assert(post.ring == v.ring);
    assert(post.cursor == c);
    let vb = hist[hist.len() - 1];
    assert(vb == t7_view(hist, c, b));
    if let Some(p) = c {
        let r = v.ring;
        assert(r[r.len() - 1].number == p.block);
        assert(h[p.block] == r.last());
        assert(a1::<S, E>(vb));
        lemma_view_agree(h, vb, start, p.block);
        lemma_canon_agree::<S, E>(h, vb, start, c);
        assert forall|i: int| 0 <= i < r.len() implies start <= #[trigger] r[i].number <= p.block by {
            if i < r.len() - 1 {
                assert(r[i].number < r[r.len() - 1].number);
            }
        }
        lemma_ring_move(r, h, vb, start, p.block);
        lemma_ring_chain_in(r, h);
    }
}

/// `lemma_apply_t7` for a non-empty batch: the ghost view moves to the last `events_in`
/// view, and the log grows by the batch.
proof fn lemma_apply_step<F: ?Sized, S, E, Er>(
    v: EngineView,
    post: EngineView,
    b: BatchView<E>,
    w: int,
    init: int,
    start: u64,
    log: Seq<(Position, E)>,
    h: ChainView,
    hist: Seq<ChainView>,
    l0: int,
    hw: u64,
    ww: u64,
    wins: Seq<(int, int)>,
)
    requires
        v.wf(),
        post.wf(),
        b.wf(),
        0 < w,
        v.status is Active,
        dinv::<F, S, E, Er>(v, init, start, log, h),
        accepted(v, b),
        !stopped::<F, E, Er>(v, b),
        post.cursor == cursor_after(v.cursor, ok_calls::<F, E, Er>(v, b)),
        ring_after(v, post, b, w),
        post.slots == v.slots,
        post.status == v.status,
        post.inv::<F, E, Er>(init, log + calls::<F, E, Er>(v, b)),
        0 <= l0,
        scanned::<S, E>(hist, l0, scan_first(v.cursor, start), hw, ww, wins, v.cursor, b),
        forall|k: int| l0 <= k < hist.len() ==> a1::<S, E>(#[trigger] hist[k]),
        a2_scan(hist, l0, wins, v.cursor),
        post.cursor matches Some(c2) ==> holds(t7_view(hist, v.cursor, b), start, c2.block),
        b.ends.len() > 0,
    ensures
        dinv::<F, S, E, Er>(post, init, start, log + calls::<F, E, Er>(v, b), t7_view(hist, v.cursor, b)),
        t7_state::<F, S, E, Er>(post, init, start, t7_view(hist, v.cursor, b)),
{
    let c = v.cursor;
    let flat = b.flat();
    let cl = calls::<F, E, Er>(v, b);
    let m = wins.len() as int;
    let vk = hist[l0 + m];
    lemma_batch_window::<S, E>(b, hist, l0, scan_first(c, start), hw, ww, wins, c);
    let first = scan_first(c, start).unwrap();
    let (wlo, whi) = (wins[m - 1].0, wins[m - 1].1);
    assert(cl == flat && flat.len() > 0) by {
        lemma_re_facts::<S, E>(vk, wlo, whi);
        assert forall|i: int| 0 <= i < flat.len() implies opt_lt(c, Some((#[trigger] flat[i]).0)) by {
            assert(flat[i] == tpos(range_entries::<S, E>(vk, wlo, whi)[i]));
        }
        lemma_newer_all(c, flat);
        lemma_applied_prefix::<F, E, Er>(v.fold, flat);
        lemma_triples_len(b, b.ends.len() as int);
        assert(b.start(b.ends.len() - 1) < b.ends[b.ends.len() - 1]);
        lemma_flat_triples(b, b.ends.len() as int);
    }
    let c2 = flat.last().0;
    assert(post.cursor == Some(c2));
    if let Some(p) = c {
        let r = v.ring;
        assert(r[r.len() - 1].number == p.block);
        assert(h[p.block] == r.last());
        assert(header(vk, p.block) == Some(r.last()));
    }
    lemma_step_canon::<S, E>(vk, h, start, c, log, first, wlo, whi, flat);
    assert forall|k: int|
        0 <= k < post.slots.len() && #[trigger] post.slots[k] is Some && post.slots[k].unwrap().cursor is Some
            implies complete::<S, E>(vk, post.slots[k].unwrap().cursor.unwrap()) by {
        let sc = post.slots[k].unwrap().cursor.unwrap();
        assert(opt_le(Some(sc), c));
        assert(header(h, sc.block) == header(vk, sc.block));
        assert(block_entries::<S, E>(h, sc.block) == block_entries::<S, E>(vk, sc.block));
    }
    assert forall|j: int|
        0 <= j < b.blocks.len() implies vk.contains_key(#[trigger] b.blocks[j]) && vk[b.blocks[j]] == b.block(j)
            && b.blocks[j] >= start by {
        lemma_re_facts::<S, E>(vk, wlo, whi);
        assert(b.start(j) < b.ends[j]);
        lemma_triples_at(b, b.ends.len() as int, j);
        assert(range_entries::<S, E>(vk, wlo, whi)[b.start(j)].0 == b.block(j));
    }
    lemma_ring_after_in(v, post, b, w, h, vk, start, wlo, whi);
    lemma_ring_chain_in(post.ring, vk);
}

/// The canon half of `lemma_apply_step`: the old log in `vk`, extended by the batch, is
/// `canon` of `vk` up to the batch's last position, which ends its block.
proof fn lemma_step_canon<S, E>(
    vk: ChainView,
    h: ChainView,
    start: u64,
    c: Option<Position>,
    log: Seq<(Position, E)>,
    first: u64,
    wlo: int,
    whi: int,
    flat: Seq<(Position, E)>,
)
    requires
        a1::<S, E>(vk),
        a1::<S, E>(h),
        log == canon::<S, E>(h, before(start), c),
        c matches Some(p) ==> {
            &&& holds(h, start, p.block)
            &&& complete::<S, E>(h, p)
            &&& h.contains_key(p.block) && vk.contains_key(p.block) && h[p.block] == vk[p.block]
            &&& p.block >= start
            &&& first == p.block + 1
        },
        c is None ==> first == start,
        flat == pentries::<S, E>(vk, wlo, whi),
        flat.len() > 0,
        first <= wlo <= whi + 1,
        whi <= u64::MAX,
        range_entries::<S, E>(vk, first as int, wlo - 1).len() == 0,
        holds(vk, start, flat.last().0.block),
    ensures
        complete::<S, E>(vk, flat.last().0),
        wlo <= flat.last().0.block <= whi,
        log + flat == canon::<S, E>(vk, before(start), Some(flat.last().0)),
        c matches Some(p) ==> forall|n: u64| start <= n <= p.block ==> #[trigger] header(h, n) == header(vk, n),
{
    let a0 = before(start);
    lemma_last_complete::<S, E>(vk, wlo, whi);
    let c2 = flat.last().0;
    assert(c2 == tpos(range_entries::<S, E>(vk, wlo, whi).last()).0);
    let lb: int = match c {
        Some(p) => p.block as int,
        None => start - 1,
    };
    if let Some(p) = c {
        lemma_view_agree(h, vk, start, p.block);
        lemma_canon_agree::<S, E>(h, vk, start, c);
        assert(header(h, p.block) == header(vk, p.block));
        assert(block_entries::<S, E>(h, p.block) == block_entries::<S, E>(vk, p.block));
    }
    lemma_canon_extend::<S, E>(vk, a0, lb, c, c2);
    lemma_pe_split::<S, E>(vk, first as int, wlo - 1, c2.block as int);
    assert(pentries::<S, E>(vk, first as int, wlo - 1).len() == 0);
    assert(pentries::<S, E>(vk, wlo, c2.block as int) == flat);
    assert(pentries::<S, E>(vk, first as int, c2.block as int) =~= flat);
}

/// `dinv` and `Inv` across `poll_apply`'s recovery arm: the rejected apply changed
/// nothing the invariants read, then `recovered` gives the rollback, resync or unchanged
/// state.
proof fn lemma_recover_t7<F: Fold, S: Source<Event = F::Event>, K: SnapshotSink<F>>(
    old: Driver<F, S, K>,
    pre: Driver<F, S, K>,
    post: Driver<F, S, K>,
    tick: Tick,
)
    requires
        old.engine@.wf(),
        old.engine@.status is Active,
        recovered(pre, post, tick),
        pre.engine@ == (EngineView { last_verified: pre.engine@.last_verified, ..old.engine@ }),
        !accepted(old.engine@, pre.batch@),
        old.initial == pre.initial,
        old.config == pre.config,
        sview_log::<S>(&old.source).len() <= sview_log::<S>(&pre.source).len(),
    ensures
        forall|init: int, log: Seq<(Position, F::Event)>|
            #[trigger] old.engine_view().inv::<F, F::Event, F::Error>(init, log) ==> tick_inv(old, post, tick, init, log),
        forall|log: Seq<(Position, F::Event)>, h: ChainView|
            #[trigger] old.dinv(log, h) ==> t7_tick(old, post, tick, log, h),
{
    let v = old.engine@;
    let bv = pre.batch@;
    assert(post.batch == pre.batch);
    assert(calls::<F, F::Event, F::Error>(v, bv) =~= Seq::empty());
    let (from, rh) = (sview_log::<S>(&pre.source).len() as int, sview_log::<S>(&post.source));
    let mid = Driver { source: post.source, ..pre };
    let init = fview::<F>(&old.initial);
    let start = old.config.start_block;
    post.engine.lemma_wf();
    assert forall|i: int, log: Seq<(Position, F::Event)>|
        #[trigger] old.engine_view().inv::<F, F::Event, F::Error>(i, log) implies tick_inv(old, post, tick, i, log) by {
        assert(log + calls::<F, F::Event, F::Error>(v, bv) =~= log);
        assert(pre.engine@.inv::<F, F::Event, F::Error>(i, log));
    }
    assert forall|log: Seq<(Position, F::Event)>, h: ChainView|
        #[trigger] old.dinv(log, h) implies t7_tick(old, post, tick, log, h) by {
        assert(dinv::<F, S, F::Event, F::Error>(pre.engine@, init, start, log, h));
        match tick {
            Tick::RolledBack { to } => {
                let ring = v.ring;
                let (lo, k) = choose|lo: int, k: int|
                    0 < lo <= ring.len() && from <= k < rh.len() && #[trigger] probe_held(ring, lo, rh[k])
                        && rolled_back(mid, post, ring[lo - 1].number, to);
                let e = pre.engine@;
                let kk = choose|kk: int| #[trigger] e.rollback_target(ring[lo - 1].number, kk) && to == e.slots[kk].unwrap().cursor;
                lemma_rollback_t7::<F, S, F::Event, F::Error>(
                    e, post.engine@, init, start, log, h, ring[lo - 1].number, kk, to, rh[k], lo,
                );
                assert(post.dinv(upto(log, to), h));
            },
            Tick::Resynced => {
                lemma_fresh_dinv::<F, S, F::Event, F::Error>(post.engine@, init, start);
                assert(post.dinv(Seq::empty(), Map::empty()));
            },
            Tick::Terminal(_) => {
                assert(log + calls::<F, F::Event, F::Error>(v, bv) =~= log);
                assert(post.engine@.inv::<F, F::Event, F::Error>(init, log));
                assert(post.dinv(log, h));
            },
            _ => {
                assert(post.dinv(log, h));
            },
        }
    }
}

/// A fresh engine (no cursor, empty ring) satisfies `dinv` with the empty log
/// and the empty view.
proof fn lemma_fresh_dinv<F: ?Sized, S, E, Er>(e: EngineView, init: int, start: u64)
    requires
        e.wf(),
        e.cursor is None,
        e.ring.len() == 0,
        e.inv::<F, E, Er>(init, Seq::empty()),
    ensures
        dinv::<F, S, E, Er>(e, init, start, Seq::empty(), Map::empty()),
{
    assert(canon::<S, E>(Map::empty(), before(start), None) =~= Seq::<(Position, E)>::empty());
    assert forall|k: int|
        0 <= k < e.slots.len() && #[trigger] e.slots[k] is Some && e.slots[k].unwrap().cursor is Some implies false by {
        assert(opt_le(e.slots[k].unwrap().cursor, e.cursor));
    }
}

/// `dinv` through a rollback to slot `k`'s cursor `to`: the ghost view stays, the log is
/// cut at `to`; and a probe view that confirmed `ring[lo - 1]` and holds
/// `[start, ring[lo - 1]]` agrees with the ghost view up to `to`.
proof fn lemma_rollback_t7<F: ?Sized, S, E, Er>(
    e: EngineView,
    f: EngineView,
    init: int,
    start: u64,
    log: Seq<(Position, E)>,
    h: ChainView,
    ancestor: u64,
    k: int,
    to: Option<Position>,
    pv: ChainView,
    lo: int,
)
    requires
        e.wf(),
        e.status is Active,
        dinv::<F, S, E, Er>(e, init, start, log, h),
        e.rollback_target(ancestor, k),
        to == e.slots[k].unwrap().cursor,
        f.cursor == to,
        f.ring == e.ring.subrange(0, f.ring.len() as int),
        to is None ==> f.ring.len() == 0,
        to matches Some(c) ==> prefix_at_or_below(e.ring, c.block, f.ring.len() as int),
        f.status is Active,
        f.slots.len() == e.slots.len(),
        forall|j: int| 0 <= j < f.slots.len() && #[trigger] f.slots[j] is Some ==> f.slots[j] == e.slots[j],
        f.inv::<F, E, Er>(init, upto(log, to)),
    ensures
        dinv::<F, S, E, Er>(f, init, start, upto(log, to), h),
        0 < lo <= e.ring.len() && ancestor == e.ring[lo - 1].number && a1::<S, E>(pv) && confirms(pv, e.ring[lo - 1])
            && holds(pv, start, ancestor) ==> f.inv::<F, E, Er>(init, canon::<S, E>(pv, before(start), to)),
{
    let a0 = before(start);
    let sl = e.slots[k].unwrap();
    assert(opt_le(sl.cursor, e.cursor));
    match e.cursor {
        None => {
            assert(to is None);
            assert(log.len() == 0);
            assert(upto(log, to) == log);
        },
        Some(cc) => {
            if let Some(q) = to {
                assert(q.block >= start);
            }
            lemma_canon_upto::<S, E>(h, a0, cc, to);
            if 0 < lo <= e.ring.len() && ancestor == e.ring[lo - 1].number && a1::<S, E>(pv) && confirms(pv, e.ring[lo - 1])
                && holds(pv, start, ancestor) {
                let r = e.ring;
                assert(r[r.len() - 1].number == cc.block);
                if lo - 1 < r.len() - 1 {
                    assert(r[lo - 1].number < r[r.len() - 1].number);
                }
                assert(h[ancestor] == r[lo - 1]);
                assert(ancestor >= start);
                lemma_view_agree(h, pv, start, ancestor);
                lemma_canon_agree::<S, E>(h, pv, start, to);
            }
        },
    }
    assert forall|i: int| 0 <= i < f.ring.len() implies h.contains_key(#[trigger] f.ring[i].number) && h[f.ring[i].number]
        == f.ring[i] && f.ring[i].number >= start by {
        assert(f.ring[i] == e.ring[i]);
    }
    assert forall|j: int|
        0 <= j < f.slots.len() && #[trigger] f.slots[j] is Some && f.slots[j].unwrap().cursor is Some
            implies f.slots[j].unwrap().cursor.unwrap().block >= start && complete::<S, E>(
            h,
            f.slots[j].unwrap().cursor.unwrap(),
        ) by {
        assert(f.slots[j] == e.slots[j]);
    }
}

/// A checkpoint keeps `dinv`: the new slot's cursor is the cursor.
proof fn lemma_checkpoint_dinv<F: ?Sized, S, E, Er>(
    pre: EngineView,
    init: int,
    start: u64,
    log: Seq<(Position, E)>,
    h: ChainView,
)
    requires
        pre.wf(),
        dinv::<F, S, E, Er>(pre, init, start, log, h),
        checkpointed(pre).inv::<F, E, Er>(init, log),
    ensures
        dinv::<F, S, E, Er>(checkpointed(pre), init, start, log, h),
{
    let post = checkpointed(pre);
    if pre.status is Active && pre.slots.len() > 0 {
        let n = pre.slots.len() as int;
        if let Some(c) = pre.cursor {
            assert(pre.ring[pre.ring.len() - 1].number == c.block);
        }
        assert forall|k: int|
            0 <= k < post.slots.len() && #[trigger] post.slots[k] is Some && post.slots[k].unwrap().cursor is Some
                implies post.slots[k].unwrap().cursor.unwrap().block >= start && complete::<S, E>(
                h,
                post.slots[k].unwrap().cursor.unwrap(),
            ) by {
            if k < n - 1 {
                assert(post.slots[k] == pre.slots[k + 1]);
            }
        }
    }
}

/// The durable floor through apply: the cursor does not move back and a dead slot stays
/// dead.
proof fn lemma_apply_floor<F: ?Sized, E, Er>(v: EngineView, post: EngineView, b: BatchView<E>, w: int, off: Set<Position>)
    requires
        v.wf(),
        0 < w,
        floor_ok(off, v),
        post.slots == v.slots,
        post.cursor == cursor_after(v.cursor, ok_calls::<F, E, Er>(v, b)),
        accepted(v, b) ==> ring_after(v, post, b, w),
        !accepted(v, b) ==> post.ring == v.ring,
    ensures
        floor_ok(off, post),
{
    lemma_cursor_advances::<F, E, Er>(v, b);
    assert forall|k: int| #[trigger] post.live_at(k) implies v.live_at(k) by {
        if let Some(q) = post.slots[k].unwrap().cursor {
            assert(opt_le(v.slots[k].unwrap().cursor, v.cursor));
            let i = choose|i: int| 0 <= i < post.ring.len() && #[trigger] post.ring[i].number == q.block;
            if accepted(v, b) {
                let (i0, i1) = choose|i0: int, i1: int|
                    #![trigger split_at_tip(b, v.cursor, i0), split_at_tip(b, post.cursor, i1)]
                    {
                        &&& i0 <= i1
                        &&& split_at_tip(b, v.cursor, i0)
                        &&& split_at_tip(b, post.cursor, i1)
                        &&& post.ring == ring_ext(v.ring, w, span_refs(b).subrange(i0, i1))
                    };
                let g = span_refs(b).subrange(i0, i1);
                lemma_ring_ext_from(v.ring, w, g);
                if !v.ring.contains(post.ring[i]) {
                    let j = choose|j: int| 0 <= j < g.len() && g[j] == post.ring[i];
                    assert(g[j] == span_refs(b)[i0 + j]);
                    assert(false);
                } else {
                    let j = choose|j: int| 0 <= j < v.ring.len() && v.ring[j] == post.ring[i];
                    assert(v.ring[j].number == q.block);
                }
            } else {
                assert(v.ring[i].number == q.block);
            }
        }
    }
    assert forall|p: Position| #[trigger] off.contains(p) implies opt_le(Some(p), post.cursor) by {
        lemma_opt_lt_order(Some(p), v.cursor, post.cursor);
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
