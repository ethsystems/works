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
        Head,
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
/// Most `events_in` windows one walk reads.
#[cfg_attr(verus_keep_ghost, verus_verify)]
const MAX_SPAN: u64 = 64;

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
    /// Batch applied; the summary counts what the fold saw. Also a walk cut at its cap
    /// with nothing found, with an empty summary: the next tick walks on.
    Progressed(ApplySummary),
    /// Poll read up to the head and found nothing new.
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
    /// The source's head is below the tip or the cursor block, and no block the driver
    /// holds contradicts it: a node behind the one the last poll read answered. Nothing
    /// changes.
    Behind,
    /// Sink refused a snapshot offer; reported once, folding continues unpersisted.
    DurabilityLost,
    /// Engine can make no further automated progress.
    Terminal(EngineStatus),
}

/// What a scan read.
#[cfg_attr(verus_keep_ghost, verus_verify)]
enum Scan {
    /// A batch for the engine; `capped` when the walk stopped at its cap with nothing
    /// found, so the batch is empty and the tip falls short of its head.
    Batch { capped: bool },
    /// The head block moved during the scan; the batch is empty.
    Moved,
    /// The head is below the tip or the cursor block and contradicts no hash the ring
    /// holds; the batch is empty.
    Behind,
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
    /// True once the most recent applied poll read up to the head and found nothing new;
    /// a `Behind` or `SourceError` tick leaves it as it was, and a `Terminal` tick clears
    /// it.
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
    /// Head a scan read, and how far the chain it commits to holds nothing left to fold.
    tip: Option<Mark>,
    /// Windows the next walk reads at most: halved after a failed scan, doubled after an
    /// applied one.
    span: u64,
}

/// A head a scan read, and the height up to which the chain its hash commits to holds
/// nothing left to fold.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Mark {
    at: BlockRef,
    done: u64,
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
    ///
    /// With `checkpoint_interval` set, an engine that has a cursor and no live checkpoint,
    /// such as a decoded snapshot, takes one at its cursor here. A reorg of the blocks
    /// the first ticks read then rolls back to it rather than resyncing.
    ///
    /// The proved end-to-end claim (T7 in the README) covers the resumed driver when the
    /// engine is `Active`, its fold is the fold of the source chain's events through its
    /// cursor, that cursor ends its block in the chain, and its ring names blocks of the
    /// chain the source holds. An engine whose cursor is inside a block, such as one
    /// decoded from a `Halted` snapshot or fed part of a block by the caller, gets the rest
    /// of that block folded. Tests check that case; no proof covers it.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            engine.wf(),
        ensures
            r matches Ok(d) ==> d.wf() && d.synced() && d.engine_view() == resumed(engine@, config) && d.durable_ok(),
            r matches Ok(d) ==> forall|log: Seq<(Position, F::Event)>, h: ChainView|
                #[trigger] dinv::<F, S, F::Event, F::Error>(engine@, fview::<F>(&genesis), config.start_block, log, h)
                    ==> d.dinv(log, h),
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
    ///
    /// What the proofs cover of a resumed driver is as for [`Driver::resume`].
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            engine.wf(),
        ensures
            r matches Ok(d) ==> d.wf() && d.synced() && d.engine_view() == resumed(engine@, config)
                && (floor_ok(sink_offered::<K>(&sink), engine@) ==> d.durable_ok()),
            r matches Ok(d) ==> forall|log: Seq<(Position, F::Event)>, h: ChainView|
                #[trigger] dinv::<F, S, F::Event, F::Error>(engine@, fview::<F>(&genesis), config.start_block, log, h)
                    ==> d.dinv(log, h),
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
                && fview::<F>(&d.initial) == fview::<F>(&fold) && d.tip is None
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
                &&& d.engine@ == resumed(engine@, driver_config)
                &&& d.source == source
                &&& d.initial == initial
                &&& d.config == driver_config
                &&& d.batch@.ends.len() == 0 && d.batch@.boundary is None
                &&& d.last_checkpoint_block == if resume_checkpoint(engine@, driver_config) {
                    Some(engine@.cursor.unwrap().block)
                } else {
                    None
                }
                &&& d.last_snapshot_block is None
                &&& forall|log: Seq<(Position, F::Event)>, h: ChainView|
                    #[trigger] dinv::<F, S, F::Event, F::Error>(engine@, fview::<F>(&initial), driver_config.start_block, log, h)
                        ==> dinv::<F, S, F::Event, F::Error>(d.engine@, fview::<F>(&initial), driver_config.start_block, log, h)
                &&& !d.durability_lost && !d.caught_up && d.consecutive_errors == 0 && d.tip is None
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
        let mut driver = Self {
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
            tip: None,
            span: MAX_SPAN,
        };
        // A decoded engine holds no checkpoint, so a reorg of the blocks read after a
        // restart would resync. One at the cursor lets it roll back there.
        if driver.config.checkpoint_interval.is_some()
            && driver.engine.cursor().is_some()
            && driver.engine.checkpoint_count() == 0
        {
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost pre = driver.engine@;
                driver.engine.lemma_wf();
            }
            driver.run_checkpoint();
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|log: Seq<(Position, F::Event)>, h: ChainView|
                    #[trigger] dinv::<F, S, F::Event, F::Error>(pre, fview::<F>(&driver.initial), driver.config.start_block, log, h)
                        implies dinv::<F, S, F::Event, F::Error>(
                        driver.engine@,
                        fview::<F>(&driver.initial),
                        driver.config.start_block,
                        log,
                        h,
                    ) by {
                    lemma_checkpoint_dinv::<F, S, F::Event, F::Error>(pre, fview::<F>(&driver.initial), driver.config.start_block, log, h);
                }
            }
        }
        Ok(driver)
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
            // A reset leaves the driver out of sync, so `durable_ok` holds until the next
            // tick reconciles the sink.
            old(self).synced() && final(r)@.resets != r@.resets ==> final(self).durable_ok(),
            final(self).unanchored(),
    ))]
    pub fn engine_mut(&mut self) -> &mut Engine<F> {
        self.tip = None;
        &mut self.engine
    }

    /// Mutable access to the underlying event source. Clears the scan tip, so the next
    /// poll reads again from the cursor block: a changed filter may match events at
    /// heights the tip vouched held none.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures
            final(self).engine_view() == old(self).engine_view(),
            old(self).wf() ==> final(self).wf(),
            old(self).synced() ==> final(self).synced(),
            old(self).durable_ok() ==> final(self).durable_ok(),
            final(self).unanchored(),
            forall|log: Seq<(Position, F::Event)>, h: ChainView|
                #[trigger] old(self).dinv(log, h) ==> final(self).dinv(log, h),
    ))]
    pub fn source_mut(&mut self) -> &mut S {
        self.tip = None;
        &mut self.source
    }

    /// True once the most recent applied poll read up to the head and found nothing new;
    /// a `Behind` or `SourceError` tick leaves it as it was, and a `Terminal` tick clears
    /// it.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            r == self.caught_up_view(),
    ))]
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
            r is Terminal ==> *final(self) == (Driver { engine: final(self).engine, caught_up: false, ..*old(self) })
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
                self.caught_up = false;
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
            r is Terminal ==> *final(self) == (Driver { engine: final(self).engine, caught_up: false, ..*old(self) })
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
                self.caught_up = false;
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
            r is Resynced ==> final(self).dinv(Seq::empty(), Map::empty()),
            r is SourceError ==> !infallible::<S>(&old(self).source) || moved(
                sview_log::<S>(&final(self).source),
                sview_log::<S>(&old(self).source).len() as int,
            ),
            r is Idle ==> final(self).caught_up_view(),
            r is Progressed || r is RolledBack || r is Resynced || r is Terminal ==> !final(self).caught_up_view(),
            r is Behind || r is SourceError ==> final(self).caught_up_view() == old(self).caught_up_view(),
            r is Behind ==> final(self).engine_view() == old(self).engine_view() && final(self).tip_view()
                == old(self).tip_view() && final(self).tip_same(*old(self)) && exists|hd: Head| #[trigger] behind(
                hd,
                old(self).tip_view(),
                old(self).engine_view().cursor,
                old(self).engine_view().ring,
            ) && head_read(final(self).source_log()[old(self).source_log().len() as int], hd),
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
        // Only forward cursor movement, or a walk cut at its cap (the one Progressed tick
        // with an empty batch), earns an immediate re-poll; a batch the engine fully deduped
        // leaves the loop on its poll interval.
        self.advanced = matches!(
            tick,
            Tick::Progressed(summary)
                if summary.applied > 0 || summary.skipped > 0 || self.batch.is_empty()
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(mid.engine_view() == old(self).engine_view());
            assert(mid.source_log() == old(self).source_log());
            assert(pa.engine_view() == self.engine_view() && pa.source_log() == self.source_log()
                && pa.batch_view() == self.batch_view() && pa.init_view() == self.init_view());
            if tick is Resynced {
                assert(pa.dinv(Seq::empty(), Map::empty()));
                assert(self.dinv(Seq::empty(), Map::empty()));
            }
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
            r is Resynced ==> final(self).dinv(Seq::empty(), Map::empty()),
            r is SourceError ==> !infallible::<S>(&old(self).source) || moved(
                sview_log::<S>(&final(self).source),
                sview_log::<S>(&old(self).source).len() as int,
            ),
            r is Idle ==> final(self).caught_up_view(),
            r is Progressed || r is RolledBack || r is Resynced || r is Terminal ==> !final(self).caught_up_view(),
            r is Behind || r is SourceError ==> final(self).caught_up_view() == old(self).caught_up_view(),
            r is Behind ==> final(self).engine_view() == old(self).engine_view() && final(self).tip_view()
                == old(self).tip_view() && final(self).tip_same(*old(self)) && exists|hd: Head| #[trigger] behind(
                hd,
                old(self).tip_view(),
                old(self).engine_view().cursor,
                old(self).engine_view().ring,
            ) && head_read(final(self).source_log()[old(self).source_log().len() as int], hd),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verifier::rlimit(20))]
    fn poll_apply(&mut self) -> Tick {
        self.generation = self.generation.wrapping_add(1);
        if !self.engine.status().is_active() {
            self.caught_up = false;
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
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let tracked mut seen = Ghost(arbitrary::<Head>());
        }
        #[cfg(verus_keep_ghost)]
        proof_with! {Tracked(&mut seen)}
        let read = self.scan();
        if matches!(read, Ok(Scan::Behind)) {
            self.consecutive_errors = 0;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|log: Seq<(Position, F::Event)>, h: ChainView|
                    #[trigger] old(self).dinv(log, h) implies t7_tick(*old(self), *self, Tick::Behind, log, h) by {
                    assert(self.dinv(log, h));
                }
                assert(self.caught_up_view() == old(self).caught_up_view());
            }
            return Tick::Behind;
        }
        if !matches!(read, Ok(Scan::Batch { .. })) {
            self.consecutive_errors = self.consecutive_errors.saturating_add(1);
            self.span = (self.span / 2).max(1);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|log: Seq<(Position, F::Event)>, h: ChainView|
                    #[trigger] old(self).dinv(log, h) implies t7_tick(*old(self), *self, Tick::SourceError, log, h) by {
                    assert(self.dinv(log, h));
                }
                assert(self.caught_up_view() == old(self).caught_up_view());
            }
            return Tick::SourceError;
        }
        self.consecutive_errors = 0;
        let capped = matches!(read, Ok(Scan::Batch { capped: true }));
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost v = self.engine@;
            let ghost bv = self.batch@;
            let ghost w = self.engine.window();
            let ghost off = sink_offered::<K>(&self.sink);
            let ghost (l0, hist) = (sview_log::<S>(&old(self).source).len() as int, sview_log::<S>(&self.source));
            let ghost start = self.config.start_block;
            let ghost (t0, t1) = (old(self).tip, self.tip);
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
                    let ghost k = lemma_poll_t7::<F, S, F::Event, F::Error>(
                        v,
                        post,
                        bv,
                        w,
                        fview::<F>(&self.initial),
                        start,
                        sview_log::<S>(&old(self).source),
                        hist,
                        t0,
                        t1,
                    );
                }
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(accepted(v, bv) && !stopped::<F, F::Event, F::Error>(v, bv));
                    let cl = calls::<F, F::Event, F::Error>(v, bv);
                    assert forall|log: Seq<(Position, F::Event)>, h: ChainView|
                        #[trigger] old(self).dinv(log, h) && views_ok(hist, l0, start)
                            implies dinv::<F, S, F::Event, F::Error>(
                        post,
                        fview::<F>(&self.initial),
                        start,
                        log + cl,
                        if bv.ends.len() > 0 { hist[k] } else { h },
                    ) && t7_state::<F, S, F::Event, F::Error>(
                        post,
                        fview::<F>(&self.initial),
                        start,
                        hist[k],
                    ) && mark_ok::<S, F::Event>(
                        t1,
                        post.cursor,
                        if bv.ends.len() > 0 { hist[k] } else { h },
                        start,
                    ) by {}
                }
                if self.span < MAX_SPAN {
                    self.span = (self.span * 2).min(MAX_SPAN);
                }
                // A walk cut at its cap is not caught up, though it found nothing.
                self.caught_up = self.batch.is_empty() && !capped;
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
                            if views_ok(hist, l0, start) {
                                let h2 = if bv.ends.len() > 0 { hist[k] } else { h };
                                assert(dinv::<F, S, F::Event, F::Error>(post, fview::<F>(&self.initial), start, log + cl, h2));
                                assert(self.dinv(log + cl, h2));
                            }
                        }
                    }
                    return tick;
                }
                let tick = if self.batch.is_empty() && !capped {
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
                        if views_ok(hist, l0, start) {
                            let h2 = if bv.ends.len() > 0 { hist[k] } else { h };
                            assert(dinv::<F, S, F::Event, F::Error>(post, fview::<F>(&self.initial), start, log + cl, h2));
                            assert(self.dinv(log + cl, h2));
                            assert(t7_state::<F, S, F::Event, F::Error>(
                                self.engine@,
                                fview::<F>(&self.initial),
                                start,
                                hist[k],
                            ));
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
                self.tip = None;
                #[cfg(verus_keep_ghost)]
                proof_decl! {
                    let ghost pre = *self;
                }
                let tick = self.recover_via_bisection();
                #[cfg(verus_keep_ghost)]
                proof! {
                    lemma_recover_t7(*old(self), pre, *self, tick);
                    if tick is SourceError {
                        assert(self.caught_up_view() == old(self).caught_up_view());
                    }
                    if tick is Resynced {
                        self.engine.lemma_wf();
                        lemma_fresh_dinv::<F, S, F::Event, F::Error>(
                            self.engine@,
                            fview::<F>(&self.initial),
                            self.config.start_block,
                        );
                    }
                }
                tick
            }
            Err(ApplyError::Halted { .. } | ApplyError::Poisoned { .. }) => {
                self.tip = None;
                self.caught_up = false;
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
            // Unreachable: `scan` hands over a shaped batch whose boundary is at the cursor
            // block.
            Err(ApplyError::Shape(_) | ApplyError::BoundaryNumberMismatch { .. }) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(false);
                }
                self.tip = None;
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
    /// header. `Moved` when the head block moved during a walk, and `Behind` when the head
    /// lags the tip or the cursor block; the batch is then empty. Every result but a batch
    /// keeps the tip.
    ///
    /// Cheapest first: a head equal to the tip is one call; a head whose parent is the tip
    /// reads its own block by hash; a gap past the tip, when that costs fewer calls than
    /// the cursor walk, reads above the tip and then the tip; otherwise the walk starts at
    /// the cursor block, whose header the first answer carries. A walk reads at most `span`
    /// windows; one cut there with nothing found leaves a tip short of its head, and the
    /// next scan walks on from the tip's end, with no read of the tip when the head is the
    /// tip or its child.
    // One answer is one view. A tip is a head a scan covered: the chain its hash commits
    // to holds nothing left to fold above the cursor up to it (A1), so a view that holds
    // the tip needs no events or boundary read below it. Every walk ends by reading the
    // head block again, so under no ABA every call between the two reads saw the head's
    // chain. `seen` is the head the source answered.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        with
            Tracked(seen): Tracked<&mut Ghost<Head>>,
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            ({
                let (l0, hist) = (
                    sview_log::<S>(&old(self).source).len() as int,
                    sview_log::<S>(&final(self).source),
                );
                &&& *final(self) == (Driver {
                    source: final(self).source,
                    batch: final(self).batch,
                    scratch: final(self).scratch,
                    tip: final(self).tip,
                    last_checkpoint_block: final(self).last_checkpoint_block,
                    last_snapshot_block: final(self).last_snapshot_block,
                    ..*old(self)
                })
                &&& marks_lowered(*old(self), *final(self), r is Ok)
                &&& l0 < hist.len()
                &&& grew::<S, S::Event>(sview_log::<S>(&old(self).source), hist)
                &&& !(r matches Ok(Scan::Batch { .. })) ==> final(self).tip == old(self).tip
                &&& infallible::<S>(&old(self).source) ==> r is Ok && infallible::<S>(&final(self).source)
                &&& r matches Ok(Scan::Moved) ==> moved(hist, l0)
                &&& r matches Ok(Scan::Behind) ==> final(self).batch@.ends.len() == 0
                    && final(self).batch@.boundary is None && behind(
                    (*final(seen))@,
                    old(self).tip_view(),
                    old(self).engine@.cursor,
                    old(self).engine@.ring,
                ) && head_read(hist[l0], (*final(seen))@)
                &&& r matches Ok(Scan::Batch { .. }) ==> shaped_at(final(self).batch@, old(self).engine@.cursor)
                &&& r matches Ok(Scan::Batch { .. }) ==> boundary_read(
                    hist,
                    l0,
                    old(self).engine@.cursor,
                    old(self).engine@.ring.last(),
                    final(self).batch@.boundary,
                )
                &&& r matches Ok(Scan::Batch { .. }) ==> scanned::<S, S::Event>(
                    hist,
                    l0,
                    old(self).config.start_block,
                    old(self).engine@.cursor,
                    old(self).tip,
                    final(self).tip,
                    final(self).batch@,
                )
            }),
    ))]
    // A nested `if let`, not a `let` chain: Verus does not take `let` chains.
    #[allow(clippy::collapsible_if)]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    fn scan(&mut self) -> Result<Scan, S::Error> {
        self.batch.clear();
        let cursor = self.engine.cursor();
        #[cfg(verus_keep_ghost)]
        proof! {
            lemma_grew_refl::<S, S::Event>(sview_log::<S>(&self.source));
            lemma_grew_next::<S, S::Event>(sview_log::<S>(&old(self).source), sview_log::<S>(&self.source));
        }
        let head = self.source.head()?;
        let tip = self.tip;
        let window = self.source.window().max(1);
        let from = match cursor {
            Some(cursor) => cursor.block,
            None => self.config.start_block,
        };
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost l0 = sview_log::<S>(&old(self).source).len() as int;
            let ghost h1 = sview_log::<S>(&self.source);
            lemma_grew_next::<S, S::Event>(sview_log::<S>(&old(self).source), h1);
            assert(header(h1[l0], head.block.number) == Some(head.block));
            *seen = Ghost(head);
        }
        if let Some(tip) = tip {
            let full = tip.done == tip.at.number;
            if full && head.block == tip.at {
                #[cfg(verus_keep_ghost)]
                proof_decl! {
                    let ghost b0 = self.batch;
                }
                self.batch.boundary = self.cursor_block();
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::batch::lemma_batch_view(b0);
                    crate::batch::lemma_batch_view(self.batch);
                    lemma_triples_ignore_boundary(self.batch@, b0@, b0@.ends.len() as int);
                    assert(b0@.triples() =~= Seq::<(BlockRef, u32, F::Event)>::empty());
                    lemma_rung_same::<S, F::Event>(h1, l0, self.config.start_block, cursor, self.batch@, tip);
                }
                return Ok(Scan::Batch { capped: false });
            }
            let parent = head.parent == tip.at.hash
                && tip.at.number.checked_add(1) == Some(head.block.number);
            // The head's own view holds the tip when the tip is the head or its parent, so a
            // walk above the tip then needs no read of it.
            let implied = parent || head.block == tip.at;
            #[cfg(verus_keep_ghost)]
            proof! {
                broadcast use vstd::array::group_array_axioms;
                if parent {
                    assert(head.parent =~= tip.at.hash);
                }
                if implied {
                    lemma_carries::<S, S::Event>(head, tip.at, self.config.start_block);
                }
            }
            if parent && full {
                if self.next_block(head)? {
                    return Ok(Scan::Batch { capped: false });
                }
            } else if tip.done < head.block.number
                // A head at the tip's height with another hash disproves the tip.
                && (head.block == tip.at || tip.at.number < head.block.number)
                && walk_calls(tip.done + 1, head.block.number, window)
                    .saturating_add(if implied { 0 } else { 1 })
                    < walk_calls(from, head.block.number, window)
            {
                if let Some(read) = self.above_tip(tip, head.block, window, implied)? {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        if !read {
                            lemma_lost_moved(sview_log::<S>(&self.source), l0, l0 + 1, head.block);
                        }
                    }
                    return Ok(if read {
                        Scan::Batch {
                            capped: self.resuming(),
                        }
                    } else {
                        Scan::Moved
                    });
                }
            }
        } else {
            // No tip, as `engine_mut` leaves it, so the scan walks from the cursor. A rollback
            // through `engine_mut` leaves the cadence marks above the cursor: lower them, as
            // `roll_back_to` does, so neither the next checkpoint nor the next offer waits.
            // At or below the cursor they stay as they are.
            self.last_checkpoint_block = clamp(self.last_checkpoint_block, cursor);
            self.last_snapshot_block = clamp(self.last_snapshot_block, cursor);
        }
        // Every rung above needs a head above the tip, so a head below it, or below the
        // cursor block, lands here without another call.
        let below_tip = match tip {
            Some(tip) => head.block.number < tip.at.number,
            None => false,
        };
        let below_cursor = match cursor {
            Some(cursor) => head.block.number < cursor.block,
            None => false,
        };
        if (below_tip || below_cursor) && self.ring_agrees(head) {
            return Ok(Scan::Behind);
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost hw = sview_log::<S>(&self.source);
            lemma_grew_next::<S, S::Event>(sview_log::<S>(&old(self).source), hw);
            assert(hw[l0] == h1[l0]);
        }
        let read = self.cursor_walk(head.block, window, from)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            if !read {
                lemma_lost_moved(sview_log::<S>(&self.source), l0, hw.len() as int, head.block);
            }
        }
        Ok(if read {
            Scan::Batch {
                capped: self.resuming(),
            }
        } else {
            Scan::Moved
        })
    }

    /// True when the ring holds no hash other than `head`'s at its height, nor other than
    /// its parent's at the height below.
    // A lagging head that contradicts the ring goes to the walk, which reports the fork.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
        ensures
            r ==> ring_agrees(head, self.engine@.ring),
    ))]
    // Nested `if let`s, not `let` chains: Verus does not take `let` chains.
    #[allow(clippy::collapsible_if)]
    fn ring_agrees(&self, head: Head) -> bool {
        let number = head.block.number;
        #[cfg(verus_keep_ghost)]
        proof! {
            broadcast use vstd::array::group_array_axioms;
            self.engine.lemma_wf();
        }
        let ring = self.engine.ring();
        if let Some(hash) = ring.hash_at(number) {
            if hash != head.block.hash {
                return false;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(hash =~= head.block.hash);
            }
        }
        if let Some(parent) = number.checked_sub(1) {
            if let Some(hash) = ring.hash_at(parent) {
                if hash != head.parent {
                    return false;
                }
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(hash =~= head.parent);
                }
            }
        }
        true
    }

    /// `scan` with the head one block on top of the tip: reads the head block by its hash,
    /// and takes it only when every entry carries that hash. `Ok(false)` when some entry
    /// does not; the batch is then empty. The check catches a source that breaks A2 (ii) by
    /// answering another block's logs; T7 does not rest on it.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
            old(self).batch@.ends.len() == 0,
            old(self).batch@.boundary is None,
            sview_log::<S>(&old(self).source).len() > 0,
            header(sview_log::<S>(&old(self).source).last(), head.block.number) == Some(head.block),
            head.block.number > 0 ==> anc(head.block.hash, (head.block.number - 1) as u64).hash == head.parent,
            a1::<S, S::Event>(sview_log::<S>(&old(self).source).last()),
        ensures
            final(self).wf(),
            *final(self) == (Driver {
                source: final(self).source,
                batch: final(self).batch,
                scratch: final(self).scratch,
                tip: final(self).tip,
                ..*old(self)
            }),
            grew::<S, S::Event>(sview_log::<S>(&old(self).source), sview_log::<S>(&final(self).source)),
            !(r matches Ok(true)) ==> final(self).tip == old(self).tip && final(self).batch@.ends.len() == 0
                && final(self).batch@.boundary is None,
            infallible::<S>(&old(self).source) ==> r is Ok && infallible::<S>(&final(self).source),
            r matches Ok(true) ==> shaped_at(final(self).batch@, old(self).engine@.cursor),
            r matches Ok(true) ==> final(self).batch@.boundary == match old(self).engine@.cursor {
                Some(_) => Some(old(self).engine@.ring.last()),
                None => None,
            },
            r matches Ok(true) ==> forall|tip: Mark|
                tip.at.hash == head.parent && tip.at.number + 1 == head.block.number && tip.done == tip.at.number
                    ==> #[trigger] scanned::<S, S::Event>(
                    sview_log::<S>(&final(self).source),
                    sview_log::<S>(&old(self).source).len() - 1,
                    old(self).config.start_block,
                    old(self).engine@.cursor,
                    Some(tip),
                    final(self).tip,
                    final(self).batch@,
                ),
    ))]
    fn next_block(&mut self, head: Head) -> Result<bool, S::Error> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost l0 = sview_log::<S>(&old(self).source).len() - 1;
            lemma_grew_refl::<S, S::Event>(sview_log::<S>(&self.source));
            lemma_grew_next::<S, S::Event>(sview_log::<S>(&old(self).source), sview_log::<S>(&self.source));
        }
        self.scratch.clear();
        self.source.events_at(&head.block, &mut self.scratch)?;
        if !all_in(self.scratch.as_slice(), head.block) {
            return Ok(false);
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost got = self.scratch@;
            let ghost h2 = sview_log::<S>(&self.source);
            assert(got == got.subrange(0, got.len() as int));
            assert(h2[l0] == sview_log::<S>(&old(self).source).last());
            lemma_hash_entries::<S, S::Event>(h2[l0], head.block);
            lemma_re_one_view::<S, S::Event>(h2[l0], head.block.number as int, head.block.number as int);
        }
        if !self.scratch.is_empty() {
            group_into(&mut self.batch, &mut self.scratch);
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost b0 = self.batch;
            if got.len() == 0 {
                assert(b0@.triples() =~= got);
            }
        }
        self.batch.boundary = self.cursor_block();
        self.tip = Some(Mark {
            at: head.block,
            done: head.block.number,
        });
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::batch::lemma_batch_view(b0);
            crate::batch::lemma_batch_view(self.batch);
            lemma_triples_ignore_boundary(self.batch@, b0@, b0@.ends.len() as int);
            assert forall|tip: Mark|
                tip.at.hash == head.parent && tip.at.number + 1 == head.block.number && tip.done == tip.at.number
                    implies #[trigger] scanned::<
                S,
                S::Event,
            >(h2, l0, self.config.start_block, self.engine@.cursor, Some(tip), self.tip, self.batch@) by {
                lemma_rung_next::<S, F::Event>(h2, l0, self.config.start_block, self.engine@.cursor, tip, self.batch@, head, got);
            }
        }
        Ok(true)
    }

    /// `scan` with a gap past the tip: walks above the tip, then reads the tip back unless
    /// `implied`, and the head block again. `Ok(None)` when the tip is gone; the batch is
    /// then empty.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
            old(self).batch@.ends.len() == 0,
            old(self).batch@.boundary is None,
            tip.done < head.number,
            tip.at.number <= head.number,
            window >= 1,
            implied ==> carries::<S, S::Event>(head, tip.at, old(self).config.start_block),
        ensures
            final(self).wf(),
            *final(self) == (Driver {
                source: final(self).source,
                batch: final(self).batch,
                scratch: final(self).scratch,
                tip: final(self).tip,
                ..*old(self)
            }),
            grew::<S, S::Event>(sview_log::<S>(&old(self).source), sview_log::<S>(&final(self).source)),
            !(r matches Ok(Some(true))) ==> final(self).tip == old(self).tip,
            r matches Ok(None) ==> final(self).batch@.ends.len() == 0 && final(self).batch@.boundary is None,
            infallible::<S>(&old(self).source) ==> r is Ok && infallible::<S>(&final(self).source),
            r matches Ok(Some(false)) ==> lost(
                sview_log::<S>(&final(self).source),
                sview_log::<S>(&old(self).source).len() as int,
                head,
            ),
            r matches Ok(Some(true)) ==> shaped_at(final(self).batch@, old(self).engine@.cursor),
            r matches Ok(Some(true)) ==> final(self).batch@.boundary == match old(self).engine@.cursor {
                Some(_) => Some(old(self).engine@.ring.last()),
                None => None,
            },
            r matches Ok(Some(true)) ==> forall|l0: int|
                0 <= l0 && l0 + 1 == sview_log::<S>(&old(self).source).len() && header(
                    sview_log::<S>(&old(self).source)[l0],
                    head.number,
                ) == Some(head) && a1::<S, S::Event>(sview_log::<S>(&old(self).source)[l0]) ==> #[trigger] scanned::<
                    S,
                    S::Event,
                >(
                    sview_log::<S>(&final(self).source),
                    l0,
                    old(self).config.start_block,
                    old(self).engine@.cursor,
                    Some(tip),
                    final(self).tip,
                    final(self).batch@,
                ),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    fn above_tip(
        &mut self,
        tip: Mark,
        head: BlockRef,
        window: u64,
        implied: bool,
    ) -> Result<Option<bool>, S::Error> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost h1 = sview_log::<S>(&self.source);
            let ghost w0 = h1.len() as int;
            lemma_grew_refl::<S, S::Event>(h1);
            lemma_grew_next::<S, S::Event>(h1, h1);
        }
        let end = capped(tip.done + 1, head.number, self.span, window);
        let Some((_at, _reads, reached)) =
            self.walk(tip.done + 1, end, window, false, 0)?
        else {
            return Ok(Some(false));
        };
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost d2 = *self;
            let ghost h2 = sview_log::<S>(&self.source);
            let ghost wins = choose|wins: Seq<(int, int)>| #[trigger] walked::<S, S::Event>(
                h2,
                w0,
                (tip.done + 1) as u64,
                end,
                window,
                false,
                0,
                wins,
                d2.batch@.triples(),
                _at,
                _reads,
                reached,
            );
            lemma_grew_next::<S, S::Event>(h1, h2);
            lemma_grew_refl::<S, S::Event>(h2);
            lemma_grew_next::<S, S::Event>(h2, h2);
        }
        if !implied && self.source.header_at(tip.at.number)? != Some(tip.at) {
            self.batch.clear();
            return Ok(None);
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost h3 = sview_log::<S>(&self.source);
            lemma_grew_next::<S, S::Event>(h1, h3);
            lemma_grew_next::<S, S::Event>(h2, h3);
            lemma_grew_refl::<S, S::Event>(h3);
            lemma_grew_next::<S, S::Event>(h3, h3);
        }
        if self.source.header_at(head.number)? != Some(head) {
            self.batch.clear();
            #[cfg(verus_keep_ghost)]
            proof! {
                let hist = sview_log::<S>(&self.source);
                assert(header(hist[hist.len() - 1], head.number) != Some(head));
            }
            return Ok(Some(false));
        }
        self.batch.boundary = self.cursor_block();
        // A walk cut at the cap with nothing found covers the head's chain up to its end.
        if reached && (end == head.number || self.batch.is_empty()) {
            self.tip = Some(Mark {
                at: head,
                done: end,
            });
        } else {
            self.tip = None;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::batch::lemma_batch_view(d2.batch);
            crate::batch::lemma_batch_view(self.batch);
            lemma_triples_ignore_boundary(self.batch@, d2.batch@, d2.batch@.ends.len() as int);
            let hist = sview_log::<S>(&self.source);
            lemma_grew_next::<S, S::Event>(h1, hist);
            assert forall|l0: int|
                0 <= l0 && l0 + 1 == h1.len() && header(h1[l0], head.number) == Some(head) && a1::<S, S::Event>(h1[l0])
                    implies #[trigger] scanned::<S, S::Event>(
                hist,
                l0,
                self.config.start_block,
                self.engine@.cursor,
                Some(tip),
                self.tip,
                self.batch@,
            ) by {
                assert(hist[l0] == h1[l0]);
                lemma_rung_gap::<S, F::Event>(
                    hist,
                    h2,
                    h3,
                    l0,
                    w0,
                    self.config.start_block,
                    self.engine@.cursor,
                    tip,
                    self.tip,
                    self.batch@,
                    head,
                    end,
                    window,
                    wins,
                    _reads,
                    reached,
                    implied,
                );
            }
        }
        Ok(Some(true))
    }

    /// `scan` from the cursor block, at most `span` windows: the first window's answer carries
    /// that block's header, else `header_at` reads it; a walk of one window or more ends by
    /// reading the head block again. `Ok(false)` when the head block moved; the batch is then
    /// empty.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
            old(self).batch@.ends.len() == 0,
            old(self).batch@.boundary is None,
            window >= 1,
            from == match old(self).engine@.cursor {
                Some(c) => c.block,
                None => old(self).config.start_block,
            },
        ensures
            final(self).wf(),
            *final(self) == (Driver {
                source: final(self).source,
                batch: final(self).batch,
                scratch: final(self).scratch,
                tip: final(self).tip,
                ..*old(self)
            }),
            grew::<S, S::Event>(sview_log::<S>(&old(self).source), sview_log::<S>(&final(self).source)),
            !(r matches Ok(true)) ==> final(self).tip == old(self).tip,
            infallible::<S>(&old(self).source) ==> r is Ok && infallible::<S>(&final(self).source),
            r matches Ok(false) ==> lost(
                sview_log::<S>(&final(self).source),
                sview_log::<S>(&old(self).source).len() as int,
                head,
            ),
            r matches Ok(true) ==> shaped_at(final(self).batch@, old(self).engine@.cursor),
            r matches Ok(true) ==> boundary_read(
                sview_log::<S>(&final(self).source),
                sview_log::<S>(&old(self).source).len() as int,
                old(self).engine@.cursor,
                old(self).engine@.ring.last(),
                final(self).batch@.boundary,
            ),
            r matches Ok(true) ==> forall|l0: int, t0: Option<Mark>|
                0 <= l0 < sview_log::<S>(&old(self).source).len() && header(
                    sview_log::<S>(&old(self).source)[l0],
                    head.number,
                ) == Some(head) && (forall|q: int|
                    l0 <= q < sview_log::<S>(&old(self).source).len() ==> a1::<S, S::Event>(
                        #[trigger] sview_log::<S>(&old(self).source)[q],
                    )) && t0 != Some(Mark { at: head, done: head.number }) ==> #[trigger] scanned::<S, S::Event>(
                    sview_log::<S>(&final(self).source),
                    l0,
                    old(self).config.start_block,
                    old(self).engine@.cursor,
                    t0,
                    final(self).tip,
                    final(self).batch@,
                ),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    fn cursor_walk(
        &mut self,
        head: BlockRef,
        window: u64,
        from: u64,
    ) -> Result<bool, S::Error> {
        let cursor = self.engine.cursor();
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost hw = sview_log::<S>(&self.source);
            let ghost w0 = hw.len() as int;
            lemma_grew_refl::<S, S::Event>(hw);
            lemma_grew_next::<S, S::Event>(hw, hw);
        }
        let end = capped(from, head.number, self.span, window);
        let after = match cursor {
            Some(c) => c.log_index,
            None => 0,
        };
        let Some((at, reads, reached)) =
            self.walk(from, end, window, cursor.is_some(), after)?
        else {
            return Ok(false);
        };
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost d2 = *self;
            let ghost h2 = sview_log::<S>(&self.source);
            let ghost wins = choose|wins: Seq<(int, int)>| #[trigger] walked::<S, S::Event>(
                h2,
                w0,
                from,
                end,
                window,
                cursor is Some,
                after,
                wins,
                d2.batch@.triples(),
                at,
                reads,
                reached,
            );
            lemma_grew_next::<S, S::Event>(hw, h2);
            lemma_grew_refl::<S, S::Event>(h2);
            lemma_grew_next::<S, S::Event>(h2, h2);
        }
        let boundary = match cursor {
            Some(cursor) => match at {
                Some(at) => Some(at),
                None => self.source.header_at(cursor.block)?,
            },
            None => None,
        };
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost h3 = sview_log::<S>(&self.source);
            lemma_grew_next::<S, S::Event>(hw, h3);
            lemma_grew_next::<S, S::Event>(h2, h3);
            lemma_grew_refl::<S, S::Event>(h3);
            lemma_grew_next::<S, S::Event>(h3, h3);
        }
        if reads > 0 && self.source.header_at(head.number)? != Some(head) {
            self.batch.clear();
            #[cfg(verus_keep_ghost)]
            proof! {
                let hist = sview_log::<S>(&self.source);
                assert(header(hist[hist.len() - 1], head.number) != Some(head));
            }
            return Ok(false);
        }
        self.batch.boundary = boundary;
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Some(p) = cursor {
                let hf = sview_log::<S>(&self.source);
                if at is Some {
                    assert(hf[w0] == h2[w0]);
                    assert(boundary == header(hf[w0], p.block));
                } else {
                    let n = h2.len() as int;
                    assert(hf[n] == h3[n]);
                    assert(boundary == header(hf[n], p.block));
                }
            }
        }
        if reached && (end == head.number || self.batch.is_empty()) {
            self.tip = Some(Mark {
                at: head,
                done: end,
            });
        } else {
            self.tip = None;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::batch::lemma_batch_view(d2.batch);
            crate::batch::lemma_batch_view(self.batch);
            lemma_triples_ignore_boundary(self.batch@, d2.batch@, d2.batch@.ends.len() as int);
            let hist = sview_log::<S>(&self.source);
            lemma_grew_next::<S, S::Event>(hw, hist);
            assert forall|l0: int, t0: Option<Mark>|
                0 <= l0 < hw.len() && header(hw[l0], head.number) == Some(head) && (forall|q: int|
                    l0 <= q < hw.len() ==> a1::<S, S::Event>(#[trigger] hw[q])) && t0 != Some(
                    Mark { at: head, done: head.number },
                ) implies #[trigger] scanned::<
                S,
                S::Event,
            >(hist, l0, self.config.start_block, cursor, t0, self.tip, self.batch@) by {
                assert(hist[l0] == hw[l0]);
                assert forall|q: int| l0 <= q < hist.len() implies a1::<S, S::Event>(#[trigger] hist[q]) by {
                    if q < hw.len() {
                        assert(hist[q] == hw[q]);
                    }
                }
                lemma_rung_walk::<S, F::Event>(
                    hist,
                    h2,
                    h3,
                    l0,
                    w0,
                    self.config.start_block,
                    cursor,
                    t0,
                    self.tip,
                    self.batch@,
                    head,
                    from,
                    end,
                    window,
                    after,
                    wins,
                    at,
                    reads,
                    reached,
                );
            }
        }
        Ok(true)
    }

    /// True when the tip covers less than its head: the next scan walks on from its end.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            r == (self.tip matches Some(m) && m.done < m.at.number),
    ))]
    fn resuming(&self) -> bool {
        match self.tip {
            Some(tip) => tip.done < tip.at.number,
            None => false,
        }
    }

    /// The cursor block as the ring holds it: the boundary a scan anchored on the tip
    /// reports.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
        ensures
            r == match self.engine@.cursor {
                Some(_) => Some(self.engine@.ring.last()),
                None => None,
            },
            r is Some ==> r.unwrap().number == self.engine@.cursor.unwrap().block,
    ))]
    fn cursor_block(&self) -> Option<BlockRef> {
        let cursor = self.engine.cursor()?;
        #[cfg(verus_keep_ghost)]
        proof! {
            self.engine.lemma_wf();
            let r = self.engine@.ring;
            assert(r[r.len() - 1].number == cursor.block);
        }
        let hash = self.engine.ring().hash_at(cursor.block)?;
        Some(BlockRef {
            number: cursor.block,
            hash,
        })
    }

    /// Reads `events_in` windows from `from` through `hi` and groups the first one with an
    /// entry above the floor into the batch. With `floor`, the floor is block `from` itself:
    /// its entries up to log index `after` are dropped and the first answer's header for it
    /// is returned. Also
    /// returns the windows read, capped at 2, and whether the last one reached `hi`.
    /// `Ok(None)` when an answer holds an entry outside its window, or two headers at the
    /// floor; the batch is then empty.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
            old(self).batch@.ends.len() == 0,
            old(self).batch@.boundary is None,
            window >= 1,
        ensures
            final(self).wf(),
            final(self).batch@.boundary is None,
            *final(self) == (Driver {
                source: final(self).source,
                batch: final(self).batch,
                scratch: final(self).scratch,
                ..*old(self)
            }),
            grew::<S, S::Event>(sview_log::<S>(&old(self).source), sview_log::<S>(&final(self).source)),
            r matches Ok(o) ==> o is Some,
            r matches Ok(Some(p)) ==> (p.0 matches Some(b) ==> floor),
            r matches Ok(Some(p)) ==> p.1 <= 2,
            r is Ok ==> final(self).batch@.shaped(),
            infallible::<S>(&old(self).source) ==> r is Ok && infallible::<S>(&final(self).source),
            r matches Ok(Some(p)) ==> exists|wins: Seq<(int, int)>|
                #[trigger] walked::<S, S::Event>(
                    sview_log::<S>(&final(self).source),
                    sview_log::<S>(&old(self).source).len() as int,
                    from,
                    hi,
                    window,
                    floor,
                    after,
                    wins,
                    final(self).batch@.triples(),
                    p.0,
                    p.1,
                    p.2,
                ),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    fn walk(
        &mut self,
        from: u64,
        hi: u64,
        window: u64,
        floor: bool,
        after: u64,
    ) -> Result<Option<Walk>, S::Error> {
        let mut next = from;
        let mut at: Option<BlockRef> = None;
        let mut reads = 0u8;
        let mut reached = false;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost l0 = sview_log::<S>(&old(self).source).len() as int;
            let ghost d1 = *self;
            let ghost mut wins: Seq<(int, int)> = Seq::empty();
            assert(d1.batch@.triples() == Seq::<(BlockRef, u32, F::Event)>::empty());
            assert(sview_log::<S>(&self.source).subrange(0, l0) =~= sview_log::<S>(&old(self).source));
            lemma_grew_refl::<S, S::Event>(sview_log::<S>(&self.source));
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                // Loops do not see the fn's requires: carry wf and d1's link to old.
                old(self).wf(),
                d1 == *old(self),
                l0 == sview_log::<S>(&old(self).source).len(),
                d1.batch@.triples().len() == 0,
                d1.batch@.ends.len() == 0,
                *self == (Driver { source: self.source, scratch: self.scratch, batch: self.batch, ..d1 }),
                self.batch@.wf(),
                self.batch@.shaped(),
                self.batch@.boundary is None,
                sview_log::<S>(&self.source).len() == l0 + wins.len(),
                sview_log::<S>(&self.source).subrange(0, l0) == sview_log::<S>(&old(self).source),
                forall|k: int| l0 <= k < sview_log::<S>(&self.source).len()
                    ==> a1::<S, S::Event>(#[trigger] sview_log::<S>(&self.source)[k]),
                grew::<S, S::Event>(sview_log::<S>(&old(self).source), sview_log::<S>(&self.source)),
                infallible::<S>(&old(self).source) ==> infallible::<S>(&self.source),
                window >= 1,
                scan_windows(wins, from as int, window, hi),
                reads as int == if wins.len() < 2 { wins.len() as int } else { 2 },
                reached == (wins.len() > 0 && wins.last().1 == hi),
                at matches Some(b) ==> floor && wins.len() > 0 && header(
                    sview_log::<S>(&self.source)[l0],
                    from,
                ) == Some(b),
                floor && wins.len() > 0 && at is None ==> block_entries::<S, S::Event>(
                    sview_log::<S>(&self.source)[l0],
                    from,
                ).len() == 0,
            invariant_except_break
                self.batch == d1.batch,
                forall|i: int| 0 <= i < wins.len() ==> range_entries::<S, S::Event>(
                    sview_log::<S>(&self.source)[l0 + i],
                    wlo(wins, floor, i),
                    (#[trigger] wins[i]).1,
                ).len() == 0,
                next as int == if wins.len() == 0 { from as int } else { wins.last().1 + 1 },
                wins.len() > 0 ==> self.batch@.triples().to_multiset() == range_entries::<S, S::Event>(
                    sview_log::<S>(&self.source)[l0 + wins.len() - 1],
                    wlo(wins, floor, wins.len() - 1),
                    wins.last().1,
                ).to_multiset().add(fkept::<S, S::Event>(
                    sview_log::<S>(&self.source)[l0 + wins.len() - 1],
                    floor && wins.len() == 1,
                    from,
                    after,
                )),
            ensures
                self.batch@.wf(),
                self.batch@.shaped(),
                self.batch@.boundary is None,
                *self == (Driver { source: self.source, scratch: self.scratch, batch: self.batch, ..d1 }),
                sview_log::<S>(&self.source).len() == l0 + wins.len(),
                sview_log::<S>(&self.source).subrange(0, l0) == sview_log::<S>(&old(self).source),
                forall|k: int| l0 <= k < sview_log::<S>(&self.source).len()
                    ==> a1::<S, S::Event>(#[trigger] sview_log::<S>(&self.source)[k]),
                grew::<S, S::Event>(sview_log::<S>(&old(self).source), sview_log::<S>(&self.source)),
                infallible::<S>(&old(self).source) ==> infallible::<S>(&self.source),
                scan_windows(wins, from as int, window, hi),
                reads as int == if wins.len() < 2 { wins.len() as int } else { 2 },
                reached == (wins.len() > 0 && wins.last().1 == hi),
                at matches Some(b) ==> floor && wins.len() > 0 && header(
                    sview_log::<S>(&self.source)[l0],
                    from,
                ) == Some(b),
                floor && wins.len() > 0 && at is None ==> block_entries::<S, S::Event>(
                    sview_log::<S>(&self.source)[l0],
                    from,
                ).len() == 0,
                forall|i: int| 0 <= i < wins.len() - 1 ==> range_entries::<S, S::Event>(
                    sview_log::<S>(&self.source)[l0 + i],
                    wlo(wins, floor, i),
                    (#[trigger] wins[i]).1,
                ).len() == 0,
                wins.len() > 0 ==> self.batch@.triples().to_multiset() == range_entries::<S, S::Event>(
                    sview_log::<S>(&self.source)[l0 + wins.len() - 1],
                    wlo(wins, floor, wins.len() - 1),
                    wins.last().1,
                ).to_multiset().add(fkept::<S, S::Event>(
                    sview_log::<S>(&self.source)[l0 + wins.len() - 1],
                    floor && wins.len() == 1,
                    from,
                    after,
                )),
                wins.len() == 0 ==> self.batch@.triples().len() == 0 && from > hi,
                self.batch@.triples().len() == 0 && wins.len() > 0 ==> wins.last().1 == hi,
            decreases hi as int + 1 - next as int,
        ))]
        while next <= hi {
            let to = hi.min(next.saturating_add(window - 1));
            reached = to == hi;
            self.scratch.clear();
            #[cfg(verus_keep_ghost)]
            proof! {
                wins = wins.push((next as int, to as int));
                lemma_grew_next::<S, S::Event>(sview_log::<S>(&old(self).source), sview_log::<S>(&self.source));
            }
            self.source.events_in(next, to, &mut self.scratch)?;
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost v = sview_log::<S>(&self.source).last();
                let ghost got = self.scratch@;
                assert(got == got.subrange(0, got.len() as int));
                assert(got.to_multiset() == range_entries::<S, S::Event>(v, next as int, to as int).to_multiset());
                assert(sview_log::<S>(&self.source)[l0 + wins.len() - 1] == v);
                lemma_answer_within::<S, S::Event>(v, next as int, to as int, got);
            }
            if floor && reads == 0 {
                let (floor_at, below) = take_floor(&mut self.scratch, next, after);
                if below {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        lemma_floor::<S, S::Event>(v, next, to, got, self.scratch@, after);
                    }
                    return Ok(None);
                }
                at = floor_at;
                #[cfg(verus_keep_ghost)]
                proof! {
                    lemma_floor::<S, S::Event>(v, next, to, got, self.scratch@, after);
                    assert(wlo(wins, floor, 0) == next + 1);
                    if let Some(b) = at {
                        let i = choose|i: int| 0 <= i < got.len() && #[trigger] got[i].0 == b;
                        assert(got[i].0.number == next);
                    }
                }
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                broadcast use vstd::multiset::group_multiset_axioms;
                let fk = fkept::<S, S::Event>(v, floor && wins.len() == 1, from, after);
                if !(floor && wins.len() == 1) {
                    assert(fk =~= vstd::multiset::Multiset::empty());
                }
                assert(self.scratch@.to_multiset() =~= range_entries::<S, S::Event>(
                    v,
                    wlo(wins, floor, wins.len() - 1),
                    to as int,
                ).to_multiset().add(fk));
                assert(forall|x: (BlockRef, u32, S::Event)| #[trigger] self.scratch@.to_multiset().count(x)
                    <= got.to_multiset().count(x));
                vstd::seq_lib::to_multiset_len(self.scratch@);
                vstd::seq_lib::to_multiset_len(range_entries::<S, S::Event>(
                    v,
                    wlo(wins, floor, wins.len() - 1),
                    to as int,
                ));
                lemma_re_one_view::<S, S::Event>(v, next as int, to as int);
                lemma_one_view_sub(got.to_multiset(), self.scratch@.to_multiset());
            }
            if reads < 2 {
                reads += 1;
            }
            if !self.scratch.is_empty() {
                #[cfg(verus_keep_ghost)]
                proof_decl! {
                    let ghost sc = self.scratch@;
                }
                group_into(&mut self.batch, &mut self.scratch);
                #[cfg(verus_keep_ghost)]
                proof! {
                    vstd::seq_lib::to_multiset_len(self.batch@.triples());
                    assert(forall|x: (BlockRef, u32, S::Event)| #[trigger] self.batch@.triples().to_multiset().count(x)
                        <= got.to_multiset().count(x)) by {
                        assert(self.batch@.triples().to_multiset() == sc.to_multiset());
                    }
                    lemma_sub_within(next as int, to as int, got, self.batch@.triples());
                    lemma_triples_within(self.batch@, next, to);
                }
                if !self.batch.blocks_within(next, to) {
                    self.batch.clear();
                    return Ok(None);
                }
                break;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(self.batch@.triples() =~= self.scratch@);
            }
            let Some(after) = to.checked_add(1) else {
                break;
            };
            next = after;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(walked::<S, S::Event>(
                sview_log::<S>(&self.source),
                l0,
                from,
                hi,
                window,
                floor,
                after,
                wins,
                self.batch@.triples(),
                at,
                reads,
                reached,
            ));
            assert(*self == (Driver { source: self.source, scratch: self.scratch, batch: self.batch, ..*old(self) }));
            assert(grew::<S, S::Event>(sview_log::<S>(&old(self).source), sview_log::<S>(&self.source)));
        }
        let read = (at, reads, reached);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(walked::<S, S::Event>(
                sview_log::<S>(&self.source),
                sview_log::<S>(&old(self).source).len() as int,
                from,
                hi,
                window,
                floor,
                after,
                wins,
                self.batch@.triples(),
                read.0,
                read.1,
                read.2,
            ));
        }
        Ok(Some(read))
    }

    /// Bisects the observed ring for the deepest still-canonical block, then rolls back.
    // A RolledBack restore sits at or below a ring block some probe's view confirmed.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
            old(self).synced(),
        ensures
            recovered(*old(self), *final(self), r),
            r is SourceError ==> !infallible::<S>(&old(self).source),
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
            r is Resynced ==> final(self).dinv(Seq::empty(), Map::empty()),
            r is SourceError ==> !old(self).source_infallible() || moved(
                final(self).source_log(),
                old(self).source_log().len() as int,
            ),
            r is Idle ==> final(self).caught_up_view(),
            r is Progressed || r is RolledBack || r is Resynced || r is Terminal ==> !final(self).caught_up_view(),
            r is Behind || r is SourceError ==> final(self).caught_up_view() == old(self).caught_up_view(),
            r is Behind ==> final(self).engine_view() == old(self).engine_view() && final(self).tip_view()
                == old(self).tip_view() && final(self).tip_same(*old(self)) && exists|hd: Head| #[trigger] behind(
                hd,
                old(self).tip_view(),
                old(self).engine_view().cursor,
                old(self).engine_view().ring,
            ) && head_read(final(self).source_log()[old(self).source_log().len() as int], hd),
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
            r.last_verified == self.engine_view().last_verified,
            r.engine == self.engine_view().status,
            r.caught_up == self.caught_up_view(),
            r.skips == self.engine_view().skips,
            !self.synced() ==> r.durable_cursor is None,
            self.durable_ok() ==> opt_le(r.durable_cursor, r.cursor),
            r.durability_lost == self.durability_lost_view(),
            r.generation == self.generation_view(),
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

/// True when every entry lies in `block`.
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == forall|i: int| 0 <= i < entries@.len() ==> #[trigger] entries@[i].0 == block,
))]
fn all_in<E>(entries: &[(BlockRef, u32, E)], block: BlockRef) -> bool {
    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= entries@.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] entries@[j].0 == block,
        decreases entries@.len() - i,
    ))]
    while i < entries.len() {
        if entries[i].0 != block {
            return false;
        }
        i += 1;
    }
    true
}

/// A walk's result: the first answer's header for the floor block, the windows read (at
/// most 2), and whether the last one reached the walk's end.
type Walk = (Option<BlockRef>, u8, bool);

/// `events_in` calls a walk over `from..=hi` makes, plus the head read that follows.
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires
        window >= 1,
))]
fn walk_calls(from: u64, hi: u64, window: u64) -> u64 {
    if from > hi {
        return 0;
    }
    ((hi - from) / window).saturating_add(2)
}

/// The last block of `span` windows of `window` blocks from `from`, or `hi` when that is
/// lower.
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        span >= 1,
        window >= 1,
    ensures
        r <= hi,
        from <= hi ==> from <= r,
))]
fn capped(from: u64, hi: u64, span: u64, window: u64) -> u64 {
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(span * window >= 1) by (nonlinear_arith)
            requires
                span >= 1,
                window >= 1,
        ;
    }
    hi.min(from.saturating_add(span.saturating_mul(window) - 1))
}

/// Drops the entries at or below block `floor`, except those at `floor` after log index
/// `after`, in place and out of order, and returns the header one of them carried at
/// `floor`, and whether the answer is refused: one lay below `floor`, or two carried
/// different headers at it.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        forall|x: (BlockRef, u32, E)| #[trigger] final(entries)@.to_multiset().count(x)
            == if past_floor(x, floor, after) { old(entries)@.to_multiset().count(x) } else { 0 },
        r.0 matches Some(b) ==> b.number == floor && exists|i: int|
            0 <= i < old(entries)@.len() && #[trigger] old(entries)@[i].0 == b,
        r.0 is None ==> forall|i: int| 0 <= i < old(entries)@.len() ==> #[trigger] old(entries)@[i].0.number != floor,
        !r.1 ==> forall|i: int| 0 <= i < old(entries)@.len() ==> (#[trigger] old(entries)@[i]).0.number >= floor,
        !r.1 ==> (r.0 matches Some(b) ==> forall|i: int|
            0 <= i < old(entries)@.len() && (#[trigger] old(entries)@[i]).0.number == floor ==> old(entries)@[i].0 == b),
        r.1 ==> (exists|i: int| 0 <= i < old(entries)@.len() && (#[trigger] old(entries)@[i]).0.number < floor) || exists|
            i: int,
            j: int,
        |
            0 <= i < old(entries)@.len() && 0 <= j < old(entries)@.len() && (#[trigger] old(entries)@[i]).0.number
                == floor && (#[trigger] old(entries)@[j]).0.number == floor && old(entries)@[i].0 != old(entries)@[j].0,
))]
// A nested `if let`, not a `let` chain: Verus does not take `let` chains.
#[allow(clippy::collapsible_if)]
fn take_floor<E>(
    entries: &mut Vec<(BlockRef, u32, E)>,
    floor: u64,
    after: u64,
) -> (Option<BlockRef>, bool) {
    let mut at: Option<BlockRef> = None;
    let mut below = false;
    let mut i = entries.len();
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost s = entries@;
        let ghost mut gone: Seq<(BlockRef, u32, E)> = Seq::empty();
        assert(entries@.to_multiset().add(gone.to_multiset()) =~= s.to_multiset()) by {
            broadcast use vstd::multiset::group_multiset_axioms;
            vstd::seq_lib::to_multiset_len(gone);
        }
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= entries@.len() <= s.len(),
            s == old(entries)@,
            entries@.subrange(0, i as int) == s.subrange(0, i as int),
            forall|j: int| i <= j < entries@.len() ==> past_floor(#[trigger] entries@[j], floor, after),
            forall|j: int| 0 <= j < gone.len() ==> !past_floor(#[trigger] gone[j], floor, after),
            entries@.to_multiset().add(gone.to_multiset()) == s.to_multiset(),
            at matches Some(b) ==> b.number == floor && exists|j: int| i <= j < s.len() && #[trigger] s[j].0 == b,
            at is None ==> forall|j: int| i <= j < s.len() ==> #[trigger] s[j].0.number != floor,
            !below ==> forall|j: int| i <= j < s.len() ==> (#[trigger] s[j]).0.number >= floor,
            !below ==> (at matches Some(b) ==> forall|j: int|
                i <= j < s.len() && (#[trigger] s[j]).0.number == floor ==> s[j].0 == b),
            below ==> (exists|j: int| i <= j < s.len() && (#[trigger] s[j]).0.number < floor) || exists|j: int, k: int|
                i <= j < s.len() && i <= k < s.len() && (#[trigger] s[j]).0.number == floor && (#[trigger] s[k]).0.number
                    == floor && s[j].0 != s[k].0,
        decreases i,
    ))]
    while i > 0 {
        i -= 1;
        let mut gone_now = false;
        if entries[i].0.number <= floor {
            if entries[i].0.number == floor {
                // Two headers at the floor are two blocks at one height in one answer.
                match at {
                    Some(seen) => {
                        if seen != entries[i].0 {
                            below = true;
                        }
                    }
                    None => at = Some(entries[i].0),
                }
                // An entry after the cursor is one the engine has not folded yet.
                gone_now = entries[i].1 as u64 <= after;
            } else {
                below = true;
                gone_now = true;
            }
        }
        if gone_now {
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost pre = entries@;
                assert(pre[i as int] == s[i as int]) by {
                    assert(pre.subrange(0, i + 1)[i as int] == s.subrange(0, i + 1)[i as int]);
                }
            }
            entries.swap_remove(i);
            #[cfg(verus_keep_ghost)]
            proof! {
                broadcast use vstd::multiset::group_multiset_axioms;
                let u = pre.update(i as int, pre.last());
                vstd::seq_lib::to_multiset_update(pre, i as int, pre.last());
                vstd::seq_lib::to_multiset_remove(u, u.len() - 1);
                assert(u.remove(u.len() - 1) =~= entries@);
                vstd::seq_lib::to_multiset_contains(pre, pre[i as int]);
                vstd::seq_lib::to_multiset_contains(pre, pre.last());
                vstd::seq_lib::to_multiset_build(gone, pre[i as int]);
                gone = gone.push(pre[i as int]);
                assert(entries@.to_multiset().add(gone.to_multiset()) =~= s.to_multiset());
                assert(entries@.subrange(0, i as int) =~= s.subrange(0, i as int)) by {
                    assert forall|j: int| 0 <= j < i implies entries@[j] == s[j] by {
                        assert(pre.subrange(0, i + 1)[j] == s.subrange(0, i + 1)[j]);
                    }
                }
            }
        } else {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(entries@[i as int] == s[i as int]) by {
                    assert(entries@.subrange(0, i + 1)[i as int] == s.subrange(0, i + 1)[i as int]);
                }
                assert(entries@.subrange(0, i as int) =~= s.subrange(0, i as int)) by {
                    assert forall|j: int| 0 <= j < i implies entries@[j] == s[j] by {
                        assert(entries@.subrange(0, i + 1)[j] == s.subrange(0, i + 1)[j]);
                    }
                }
            }
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        broadcast use vstd::multiset::group_multiset_axioms;
        assert forall|x: (BlockRef, u32, E)| #[trigger] entries@.to_multiset().count(x)
            == if past_floor(x, floor, after) { s.to_multiset().count(x) } else { 0 } by {
            vstd::seq_lib::to_multiset_contains(entries@, x);
            vstd::seq_lib::to_multiset_contains(gone, x);
            if past_floor(x, floor, after) {
                if gone.contains(x) {
                    let j = choose|j: int| 0 <= j < gone.len() && gone[j] == x;
                }
            } else if entries@.contains(x) {
                let j = choose|j: int| 0 <= j < entries@.len() && entries@[j] == x;
            }
        }
    }
    (at, below)
}

/// `group_into`'s sort key. `MAX - x` reverses each lane, so the sort is descending
/// without `Reverse`.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r.0 == u64::MAX - e.0.number,
        r.1 == u32::MAX - e.1,
))]
fn descending<E>(e: &(BlockRef, u32, E)) -> (u64, u32) {
    (u64::MAX - e.0.number, u32::MAX - e.1)
}

/// Moves `entries` into `batch`, one span per run of equal `BlockRef`s, so two hashes
/// at one height become two equal-number spans that `Batch::validate` rejects.
///
/// Sorted by descending position and popped from the tail, the entries leave in
/// ascending order with no intermediate buffer; the sort is in place. Entries one view
/// could answer give a batch `validate` accepts.
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
        one_view(old(entries)@.to_multiset()) ==> final(batch)@.shaped(),
))]
// `loop` + `match`, not `while let`: Verus keeps no facts after a `while let` loop.
#[allow(clippy::while_let_loop)]
fn group_into<E>(batch: &mut Batch<E>, entries: &mut Vec<(BlockRef, u32, E)>) {
    entries.sort_unstable_by_key(descending);
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost s = entries@;
        let ghost ok = one_view(old(entries)@.to_multiset());
        assert(batch@.triples() =~= Seq::empty());
        if ok {
            assert forall|i: int, j: int| 0 <= i < j < s.len() implies #[trigger] key_le(s[i], s[j]) by {
                let (a, b) = choose|a: (u64, u32), b: (u64, u32)| descending::<E>.ensures((&s[i],), a)
                    && descending::<E>.ensures((&s[j],), b) && vstd::std_specs::cmp::OrdSpec::cmp_spec(&a, &b) != core::cmp::Ordering::Greater;
            }
            lemma_sorted_desc(s);
        }
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
            ok ==> popped_desc(batch@, s, entries@.len() as int),
        ensures
            batch@.wf(),
            batch@.boundary == old(batch)@.boundary,
            entries@.len() == 0,
            batch@.triples() =~= s.reverse(),
            ok ==> batch@.shaped(),
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
                    if ok {
                        lemma_push_desc(pre, batch@, before, entries@, block, s);
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

        fn head(&mut self) -> Result<Head, PollFailure> {
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

        fn events_at(
            &mut self,
            block: &BlockRef,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            self.inner.events_at(block, out)
        }

        fn horizon(&self) -> ReplayHorizon {
            self.inner.horizon()
        }

        fn window(&self) -> u64 {
            self.inner.window()
        }
    }

    /// Wraps a scripted chain, counting every call. With a `period`, every `period`-th call
    /// fails; with a `budget`, every call past it fails until the budget is set again.
    struct Counted {
        inner: ScriptedChain,
        calls: u32,
        period: Option<u32>,
        budget: Option<u32>,
    }

    impl Counted {
        /// Counts one call, and fails it when the period or the budget says so.
        fn call(&mut self) -> Result<(), PollFailure> {
            self.calls += 1;
            let spent = match &mut self.budget {
                Some(0) => true,
                Some(left) => {
                    *left -= 1;
                    false
                }
                None => false,
            };
            if spent
                || self
                    .period
                    .is_some_and(|period| self.calls.is_multiple_of(period))
            {
                return Err(PollFailure);
            }
            Ok(())
        }
    }

    impl Source for Counted {
        type Event = u64;
        type Error = PollFailure;

        fn head(&mut self) -> Result<Head, PollFailure> {
            self.call()?;
            self.inner.head()
        }

        fn header_at(&mut self, number: u64) -> Result<Option<BlockRef>, PollFailure> {
            self.call()?;
            self.inner.header_at(number)
        }

        fn events_in(
            &mut self,
            from: u64,
            to: u64,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            self.call()?;
            self.inner.events_in(from, to, out)
        }

        fn events_at(
            &mut self,
            block: &BlockRef,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            self.call()?;
            self.inner.events_at(block, out)
        }

        fn window(&self) -> u64 {
            self.inner.window()
        }
    }

    /// Load balancer over two nodes: `head` comes from the up-to-date one, and while
    /// `lagging` is set every other call goes to that older copy, which answers a range
    /// past its own head with the blocks it holds.
    struct Lagging {
        inner: ScriptedChain,
        lagging: Option<ScriptedChain>,
    }

    impl Lagging {
        fn node(&mut self) -> &mut ScriptedChain {
            self.lagging.as_mut().unwrap_or(&mut self.inner)
        }
    }

    impl Source for Lagging {
        type Event = u64;
        type Error = PollFailure;

        fn head(&mut self) -> Result<Head, PollFailure> {
            self.inner.head()
        }

        fn header_at(&mut self, number: u64) -> Result<Option<BlockRef>, PollFailure> {
            self.node().header_at(number)
        }

        fn events_in(
            &mut self,
            from: u64,
            to: u64,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            self.node().events_in(from, to, out)
        }

        fn events_at(
            &mut self,
            block: &BlockRef,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            self.node().events_at(block, out)
        }

        fn window(&self) -> u64 {
            self.inner.window()
        }
    }

    /// Proxy in front of a lagging node that answers a range starting past that node's
    /// head with the logs of its head block.
    struct Proxy(Lagging);

    impl Source for Proxy {
        type Event = u64;
        type Error = PollFailure;

        fn head(&mut self) -> Result<Head, PollFailure> {
            self.0.head()
        }

        fn header_at(&mut self, number: u64) -> Result<Option<BlockRef>, PollFailure> {
            self.0.header_at(number)
        }

        fn events_in(
            &mut self,
            from: u64,
            to: u64,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            if let Some(tip) = self.0.lagging.as_ref().and_then(ScriptedChain::tip)
                && from > tip.number
            {
                return self.0.events_in(tip.number, tip.number, out);
            }
            self.0.events_in(from, to, out)
        }

        fn events_at(
            &mut self,
            block: &BlockRef,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            self.0.events_at(block, out)
        }

        fn window(&self) -> u64 {
            self.0.window()
        }
    }

    /// Load balancer over two nodes: each call goes to `b` when the next queued route is
    /// `b'B'`, else to `a`. A node errs on a range past its own head, except that with
    /// `proxy` a range starting past `b`'s head is answered with the logs of that head
    /// block. Counts every call.
    struct Pool {
        a: ScriptedChain,
        b: ScriptedChain,
        route: Vec<u8>,
        proxy: bool,
        calls: u32,
    }

    impl Pool {
        fn new(a: ScriptedChain, b: ScriptedChain) -> Self {
            Self {
                a,
                b,
                route: Vec::new(),
                proxy: false,
                calls: 0,
            }
        }

        /// The node the next call goes to, and whether it is `b`.
        fn pick(&mut self) -> (bool, &mut ScriptedChain) {
            self.calls += 1;
            let to_b = !self.route.is_empty() && self.route.remove(0) == b'B';
            if to_b {
                (true, &mut self.b)
            } else {
                (false, &mut self.a)
            }
        }
    }

    /// Node a, with node b's logs added to every range b holds, listed after a's or
    /// first.
    struct Merge {
        a: ScriptedChain,
        b: ScriptedChain,
        merge: bool,
        b_first: bool,
    }

    impl Source for Merge {
        type Event = u64;
        type Error = PollFailure;

        fn head(&mut self) -> Result<Head, PollFailure> {
            self.a.head()
        }

        fn header_at(&mut self, number: u64) -> Result<Option<BlockRef>, PollFailure> {
            self.a.header_at(number)
        }

        fn events_in(
            &mut self,
            from: u64,
            to: u64,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            let top = self.b.tip().map_or(0, |tip| tip.number);
            if !self.merge || to > top {
                return self.a.events_in(from, to, out);
            }
            if self.b_first {
                self.b.events_in(from, to, out)?;
                self.a.events_in(from, to, out)
            } else {
                self.a.events_in(from, to, out)?;
                self.b.events_in(from, to, out)
            }
        }

        fn events_at(
            &mut self,
            block: &BlockRef,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            self.a.events_at(block, out)
        }

        fn window(&self) -> u64 {
            self.a.window()
        }
    }

    impl Source for Pool {
        type Event = u64;
        type Error = PollFailure;

        fn head(&mut self) -> Result<Head, PollFailure> {
            self.pick().1.head()
        }

        fn header_at(&mut self, number: u64) -> Result<Option<BlockRef>, PollFailure> {
            self.pick().1.header_at(number)
        }

        fn events_in(
            &mut self,
            from: u64,
            to: u64,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            let proxy = self.proxy;
            let (to_b, node) = self.pick();
            let top = node.tip().map_or(0, |tip| tip.number);
            if to_b && proxy && from > top {
                return node.events_in(top, top, out);
            }
            if to > top {
                return Err(PollFailure);
            }
            node.events_in(from, to, out)
        }

        fn events_at(
            &mut self,
            block: &BlockRef,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            self.pick().1.events_at(block, out)
        }

        fn window(&self) -> u64 {
            self.a.window()
        }
    }

    /// Source that serves the same one-event block for every block asked for and every range
    /// that reaches it, so each read above the block is served it again.
    struct Stuck {
        block: BlockRef,
    }

    impl Stuck {
        /// The head, one past the block, so the scan keeps querying and keeps being
        /// re-served it.
        fn head_block(&self) -> BlockRef {
            BlockRef {
                number: self.block.number + 1,
                hash: [0; 32],
            }
        }
    }

    impl Source for Stuck {
        type Event = u64;
        type Error = PollFailure;

        fn head(&mut self) -> Result<Head, PollFailure> {
            Ok(Head {
                block: self.head_block(),
                parent: self.block.hash,
            })
        }

        fn header_at(&mut self, number: u64) -> Result<Option<BlockRef>, PollFailure> {
            let head = self.head_block();
            Ok(Some(if number == head.number {
                head
            } else {
                self.block
            }))
        }

        fn events_in(
            &mut self,
            _from: u64,
            to: u64,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            if to >= self.block.number {
                out.push((self.block, 0, 1));
            }
            Ok(())
        }

        fn events_at(
            &mut self,
            _block: &BlockRef,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            out.push((self.block, 0, 1));
            Ok(())
        }

        fn window(&self) -> u64 {
            1
        }
    }

    /// Replaces the last `depth` blocks with one block per entry of `events`.
    fn reorg_to(chain: &mut ScriptedChain, depth: usize, events: &[u64]) {
        let blocks: Vec<[u64; 1]> = events.iter().map(|event| [*event]).collect();
        let slices: Vec<&[u64]> = blocks.iter().map(|block| block.as_slice()).collect();
        chain.reorg(depth, &slices);
    }

    /// One `events_in` answer: header, log index, event.
    type Answer = Vec<(BlockRef, u32, u64)>;

    /// Scripted chain that misbehaves once, inside a single scan.
    struct Adversary {
        inner: ScriptedChain,
        /// Reorg run by the next `head` call.
        on_head: Option<(usize, Vec<u64>)>,
        /// Reorg run by the `events_in` call for the window starting at the given block,
        /// or the `events_at` call for a block of that number, before it answers: depth,
        /// then the replacement blocks' events.
        before_window: Option<(u64, usize, Vec<Vec<u64>>)>,
        /// Answer served as is by the `events_in` call for the window starting at the
        /// given block, or the `events_at` call for a block of that number.
        torn: Option<(u64, Answer)>,
        /// Extra entry served whenever the queried range or block covers its block.
        rogue: Option<(BlockRef, u32, u64)>,
    }

    impl Adversary {
        fn new(inner: ScriptedChain) -> Self {
            Self {
                inner,
                on_head: None,
                before_window: None,
                torn: None,
                rogue: None,
            }
        }

        /// Runs the reorg set for a read starting at `from`, then serves the torn answer
        /// set for it; true when it served one.
        fn misbehave(&mut self, from: u64, out: &mut Answer) -> bool {
            if self
                .before_window
                .as_ref()
                .is_some_and(|(start, ..)| *start == from)
                && let Some((_, depth, blocks)) = self.before_window.take()
            {
                let slices: Vec<&[u64]> = blocks.iter().map(Vec::as_slice).collect();
                self.inner.reorg(depth, &slices);
            }
            if self.torn.as_ref().is_some_and(|(start, _)| *start == from)
                && let Some((_, mut answer)) = self.torn.take()
            {
                out.append(&mut answer);
                return true;
            }
            false
        }
    }

    impl Source for Adversary {
        type Event = u64;
        type Error = PollFailure;

        fn head(&mut self) -> Result<Head, PollFailure> {
            if let Some((depth, events)) = self.on_head.take() {
                reorg_to(&mut self.inner, depth, &events);
            }
            self.inner.head()
        }

        fn header_at(&mut self, number: u64) -> Result<Option<BlockRef>, PollFailure> {
            self.inner.header_at(number)
        }

        fn events_in(
            &mut self,
            from: u64,
            to: u64,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            if self.misbehave(from, out) {
                return Ok(());
            }
            if let Some(entry) = self.rogue
                && (from..=to).contains(&entry.0.number)
            {
                out.push(entry);
            }
            self.inner.events_in(from, to, out)
        }

        fn events_at(
            &mut self,
            block: &BlockRef,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            if self.misbehave(block.number, out) {
                return Ok(());
            }
            if let Some(entry) = self.rogue
                && entry.0.number == block.number
            {
                out.push(entry);
            }
            self.inner.events_at(block, out)
        }

        fn window(&self) -> u64 {
            self.inner.window()
        }
    }

    /// Chain whose only block is number `u64::MAX`; errors on a second log read in one
    /// tick, so a scan that spins fails the tick instead of hanging the test.
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

        fn head(&mut self) -> Result<Head, PollFailure> {
            self.queries = 0;
            Ok(Head {
                block: Self::BLOCK,
                parent: [0; 32],
            })
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

        fn events_at(
            &mut self,
            block: &BlockRef,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            self.queries += 1;
            if self.queries > 1 || *block != Self::BLOCK {
                return Err(PollFailure);
            }
            out.extend(self.event.map(|event| (Self::BLOCK, 0, event)));
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
    fn a_block_served_again_for_a_later_range_is_refused() {
        // given a source that serves its one-event block again for every range above it
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
        // when the first tick applies the block and the second is served it again
        let applying = driver.tick();
        let after_apply = driver.next_delay();
        let again = driver.tick();
        let after_again = driver.next_delay();
        // then the second answer is refused, and only the applying tick asks for an
        // immediate re-poll
        assert_eq!(
            applying,
            Tick::Progressed(ApplySummary {
                applied: 1,
                deduped: 0,
                skipped: 0,
            })
        );
        assert_eq!(after_apply, Duration::ZERO);
        assert_eq!(again, Tick::SourceError);
        assert_eq!(after_again, DriverConfig::default().backoff_base);
        assert_eq!(driver.engine().fold().applied.len(), 1);
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
    fn a_rollback_through_engine_mut_keeps_the_checkpoint_cadence() {
        // given a driver at the defaults, synced over 5,000 one-event blocks and then 300
        // more read one block a poll, so it holds its four checkpoints 64 blocks apart
        let mut chain = ScriptedChain::new(1);
        for value in 1..=5_000u64 {
            chain.push_block(&[value]);
        }
        let mut driver =
            new_driver(chain, EngineConfig::default(), DriverConfig::from_block(1));
        run_to_idle(&mut driver);
        for value in 5_001..=5_300u64 {
            driver.source.push_block(&[value]);
            run_to_idle(&mut driver);
        }
        assert_eq!(driver.engine().checkpoint_count(), 4);
        // when the caller rolls back past a checkpoint through engine_mut, and the driver
        // refolds to the head
        let to = driver.engine_mut().rollback_at_or_below(5_200).unwrap();
        assert_eq!(to, Some(Position::new(5_192, 0)));
        run_to_idle(&mut driver);
        // then the refold takes a checkpoint at the head, 108 blocks above the restore point
        assert_eq!(driver.engine().cursor(), Some(Position::new(5_300, 0)));
        assert_eq!(driver.last_checkpoint_block, Some(5_300));
        // and a rollback to that checkpoint 40 blocks later takes none on the 40-block refold
        for value in 5_301..=5_340u64 {
            driver.source.push_block(&[value]);
            run_to_idle(&mut driver);
        }
        let to = driver.engine_mut().rollback_at_or_below(5_339).unwrap();
        assert_eq!(to, Some(Position::new(5_300, 0)));
        run_to_idle(&mut driver);
        assert_eq!(driver.engine().cursor(), Some(Position::new(5_340, 0)));
        assert_eq!(driver.last_checkpoint_block, Some(5_300));
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
    fn a_terminal_tick_is_not_caught_up() {
        for kind in [FailKind::Halt, FailKind::Poison] {
            // given a driver caught up on blocks 0..=1, and a fold that fails at the event of
            // the next block
            let mut chain = ScriptedChain::new(0);
            chain.push_block(&[1]);
            chain.push_block(&[]);
            let mut driver =
                new_driver(chain, engine_config(2), DriverConfig::from_block(0));
            run_to_idle(&mut driver);
            assert!(driver.is_caught_up());
            driver.source.push_block(&[2]);
            driver.engine_mut().fold_mut().fail_at = Some((Position::new(2, 0), kind));
            // when the poll that reads it ends the engine
            let tick = driver.tick();
            // then the driver does not report caught up
            assert!(matches!(tick, Tick::Terminal(_)));
            assert!(!driver.is_caught_up());
            assert!(!driver.status().caught_up);
        }

        // given a driver caught up on blocks 1..=5, on a source whose horizon then rises
        // above the start block
        let mut chain = ScriptedChain::new(1);
        for value in 1..=5u64 {
            chain.push_block(&[value]);
        }
        let mut driver = new_driver(chain, engine_config(0), DriverConfig::default());
        run_to_idle(&mut driver);
        assert!(driver.is_caught_up());
        driver.source_mut().reorg(3, &[&[10], &[20], &[30]]);
        driver.source_mut().set_horizon(ReplayHorizon::FromBlock(1));
        // when a fork surfaces that only a resync could recover from
        let tick = driver.tick();
        // then the engine is unrecoverable, and the driver does not report caught up
        assert!(matches!(
            tick,
            Tick::Terminal(EngineStatus::Unrecoverable { .. })
        ));
        assert!(!driver.is_caught_up());
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
        driver.source_mut().inner.push_block(&[7]);
        let stale = driver.tick();
        // when blocks 6 and 7 are replaced after the events read, before the next tick
        driver.source_mut().on_head = Some((2, vec![600, 700]));
        let next = driver.tick();
        run_to_idle(&mut driver);
        // then the stale blocks fold, the next first window carries the new cursor
        // block's hash, and the fold converges on the canonical chain
        assert!(matches!(stale, Tick::Progressed(_)), "got {stale:?}");
        assert!(
            matches!(next, Tick::RolledBack { .. } | Tick::Resynced),
            "got {next:?}"
        );
        let chain = driver.source_mut().inner.clone();
        assert_eq!(driver.engine().fold().applied, canonical_fold(chain));
    }

    #[test]
    fn reorg_between_two_windows_of_one_scan_is_dropped_then_folded() {
        // given a driver caught up on block 5, then empty blocks 6..=10 read two per window
        let mut driver = adversary_driver(one_event_chain(5));
        run_to_idle(&mut driver);
        for _ in 6..=10 {
            driver.source_mut().inner.push_block(&[]);
        }
        driver.source_mut().inner.set_window(2);
        // when blocks 6..=10 are replaced after the window [5, 6] answers empty, block 6
        // gaining an event and block 9 another
        driver.source_mut().before_window =
            Some((7, 5, vec![vec![66], vec![], vec![], vec![99], vec![]]));
        let outcome = driver.tick();
        run_to_idle(&mut driver);
        // then the head block moved under the walk, so the scan keeps nothing, and the
        // fold converges on the new chain with both events
        assert_eq!(outcome, Tick::SourceError);
        let chain = driver.source_mut().inner.clone();
        let folded = canonical_fold(chain);
        assert!(folded.contains(&(Position::new(6, 0), 66)));
        assert_eq!(driver.engine().fold().applied, folded);
    }

    #[test]
    fn torn_answer_inside_a_walk_of_two_windows_is_dropped_then_folded() {
        // given a driver caught up on block 1, then blocks 2..=6 with events at 4 and 6,
        // read three per window
        let mut chain = ScriptedChain::new(1);
        chain.push_block(&[1]);
        chain.set_window(3);
        let mut driver = adversary_driver(chain);
        run_to_idle(&mut driver);
        for events in [&[][..], &[], &[40], &[], &[60]] {
            driver.source_mut().inner.push_block(events);
        }
        let replacement = vec![vec![31], vec![], vec![], vec![61]];
        let mut reorged = driver.source_mut().inner.clone();
        let slices: Vec<&[u64]> = replacement.iter().map(Vec::as_slice).collect();
        reorged.reorg(4, &slices);
        let old_four = driver.source_mut().inner.header(4).unwrap();
        let new_six = reorged.header(6).unwrap();
        // when blocks 3..=6 are replaced as the window [4, 6] is read, and its one answer
        // mixes old block 4 with new block 6
        driver.source_mut().before_window = Some((4, 4, replacement));
        driver.source_mut().torn = Some((4, vec![(old_four, 0, 40), (new_six, 0, 61)]));
        let outcome = driver.tick();
        run_to_idle(&mut driver);
        // then the head block moved under the walk, so the torn answer is not folded, and
        // the fold converges on the new chain
        assert_eq!(outcome, Tick::SourceError);
        assert_eq!(driver.source_mut().inner.header(6), Some(new_six));
        let chain = driver.source_mut().inner.clone();
        let folded = canonical_fold(chain);
        assert!(folded.contains(&(Position::new(3, 0), 31)));
        assert_eq!(driver.engine().fold().applied, folded);
    }

    #[test]
    fn torn_single_window_is_dropped_then_folded() {
        // given a driver caught up on block 1, then blocks 2..=6 with events at 4 and 6,
        // all in the one window [1, 6] from the cursor block
        let mut chain = ScriptedChain::new(1);
        chain.push_block(&[1]);
        chain.set_window(6);
        let mut driver = adversary_driver(chain);
        run_to_idle(&mut driver);
        for events in [&[][..], &[], &[40], &[], &[60]] {
            driver.source_mut().inner.push_block(events);
        }
        let replacement = vec![vec![31], vec![], vec![], vec![61]];
        let mut reorged = driver.source_mut().inner.clone();
        let slices: Vec<&[u64]> = replacement.iter().map(Vec::as_slice).collect();
        reorged.reorg(4, &slices);
        let one = driver.source_mut().inner.header(1).unwrap();
        let old_four = driver.source_mut().inner.header(4).unwrap();
        let new_six = reorged.header(6).unwrap();
        // when blocks 3..=6 are replaced as that window is read, and its one answer
        // carries the cursor block and mixes old block 4 with new block 6
        driver.source_mut().before_window = Some((1, 4, replacement));
        driver.source_mut().torn =
            Some((1, vec![(one, 0, 1), (old_four, 0, 40), (new_six, 0, 61)]));
        let outcome = driver.tick();
        run_to_idle(&mut driver);
        // then the head block moved under the read, so the torn answer is not folded,
        // and the fold converges on the new chain
        assert_eq!(outcome, Tick::SourceError);
        assert_eq!(driver.source_mut().inner.header(6), Some(new_six));
        let chain = driver.source_mut().inner.clone();
        let folded = canonical_fold(chain);
        assert!(folded.contains(&(Position::new(3, 0), 31)));
        assert_eq!(driver.engine().fold().applied, folded);
    }

    /// Scripted chain whose events carry their log index in the high 32 bits, so a block's
    /// indices can be any ascending set.
    #[derive(Clone)]
    struct Indexed(ScriptedChain);

    impl Source for Indexed {
        type Event = u64;
        type Error = PollFailure;

        fn head(&mut self) -> Result<Head, PollFailure> {
            self.0.head()
        }

        fn header_at(&mut self, number: u64) -> Result<Option<BlockRef>, PollFailure> {
            self.0.header_at(number)
        }

        fn events_in(
            &mut self,
            from: u64,
            to: u64,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            let at = out.len();
            self.0.events_in(from, to, out)?;
            for entry in &mut out[at..] {
                entry.1 = u32::try_from(entry.2 >> 32).expect("index lane fits in u32");
            }
            Ok(())
        }

        fn events_at(
            &mut self,
            block: &BlockRef,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            let at = out.len();
            self.0.events_at(block, out)?;
            for entry in &mut out[at..] {
                entry.1 = u32::try_from(entry.2 >> 32).expect("index lane fits in u32");
            }
            Ok(())
        }

        fn window(&self) -> u64 {
            self.0.window()
        }
    }

    /// Splitmix64, so each seed replays the same run.
    struct Rng(u64);

    impl Rng {
        fn below(&mut self, n: u64) -> u64 {
            self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut x = self.0;
            x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            (x ^ (x >> 31)) % n
        }

        fn pick<T: Copy>(&mut self, options: &[T]) -> T {
            options[self.below(options.len() as u64) as usize]
        }
    }

    /// Up to four events with ascending random log indices, at times up to `u32::MAX`.
    fn random_events(rng: &mut Rng) -> Vec<u64> {
        let mut index = if rng.below(8) == 0 {
            u64::from(u32::MAX) - 12
        } else {
            rng.below(1_000)
        };
        (0..rng.below(5))
            .map(|_| {
                index += 1 + rng.below(3);
                (index << 32) | rng.below(1 << 32)
            })
            .collect()
    }

    /// Blocks `chain` can still push before its numbers run out.
    fn room(chain: &ScriptedChain, first: u64) -> u64 {
        chain
            .tip()
            .map_or(Some(first), |tip| tip.number.checked_add(1))
            .map_or(0, |next| (u64::MAX - next).saturating_add(1))
    }

    /// The fold of `chain`'s logs from `start` through `cursor`, from scratch.
    fn from_scratch(
        mut chain: Indexed,
        start: u64,
        cursor: Option<Position>,
    ) -> Vec<(Position, u64)> {
        let Some(cursor) = cursor else {
            return Vec::new();
        };
        let mut entries = Vec::new();
        chain.events_in(start, cursor.block, &mut entries).unwrap();
        let mut folded: Vec<(Position, u64)> = entries
            .into_iter()
            .map(|(block, index, event)| {
                (Position::new(block.number, u64::from(index)), event)
            })
            .filter(|(position, _)| *position <= cursor)
            .collect();
        folded.sort_unstable();
        folded
    }

    /// The driver's source: through `source_mut`, which clears the tip, unless `keep_tip`.
    fn indexed(
        driver: &mut Driver<RecordingFold, Indexed>,
        keep_tip: bool,
    ) -> &mut Indexed {
        if keep_tip {
            &mut driver.source
        } else {
            driver.source_mut()
        }
    }

    /// Ticks random runs and checks every tick's fold against a fold from scratch; with
    /// `older_views`, some ticks read a copy of the chain saved at an earlier step. With
    /// `capped`, a tick reads one or two windows, so most walks stop short of the head, and
    /// the chain moves under the driver, so the tip carries to the next tick and blocks
    /// arrive or reorg away above and below its end.
    fn check_every_tick_against_a_fold_from_scratch(older_views: bool, capped: bool) {
        for seed in 0..2_000 {
            // given a well-behaved source: random log indices, windows from 1 block up,
            // and at times heights near u64::MAX
            let mut rng = Rng(seed);
            let first = if rng.below(4) == 0 {
                u64::MAX - rng.below(120)
            } else {
                rng.below(50)
            };
            let start = first + rng.below(3).min(u64::MAX - first);
            // The chain always holds a block: an empty `ScriptedChain` reports a head it
            // does not hold.
            let mut chain = ScriptedChain::new(first);
            chain.push_block(&random_events(&mut rng));
            chain.set_window(rng.pick(&[1, 2, 3, 7, 64, u64::MAX]));
            let engine = EngineConfig {
                ring_capacity: rng.pick(&[2, 4, 8, 32]),
                checkpoint_slots: rng.pick(&[0, 1, 2, 4]),
            };
            let config = DriverConfig {
                checkpoint_interval: rng.pick(&[None, Some(1), Some(2), Some(5)]),
                ..DriverConfig::from_block(start)
            };
            let mut driver =
                Driver::new(RecordingFold::default(), Indexed(chain), engine, config)
                    .unwrap();
            let mut saved = None;
            for step in 0..400 {
                // when blocks arrive or reorg away to a random depth between ticks, the
                // driver at times restarts from its snapshot, and with `older_views` a
                // tick at times reads a saved copy of the chain
                if older_views && rng.below(4) == 0 {
                    saved = Some(indexed(&mut driver, capped).clone());
                }
                let chain = &mut indexed(&mut driver, capped).0;
                match rng.below(10) {
                    0..=4 => {
                        for _ in 0..rng.below(4).min(room(chain, first)) {
                            chain.push_block(&random_events(&mut rng));
                        }
                    }
                    5 | 6 => {
                        let held = chain.tip().map_or(0, |tip| tip.number - first + 1);
                        let reach = rng.pick(&[4, 40]);
                        let depth = (1 + rng.below(reach)).min(held);
                        let count = rng
                            .below(depth + 2)
                            .clamp(1, room(chain, first).saturating_add(depth));
                        let blocks: Vec<Vec<u64>> =
                            (0..count).map(|_| random_events(&mut rng)).collect();
                        let slices: Vec<&[u64]> =
                            blocks.iter().map(Vec::as_slice).collect();
                        chain.reorg(depth as usize, &slices);
                    }
                    _ => {}
                }
                #[cfg(feature = "wincode")]
                if rng.below(20) == 0 {
                    let mut bytes = Vec::new();
                    driver.engine().encode_snapshot(&mut bytes).unwrap();
                    let restored = Engine::decode_snapshot(&bytes, engine).unwrap();
                    let source = driver.source_mut().clone();
                    driver = Driver::resume(
                        restored,
                        source,
                        RecordingFold::default(),
                        config,
                    )
                    .unwrap();
                }
                let newer = match saved.clone() {
                    Some(view) if rng.below(4) == 0 => {
                        Some(core::mem::replace(indexed(&mut driver, capped), view))
                    }
                    _ => None,
                };
                if capped {
                    driver.span = 1 + rng.below(2);
                }
                let before = driver.engine().fold().applied.clone();
                let tick = driver.tick();
                // then no tick errs, and the fold is the fold from scratch over the chain
                // the tick read, up to the cursor; a head below the cursor block or the tip
                // that the ring cannot tell from a lagging node leaves the fold as it was
                assert!(
                    !matches!(tick, Tick::SourceError | Tick::Terminal(_)),
                    "seed {seed} step {step}: {tick:?}"
                );
                let want = if tick == Tick::Behind {
                    before
                } else {
                    from_scratch(
                        indexed(&mut driver, capped).clone(),
                        start,
                        driver.engine().cursor(),
                    )
                };
                assert_eq!(
                    driver.engine().fold().applied,
                    want,
                    "seed {seed} step {step}: {tick:?}"
                );
                if let Some(newer) = newer {
                    *indexed(&mut driver, capped) = newer;
                }
            }
        }
    }

    #[test]
    fn every_tick_folds_what_a_fold_from_scratch_does() {
        check_every_tick_against_a_fold_from_scratch(false, false);
    }

    #[test]
    fn a_tick_on_an_older_view_folds_what_a_fold_from_scratch_of_it_does() {
        check_every_tick_against_a_fold_from_scratch(true, false);
    }

    #[test]
    fn a_walk_cut_at_its_cap_folds_what_a_fold_from_scratch_does() {
        check_every_tick_against_a_fold_from_scratch(false, true);
        check_every_tick_against_a_fold_from_scratch(true, true);
    }

    fn counted_driver(chain: ScriptedChain) -> Driver<RecordingFold, Counted> {
        Driver::new(
            RecordingFold::default(),
            Counted {
                inner: chain,
                calls: 0,
                period: None,
                budget: None,
            },
            engine_config(2),
            DriverConfig::from_block(1),
        )
        .unwrap()
    }

    /// One tick, with the `Source` calls it made.
    fn counted_tick(driver: &mut Driver<RecordingFold, Counted>) -> (Tick, u32) {
        // The field, not `source_mut`: the chain moves under the driver, and `source_mut`
        // clears the tip.
        let before = driver.source.calls;
        let tick = driver.tick();
        (tick, driver.source.calls - before)
    }

    #[test]
    fn polls_at_the_tip_read_only_what_changed() {
        // given a driver caught up on five one-event blocks
        let mut driver = counted_driver(one_event_chain(5));
        run_to_idle(&mut driver);
        // when polled with no new block, after one new empty block, and after one with
        // an event
        let unchanged = counted_tick(&mut driver);
        driver.source.inner.push_block(&[]);
        let empty = counted_tick(&mut driver);
        let after_empty = counted_tick(&mut driver);
        driver.source.inner.push_block(&[7]);
        let event = counted_tick(&mut driver);
        // then an unchanged head costs one call, and one new block two
        assert_eq!(unchanged, (Tick::Idle, 1));
        assert_eq!(empty, (Tick::Idle, 2));
        assert_eq!(after_empty, (Tick::Idle, 1));
        assert!(matches!(event, (Tick::Progressed(_), 2)), "got {event:?}");
        assert_eq!(driver.engine().cursor(), Some(Position::new(7, 0)));
    }

    #[test]
    fn a_sparse_gap_is_read_from_the_tip() {
        // given a driver caught up on block 5 and then on ten empty blocks, two per window
        let mut driver = counted_driver(one_event_chain(5));
        run_to_idle(&mut driver);
        driver.source.inner.set_window(2);
        for _ in 6..=15 {
            driver.source.inner.push_block(&[]);
        }
        let catch_up = counted_tick(&mut driver);
        // when five more empty blocks arrive
        for _ in 16..=20 {
            driver.source.inner.push_block(&[]);
        }
        let gap = counted_tick(&mut driver);
        // then the first walk reads from the cursor block, the head and a bracket around
        // six windows; the second reads above the tip, then the tip and the head again,
        // instead of every window from the cursor
        assert_eq!(catch_up, (Tick::Idle, 8));
        assert_eq!(gap, (Tick::Idle, 6));
        assert_eq!(driver.engine().cursor(), Some(Position::new(5, 0)));
    }

    #[test]
    fn reorg_under_the_tip_is_folded_next_tick() {
        // given a driver caught up on block 5 and then on ten empty blocks, two per window
        let mut driver = counted_driver(one_event_chain(5));
        run_to_idle(&mut driver);
        driver.source.inner.set_window(2);
        for _ in 6..=15 {
            driver.source.inner.push_block(&[]);
        }
        run_to_idle(&mut driver);
        assert_eq!(counted_tick(&mut driver), (Tick::Idle, 1));
        // when blocks 8..=15 are replaced by a longer chain whose block 8 carries an event
        let mut blocks: Vec<&[u64]> = vec![&[80]];
        blocks.extend([&[][..]; 8]);
        driver.source.inner.reorg(8, &blocks);
        let outcome = driver.tick();
        run_to_idle(&mut driver);
        // then the tip no longer matches, the walk restarts at the cursor, and the event
        // folds
        assert!(matches!(outcome, Tick::Progressed(_)), "got {outcome:?}");
        let chain = driver.source.inner.clone();
        let folded = canonical_fold(chain);
        assert!(folded.contains(&(Position::new(8, 0), 80)));
        assert_eq!(driver.engine().fold().applied, folded);
    }

    #[test]
    fn manual_rollback_at_the_tip_refolds_the_blocks_above_it() {
        // given a driver at the tip of six blocks with one event each, checkpointed at 3
        let mut chain = ScriptedChain::new(1);
        for value in 1..=3u64 {
            chain.push_block(&[value]);
        }
        let mut driver = new_driver(chain, engine_config(2), DriverConfig::from_block(1));
        run_to_idle(&mut driver);
        driver.checkpoint();
        for value in 4..=6u64 {
            driver.source.push_block(&[value]);
        }
        run_to_idle(&mut driver);
        // when the engine is rolled back by hand to block 3, then block 7 lands
        let restored = driver.engine_mut().rollback_at_or_below(3).unwrap();
        driver.source.push_block(&[7]);
        run_to_idle(&mut driver);
        // then blocks 4..=6 fold again, and the fold is the fold from scratch
        assert_eq!(restored, Some(Position::new(3, 0)));
        let chain = driver.source.clone();
        assert_eq!(driver.engine().fold().applied, canonical_fold(chain));
    }

    /// A chain whose filter is instance state: it answers only events of at least `min`.
    #[derive(Clone)]
    struct Filtered {
        inner: ScriptedChain,
        min: u64,
    }

    impl Source for Filtered {
        type Event = u64;
        type Error = PollFailure;

        fn head(&mut self) -> Result<Head, PollFailure> {
            self.inner.head()
        }

        fn header_at(&mut self, number: u64) -> Result<Option<BlockRef>, PollFailure> {
            self.inner.header_at(number)
        }

        fn events_in(
            &mut self,
            from: u64,
            to: u64,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            self.inner.events_in(from, to, out)?;
            out.retain(|entry| entry.2 >= self.min);
            Ok(())
        }

        fn events_at(
            &mut self,
            block: &BlockRef,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            self.inner.events_at(block, out)?;
            out.retain(|entry| entry.2 >= self.min);
            Ok(())
        }

        fn horizon(&self) -> ReplayHorizon {
            self.inner.horizon()
        }

        fn window(&self) -> u64 {
            self.inner.window()
        }
    }

    #[test]
    fn a_filter_widened_through_source_mut_folds_below_the_old_tip() {
        // given a driver at the tip of four blocks whose filter drops the events of 2..=4
        let mut chain = ScriptedChain::new(1);
        for value in [10, 2, 3, 4] {
            chain.push_block(&[value]);
        }
        let source = Filtered {
            inner: chain,
            min: 10,
        };
        let engine = engine_config(2);
        let mut driver = Driver::new(
            RecordingFold::default(),
            source,
            engine,
            DriverConfig::from_block(1),
        )
        .unwrap();
        run_to_idle(&mut driver);
        assert_eq!(driver.status().cursor, Some(Position::new(1, 0)));
        // when the filter is widened to every event
        driver.source_mut().min = 0;
        run_to_idle(&mut driver);
        // then the events above the cursor, up to the old tip, fold
        let expected: Vec<(Position, u64)> = (1..=4u64)
            .zip([10, 2, 3, 4])
            .map(|(block, value)| (Position::new(block, 0), value))
            .collect();
        assert_eq!(driver.engine().fold().applied, expected);
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
    fn a_dropped_log_is_folded_as_given() {
        // given a driver caught up on five blocks, and a sixth with two events
        let mut driver = adversary_driver(one_event_chain(5));
        run_to_idle(&mut driver);
        driver.source_mut().inner.push_block(&[6, 7]);
        let six = driver.source_mut().inner.header(6).unwrap();
        // when the source answers block 6 without its second log
        driver.source_mut().torn = Some((6, vec![(six, 0, 6)]));
        let outcome = driver.tick();
        let settled = run_to_idle(&mut driver);
        // then the answer is folded as given: no error, the engine stays Active, and the
        // fold lacks the dropped event for good
        assert!(matches!(outcome, Tick::Progressed(_)), "got {outcome:?}");
        assert_eq!(settled, Tick::Idle);
        assert!(driver.engine().status().is_active());
        let folded = &driver.engine().fold().applied;
        assert!(folded.contains(&(Position::new(6, 0), 6)));
        assert!(!folded.contains(&(Position::new(6, 1), 7)));
        assert_eq!(driver.engine().cursor(), Some(Position::new(6, 0)));
    }

    /// Ticks `source` over a new block its lagging node lacks, then without the lag, and
    /// checks the block folds.
    fn fold_past_a_lagging_node<S>(source: S, nodes: fn(&mut S) -> &mut Lagging)
    where
        S: Source<Event = u64, Error = PollFailure>,
    {
        // given a driver caught up on five one-event blocks, two per window
        let mut driver = Driver::new(
            RecordingFold::default(),
            source,
            engine_config(2),
            DriverConfig::from_block(1),
        )
        .unwrap();
        run_to_idle(&mut driver);
        let lagging = nodes(driver.source_mut());
        lagging.inner.set_window(2);
        // when block 6 arrives with an event, and a tick reads it from a node that does
        // not hold it yet
        lagging.lagging = Some(lagging.inner.clone());
        lagging.inner.push_block(&[6]);
        driver.tick();
        let lagging = nodes(driver.source_mut());
        lagging.lagging = None;
        run_to_idle(&mut driver);
        // then once the node catches up, block 6 folds
        let chain = nodes(driver.source_mut()).inner.clone();
        let folded = canonical_fold(chain);
        assert!(folded.contains(&(Position::new(6, 0), 6)));
        assert_eq!(driver.engine().fold().applied, folded);
    }

    #[test]
    fn lagging_backend_new_block_is_not_skipped() {
        let chain = one_event_chain(5);
        fold_past_a_lagging_node(
            Lagging {
                inner: chain.clone(),
                lagging: None,
            },
            |source| source,
        );
        fold_past_a_lagging_node(
            Proxy(Lagging {
                inner: chain,
                lagging: None,
            }),
            |source| &mut source.0,
        );
    }

    /// A chain of block 0, with event 10, and blocks 1..=20, empty, for `a`; and for `b`, a
    /// fork of it from block 1 whose blocks carry `fork` (one event per block, 0 for none).
    fn pool_driver(fork: &[u64]) -> Driver<RecordingFold, Pool> {
        let mut base = ScriptedChain::new(0);
        base.set_window(2);
        base.push_block(&[10]);
        let mut b = base.clone();
        for event in fork {
            b.push_block(if *event == 0 {
                &[]
            } else {
                core::slice::from_ref(event)
            });
        }
        let mut a = base.clone();
        // A push that a reorg drops, so `a`'s blocks from 1 get other hashes than `b`'s.
        a.push_block(&[]);
        a.reorg(1, &[]);
        for _ in 1..=20 {
            a.push_block(&[]);
        }
        assert_ne!(a.header(1), b.header(1));
        Driver::new(
            RecordingFold::default(),
            Pool::new(a, b),
            engine_config(2),
            DriverConfig::from_block(0),
        )
        .unwrap()
    }

    /// The fold of a fresh driver over the pool's node `a`.
    fn pool_canonical(driver: &Driver<RecordingFold, Pool>) -> Vec<(Position, u64)> {
        let mut fresh = new_driver(
            driver.source.a.clone(),
            engine_config(2),
            DriverConfig::from_block(0),
        );
        run_to_idle(&mut fresh);
        fresh.engine().fold().applied.clone()
    }

    #[test]
    fn an_entry_outside_its_window_is_refused() {
        // given a driver caught up on node a to block 20, with its tip there, then ten more
        // blocks; node b, behind a proxy, lags at block 2 of a fork whose block 2 carries 777
        let mut driver = pool_driver(&[0, 777]);
        run_to_idle(&mut driver);
        for _ in 21..=30 {
            driver.source.a.push_block(&[]);
        }
        driver.source.proxy = true;
        // when the first window above the tip, 21..=22, is answered by b with its block 2
        driver.source.route = b"ABAA".to_vec();
        let outcome = driver.tick();
        // then the answer is refused, and nothing of b's fork is folded
        assert_eq!(outcome, Tick::SourceError);
        assert_eq!(
            driver.engine().fold().applied,
            vec![(Position::new(0, 0), 10)]
        );
        run_to_idle(&mut driver);
        assert_eq!(driver.engine().fold().applied, pool_canonical(&driver));

        // given the same, with b lagging at block 1 of a fork whose block 1 carries 777
        let mut driver = pool_driver(&[777]);
        run_to_idle(&mut driver);
        // when a walk from the cursor, since `source_mut` drops the tip, has its second
        // window, 2..=3, answered by b with its block 1
        driver.source_mut().proxy = true;
        driver.source_mut().route = b"AAB".to_vec();
        let outcome = driver.tick();
        // then that answer is refused too
        assert_eq!(outcome, Tick::SourceError);
        assert_eq!(
            driver.engine().fold().applied,
            vec![(Position::new(0, 0), 10)]
        );
        run_to_idle(&mut driver);
        assert_eq!(driver.engine().fold().applied, pool_canonical(&driver));

        // given a driver whose cursor is its tip, at block 20 with an event, then block 21
        // with an event and an empty block 22; node b, behind a proxy, lags at block 19 of a
        // fork whose block 19 carries 777
        let mut fork = [0; 19];
        fork[18] = 777;
        let mut driver = pool_driver(&fork);
        driver.source.a.reorg(1, &[&[20]]);
        run_to_idle(&mut driver);
        driver.source.a.push_block(&[21]);
        driver.source.a.push_block(&[]);
        driver.source.proxy = true;
        // when the first window of a walk from the cursor, 20..=21, is answered by b with its
        // block 19
        driver.source.route = b"AB".to_vec();
        let outcome = driver.tick();
        // then that answer is refused too, not read as a window with nothing above the
        // cursor block, and block 21 folds
        assert_eq!(outcome, Tick::SourceError);
        run_to_idle(&mut driver);
        assert!(
            driver
                .engine()
                .fold()
                .applied
                .contains(&(Position::new(21, 0), 21))
        );
        assert_eq!(driver.engine().fold().applied, pool_canonical(&driver));
    }

    #[test]
    fn a_failed_head_keeps_the_tip() {
        // given a driver caught up on block 5 and then on twenty empty blocks, two per
        // window, so its tip is far above its cursor
        let mut driver = counted_driver(one_event_chain(5));
        driver.source.inner.set_window(2);
        for _ in 6..=25 {
            driver.source.inner.push_block(&[]);
        }
        run_to_idle(&mut driver);
        // when one head call fails, and the next poll finds no new block
        driver.source.inner.fail_next_polls(1);
        let failed = counted_tick(&mut driver);
        let next = counted_tick(&mut driver);
        // then the next poll still reads only the head
        assert_eq!(failed, (Tick::SourceError, 1));
        assert_eq!(next, (Tick::Idle, 1));
    }

    /// Calls one tick costs on a pool with no route queued.
    fn pool_tick(driver: &mut Driver<RecordingFold, Pool>) -> (Tick, u32) {
        let before = driver.source.calls;
        let tick = driver.tick();
        (tick, driver.source.calls - before)
    }

    #[test]
    fn an_error_mid_walk_keeps_the_tip() {
        // given two drivers caught up on node a to block 20, with their tip there, then
        // ten more blocks; node b lags at block 20 and errs on a range past it
        let mut failing = pool_driver(&[]);
        let mut twin = pool_driver(&[]);
        for driver in [&mut failing, &mut twin] {
            run_to_idle(driver);
            driver.source.b = driver.source.a.clone();
            for _ in 21..=30 {
                driver.source.a.push_block(&[]);
            }
        }
        // when one driver's first window above the tip goes to b, and then both poll
        failing.source.route = b"AB".to_vec();
        let failed = pool_tick(&mut failing);
        let retry = pool_tick(&mut failing);
        let clean = pool_tick(&mut twin);
        // then the retry reads above the tip, as a tick without the error does
        assert_eq!(failed.0, Tick::SourceError);
        assert_eq!(retry, clean);
        assert_eq!(failing.engine().fold().applied, pool_canonical(&failing));

        // given the same, with b behind a proxy at block 2 of a fork whose block 2 carries
        // 777
        let mut refused = pool_driver(&[0, 777]);
        let mut twin = pool_driver(&[0, 777]);
        for driver in [&mut refused, &mut twin] {
            run_to_idle(driver);
            for _ in 21..=30 {
                driver.source.a.push_block(&[]);
            }
        }
        // when one driver's first window above the tip is answered by b with its block 2
        refused.source.proxy = true;
        refused.source.route = b"AB".to_vec();
        let failed = pool_tick(&mut refused);
        let retry = pool_tick(&mut refused);
        let clean = pool_tick(&mut twin);
        // then the refused answer keeps the tip too
        assert_eq!(failed.0, Tick::SourceError);
        assert_eq!(retry, clean);
        assert_eq!(refused.engine().fold().applied, pool_canonical(&refused));

        // given a driver whose cursor is its tip, at block 20 with an event, then two empty
        // blocks; node b, behind a proxy, lags at block 19 of a fork whose block 19 carries
        // 777
        let mut fork = [0; 19];
        fork[18] = 777;
        let mut refused = pool_driver(&fork);
        refused.source.a.reorg(1, &[&[20]]);
        run_to_idle(&mut refused);
        let tip = refused.tip;
        refused.source.a.push_block(&[]);
        refused.source.a.push_block(&[]);
        // when the first window of the walk from the cursor goes to b
        refused.source.proxy = true;
        refused.source.route = b"AB".to_vec();
        let failed = refused.tick();
        // then the refused answer keeps the tip
        assert_eq!(failed, Tick::SourceError);
        assert!(tip.is_some());
        assert_eq!(refused.tip, tip);
    }

    #[test]
    fn a_head_behind_the_tip_costs_one_call() {
        // given a driver caught up on node a to block 20, with its tip there; node b is a
        // without its last block
        let mut driver = pool_driver(&[]);
        run_to_idle(&mut driver);
        let mut behind = driver.source.a.clone();
        behind.reorg(1, &[]);
        driver.source.b = behind;
        let before = driver.engine().fold().clone();
        // when one head call goes to b, and the next poll to a
        driver.source.route = b"B".to_vec();
        let lagging = pool_tick(&mut driver);
        let caught_up = driver.is_caught_up();
        let delay = driver.next_delay();
        let next = pool_tick(&mut driver);
        // then the lagging head costs one call and changes nothing, and the tip stays
        assert_eq!(lagging, (Tick::Behind, 1));
        assert_eq!(driver.engine().fold(), &before);
        assert!(caught_up);
        assert_eq!(delay, DriverConfig::default().poll_interval);
        assert_eq!(next, (Tick::Idle, 1));

        // given a driver with no cursor yet, at the tip of ten empty blocks
        let mut empty = ScriptedChain::new(0);
        for _ in 0..10 {
            empty.push_block(&[]);
        }
        let mut behind = empty.clone();
        behind.reorg(1, &[]);
        let mut driver = Driver::new(
            RecordingFold::default(),
            Pool::new(empty, behind),
            engine_config(2),
            DriverConfig::from_block(0),
        )
        .unwrap();
        run_to_idle(&mut driver);
        // when one head call goes to b, and then a block with an event lands
        driver.source.route = b"B".to_vec();
        let lagging = pool_tick(&mut driver);
        driver.source.a.push_block(&[11]);
        run_to_idle(&mut driver);
        // then the lagging head changes nothing, and the event folds
        assert_eq!(lagging, (Tick::Behind, 1));
        assert_eq!(
            driver.engine().fold().applied,
            vec![(Position::new(10, 0), 11)]
        );
    }

    #[test]
    fn a_lagging_or_failed_poll_does_not_report_caught_up() {
        // given a driver on node a that has just folded a new block's event, so it is not
        // caught up; node b is a without that block
        let mut driver = pool_driver(&[]);
        run_to_idle(&mut driver);
        driver.source.b = driver.source.a.clone();
        driver.source.a.push_block(&[7]);
        let progressed = driver.tick();
        assert!(matches!(progressed, Tick::Progressed(_)));
        assert!(!driver.is_caught_up());
        // when the next head call goes to b
        driver.source.route = b"B".to_vec();
        let lagging = driver.tick();
        // and the poll after that fails
        driver.source.route.clear();
        driver.source.a.fail_next_polls(1);
        let failed = driver.tick();
        // then neither the lagging head nor the failure reports the driver caught up
        assert_eq!(lagging, Tick::Behind);
        assert_eq!(failed, Tick::SourceError);
        assert!(!driver.is_caught_up());
        assert!(!driver.status().caught_up);
    }

    #[test]
    fn a_second_hash_at_the_cursor_block_is_refused() {
        for b_first in [false, true] {
            // given a driver caught up on node a, blocks 0..=9 with events at 0 and 1, so
            // the cursor is block 1; node b shares block 0, then holds 1' and 2' [666]
            let mut base = ScriptedChain::new(0);
            base.push_block(&[10]);
            let mut a = base.clone();
            a.push_block(&[11]);
            let mut b = base.clone();
            // A push that a reorg drops, so `b`'s blocks from 1 get other hashes than `a`'s.
            b.push_block(&[]);
            b.reorg(1, &[&[99], &[666]]);
            for _ in 2..=9 {
                a.push_block(&[]);
            }
            assert_ne!(a.header(1), b.header(1));
            a.set_window(2);
            let source = Merge {
                a,
                b,
                merge: false,
                b_first,
            };
            let mut driver = Driver::new(
                RecordingFold::default(),
                source,
                engine_config(2),
                DriverConfig::from_block(0),
            )
            .unwrap();
            run_to_idle(&mut driver);
            assert_eq!(driver.engine().cursor().map(|c| c.block), Some(1));
            let before = driver.engine().fold().clone();
            // when one answer holds both nodes' logs for blocks 1 and 2
            driver.source_mut().merge = true;
            driver.source.a.push_block(&[]);
            let merged = driver.tick();
            // then the answer is refused, and node b's events are not folded
            assert_eq!(merged, Tick::SourceError);
            assert_eq!(driver.engine().fold(), &before);
            driver.source.merge = false;
            run_to_idle(&mut driver);
            assert_eq!(driver.engine().fold(), &before);
        }
    }

    /// Blocks 1..=20, each with three events.
    fn three_event_chain() -> ScriptedChain {
        let mut chain = ScriptedChain::new(1);
        for _ in 1..=20 {
            chain.push_block(&[7, 8, 9]);
        }
        chain
    }

    /// Asserts the fold took every event of `three_event_chain` once, in order.
    fn assert_folded_once(fold: &RecordingFold) {
        let want: Vec<Position> = (1..=20u64)
            .flat_map(|block| (0..3).map(move |index| Position::new(block, index)))
            .collect();
        let got: Vec<Position> = fold.applied.iter().map(|(at, _)| *at).collect();
        assert_eq!(got, want);
    }

    #[cfg(feature = "wincode")]
    #[test]
    fn a_halted_snapshot_resumes_with_the_rest_of_its_block() {
        // given a driver halted at the second event of block 10, so its cursor is (10, 0)
        let fold = RecordingFold {
            fail_at: Some((Position::new(10, 1), FailKind::Halt)),
            ..RecordingFold::default()
        };
        let mut driver = Driver::new(
            fold,
            three_event_chain(),
            EngineConfig::default(),
            DriverConfig::from_block(1),
        )
        .unwrap();
        while !matches!(driver.tick(), Tick::Terminal(_)) {}
        assert_eq!(driver.engine().cursor(), Some(Position::new(10, 0)));
        // when its snapshot is resumed with a fixed fold (decoding clears `fail_at`)
        let mut bytes = Vec::new();
        driver.engine().encode_snapshot(&mut bytes).unwrap();
        let engine = Engine::decode_snapshot(&bytes, EngineConfig::default()).unwrap();
        let mut resumed = Driver::resume(
            engine,
            three_event_chain(),
            RecordingFold::default(),
            DriverConfig::from_block(1),
        )
        .unwrap();
        run_to_idle(&mut resumed);
        // then the fold holds every event once, the rest of block 10 too
        assert_folded_once(resumed.engine().fold());
    }

    #[cfg(feature = "wincode")]
    #[test]
    fn a_reorg_of_the_head_right_after_a_restart_rolls_back() {
        // given a driver at the defaults over a 500-block window, synced over 5,000
        // one-event blocks and then 300 more read one block a poll
        let mut chain = ScriptedChain::new(1);
        chain.set_window(500);
        for value in 1..=5_000u64 {
            chain.push_block(&[value]);
        }
        let mut driver =
            new_driver(chain, EngineConfig::default(), DriverConfig::from_block(1));
        run_to_idle(&mut driver);
        for value in 5_001..=5_300u64 {
            driver.source.push_block(&[value]);
            run_to_idle(&mut driver);
        }
        // when it restarts from its durable snapshot, its oldest checkpoint, and reads
        // back to the head
        let mut bytes = Vec::new();
        let point = driver.engine().encode_durable_snapshot(&mut bytes).unwrap();
        assert_eq!(point, Some(Position::new(5_055, 0)));
        let engine = Engine::decode_snapshot(&bytes, EngineConfig::default()).unwrap();
        let mut resumed = Driver::resume(
            engine,
            driver.source.clone(),
            RecordingFold::default(),
            DriverConfig::from_block(1),
        )
        .unwrap();
        run_to_idle(&mut resumed);
        // then a reorg of the head block rolls back to the restored cursor, not to the
        // start block
        resumed.source.reorg(1, &[&[5_300]]);
        assert_eq!(
            resumed.tick(),
            Tick::RolledBack {
                to: Some(Position::new(5_055, 0))
            }
        );
    }

    #[test]
    fn a_partial_block_fed_before_resume_is_folded_once() {
        // given an engine fed blocks 1..=9 and the first event of block 10
        let chain = three_event_chain();
        let mut engine =
            Engine::new(RecordingFold::default(), EngineConfig::default()).unwrap();
        let mut batch = Batch::new();
        for block in 1..=9 {
            batch
                .push_block(chain.header(block).unwrap(), [(0u32, 7u64), (1, 8), (2, 9)]);
        }
        batch.push_block(chain.header(10).unwrap(), [(0u32, 7u64)]);
        engine.apply_batch(&batch).unwrap();
        assert_eq!(engine.cursor(), Some(Position::new(10, 0)));
        // when a driver resumes it and polls to the head
        let mut driver = Driver::resume(
            engine,
            chain,
            RecordingFold::default(),
            DriverConfig::from_block(1),
        )
        .unwrap();
        run_to_idle(&mut driver);
        // then the fold holds every event once
        assert_folded_once(driver.engine().fold());
    }

    #[test]
    fn a_head_below_the_cursor_changes_nothing() {
        // given a driver caught up on node a, blocks 0..=3 with events at 0, 2 and 3; node
        // b stops at block 1, and node c at block 0
        let mut a = ScriptedChain::new(0);
        a.set_window(10);
        a.push_block(&[1]);
        a.push_block(&[]);
        let b = a.clone();
        a.push_block(&[2]);
        a.push_block(&[3]);
        let mut c = b.clone();
        c.reorg(1, &[]);
        let mut driver = Driver::new(
            RecordingFold::default(),
            Pool::new(a, b),
            engine_config(2),
            DriverConfig::from_block(0),
        )
        .unwrap();
        run_to_idle(&mut driver);
        let before = driver.engine().fold().clone();
        // when every call of one poll goes to b, then to c
        driver.source.route = b"BBBBBBBBBB".to_vec();
        let at_one = driver.tick();
        driver.source.b = c;
        driver.source.route = b"BBBBBBBBBB".to_vec();
        let at_zero = driver.tick();
        driver.source.route.clear();
        // then neither rolls back or resyncs, and the fold is kept
        assert_eq!(at_one, Tick::Behind);
        assert_eq!(at_zero, Tick::Behind);
        assert_eq!(driver.engine().fold(), &before);
        assert_eq!(run_to_idle(&mut driver), Tick::Idle);
        assert_eq!(driver.engine().fold().applied, pool_canonical(&driver));
    }

    #[test]
    fn a_lower_head_off_the_cursor_block_is_not_behind() {
        // given a driver at the tip of blocks 0..=10, events at 0 and 2, so the cursor is
        // block 2 and the tip block 10
        let mut chain = ScriptedChain::new(0);
        chain.push_block(&[1]);
        chain.push_block(&[]);
        chain.push_block(&[2]);
        for _ in 3..=10 {
            chain.push_block(&[]);
        }
        let mut driver = new_driver(chain, engine_config(2), DriverConfig::from_block(0));
        run_to_idle(&mut driver);
        assert_eq!(driver.engine().cursor().map(|c| c.block), Some(2));
        // when the chain reorgs to a shorter one that replaces the cursor block: its head
        // is block 3, whose parent is not the block 2 the ring holds
        driver.source.reorg(9, &[&[9], &[]]);
        let first = driver.tick();
        // then the head is not taken as a lagging node, and the fold follows the new chain
        assert_ne!(first, Tick::Behind);
        let mut n = 0;
        while driver.tick() != Tick::Idle && n < 20 {
            n += 1;
        }
        assert_eq!(
            driver.engine().fold().applied,
            vec![(Position::new(0, 0), 1), (Position::new(2, 0), 9)]
        );
    }

    #[test]
    fn a_head_at_the_cursor_block_without_a_tip_is_not_behind() {
        // given a driver at the tip of blocks 0..=5, events at 0 and 5, so the cursor is the
        // head block 5, and an engine_mut call that clears the tip
        let mut chain = ScriptedChain::new(0);
        chain.push_block(&[1]);
        for _ in 1..5 {
            chain.push_block(&[]);
        }
        chain.push_block(&[5]);
        let mut driver = new_driver(chain, engine_config(2), DriverConfig::from_block(0));
        run_to_idle(&mut driver);
        assert_eq!(driver.engine().cursor(), Some(Position::new(5, 0)));
        driver.engine_mut();
        // when polled with the head still at the cursor block
        let tick = driver.tick();
        // then the head is not taken as a lagging node: the driver is caught up
        assert_eq!(tick, Tick::Idle);
        assert!(driver.is_caught_up());
    }

    #[test]
    fn an_error_mid_walk_does_not_livelock() {
        // given a driver that folded block 0's event, over 1000 empty blocks and then an
        // event at block 1001, ten blocks per window, on a source whose every 25th call fails
        let mut chain = ScriptedChain::new(0);
        chain.set_window(10);
        chain.push_block(&[1]);
        for _ in 0..1000 {
            chain.push_block(&[]);
        }
        let mut driver = Driver::new(
            RecordingFold::default(),
            Counted {
                inner: chain,
                calls: 0,
                period: None,
                budget: None,
            },
            engine_config(2),
            DriverConfig::from_block(0),
        )
        .unwrap();
        driver.tick();
        driver.source.period = Some(25);
        driver.source.inner.push_block(&[42]);
        // when polled forty times
        for _ in 0..40 {
            driver.tick();
        }
        // then the event at block 1001 is folded
        assert!(
            driver
                .engine()
                .fold()
                .applied
                .contains(&(Position::new(1001, 0), 42))
        );
    }

    #[test]
    fn a_long_gap_is_walked_in_capped_ticks() {
        // given a driver caught up on block 1, then 200 empty blocks, one per window
        let mut driver = counted_driver(one_event_chain(1));
        run_to_idle(&mut driver);
        for _ in 2..=201 {
            driver.source.inner.push_block(&[]);
        }
        // when polled until idle
        let mut ticks = Vec::new();
        loop {
            let tick = counted_tick(&mut driver);
            ticks.push((tick, driver.is_caught_up(), driver.next_delay()));
            if tick.0 == Tick::Idle {
                break;
            }
        }
        // then each tick reads at most 64 windows, plus the head twice: three from the
        // cursor block or the last tick's end, with nothing new, not caught up and no
        // delay, and then the last nine windows
        let capped = (
            (Tick::Progressed(ApplySummary::default()), 66),
            false,
            Duration::ZERO,
        );
        let last = (
            (Tick::Idle, 11),
            true,
            DriverConfig::default().poll_interval,
        );
        assert_eq!(ticks, vec![capped, capped, capped, last]);
        assert_eq!(driver.engine().cursor(), Some(Position::new(1, 0)));
    }

    #[test]
    fn a_lost_tip_under_a_far_head_walks_twice_in_one_tick() {
        // given a driver caught up on block 1 with a tip at block 100, one block per window;
        // then the tip block reorgs away and 200 empty blocks follow
        let mut driver = counted_driver(one_event_chain(1));
        run_to_idle(&mut driver);
        for _ in 2..=100 {
            driver.source.inner.push_block(&[]);
        }
        run_to_idle(&mut driver);
        driver.source.inner.reorg(1, &[&[]]);
        for _ in 0..200 {
            driver.source.inner.push_block(&[]);
        }
        // when polled once
        let tick = counted_tick(&mut driver);
        // then it reads the head, 64 windows above the tip and the tip's header, which is
        // gone, then 64 windows from the cursor block and the head block's header again
        assert_eq!(tick, (Tick::Progressed(ApplySummary::default()), 131));
    }

    #[test]
    fn a_burst_limited_source_still_catches_up() {
        // given a driver caught up on block 1, then 200 empty blocks, one per window, and an
        // event at block 202, on a source that answers ten calls a tick
        let mut driver = counted_driver(one_event_chain(1));
        run_to_idle(&mut driver);
        for _ in 2..=201 {
            driver.source.inner.push_block(&[]);
        }
        driver.source.inner.push_block(&[202]);
        // when polled until idle, with the budget set again before each tick
        let mut ticks = 0;
        loop {
            driver.source.budget = Some(10);
            ticks += 1;
            if driver.tick() == Tick::Idle || ticks == 1_000 {
                break;
            }
        }
        // then the walk shrinks to what the budget allows and grows back: three failed
        // ticks, then a tick of eight windows and a failed one in turn, to the event
        assert_eq!(ticks, 54);
        let chain = driver.source.inner.clone();
        assert_eq!(driver.engine().fold().applied, canonical_fold(chain));
    }

    #[test]
    fn a_partial_tip_resumes_from_its_end() {
        // given a driver over node a, block 0 with an event and then 300 empty blocks, two
        // per window; node b is a without its last block
        let mut a = ScriptedChain::new(0);
        a.set_window(2);
        a.push_block(&[1]);
        for _ in 0..300 {
            a.push_block(&[]);
        }
        let mut b = a.clone();
        b.reorg(1, &[]);
        let mut driver = Driver::new(
            RecordingFold::default(),
            Pool::new(a, b),
            engine_config(2),
            DriverConfig::from_block(0),
        )
        .unwrap();
        assert!(matches!(driver.tick(), Tick::Progressed(_)));
        // when a tick walks 64 windows from the cursor block, one head call then goes to b,
        // and block 301 lands before the next poll
        let capped = pool_tick(&mut driver);
        driver.source.route = b"B".to_vec();
        let lagging = pool_tick(&mut driver);
        driver.source.a.push_block(&[]);
        let resumed = pool_tick(&mut driver);
        // then the walk stops at block 127, the head below the tip's waits, and the next
        // walk starts at block 128 with no read of the tip: its head is the new head's
        // parent
        let progressed = Tick::Progressed(ApplySummary::default());
        assert_eq!(capped, (progressed, 66));
        assert_eq!(lagging, (Tick::Behind, 1));
        assert_eq!(resumed, (progressed, 66));
        let head = driver.source.a.tip().unwrap();
        assert_eq!(
            driver.tip,
            Some(Mark {
                at: head,
                done: 255
            })
        );
        run_to_idle(&mut driver);
        assert_eq!(driver.engine().fold().applied, pool_canonical(&driver));

        // given the same driver after its first capped tick, with node b holding another
        // block at the tip's height
        let mut a = ScriptedChain::new(0);
        a.set_window(2);
        a.push_block(&[1]);
        for _ in 0..300 {
            a.push_block(&[]);
        }
        let mut b = a.clone();
        b.reorg(1, &[&[]]);
        let mut driver = Driver::new(
            RecordingFold::default(),
            Pool::new(a, b),
            engine_config(2),
            DriverConfig::from_block(0),
        )
        .unwrap();
        driver.tick();
        pool_tick(&mut driver);
        // when every call of the next poll goes to b
        driver.source.route = [b'B'; 100].to_vec();
        let sibling = pool_tick(&mut driver);
        driver.source.route.clear();
        // then the head disproves the tip, and the walk starts again at the cursor block
        assert_eq!(sibling, (Tick::Progressed(ApplySummary::default()), 66));
        run_to_idle(&mut driver);
        assert_eq!(driver.engine().fold().applied, pool_canonical(&driver));
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

/// `scan`'s cadence marks: with no tip, lowered to the cursor once the head is read
/// (always when the scan is `ok`), else as they were.
spec fn marks_lowered<F: Fold, S: Source<Event = F::Event>, K: SnapshotSink<F>>(
    pre: Driver<F, S, K>,
    post: Driver<F, S, K>,
    ok: bool,
) -> bool {
    let kept = post.last_checkpoint_block == pre.last_checkpoint_block && post.last_snapshot_block
        == pre.last_snapshot_block;
    let lowered = post.last_checkpoint_block == clamp_spec(pre.last_checkpoint_block, pre.engine@.cursor)
        && post.last_snapshot_block == clamp_spec(pre.last_snapshot_block, pre.engine@.cursor);
    if pre.tip is Some {
        kept
    } else if ok {
        lowered
    } else {
        kept || lowered
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
    &&& r is Terminal ==> post == (Driver { engine: post.engine, caught_up: false, ..mid })
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

/// A driver built around engine `e` takes a checkpoint: checkpoints are on, and `e` has a
/// cursor and no live checkpoint.
pub open spec fn resume_checkpoint(e: EngineView, c: DriverConfig) -> bool {
    &&& c.checkpoint_interval is Some
    &&& e.cursor is Some
    &&& live_count(e.slots, e.ring, e.slots.len() as int) == 0
}

/// The engine a driver built around engine `e` holds.
pub open spec fn resumed(e: EngineView, c: DriverConfig) -> EngineView {
    if resume_checkpoint(e, c) {
        checkpointed(e)
    } else {
        e
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

/// `scan`'s lowest height for events: one past the cursor block, else the start block.
pub open spec fn scan_floor(cursor: Option<Position>, start: u64) -> int {
    match cursor {
        Some(c) => c.block + 1,
        None => start as int,
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

/// Window `i`'s lowest height for events: its first block, or the next one for a walk's
/// first window when that block is the floor.
pub open spec fn wlo(wins: Seq<(int, int)>, floor: bool, i: int) -> int {
    if floor && i == 0 {
        wins[0].0 + 1
    } else {
        wins[i].0
    }
}

/// `take_floor` keeps entry `x`: it lies above block `floor`, or at it after log index
/// `after`.
pub open spec fn past_floor<E>(x: (BlockRef, u32, E), floor: u64, after: u64) -> bool {
    x.0.number > floor || (x.0.number == floor && x.1 as u64 > after)
}

/// Entries of view `v`'s block `p.block` after `p`: none when `p` ends its block.
pub open spec fn kept<S, E>(v: ChainView, p: Position) -> vstd::multiset::Multiset<(BlockRef, u32, E)> {
    block_entries::<S, E>(v, p.block).to_multiset().filter(|x: (BlockRef, u32, E)| x.1 as u64 > p.log_index)
}

/// What a walk keeps of its first window's floor block `from` in view `v`: the entries
/// after log index `after`, for a walk with a floor.
pub open spec fn fkept<S, E>(v: ChainView, floor: bool, from: u64, after: u64) -> vstd::multiset::Multiset<
    (BlockRef, u32, E),
> {
    if floor {
        kept::<S, E>(v, Position { block: from, log_index: after })
    } else {
        vstd::multiset::Multiset::empty()
    }
}

/// `walk`'s Ok result over `hist` from `l0`, one view per window `wins` from `from`: the
/// windows before the last hold no entry from their `wlo` on, the batch's entries `t` are
/// the last window's from its `wlo` on, plus, for a first window with a floor, the floor
/// block's entries after log index `after`, and an empty batch's windows reach `hi`. `at` is
/// the first answer's header for block `from`; without `at`, that answer had no entry there.
pub open spec fn walked<S, E>(
    hist: Seq<ChainView>,
    l0: int,
    from: u64,
    hi: u64,
    w: u64,
    floor: bool,
    after: u64,
    wins: Seq<(int, int)>,
    t: Seq<(BlockRef, u32, E)>,
    at: Option<BlockRef>,
    n: u8,
    reached: bool,
) -> bool {
    let m = wins.len() as int;
    &&& hist.len() == l0 + m
    &&& w >= 1
    &&& n as int == if m < 2 { m } else { 2 }
    &&& reached == (m > 0 && wins[m - 1].1 == hi)
    &&& scan_windows(wins, from as int, w, hi)
    &&& forall|i: int|
        0 <= i < m - 1 ==> range_entries::<S, E>(hist[l0 + i], wlo(wins, floor, i), (#[trigger] wins[i]).1).len() == 0
    &&& m > 0 ==> t.to_multiset() == range_entries::<S, E>(
        hist[l0 + m - 1],
        wlo(wins, floor, m - 1),
        wins[m - 1].1,
    ).to_multiset().add(fkept::<S, E>(hist[l0 + m - 1], floor && m == 1, from, after))
    &&& m == 0 ==> t.len() == 0 && from > hi
    &&& t.len() == 0 && m > 0 ==> wins[m - 1].1 == hi
    &&& at matches Some(b) ==> floor && m > 0 && header(hist[l0], from) == Some(b)
    &&& floor && m > 0 && at is None ==> block_entries::<S, E>(hist[l0], from).len() == 0
}

/// `scan`'s Ok(true) result over the source log `hist` from `l0`, for a batch `b` read
/// above cursor `c`, with the scan tip `t0` before the scan and `t1` after it.
spec fn scanned<S, E>(
    hist: Seq<ChainView>,
    l0: int,
    start: u64,
    c: Option<Position>,
    t0: Option<Mark>,
    t1: Option<Mark>,
    b: BatchView<E>,
) -> bool {
    exists|s: (int, BlockRef, int, int, int, int, int, bool)| #[trigger] scan_view::<S, E>(hist, l0, start, c, t0, t1, b, s)
}

/// One witness of `scanned`. `s.0` names the view the tick concludes in, `s.1` the head
/// block the first call read, `s.2` that view's anchor height, `[s.3, s.4]` the batch's
/// window, and `s.5`, `s.6` the view and anchor height that vouch for a new tip; with
/// `s.7`, the batch also holds the cursor block's entries after the cursor. Under
/// `views_ok`, the view is anchored, holds nothing from the anchor to the window, and holds
/// the batch's entries as the window's. A new tip has the head at its `done` or above,
/// and the vouching view holds the head: with a batch, that view is the tick's, its window
/// reaches the head and so does `done`; without one, that view is anchored and holds
/// nothing from its anchor through `done`.
spec fn scan_view<S, E>(
    hist: Seq<ChainView>,
    l0: int,
    start: u64,
    c: Option<Position>,
    t0: Option<Mark>,
    t1: Option<Mark>,
    b: BatchView<E>,
    s: (int, BlockRef, int, int, int, int, int, bool),
) -> bool {
    let (k, hd, a, wlo, whi, j, aj, f) = s;
    &&& l0 <= k < hist.len()
    &&& l0 <= j < hist.len()
    &&& header(hist[l0], hd.number) == Some(hd)
    &&& a <= wlo <= whi + 1
    &&& whi <= u64::MAX
    &&& t1 == t0 || t1 is None || (t1 matches Some(m) && m.at == hd && m.done <= hd.number && a <= m.done + 1 && aj
        <= m.done + 1)
    &&& t1 == t0 && t0 is Some ==> b.triples().len() == 0
    &&& views_ok(hist, l0, start) && (c matches Some(p) ==> p.block >= start) && (t0 matches Some(m) ==> m.done + 1
        >= start) ==> {
        &&& anchored(hist, k, c, t0, b.boundary, start, a)
        &&& range_entries::<S, E>(hist[k], a, wlo - 1).len() == 0
        &&& if f && c is Some {
            b.triples().to_multiset() == range_entries::<S, E>(hist[k], wlo, whi).to_multiset().add(
                kept::<S, E>(hist[k], c.unwrap()),
            )
        } else {
            b.triples().to_multiset() == range_entries::<S, E>(hist[k], wlo, whi).to_multiset()
        }
        &&& t1 is Some && t1 != t0 ==> {
            &&& header(hist[j], hd.number) == Some(hd)
            &&& if b.triples().len() > 0 {
                j == k && whi == hd.number && t1.unwrap().done == hd.number
            } else {
                anchored(hist, j, c, t0, b.boundary, start, aj)
                    && range_entries::<S, E>(hist[j], aj, t1.unwrap().done as int).len() == 0
            }
        }
    }
}

/// View `hist[k]` ties a scan to the engine's state below height `a`: `a` is one past the
/// cursor block, which the view holds as the boundary `bd`; the start block, with no
/// cursor; or one past the old tip `t0`'s `done`, where the view holds the tip's head when
/// it lies at or above the start block.
spec fn anchored(
    hist: Seq<ChainView>,
    k: int,
    c: Option<Position>,
    t0: Option<Mark>,
    bd: Option<BlockRef>,
    start: u64,
    a: int,
) -> bool {
    ||| c is Some && a == c.unwrap().block + 1 && header(hist[k], c.unwrap().block) == bd
    ||| c is None && a == start
    ||| t0 matches Some(m) && a == m.done + 1 && (m.at.number >= start ==> header(hist[k], m.at.number) == Some(m.at))
}

/// What a tick needs of its views over `hist` from `l0` (A2 iii, iv): each holds every
/// height from `start` up to each height it holds, and a block the first view holds is in
/// every view between two views that hold it.
#[verifier::opaque]
pub open spec fn views_ok(hist: Seq<ChainView>, l0: int, start: u64) -> bool {
    &&& forall|k: int| l0 <= k < hist.len() ==> from_start(#[trigger] hist[k], start)
    &&& forall|x: BlockRef| #[trigger] header(hist[l0], x.number) == Some(x) ==> no_aba(hist, l0, x)
}

/// Scan tip `t` holds nothing left to fold above cursor `c` up to its `done`, as a fact of
/// its head's hash: every view that holds the head agrees with `h` below the floor and
/// holds no entry from the floor through `done`, which is at most the head.
spec fn mark_ok<S, E>(t: Option<Mark>, c: Option<Position>, h: ChainView, start: u64) -> bool {
    match t {
        Some(m) => mark_vouched::<S, E>(m, c, h, start),
        None => true,
    }
}

spec fn mark_vouched<S, E>(m: Mark, c: Option<Position>, h: ChainView, start: u64) -> bool {
    &&& m.done <= m.at.number
    &&& scan_floor(c, start) <= m.done + 1
    &&& forall|v: ChainView| #[trigger] mark_seen::<S, E>(m, c, h, start, v)
}

spec fn mark_seen<S, E>(m: Mark, c: Option<Position>, h: ChainView, start: u64, v: ChainView) -> bool {
    let lo = scan_floor(c, start);
    a1::<S, E>(v) && from_start(v, start) && header(v, m.at.number) == Some(m.at) ==> {
        &&& forall|n: u64| start <= n < lo ==> #[trigger] header(v, n) == header(h, n)
        &&& range_entries::<S, E>(v, lo, m.done as int).len() == 0
    }
}

/// Every view from `start` that holds block `hd` holds block `t`, when `t` lies at or above
/// `start`.
#[verifier::opaque]
spec fn carries<S, E>(hd: BlockRef, t: BlockRef, start: u64) -> bool {
    t.number >= start ==> forall|v: ChainView|
        a1::<S, E>(v) && from_start(v, start) && #[trigger] header(v, hd.number) == Some(hd) ==> header(v, t.number)
            == Some(t)
}

/// No ABA on block `x` in `hist` from `from`: a view between two views that hold `x` holds it.
pub open spec fn no_aba(hist: Seq<ChainView>, from: int, x: BlockRef) -> bool {
    forall|i: int, j: int, k: int|
        #![trigger header(hist[i], x.number), header(hist[j], x.number), header(hist[k], x.number)]
        from <= i < j < k < hist.len() && header(hist[i], x.number) == Some(x) && header(
            hist[k],
            x.number,
        ) == Some(x) ==> header(hist[j], x.number) == Some(x)
}

/// `v` holds every height from `start` up to each height it holds.
pub open spec fn from_start(v: ChainView, start: u64) -> bool {
    forall|n: u64, m: u64| #[trigger] v.contains_key(n) && start <= m <= n ==> #[trigger] v.contains_key(m)
}

/// A view of `hist` from `l0` lacks block `b`: the chain moved under the calls.
pub open spec fn lost(hist: Seq<ChainView>, l0: int, b: BlockRef) -> bool {
    exists|k: int| l0 <= k < hist.len() && #[trigger] header(hist[k], b.number) != Some(b)
}

/// The source log `hist` from `l0` holds a view other than its first.
pub open spec fn moved(hist: Seq<ChainView>, l0: int) -> bool {
    exists|k: int| l0 <= k < hist.len() && #[trigger] hist[k] != hist[l0]
}

/// The boundary `bd` of a batch scanned above cursor `c`: the cursor block as the ring
/// holds it (`last`), or as a view of the source log `hist` from `l0` answered it.
pub open spec fn boundary_read(
    hist: Seq<ChainView>,
    l0: int,
    c: Option<Position>,
    last: BlockRef,
    bd: Option<BlockRef>,
) -> bool {
    c matches Some(p) ==> bd == Some(last) || exists|k: int|
        l0 <= k < hist.len() && bd == #[trigger] header(hist[k], p.block)
}

/// Head `hd` lies below tip `t` or cursor `c`'s block, and agrees with `ring`.
pub open spec fn behind(hd: Head, t: Option<BlockRef>, c: Option<Position>, ring: Seq<BlockRef>) -> bool {
    &&& (t matches Some(t) && hd.block.number < t.number) || (c matches Some(c) && hd.block.number < c.block)
    &&& ring_agrees(hd, ring)
}

/// Every hash `ring` holds at head `hd`'s height is `hd`'s, and every one at the height
/// below is its parent's.
/// `hd` is a head read from view `v`: its block is `v`'s block at its height, and its
/// parent is the block that block's hash commits to.
pub open spec fn head_read(v: ChainView, hd: Head) -> bool {
    &&& header(v, hd.block.number) == Some(hd.block)
    &&& hd.block.number > 0 ==> anc(hd.block.hash, (hd.block.number - 1) as u64).hash == hd.parent
}

pub open spec fn ring_agrees(hd: Head, ring: Seq<BlockRef>) -> bool {
    &&& forall|i: int|
        0 <= i < ring.len() && (#[trigger] ring[i]).number == hd.block.number ==> ring[i].hash == hd.block.hash
    &&& forall|i: int| 0 <= i < ring.len() && (#[trigger] ring[i]).number + 1 == hd.block.number ==> ring[i].hash
        == hd.parent
}

/// A batch `validate` accepts, whose boundary, if any, is at cursor `c`'s block.
pub open spec fn shaped_at<E>(b: BatchView<E>, c: Option<Position>) -> bool {
    &&& b.shaped()
    &&& c is Some && b.boundary is Some ==> b.boundary.unwrap().number == c.unwrap().block
}

/// A view that lacks block `b`, which view `l0` holds, differs from view `l0`.
proof fn lemma_lost_moved(hist: Seq<ChainView>, l0: int, from: int, b: BlockRef)
    requires
        0 <= l0 <= from,
        l0 < hist.len(),
        header(hist[l0], b.number) == Some(b),
        lost(hist, from, b),
    ensures
        moved(hist, l0),
{
    let k = choose|k: int| from <= k < hist.len() && #[trigger] header(hist[k], b.number) != Some(b);
    assert(hist[k] != hist[l0]);
}

/// `post` is the source log `pre` followed by more views, each satisfying `a1`.
pub open spec fn grew<S, E>(pre: Seq<ChainView>, post: Seq<ChainView>) -> bool {
    &&& pre.len() <= post.len()
    &&& post.subrange(0, pre.len() as int) == pre
    &&& forall|k: int| pre.len() <= k < post.len() ==> a1::<S, E>(#[trigger] post[k])
}

proof fn lemma_grew_refl<S, E>(p: Seq<ChainView>)
    ensures
        grew::<S, E>(p, p),
{
    assert(p.subrange(0, p.len() as int) =~= p);
}

/// From `grew(pre, cur)`: one more view keeps it, and so does any growth of `cur`.
proof fn lemma_grew_next<S, E>(pre: Seq<ChainView>, cur: Seq<ChainView>)
    requires
        grew::<S, E>(pre, cur),
    ensures
        forall|v: ChainView| a1::<S, E>(v) ==> #[trigger] grew::<S, E>(pre, cur.push(v)),
        forall|p: Seq<ChainView>| #[trigger] grew::<S, E>(cur, p) ==> grew::<S, E>(pre, p),
        forall|k: int| pre.len() <= k < cur.len() ==> a1::<S, E>(#[trigger] cur[k]),
        forall|k: int| 0 <= k < pre.len() ==> #[trigger] cur[k] == pre[k],
{
    assert forall|k: int| 0 <= k < pre.len() implies #[trigger] cur[k] == pre[k] by {
        assert(cur.subrange(0, pre.len() as int)[k] == cur[k]);
    }
    assert forall|v: ChainView| a1::<S, E>(v) implies #[trigger] grew::<S, E>(pre, cur.push(v)) by {
        assert(cur.push(v).subrange(0, pre.len() as int) =~= pre);
    }
    assert forall|p: Seq<ChainView>| #[trigger] grew::<S, E>(cur, p) implies grew::<S, E>(pre, p) by {
        assert forall|k: int| 0 <= k < cur.len() implies #[trigger] p[k] == cur[k] by {
            assert(p.subrange(0, cur.len() as int)[k] == p[k]);
        }
        assert(p.subrange(0, pre.len() as int) =~= pre);
    }
}

proof fn lemma_from_start(v: ChainView, start: u64, n: u64)
    requires
        from_start(v, start),
        v.contains_key(n),
    ensures
        holds(v, start, n),
{
    assert forall|m: u64| start <= m <= n implies #[trigger] v.contains_key(m) by {
        assert(v.contains_key(n));
    }
}

/// Every window of `wins` from `first` lies in `[first, h]` and is not empty.
proof fn lemma_wins_bounds(wins: Seq<(int, int)>, first: int, w: u64, h: u64, i: int)
    requires
        scan_windows(wins, first, w, h),
        w >= 1,
        0 <= i < wins.len(),
    ensures
        first <= wins[i].0 <= wins[i].1 <= h,
        i > 0 ==> wins[0].1 < wins[i].0,
    decreases i,
{
    assert(wins[i].0 <= h);
    if i > 0 {
        lemma_wins_bounds(wins, first, w, h, i - 1);
        assert(wins[i].0 == wins[i - 1].1 + 1);
    }
}

/// The windows before window `i` of a walk hold no entry from the floor on in view `v`, when
/// `v` agrees with each window's view on that window.
proof fn lemma_walk_empty<S, E>(
    hist: Seq<ChainView>,
    base: int,
    from: u64,
    hi: u64,
    w: u64,
    floor: bool,
    wins: Seq<(int, int)>,
    v: ChainView,
    i: int,
)
    requires
        scan_windows(wins, from as int, w, hi),
        w >= 1,
        0 <= i < wins.len(),
        forall|j: int|
            0 <= j < i ==> range_entries::<S, E>(hist[base + j], wlo(wins, floor, j), (#[trigger] wins[j]).1).len() == 0,
        forall|j: int, n: u64|
            0 <= j < i && wins[j].0 <= n <= wins[j].1 ==> #[trigger] header(hist[base + j], n) == header(v, n),
    ensures
        from + (if floor { 1int } else { 0int }) <= wlo(wins, floor, i) <= wins[i].1 + 1,
        range_entries::<S, E>(v, from + (if floor { 1int } else { 0int }), wlo(wins, floor, i) - 1).len() == 0,
    decreases i,
{
    let lo = from + (if floor { 1int } else { 0int });
    lemma_wins_bounds(wins, from as int, w, hi, i);
    if i > 0 {
        let j = i - 1;
        lemma_walk_empty::<S, E>(hist, base, from, hi, w, floor, wins, v, j);
        lemma_wins_bounds(wins, from as int, w, hi, j);
        assert(wins[i].0 == wins[j].1 + 1);
        lemma_re_split::<S, E>(v, lo, wlo(wins, floor, j) - 1, wins[j].1);
        assert forall|n: u64| wlo(wins, floor, j) <= n <= wins[j].1 implies #[trigger] header(hist[base + j], n)
            == header(v, n) by {}
        lemma_re_agree::<S, E>(hist[base + j], v, wlo(wins, floor, j), wins[j].1);
    }
}

/// A window's answer without its entries at or below block `lo` is the answer from `lo + 1`
/// on; an entry at `lo` carries the view's header there.
proof fn lemma_floor<S, E>(
    v: ChainView,
    lo: u64,
    hi: u64,
    pre: Seq<(BlockRef, u32, E)>,
    post: Seq<(BlockRef, u32, E)>,
    after: u64,
)
    requires
        chain(v),
        lo <= hi,
        pre.to_multiset() == range_entries::<S, E>(v, lo as int, hi as int).to_multiset(),
        forall|x: (BlockRef, u32, E)| #[trigger] post.to_multiset().count(x)
            == if past_floor(x, lo, after) { pre.to_multiset().count(x) } else { 0 },
    ensures
        post.to_multiset() == range_entries::<S, E>(v, lo + 1, hi as int).to_multiset().add(
            kept::<S, E>(v, Position { block: lo, log_index: after }),
        ),
        forall|i: int| 0 <= i < pre.len() && pre[i].0.number == lo ==> header(v, lo) == Some(#[trigger] pre[i].0),
        (forall|i: int| 0 <= i < pre.len() ==> #[trigger] pre[i].0.number != lo) ==> block_entries::<S, E>(
            v,
            lo,
        ).len() == 0,
{
    broadcast use vstd::multiset::group_multiset_axioms;
    let a = range_entries::<S, E>(v, lo as int, lo as int);
    let b = range_entries::<S, E>(v, lo + 1, hi as int);
    lemma_re_split::<S, E>(v, lo as int, lo as int, hi as int);
    vstd::seq_lib::lemma_multiset_commutative(a, b);
    lemma_re_facts::<S, E>(v, lo as int, lo as int);
    lemma_re_facts::<S, E>(v, lo + 1, hi as int);
    let kp = kept::<S, E>(v, Position { block: lo, log_index: after });
    assert(a =~= block_entries::<S, E>(v, lo)) by {
        assert(range_entries::<S, E>(v, lo as int, lo as int) =~= range_entries::<S, E>(v, lo as int, lo - 1)
            + block_entries::<S, E>(v, lo));
    }
    assert(post.to_multiset() =~= b.to_multiset().add(kp)) by {
        assert forall|x: (BlockRef, u32, E)| post.to_multiset().count(x) == b.to_multiset().add(kp).count(x) by {
            vstd::seq_lib::to_multiset_contains(a, x);
            vstd::seq_lib::to_multiset_contains(b, x);
            if a.contains(x) {
                let j = choose|j: int| 0 <= j < a.len() && a[j] == x;
            }
            if b.contains(x) {
                let j = choose|j: int| 0 <= j < b.len() && b[j] == x;
            }
        }
    }
    assert forall|i: int| 0 <= i < pre.len() && pre[i].0.number == lo implies header(v, lo) == Some(
        #[trigger] pre[i].0,
    ) by {
        let x = pre[i];
        vstd::seq_lib::to_multiset_contains(pre, x);
        vstd::seq_lib::to_multiset_contains(a, x);
        vstd::seq_lib::to_multiset_contains(b, x);
        if b.contains(x) {
            let j = choose|j: int| 0 <= j < b.len() && b[j] == x;
        }
        let j = choose|j: int| 0 <= j < a.len() && a[j] == x;
    }
    if forall|i: int| 0 <= i < pre.len() ==> #[trigger] pre[i].0.number != lo {
        assert(range_entries::<S, E>(v, lo as int, lo as int) =~= range_entries::<S, E>(v, lo as int, lo - 1)
            + block_entries::<S, E>(v, lo));
        assert(range_entries::<S, E>(v, lo as int, lo - 1).len() == 0);
        if block_entries::<S, E>(v, lo).len() > 0 {
            let x = a[0];
            vstd::seq_lib::to_multiset_contains(a, x);
            vstd::seq_lib::to_multiset_contains(pre, x);
            let i = choose|i: int| 0 <= i < pre.len() && pre[i] == x;
            assert(pre[i].0.number != lo);
        }
    }
}

/// A walk's windows over `h2` from `w0` through `hi`, inside a tick over `hist` from `l0`
/// whose first view read the head `hd`, at or above `hi`. Its last window's view holds the
/// batch as the window's entries. With the head read again last, that view also holds
/// nothing from the floor to the window, and every view of the tick agrees with it up to
/// the head.
proof fn lemma_walk_core<S, E>(
    hist: Seq<ChainView>,
    h2: Seq<ChainView>,
    l0: int,
    w0: int,
    start: u64,
    hd: BlockRef,
    from: u64,
    hi: u64,
    w: u64,
    floor: bool,
    after: u64,
    wins: Seq<(int, int)>,
    t: Seq<(BlockRef, u32, E)>,
    at: Option<BlockRef>,
    n: u8,
    reached: bool,
)
    requires
        0 <= l0,
        l0 + 1 <= w0,
        grew::<S, E>(h2, hist),
        header(hist[l0], hd.number) == Some(hd),
        forall|q: int| l0 <= q < hist.len() ==> a1::<S, E>(#[trigger] hist[q]),
        hi <= hd.number,
        walked::<S, E>(h2, w0, from, hi, w, floor, after, wins, t, at, n, reached),
        n > 0 ==> hist.len() > h2.len() && header(hist.last(), hd.number) == Some(hd),
    ensures
        ({
            let m = wins.len() as int;
            let k = w0 + m - 1;
            let lo = from + if floor { 1int } else { 0int };
            &&& m > 0 ==> {
                &&& lo <= wlo(wins, floor, m - 1) <= wins[m - 1].1 + 1
                &&& wins[m - 1].1 <= hi
                &&& from <= hi
                &&& hist[k] == h2[k]
                &&& !(floor && m == 1) ==> t.to_multiset() == range_entries::<S, E>(
                    hist[k],
                    wlo(wins, floor, m - 1),
                    wins[m - 1].1,
                ).to_multiset()
                &&& floor && m == 1 ==> t.to_multiset() == range_entries::<S, E>(
                    hist[k],
                    wlo(wins, floor, m - 1),
                    wins[m - 1].1,
                ).to_multiset().add(kept::<S, E>(hist[k], Position { block: from, log_index: after }))
                &&& reached == (wins[m - 1].1 == hi)
                &&& t.len() == 0 ==> reached
                &&& views_ok(hist, l0, start) && from >= start ==> range_entries::<S, E>(
                    hist[k],
                    lo,
                    wlo(wins, floor, m - 1) - 1,
                ).len() == 0
                &&& views_ok(hist, l0, start) && from >= start ==> forall|q: int, x: u64|
                    l0 <= q < hist.len() && start <= x <= hd.number ==> #[trigger] header(hist[q], x) == header(
                        hist[k],
                        x,
                    )
            }
            &&& m == 0 ==> from > hi && t.len() == 0 && !reached
        }),
{
    let m = wins.len() as int;
    let k = w0 + m - 1;
    lemma_grew_next::<S, E>(h2, hist);
    if m > 0 {
        lemma_wins_bounds(wins, from as int, w, hi, 0);
        lemma_wins_bounds(wins, from as int, w, hi, m - 1);
        assert(hist[k] == h2[k]);
        if !(floor && m == 1) {
            broadcast use vstd::multiset::group_multiset_axioms;
            let r = range_entries::<S, E>(hist[k], wlo(wins, floor, m - 1), wins[m - 1].1).to_multiset();
            assert(r.add(fkept::<S, E>(hist[k], false, from, after)) =~= r);
        }
        if views_ok(hist, l0, start) && from >= start {
            reveal(views_ok);
            let vk = hist[k];
            let last = hist.len() - 1;
            assert(no_aba(hist, l0, hd));
            assert forall|q: int| l0 <= q < hist.len() implies header(#[trigger] hist[q], hd.number) == Some(hd) by {
                if l0 < q && q < last {
                    assert(header(hist[l0], hd.number) == Some(hd));
                    assert(header(hist[last], hd.number) == Some(hd));
                }
            }
            assert forall|q: int, x: u64| l0 <= q < hist.len() && start <= x <= hd.number implies #[trigger] header(
                hist[q],
                x,
            ) == header(vk, x) by {
                assert(header(hist[q], hd.number) == Some(hd));
                assert(header(vk, hd.number) == Some(hd));
                assert(from_start(hist[q], start) && from_start(vk, start));
                lemma_from_start(hist[q], start, hd.number);
                lemma_from_start(vk, start, hd.number);
                lemma_view_agree(hist[q], vk, start, hd.number);
            }
            assert forall|q: int, x: u64| 0 <= q < m - 1 && wins[q].0 <= x <= wins[q].1 implies #[trigger] header(
                h2[w0 + q],
                x,
            ) == header(vk, x) by {
                lemma_wins_bounds(wins, from as int, w, hi, q);
                assert(h2[w0 + q] == hist[w0 + q]);
                assert(header(hist[w0 + q], x) == header(vk, x));
            }
            lemma_walk_empty::<S, E>(h2, w0, from, hi, w, floor, wins, vk, m - 1);
        }
    }
}

/// `scan`'s walk from the cursor block through `hi` assembles into `scanned`: the head's
/// view `h1[l0]`, the walk's windows over `h2` from `w0`, the cursor block's view
/// `h3.last()` when the walk had no entry there, and the head block's view `hist.last()`
/// read again when the walk read a window. A walk with nothing found vouches for the head
/// up to `hi`.
proof fn lemma_rung_walk<S, E>(
    hist: Seq<ChainView>,
    h2: Seq<ChainView>,
    h3: Seq<ChainView>,
    l0: int,
    w0: int,
    start: u64,
    c: Option<Position>,
    t0: Option<Mark>,
    t1: Option<Mark>,
    b: BatchView<E>,
    hd: BlockRef,
    from: u64,
    hi: u64,
    w: u64,
    after: u64,
    wins: Seq<(int, int)>,
    at: Option<BlockRef>,
    n: u8,
    reached: bool,
)
    requires
        0 <= l0,
        l0 + 1 <= w0,
        grew::<S, E>(h2, h3),
        grew::<S, E>(h3, hist),
        header(hist[l0], hd.number) == Some(hd),
        forall|q: int| l0 <= q < hist.len() ==> a1::<S, E>(#[trigger] hist[q]),
        hi <= hd.number,
        walked::<S, E>(h2, w0, from, hi, w, c is Some, after, wins, b.triples(), at, n, reached),
        c matches Some(p) ==> after == p.log_index,
        from == match c {
            Some(p) => p.block,
            None => start,
        },
        h3.len() == h2.len() + if c is Some && at is None { 1int } else { 0int },
        b.boundary == match c {
            Some(p) => match at {
                Some(a) => Some(a),
                None => header(h3.last(), p.block),
            },
            None => None,
        },
        hist.len() == h3.len() + if n > 0 { 1int } else { 0int },
        n > 0 ==> header(hist.last(), hd.number) == Some(hd),
        t1 == if reached && (hi == hd.number || b.triples().len() == 0) {
            Some(Mark { at: hd, done: hi })
        } else {
            None
        },
        t0 != Some(Mark { at: hd, done: hd.number }),
    ensures
        scanned::<S, E>(hist, l0, start, c, t0, t1, b),
{
    let m = wins.len() as int;
    let floor = c is Some;
    let f = m == 1 && floor;
    let lo = scan_floor(c, start);
    lemma_grew_next::<S, E>(h2, h3);
    lemma_grew_next::<S, E>(h3, hist);
    lemma_walk_core::<S, E>(hist, h2, l0, w0, start, hd, from, hi, w, floor, after, wins, b.triples(), at, n, reached);
    let k = if m > 0 { w0 + m - 1 } else { hist.len() - 1 };
    let (wl, wh) = if m > 0 { (wlo(wins, floor, m - 1), wins[m - 1].1) } else { (lo, lo - 1) };
    let vk = hist[k];
    assert(lo == from + if floor { 1int } else { 0int });
    if m == 0 {
        assert(hist.len() == h3.len());
        assert(hist.last() == h3.last());
    }
    if views_ok(hist, l0, start) && (c matches Some(p) ==> p.block >= start) && (t0 matches Some(t) ==> t.done + 1
        >= start) {
        if let Some(p) = c {
            if m > 0 {
                match at {
                    Some(a) => {
                        assert(header(h2[w0], from) == Some(a));
                        assert(h2[w0] == hist[w0]);
                        if m > 1 {
                            assert(header(hist[w0], p.block) == header(vk, p.block));
                        }
                    },
                    None => {
                        assert(h3.last() == hist[h3.len() - 1]);
                        assert(header(hist[h3.len() - 1], p.block) == header(vk, p.block));
                    },
                }
            }
        }
        assert(anchored(hist, k, c, t0, b.boundary, start, lo));
        if reached {
            assert(header(hist[l0], hd.number) == header(vk, hd.number));
        }
        if m == 0 {
            assert(range_entries::<S, E>(vk, lo, wl - 1) =~= Seq::empty());
            assert(b.triples() =~= range_entries::<S, E>(vk, wl, wh));
        }
        if f {
            assert(Position { block: from, log_index: after } == c.unwrap());
        }
        if t1 is Some && b.triples().len() == 0 {
            broadcast use vstd::multiset::group_multiset_axioms;
            vstd::seq_lib::to_multiset_len(b.triples());
            vstd::seq_lib::to_multiset_len(range_entries::<S, E>(vk, wl, wh));
            lemma_re_split::<S, E>(vk, lo, wl - 1, hi as int);
        }
    }
    assert(scan_view::<S, E>(hist, l0, start, c, t0, t1, b, (k, hd, lo, wl, wh, k, lo, f)));
}

/// `scan`'s walk above the tip through `hi` assembles into `scanned`: the head's view
/// `h1[l0]`, the walk's windows over `h2` from `l0 + 1`, the tip's view `h3.last()` unless
/// the head's view holds the tip (`implied`), and the head block's view `hist.last()` read
/// again.
proof fn lemma_rung_gap<S, E>(
    hist: Seq<ChainView>,
    h2: Seq<ChainView>,
    h3: Seq<ChainView>,
    l0: int,
    w0: int,
    start: u64,
    c: Option<Position>,
    tip: Mark,
    t1: Option<Mark>,
    b: BatchView<E>,
    hd: BlockRef,
    hi: u64,
    w: u64,
    wins: Seq<(int, int)>,
    n: u8,
    reached: bool,
    implied: bool,
)
    requires
        0 <= l0,
        w0 == l0 + 1,
        grew::<S, E>(h2, h3),
        grew::<S, E>(h3, hist),
        header(hist[l0], hd.number) == Some(hd),
        forall|q: int| l0 <= q < hist.len() ==> a1::<S, E>(#[trigger] hist[q]),
        tip.done < hi <= hd.number,
        tip.at.number <= hd.number,
        walked::<S, E>(h2, w0, (tip.done + 1) as u64, hi, w, false, 0, wins, b.triples(), None, n, reached),
        h3.len() == h2.len() + if implied { 0int } else { 1int },
        implied ==> carries::<S, E>(hd, tip.at, start),
        !implied ==> header(h3.last(), tip.at.number) == Some(tip.at),
        hist.len() == h3.len() + 1,
        header(hist.last(), hd.number) == Some(hd),
        t1 == if reached && (hi == hd.number || b.triples().len() == 0) {
            Some(Mark { at: hd, done: hi })
        } else {
            None
        },
    ensures
        scanned::<S, E>(hist, l0, start, c, Some(tip), t1, b),
{
    let m = wins.len() as int;
    let from = (tip.done + 1) as u64;
    let t0 = Some(tip);
    lemma_grew_next::<S, E>(h2, h3);
    lemma_grew_next::<S, E>(h3, hist);
    lemma_walk_core::<S, E>(hist, h2, l0, w0, start, hd, from, hi, w, false, 0, wins, b.triples(), None, n, reached);
    let k = w0 + m - 1;
    let (wl, wh) = (wlo(wins, false, m - 1), wins[m - 1].1);
    let vk = hist[k];
    let a = from as int;
    let p = h3.len() - 1;
    assert(hist[p] == h3.last());
    if views_ok(hist, l0, start) && (c matches Some(q) ==> q.block >= start) && tip.done + 1 >= start {
        assert(header(hist[l0], hd.number) == header(vk, hd.number));
        if tip.at.number >= start {
            if implied {
                reveal(views_ok);
                reveal(carries);
                assert(from_start(hist[l0], start));
                assert(header(hist[l0], tip.at.number) == Some(tip.at));
                assert(header(hist[l0], tip.at.number) == header(vk, tip.at.number));
            } else {
                assert(header(hist[p], tip.at.number) == header(vk, tip.at.number));
            }
        }
        assert(anchored(hist, k, c, t0, b.boundary, start, a));
        if t1 is Some && b.triples().len() == 0 {
            vstd::seq_lib::to_multiset_len(b.triples());
            vstd::seq_lib::to_multiset_len(range_entries::<S, E>(vk, wl, wh));
            lemma_re_split::<S, E>(vk, a, wl - 1, hi as int);
        }
    }
    assert(scan_view::<S, E>(hist, l0, start, c, t0, t1, b, (k, hd, a, wl, wh, k, a, false)));
}

/// `scan` with the head equal to the tip's: its one view holds the tip's head.
proof fn lemma_rung_same<S, E>(
    hist: Seq<ChainView>,
    l0: int,
    start: u64,
    c: Option<Position>,
    b: BatchView<E>,
    tip: Mark,
)
    requires
        0 <= l0,
        hist.len() == l0 + 1,
        header(hist[l0], tip.at.number) == Some(tip.at),
        b.triples().len() == 0,
    ensures
        scanned::<S, E>(hist, l0, start, c, Some(tip), Some(tip), b),
{
    let hd = tip.at;
    let a = tip.done + 1;
    assert(l0 <= l0 < hist.len() && header(hist[l0], hd.number) == Some(hd));
    assert(anchored(hist, l0, c, Some(tip), b.boundary, start, a));
    assert(range_entries::<S, E>(hist[l0], a, a - 1) =~= Seq::empty());
    assert(b.triples() =~= range_entries::<S, E>(hist[l0], a, a - 1));
    assert(scan_view::<S, E>(hist, l0, start, c, Some(tip), Some(tip), b, (l0, hd, a, a, a - 1, l0, a, false)));
}

/// A view holding head `hd`, whose parent hash is the tip's, holds the tip.
proof fn lemma_parent<S, E>(v: ChainView, hd: BlockRef, parent: [u8; 32], tip: BlockRef, start: u64)
    requires
        a1::<S, E>(v),
        from_start(v, start),
        header(v, hd.number) == Some(hd),
        anc(hd.hash, (hd.number - 1) as u64).hash == parent,
        parent == tip.hash,
        tip.number + 1 == hd.number,
        tip.number >= start,
    ensures
        header(v, tip.number) == Some(tip),
{
    lemma_from_start(v, start, hd.number);
    assert(v.contains_key(tip.number));
    assert(v[tip.number] == anc(v[hd.number].hash, tip.number));
}

/// A view that holds head `hd` holds the tip `t` when `t` is the head or its parent.
proof fn lemma_carries<S, E>(hd: Head, t: BlockRef, start: u64)
    requires
        hd.block == t || (hd.parent == t.hash && t.number + 1 == hd.block.number),
        hd.block.number > 0 ==> anc(hd.block.hash, (hd.block.number - 1) as u64).hash == hd.parent,
    ensures
        carries::<S, E>(hd.block, t, start),
{
    reveal(carries);
    assert forall|v: ChainView|
        a1::<S, E>(v) && from_start(v, start) && #[trigger] header(v, hd.block.number) == Some(hd.block) && t.number
            >= start implies header(v, t.number) == Some(t) by {
        if hd.block != t {
            lemma_parent::<S, E>(v, hd.block, hd.parent, t, start);
        }
    }
}

/// `scan` with the head one block on top of the tip: the head's view `hist[l0]` holds the
/// head block, and `got`, its entries read by hash, are that view's entries at the head.
proof fn lemma_rung_next<S, E>(
    hist: Seq<ChainView>,
    l0: int,
    start: u64,
    c: Option<Position>,
    tip: Mark,
    b: BatchView<E>,
    head: Head,
    got: Seq<(BlockRef, u32, E)>,
)
    requires
        0 <= l0 < hist.len(),
        header(hist[l0], head.block.number) == Some(head.block),
        head.block.number > 0 ==> anc(head.block.hash, (head.block.number - 1) as u64).hash == head.parent,
        head.parent == tip.at.hash,
        tip.at.number + 1 == head.block.number,
        tip.done == tip.at.number,
        a1::<S, E>(hist[l0]),
        got.to_multiset() == range_entries::<S, E>(
            hist[l0],
            head.block.number as int,
            head.block.number as int,
        ).to_multiset(),
        b.triples().to_multiset() == got.to_multiset(),
    ensures
        scanned::<S, E>(hist, l0, start, c, Some(tip), Some(Mark { at: head.block, done: head.block.number }), b),
{
    let hd = head.block;
    let n = hd.number as int;
    let v0 = hist[l0];
    vstd::seq_lib::to_multiset_len(b.triples());
    vstd::seq_lib::to_multiset_len(range_entries::<S, E>(v0, n, n));
    let t1 = Some(Mark { at: hd, done: hd.number });
    if views_ok(hist, l0, start) && (c matches Some(p) ==> p.block >= start) && tip.done + 1 >= start {
        if tip.at.number >= start {
            reveal(views_ok);
            assert(from_start(v0, start));
            lemma_parent::<S, E>(v0, hd, head.parent, tip.at, start);
        }
        assert(anchored(hist, l0, c, Some(tip), b.boundary, start, n));
    }
    assert(range_entries::<S, E>(v0, n, n - 1) =~= Seq::empty());
    assert(scan_view::<S, E>(hist, l0, start, c, Some(tip), t1, b, (l0, hd, n, n, n, l0, n, false)));
}

/// A view that holds tip `m`'s head, agrees with `h` below the floor and holds nothing from
/// the floor through `m.done` vouches for `m`: every view that holds the head agrees with
/// it up to the head.
proof fn lemma_tip_view<S, E>(m: Mark, c: Option<Position>, h: ChainView, start: u64, u: ChainView)
    requires
        a1::<S, E>(u),
        from_start(u, start),
        header(u, m.at.number) == Some(m.at),
        m.done <= m.at.number,
        start <= scan_floor(c, start) <= m.done + 1,
        forall|n: u64| start <= n < scan_floor(c, start) ==> #[trigger] header(u, n) == header(h, n),
        range_entries::<S, E>(u, scan_floor(c, start), m.done as int).len() == 0,
    ensures
        mark_vouched::<S, E>(m, c, h, start),
{
    let lo = scan_floor(c, start);
    let t = m.at;
    assert forall|v: ChainView| #[trigger] mark_seen::<S, E>(m, c, h, start, v) by {
        if a1::<S, E>(v) && from_start(v, start) && header(v, t.number) == Some(t) {
            lemma_from_start(u, start, t.number);
            lemma_from_start(v, start, t.number);
            lemma_view_agree(u, v, start, t.number);
            assert forall|n: u64| start <= n < lo implies #[trigger] header(v, n) == header(h, n) by {
                assert(header(u, n) == header(v, n));
            }
            lemma_re_agree::<S, E>(u, v, lo, m.done as int);
        }
    }
}

/// An anchored view of a tick agrees with `h` below the floor and holds nothing from the
/// floor to its anchor.
proof fn lemma_anchor<S, E>(
    e: EngineView,
    start: u64,
    h: ChainView,
    t0: Option<Mark>,
    hist: Seq<ChainView>,
    k: int,
    bd: Option<BlockRef>,
    a: int,
)
    requires
        e.wf(),
        a1::<S, E>(h),
        e.cursor matches Some(p) ==> holds(h, start, p.block) && h.contains_key(p.block) && h[p.block]
            == e.ring.last() && p.block >= start,
        mark_ok::<S, E>(t0, e.cursor, h, start),
        0 <= k < hist.len(),
        a1::<S, E>(hist[k]),
        from_start(hist[k], start),
        anchored(hist, k, e.cursor, t0, bd, start, a),
        e.cursor is Some ==> bd == Some(e.ring.last()),
    ensures
        scan_floor(e.cursor, start) <= a,
        e.cursor matches Some(p) ==> forall|n: u64| start <= n <= p.block ==> #[trigger] header(h, n) == header(hist[k], n),
        range_entries::<S, E>(hist[k], scan_floor(e.cursor, start), a - 1).len() == 0,
{
    let c = e.cursor;
    let lo = scan_floor(c, start);
    let v = hist[k];
    if c is Some && a == c.unwrap().block + 1 && header(v, c.unwrap().block) == bd {
        let p = c.unwrap();
        lemma_from_start(v, start, p.block);
        lemma_view_agree(h, v, start, p.block);
        assert(range_entries::<S, E>(v, lo, a - 1) =~= Seq::empty());
    } else if c is None && a == start {
        assert(range_entries::<S, E>(v, lo, a - 1) =~= Seq::empty());
    } else {
        let t = t0.unwrap();
        if t.at.number >= start {
            assert(mark_seen::<S, E>(t, c, h, start, v));
            if let Some(p) = c {
                assert forall|n: u64| start <= n <= p.block implies #[trigger] header(h, n) == header(v, n) by {
                    assert(n < lo);
                }
            }
        } else {
            assert(range_entries::<S, E>(v, lo, a - 1) =~= Seq::empty());
        }
    }
}

/// After an apply that took a window reaching the head `hd` in view `vk`, which holds
/// `hd`, nothing is left to fold above the new cursor up to `hd`.
proof fn lemma_tip_step<S, E>(vk: ChainView, wlo: int, hd: BlockRef, start: u64)
    requires
        a1::<S, E>(vk),
        from_start(vk, start),
        start <= wlo,
        range_entries::<S, E>(vk, wlo, hd.number as int).len() > 0,
        header(vk, hd.number) == Some(hd),
    ensures
        mark_vouched::<S, E>(
            Mark { at: hd, done: hd.number },
            Some(tpos(range_entries::<S, E>(vk, wlo, hd.number as int).last()).0),
            vk,
            start,
        ),
{
    let r = range_entries::<S, E>(vk, wlo, hd.number as int);
    let c2 = tpos(r.last()).0;
    lemma_last_complete::<S, E>(vk, wlo, hd.number as int);
    lemma_re_split::<S, E>(vk, wlo, c2.block as int, hd.number as int);
    lemma_tip_view::<S, E>(Mark { at: hd, done: hd.number }, Some(c2), vk, start, vk);
}

/// The batch's entries and shape do not read its boundary.
proof fn lemma_triples_ignore_boundary<E>(a: BatchView<E>, b: BatchView<E>, n: int)
    requires
        a == (BatchView { boundary: a.boundary, ..b }),
    ensures
        a.triples_upto(n) == b.triples_upto(n),
        b.shaped() ==> a.shaped(),
    decreases n,
{
    if b.shaped() {
        assert forall|i: int| 0 <= i < a.ends.len() implies a.start(i) < a.ends[i] by {
            assert(a.start(i) == b.start(i));
        }
    }
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
        &&& self.engine.wf()
        &&& self.batch@.wf()
        &&& 1 <= self.span <= MAX_SPAN
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

    /// The source answers every call from here on.
    pub closed spec fn source_infallible(&self) -> bool {
        infallible::<S>(&self.source)
    }

    pub closed spec fn batch_view(&self) -> BatchView<F::Event> {
        self.batch@
    }

    /// The head of the scan tip.
    pub closed spec fn tip_view(&self) -> Option<BlockRef> {
        match self.tip {
            Some(m) => Some(m.at),
            None => None,
        }
    }

    /// The scan tip is `o`'s, in every field: its head and the last block it covers.
    pub closed spec fn tip_same(&self, o: Self) -> bool {
        self.tip == o.tip
    }

    /// No scan anchor: the next poll reads from the cursor block.
    pub closed spec fn unanchored(&self) -> bool {
        self.tip is None
    }

    /// True once the most recent poll returned no new blocks.
    pub closed spec fn caught_up_view(&self) -> bool {
        self.caught_up
    }

    /// True once the sink refused an offer.
    pub closed spec fn durability_lost_view(&self) -> bool {
        self.durability_lost
    }

    /// Ticks so far, wrapping.
    pub closed spec fn generation_view(&self) -> u64 {
        self.generation
    }

    /// Ghost invariant over log `log` and chain view `h` (`dinv`), with the scan tip
    /// vouched for in the source log.
    pub closed spec fn dinv(&self, log: Seq<(Position, F::Event)>, h: ChainView) -> bool {
        &&& dinv::<F, S, F::Event, F::Error>(self.engine@, self.init_view(), self.start_block(), log, h)
        &&& mark_ok::<S, F::Event>(self.tip, self.engine@.cursor, h, self.start_block())
    }
}

/// `Inv` threading through one tick: the log grows by the applied calls, is cut at a
/// rollback target, restarts empty at a resync, and stays on a source error or a head
/// behind.
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
        Tick::Behind => f.inv::<F, F::Event, F::Error>(init, log),
        _ => f.inv::<F, F::Event, F::Error>(
            init,
            log + calls::<F, F::Event, F::Error>(pre.engine_view(), post.batch_view()),
        ),
    }
}

/// The driver's end-to-end claim across one tick from `pre` with `pre.dinv(log, h)`. The
/// hypothesis, for a tick that applied a batch: `views_ok` for the tick's views. Then the
/// invariant carries over, and after `Progressed`/`Idle` with the engine Active the fold is
/// the fold of the canonical logs of one of the tick's views, with the ring a hash chain
/// inside that view. After `RolledBack`, `Inv` holds over the canonical logs of a view that
/// confirmed the probed ring entry, when that view holds `[start_block, entry]`. After
/// `Behind`, the engine is unchanged.
pub open spec fn t7_tick<F: Fold, S: Source<Event = F::Event>, K: SnapshotSink<F>>(
    pre: Driver<F, S, K>,
    post: Driver<F, S, K>,
    r: Tick,
    log: Seq<(Position, F::Event)>,
    h: ChainView,
) -> bool {
    let (l0, hist) = (pre.source_log().len() as int, post.source_log());
    let start = pre.start_block();
    let hyp = (r is Progressed || r is Idle || r is DurabilityLost) ==> views_ok(hist, l0, start);
    let ring = pre.engine_view().ring;
    &&& hyp ==> exists|log2: Seq<(Position, F::Event)>, h2: ChainView| #[trigger] post.dinv(log2, h2)
    &&& r is Behind ==> post.engine_view() == pre.engine_view()
    &&& hyp && (r is Progressed || r is Idle) && post.engine_view().status is Active ==> exists|k: int|
        l0 <= k < hist.len() && #[trigger] t7_state::<F, S, F::Event, F::Error>(
            post.engine_view(),
            pre.init_view(),
            start,
            hist[k],
        )
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

/// A shaped, non-empty batch holding view `v`'s entries in `[lo, hi]` as a multiset holds
/// exactly those entries, in order.
proof fn lemma_batch_range<S, E>(b: BatchView<E>, v: ChainView, lo: int, hi: int)
    requires
        b.wf(),
        b.shaped(),
        b.ends.len() > 0,
        a1::<S, E>(v),
        b.triples().to_multiset() == range_entries::<S, E>(v, lo, hi).to_multiset(),
    ensures
        b.triples().len() > 0,
        b.triples() == range_entries::<S, E>(v, lo, hi),
        b.flat() == pentries::<S, E>(v, lo, hi),
{
    let n = b.ends.len() as int;
    let t = b.triples();
    let flat = b.flat();
    lemma_triples_len(b, n);
    assert(b.start(n - 1) < b.ends[n - 1]);
    if n >= 2 {
        assert(b.ends[0] <= b.ends[n - 1]);
    }
    assert(t.len() > 0);
    let r = range_entries::<S, E>(v, lo, hi);
    lemma_re_sorted::<S, E>(v, lo, hi);
    crate::batch::lemma_shaped_sorted(b);
    lemma_flat_triples(b, n);
    assert forall|i: int, j: int| 0 <= i < j < t.len() implies lt(tpos(#[trigger] t[i]).0, tpos(#[trigger] t[j]).0) by {
        assert(flat[i] == tpos(t[i]) && flat[j] == tpos(t[j]));
        assert(lt(flat[i].0, flat[j].0));
    }
    lemma_sorted_unique(t, r);
    assert(flat =~= pentries::<S, E>(v, lo, hi)) by {
        assert forall|i: int| 0 <= i < flat.len() implies flat[i] == pentries::<S, E>(v, lo, hi)[i] by {
            assert(flat[i] == tpos(t[i]));
        }
    }
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

/// `lemma_scan_t7` for every log and view `h` a tick may start from, at the view `k` of
/// one witness of `scanned`.
proof fn lemma_poll_t7<F: ?Sized, S, E, Er>(
    v: EngineView,
    post: EngineView,
    b: BatchView<E>,
    w: int,
    init: int,
    start: u64,
    old: Seq<ChainView>,
    hist: Seq<ChainView>,
    t0: Option<Mark>,
    t1: Option<Mark>,
) -> (k: int)
    requires
        v.wf(),
        post.wf(),
        b.wf(),
        0 < w,
        v.status is Active,
        grew::<S, E>(old, hist),
        accepted(v, b),
        !stopped::<F, E, Er>(v, b),
        post.cursor == cursor_after(v.cursor, ok_calls::<F, E, Er>(v, b)),
        ring_after(v, post, b, w),
        post.slots == v.slots,
        post.status == v.status,
        forall|log: Seq<(Position, E)>|
            #[trigger] v.inv::<F, E, Er>(init, log) ==> post.inv::<F, E, Er>(init, log + calls::<F, E, Er>(v, b)),
        scanned::<S, E>(hist, old.len() as int, start, v.cursor, t0, t1, b),
    ensures
        old.len() <= k < hist.len(),
        forall|log: Seq<(Position, E)>, h: ChainView|
            #[trigger] dinv::<F, S, E, Er>(v, init, start, log, h) && mark_ok::<S, E>(t0, v.cursor, h, start)
                && views_ok(hist, old.len() as int, start) ==> {
                let h2 = if b.ends.len() > 0 {
                    hist[k]
                } else {
                    h
                };
                &&& dinv::<F, S, E, Er>(post, init, start, log + calls::<F, E, Er>(v, b), h2)
                &&& t7_state::<F, S, E, Er>(post, init, start, hist[k])
                &&& mark_ok::<S, E>(t1, post.cursor, h2, start)
            },
{
    let sv = choose|sv: (int, BlockRef, int, int, int, int, int, bool)| #[trigger] scan_view::<S, E>(
        hist,
        old.len() as int,
        start,
        v.cursor,
        t0,
        t1,
        b,
        sv,
    );
    assert forall|log: Seq<(Position, E)>, h: ChainView|
        #[trigger] dinv::<F, S, E, Er>(v, init, start, log, h) && mark_ok::<S, E>(t0, v.cursor, h, start)
            && views_ok(hist, old.len() as int, start) implies {
            let h2 = if b.ends.len() > 0 {
                hist[sv.0]
            } else {
                h
            };
            &&& dinv::<F, S, E, Er>(post, init, start, log + calls::<F, E, Er>(v, b), h2)
            &&& t7_state::<F, S, E, Er>(post, init, start, hist[sv.0])
            &&& mark_ok::<S, E>(t1, post.cursor, h2, start)
        } by {
        lemma_scan_t7::<F, S, E, Er>(v, post, b, w, init, start, log, h, old, hist, t0, t1, sv);
    }
    sv.0
}

/// `dinv`, the tick's conclusion, and the new tip for an accepted apply that did not
/// stop, over the scan that built the batch and the source log `old` before it.
proof fn lemma_scan_t7<F: ?Sized, S, E, Er>(
    v: EngineView,
    post: EngineView,
    b: BatchView<E>,
    w: int,
    init: int,
    start: u64,
    log: Seq<(Position, E)>,
    h: ChainView,
    old: Seq<ChainView>,
    hist: Seq<ChainView>,
    t0: Option<Mark>,
    t1: Option<Mark>,
    sv: (int, BlockRef, int, int, int, int, int, bool),
)
    requires
        v.wf(),
        post.wf(),
        b.wf(),
        0 < w,
        v.status is Active,
        dinv::<F, S, E, Er>(v, init, start, log, h),
        mark_ok::<S, E>(t0, v.cursor, h, start),
        grew::<S, E>(old, hist),
        accepted(v, b),
        !stopped::<F, E, Er>(v, b),
        post.cursor == cursor_after(v.cursor, ok_calls::<F, E, Er>(v, b)),
        ring_after(v, post, b, w),
        post.slots == v.slots,
        post.status == v.status,
        post.inv::<F, E, Er>(init, log + calls::<F, E, Er>(v, b)),
        scan_view::<S, E>(hist, old.len() as int, start, v.cursor, t0, t1, b, sv),
        views_ok(hist, old.len() as int, start),
    ensures
        ({
            let h2 = if b.ends.len() > 0 {
                hist[sv.0]
            } else {
                h
            };
            &&& dinv::<F, S, E, Er>(post, init, start, log + calls::<F, E, Er>(v, b), h2)
            &&& t7_state::<F, S, E, Er>(post, init, start, hist[sv.0])
            &&& mark_ok::<S, E>(t1, post.cursor, h2, start)
        }),
{
    let (k, hd, a, wlo, whi, j, aj, f) = sv;
    let vk = hist[k];
    let c = v.cursor;
    let lo = scan_floor(c, start);
    lemma_grew_next::<S, E>(old, hist);
    reveal(views_ok);
    assert(from_start(vk, start) && a1::<S, E>(vk));
    if let Some(p) = c {
        let r = v.ring;
        assert(r[r.len() - 1].number == p.block);
        assert(h[p.block] == r.last());
        assert(r[r.len() - 1].number >= start);
    }
    lemma_anchor::<S, E>(v, start, h, t0, hist, k, b.boundary, a);
    if f && c is Some {
        // The cursor ends its block in `h`, which `vk` agrees with there.
        let p = c.unwrap();
        assert(header(h, p.block) == header(vk, p.block));
        lemma_kept_none::<S, E>(h, vk, p);
        let r = range_entries::<S, E>(vk, wlo, whi).to_multiset();
        assert(r.add(kept::<S, E>(vk, p)) =~= r) by {
            broadcast use vstd::multiset::group_multiset_axioms;
        }
    }
    lemma_re_split::<S, E>(vk, lo, a - 1, wlo - 1);
    if b.ends.len() == 0 {
        lemma_apply_empty::<F, S, E, Er>(v, post, b, w, init, start, log, h, vk);
    } else {
        lemma_apply_step::<F, S, E, Er>(v, post, b, w, init, start, log, h, vk, wlo, whi);
    }
    if b.ends.len() > 0 {
        lemma_batch_range::<S, E>(b, vk, wlo, whi);
    }
    if t1 is Some && t1 != t0 {
        if b.ends.len() > 0 {
            lemma_tip_step::<S, E>(vk, wlo, hd, start);
        } else {
            vstd::seq_lib::to_multiset_len(b.triples());
            assert(from_start(hist[j], start) && a1::<S, E>(hist[j]));
            lemma_anchor::<S, E>(v, start, h, t0, hist, j, b.boundary, aj);
            let m = t1.unwrap();
            lemma_re_split::<S, E>(hist[j], lo, aj - 1, m.done as int);
            if let Some(p) = c {
                assert forall|n: u64| start <= n < lo implies #[trigger] header(hist[j], n) == header(h, n) by {
                    assert(n <= p.block);
                }
            }
            lemma_tip_view::<S, E>(m, c, h, start, hist[j]);
        }
    }
}

/// A view that agrees with `h` at block `p.block`, where `p` ends its block in `h`, holds
/// no entry of that block after `p`.
proof fn lemma_kept_none<S, E>(h: ChainView, v: ChainView, p: Position)
    requires
        complete::<S, E>(h, p),
        header(h, p.block) == header(v, p.block),
    ensures
        kept::<S, E>(v, p) =~= vstd::multiset::Multiset::empty(),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    let be = block_entries::<S, E>(v, p.block);
    assert(be == block_entries::<S, E>(h, p.block));
    assert forall|x: (BlockRef, u32, E)| kept::<S, E>(v, p).count(x) == 0 by {
        vstd::seq_lib::to_multiset_contains(be, x);
        if x.1 as u64 > p.log_index && be.contains(x) {
            let i = choose|i: int| 0 <= i < be.len() && be[i] == x;
            assert(be[i].1 as u64 <= p.log_index);
        }
    }
}

/// `lemma_apply_t7` for an empty batch: nothing moves, and the view agrees with `h` up to
/// the cursor.
proof fn lemma_apply_empty<F: ?Sized, S, E, Er>(
    v: EngineView,
    post: EngineView,
    b: BatchView<E>,
    w: int,
    init: int,
    start: u64,
    log: Seq<(Position, E)>,
    h: ChainView,
    vk: ChainView,
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
        a1::<S, E>(vk),
        v.cursor matches Some(p) ==> forall|n: u64| start <= n <= p.block ==> #[trigger] header(h, n) == header(vk, n),
        b.ends.len() == 0,
    ensures
        dinv::<F, S, E, Er>(post, init, start, log + calls::<F, E, Er>(v, b), h),
        t7_state::<F, S, E, Er>(post, init, start, vk),
        post.cursor == v.cursor,
{
    let c = v.cursor;
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
    if let Some(p) = c {
        let r = v.ring;
        assert(r[r.len() - 1].number == p.block);
        lemma_canon_agree::<S, E>(h, vk, start, c);
        assert forall|i: int| 0 <= i < r.len() implies start <= #[trigger] r[i].number <= p.block by {
            if i < r.len() - 1 {
                assert(r[i].number < r[r.len() - 1].number);
            }
        }
        lemma_ring_move(r, h, vk, start, p.block);
        lemma_ring_chain_in(r, h);
    }
}

/// `lemma_apply_t7` for a non-empty batch: the ghost view moves to `vk`, and the log grows
/// by the batch.
#[verifier::spinoff_prover]
proof fn lemma_apply_step<F: ?Sized, S, E, Er>(
    v: EngineView,
    post: EngineView,
    b: BatchView<E>,
    w: int,
    init: int,
    start: u64,
    log: Seq<(Position, E)>,
    h: ChainView,
    vk: ChainView,
    wlo: int,
    whi: int,
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
        a1::<S, E>(vk),
        from_start(vk, start),
        v.cursor matches Some(p) ==> forall|n: u64| start <= n <= p.block ==> #[trigger] header(h, n) == header(vk, n),
        scan_floor(v.cursor, start) <= wlo <= whi + 1,
        whi <= u64::MAX,
        range_entries::<S, E>(vk, scan_floor(v.cursor, start), wlo - 1).len() == 0,
        b.triples().to_multiset() == range_entries::<S, E>(vk, wlo, whi).to_multiset(),
        b.ends.len() > 0,
    ensures
        dinv::<F, S, E, Er>(post, init, start, log + calls::<F, E, Er>(v, b), vk),
        t7_state::<F, S, E, Er>(post, init, start, vk),
        post.cursor == Some(tpos(range_entries::<S, E>(vk, wlo, whi).last()).0),
{
    let c = v.cursor;
    let flat = b.flat();
    let cl = calls::<F, E, Er>(v, b);
    let first = scan_floor(c, start);
    lemma_batch_range::<S, E>(b, vk, wlo, whi);
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
    assert(flat.last() == tpos(range_entries::<S, E>(vk, wlo, whi).last()));
    assert(vk.contains_key(c2.block)) by {
        lemma_re_facts::<S, E>(vk, wlo, whi);
        assert(flat.last() == tpos(range_entries::<S, E>(vk, wlo, whi).last()));
    }
    lemma_from_start(vk, start, c2.block);
    if let Some(p) = c {
        let r = v.ring;
        assert(r[r.len() - 1].number == p.block);
        assert(h[p.block] == r.last());
        assert(r[r.len() - 1].number >= start);
        assert(header(h, p.block) == header(vk, p.block));
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
    first: int,
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
        range_entries::<S, E>(vk, first, wlo - 1).len() == 0,
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
    lemma_pe_split::<S, E>(vk, first, wlo - 1, c2.block as int);
    assert(pentries::<S, E>(vk, first, wlo - 1).len() == 0);
    assert(pentries::<S, E>(vk, wlo, c2.block as int) == flat);
    assert(pentries::<S, E>(vk, first, c2.block as int) =~= flat);
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
        pre.tip is None,
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
        lemma_recover_one(old, pre, post, tick, log, h);
    }
}

/// `lemma_recover_t7`'s `dinv` half for one `log` and `h`.
proof fn lemma_recover_one<F: Fold, S: Source<Event = F::Event>, K: SnapshotSink<F>>(
    old: Driver<F, S, K>,
    pre: Driver<F, S, K>,
    post: Driver<F, S, K>,
    tick: Tick,
    log: Seq<(Position, F::Event)>,
    h: ChainView,
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
        pre.tip is None,
        old.dinv(log, h),
    ensures
        t7_tick(old, post, tick, log, h),
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
    assert(!(tick is Progressed || tick is Idle || tick is DurabilityLost));
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
            assert(exists|l2: Seq<(Position, F::Event)>, h2: ChainView| #[trigger] post.dinv(l2, h2));
            let (l0, hist) = (old.source_log().len() as int, post.source_log());
            let r0 = old.engine_view().ring;
            assert(hist == rh && r0 == ring);
            assert(0 < lo <= r0.len() && l0 <= k < hist.len() && probe_held(r0, lo, hist[k]) && (holds(
                hist[k],
                start,
                r0[lo - 1].number,
            ) ==> post.engine_view().inv::<F, F::Event, F::Error>(
                old.init_view(),
                canon::<S, F::Event>(hist[k], before(start), to),
            )));
        },
        Tick::Resynced => {
            lemma_fresh_dinv::<F, S, F::Event, F::Error>(post.engine@, init, start);
            assert(post.dinv(Seq::empty(), Map::empty()));
            assert(exists|l2: Seq<(Position, F::Event)>, h2: ChainView| #[trigger] post.dinv(l2, h2));
        },
        Tick::Terminal(_) => {
            assert(log + calls::<F, F::Event, F::Error>(v, bv) =~= log);
            assert(post.engine@.inv::<F, F::Event, F::Error>(init, log));
            assert(post.dinv(log, h));
            assert(exists|l2: Seq<(Position, F::Event)>, h2: ChainView| #[trigger] post.dinv(l2, h2));
        },
        _ => {
            assert(post.dinv(log, h));
            assert(exists|l2: Seq<(Position, F::Event)>, h2: ChainView| #[trigger] post.dinv(l2, h2));
        },
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

/// Entries one view could answer: one block per height, and no position twice.
pub open spec fn one_view<E>(m: vstd::multiset::Multiset<(BlockRef, u32, E)>) -> bool {
    forall|x: (BlockRef, u32, E), y: (BlockRef, u32, E)|
        #![trigger m.count(x), m.count(y)]
        m.count(x) > 0 && m.count(y) > 0 && x.0.number == y.0.number ==> x.0 == y.0 && (x.1 == y.1 ==> x == y
            && m.count(x) == 1)
}

/// `descending(x) <= descending(y)`: `y` is not above `x` by position.
pub open spec fn key_le<E>(x: (BlockRef, u32, E), y: (BlockRef, u32, E)) -> bool {
    y.0.number < x.0.number || (y.0.number == x.0.number && y.1 <= x.1)
}

/// `s` descends strictly by position, with one block per height.
pub open spec fn desc<E>(s: Seq<(BlockRef, u32, E)>) -> bool {
    forall|i: int, j: int|
        #![trigger s[i], s[j]]
        0 <= i < j < s.len() ==> s[j].0.number < s[i].0.number || (s[j].0 == s[i].0 && s[j].1 < s[i].1)
}

/// `group_into`'s loop over the descending `s` with `m` entries left: the batch so far is
/// shaped, its last span is `s[m]`'s block, and the next entry is in another block.
pub open spec fn popped_desc<E>(b: BatchView<E>, s: Seq<(BlockRef, u32, E)>, m: int) -> bool {
    &&& desc(s)
    &&& b.shaped()
    &&& b.ends.len() > 0 ==> 0 <= m < s.len() && b.blocks.last() == s[m].0.number && (m > 0 ==> s[m - 1].0
        != s[m].0)
}

/// Entries one view answers for a range have ascending positions.
proof fn lemma_re_ascending<S, E>(v: ChainView, lo: int, hi: int)
    requires
        a1::<S, E>(v),
    ensures
        forall|i: int, j: int|
            #![trigger range_entries::<S, E>(v, lo, hi)[i], range_entries::<S, E>(v, lo, hi)[j]]
            0 <= i < j < range_entries::<S, E>(v, lo, hi).len() ==> {
                let (x, y) = (range_entries::<S, E>(v, lo, hi)[i], range_entries::<S, E>(v, lo, hi)[j]);
                x.0.number < y.0.number || (x.0.number == y.0.number && x.1 < y.1)
            },
    decreases hi - lo + 1,
{
    if !(hi < lo || hi < 0 || hi > u64::MAX) {
        lemma_re_ascending::<S, E>(v, lo, hi - 1);
        lemma_re_facts::<S, E>(v, lo, hi - 1);
        let (t, r0, b) = (
            range_entries::<S, E>(v, lo, hi),
            range_entries::<S, E>(v, lo, hi - 1),
            block_entries::<S, E>(v, hi as u64),
        );
        assert(t == r0 + b);
        if v.contains_key(hi as u64) {
            assert(logs_ascending(logs::<S, E>(v[hi as u64].hash)));
        }
        assert forall|i: int, j: int| 0 <= i < j < t.len() implies #[trigger] t[i].0.number < #[trigger] t[j].0.number
            || (t[i].0.number == t[j].0.number && t[i].1 < t[j].1) by {
            if j < r0.len() {
                assert(t[i] == r0[i] && t[j] == r0[j]);
            } else if i < r0.len() {
                assert(t[i] == r0[i] && t[j] == b[j - r0.len()]);
            } else {
                let l = logs::<S, E>(v[hi as u64].hash);
                assert(t[i] == b[i - r0.len()] && t[j] == b[j - r0.len()]);
                assert(l[i - r0.len()].0 < l[j - r0.len()].0);
            }
        }
    }
}

/// Entries `t`, each at most as often as in `got`, lie where `got`'s do.
proof fn lemma_sub_within<E>(lo: int, hi: int, got: Seq<(BlockRef, u32, E)>, t: Seq<(BlockRef, u32, E)>)
    requires
        forall|i: int| 0 <= i < got.len() ==> lo <= (#[trigger] got[i]).0.number <= hi,
        forall|x: (BlockRef, u32, E)| #[trigger] t.to_multiset().count(x) <= got.to_multiset().count(x),
    ensures
        forall|i: int| 0 <= i < t.len() ==> lo <= (#[trigger] t[i]).0.number <= hi,
{
    assert forall|i: int| 0 <= i < t.len() implies lo <= (#[trigger] t[i]).0.number <= hi by {
        vstd::seq_lib::to_multiset_contains(t, t[i]);
        assert(t.contains(t[i]));
        assert(t.to_multiset().count(t[i]) <= got.to_multiset().count(t[i]));
        vstd::seq_lib::to_multiset_contains(got, t[i]);
        let j = choose|j: int| 0 <= j < got.len() && got[j] == t[i];
    }
}

/// A multiset with no entry more often than in a one-view multiset is one view too.
proof fn lemma_one_view_sub<E>(
    m: vstd::multiset::Multiset<(BlockRef, u32, E)>,
    n: vstd::multiset::Multiset<(BlockRef, u32, E)>,
)
    requires
        one_view(m),
        forall|x: (BlockRef, u32, E)| #[trigger] n.count(x) <= m.count(x),
    ensures
        one_view(n),
{
    assert forall|x: (BlockRef, u32, E), y: (BlockRef, u32, E)|
        #![trigger n.count(x), n.count(y)]
        n.count(x) > 0 && n.count(y) > 0 && x.0.number == y.0.number implies x.0 == y.0 && (x.1 == y.1 ==> x == y
            && n.count(x) == 1) by {
        assert(n.count(x) <= m.count(x) && n.count(y) <= m.count(y));
        assert(m.count(x) > 0 && m.count(y) > 0);
    }
}

/// An answer with the entries of `v`'s heights `lo..=hi` holds no entry outside them.
proof fn lemma_answer_within<S, E>(v: ChainView, lo: int, hi: int, got: Seq<(BlockRef, u32, E)>)
    requires
        a1::<S, E>(v),
        got.to_multiset() == range_entries::<S, E>(v, lo, hi).to_multiset(),
    ensures
        forall|i: int| 0 <= i < got.len() ==> lo <= (#[trigger] got[i]).0.number <= hi,
{
    let t = range_entries::<S, E>(v, lo, hi);
    lemma_re_facts::<S, E>(v, lo, hi);
    assert forall|i: int| 0 <= i < got.len() implies lo <= (#[trigger] got[i]).0.number <= hi by {
        vstd::seq_lib::to_multiset_contains(got, got[i]);
        vstd::seq_lib::to_multiset_contains(t, got[i]);
        assert(got.contains(got[i]));
        let j = choose|j: int| 0 <= j < t.len() && t[j] == got[i];
        assert(t[j] == got[i]);
    }
}

/// A shaped batch whose entries lie at heights `lo..=hi` carries only blocks there.
proof fn lemma_triples_within<E>(b: BatchView<E>, lo: u64, hi: u64)
    requires
        b.wf(),
        b.shaped(),
        forall|i: int| 0 <= i < b.triples().len() ==> lo <= (#[trigger] b.triples()[i]).0.number <= hi,
    ensures
        forall|i: int| 0 <= i < b.blocks.len() ==> lo <= #[trigger] b.blocks[i] <= hi,
{
    assert forall|i: int| 0 <= i < b.blocks.len() implies lo <= #[trigger] b.blocks[i] <= hi by {
        lemma_triples_at(b, b.ends.len() as int, i);
        assert(b.triples()[b.start(i)].0 == b.block(i));
    }
}

/// A range one view answers is `one_view`.
proof fn lemma_re_one_view<S, E>(v: ChainView, lo: int, hi: int)
    requires
        a1::<S, E>(v),
    ensures
        one_view(range_entries::<S, E>(v, lo, hi).to_multiset()),
{
    let t = range_entries::<S, E>(v, lo, hi);
    let m = t.to_multiset();
    lemma_re_facts::<S, E>(v, lo, hi);
    lemma_re_ascending::<S, E>(v, lo, hi);
    assert forall|i: int, j: int| 0 <= i < t.len() && 0 <= j < t.len() && i != j implies t[i] != t[j] by {
        if i < j {
            assert(t[i].0.number < t[j].0.number || t[i].1 < t[j].1);
        } else {
            assert(t[j].0.number < t[i].0.number || t[j].1 < t[i].1);
        }
    }
    assert(t.no_duplicates());
    t.lemma_multiset_has_no_duplicates();
    assert forall|x: (BlockRef, u32, E), y: (BlockRef, u32, E)|
        m.count(x) > 0 && m.count(y) > 0 && x.0.number == y.0.number implies #[trigger] m.count(x) > 0
            && #[trigger] m.count(y) > 0 && x.0 == y.0 && (x.1 == y.1 ==> x == y && m.count(x) == 1) by {
        vstd::seq_lib::to_multiset_contains(t, x);
        vstd::seq_lib::to_multiset_contains(t, y);
        let i = choose|i: int| 0 <= i < t.len() && t[i] == x;
        let j = choose|j: int| 0 <= j < t.len() && t[j] == y;
        if i < j {
            assert(t[i].0.number < t[j].0.number || t[i].1 < t[j].1);
        } else if j < i {
            assert(t[j].0.number < t[i].0.number || t[j].1 < t[i].1);
        }
    }
}

/// Keys in order over `one_view` entries give a strictly descending `s`.
proof fn lemma_sorted_desc<E>(s: Seq<(BlockRef, u32, E)>)
    requires
        one_view(s.to_multiset()),
        forall|i: int, j: int| 0 <= i < j < s.len() ==> #[trigger] key_le(s[i], s[j]),
    ensures
        desc(s),
{
    let m = s.to_multiset();
    assert forall|x: (BlockRef, u32, E)| m.contains(x) implies m.count(x) == 1 by {
        assert(m.count(x) > 0 && m.count(x) > 0 && x.0.number == x.0.number);
    }
    s.lemma_multiset_has_no_duplicates_conv();
    assert forall|i: int, j: int|
        #![trigger s[i], s[j]]
        0 <= i < j < s.len() implies s[j].0.number < s[i].0.number || (s[j].0 == s[i].0 && s[j].1 < s[i].1) by {
        assert(key_le(s[i], s[j]));
        vstd::seq_lib::to_multiset_contains(s, s[i]);
        vstd::seq_lib::to_multiset_contains(s, s[j]);
        assert(s.contains(s[i]) && s.contains(s[j]));
        if s[i].0.number == s[j].0.number {
            assert(m.count(s[i]) > 0 && m.count(s[j]) > 0);
            assert(s[i] != s[j]);
        }
    }
}

/// One `push_block_from_tail` over the descending `s` keeps `popped_desc`.
#[verifier::rlimit(20)]
proof fn lemma_push_desc<E>(
    pre: BatchView<E>,
    post: BatchView<E>,
    before: Seq<(BlockRef, u32, E)>,
    after: Seq<(BlockRef, u32, E)>,
    block: BlockRef,
    s: Seq<(BlockRef, u32, E)>,
)
    requires
        pre.wf(),
        pushed_block(pre, post, block),
        popped_tail(pre, post, before, after, block),
        before.len() > 0,
        before.last().0 == block,
        before.len() <= s.len(),
        before == s.subrange(0, before.len() as int),
        popped_desc(pre, s, before.len() as int),
    ensures
        popped_desc(post, s, after.len() as int),
{
    let (n, bl, m) = (pre.ends.len() as int, before.len() as int, after.len() as int);
    if m == bl {
        assert(after.last() == before.last());
    }
    let k = bl - m;
    let p = pre.events.len() as int;
    assert(appended_at(pre, post, before, k - 1, block));
    assert(s[m] == before[m] && s[bl - 1] == before[bl - 1]);
    if n > 0 {
        assert(s[bl].0.number < s[bl - 1].0.number || s[bl].0 == s[bl - 1].0);
        assert(pre.blocks.last() < block.number);
    }
    assert(p == if n == 0 { 0 } else { pre.ends[n - 1] as int });
    assert forall|i: int, j: int| 0 <= i < j < post.blocks.len() implies #[trigger] post.blocks[i]
        < #[trigger] post.blocks[j] by {
        if j < n {
            assert(pre.blocks[i] < pre.blocks[j]);
        } else if i < n - 1 {
            assert(pre.blocks[i] < pre.blocks[n - 1]);
        }
    }
    assert forall|i: int| 0 <= i < post.ends.len() implies post.start(i) < #[trigger] post.ends[i] by {
        if i < n {
            assert(pre.start(i) < pre.ends[i]);
            if i > 0 {
                assert(post.ends[i - 1] == pre.ends[i - 1]);
            }
        } else if n > 0 {
            assert(post.ends[n - 1] == pre.ends[n - 1]);
        }
    }
    lemma_push_desc_indices(pre, post, before, after, block, s);
    if m > 0 {
        assert(after.last() == s[m - 1]);
    }
}

/// One `push_block_from_tail` over the descending `s` leaves the log indices of each span
/// ascending.
proof fn lemma_push_desc_indices<E>(
    pre: BatchView<E>,
    post: BatchView<E>,
    before: Seq<(BlockRef, u32, E)>,
    after: Seq<(BlockRef, u32, E)>,
    block: BlockRef,
    s: Seq<(BlockRef, u32, E)>,
)
    requires
        pre.wf(),
        pushed_block(pre, post, block),
        popped_tail(pre, post, before, after, block),
        before.len() > 0,
        before.last().0 == block,
        before.len() <= s.len(),
        before == s.subrange(0, before.len() as int),
        popped_desc(pre, s, before.len() as int),
    ensures
        forall|i: int, j: int, q: int|
            #![trigger post.ends[i], post.log_indices[j], post.log_indices[q]]
            0 <= i < post.ends.len() && post.start(i) <= j < q < post.ends[i] ==> post.log_indices[j]
                < post.log_indices[q],
{
    let (n, bl, m) = (pre.ends.len() as int, before.len() as int, after.len() as int);
    if m == bl {
        assert(after.last() == before.last());
    }
    let k = bl - m;
    let p = pre.events.len() as int;
    assert(appended_at(pre, post, before, k - 1, block));
    assert(s[m] == before[m] && s[bl - 1] == before[bl - 1]);
    assert(p == if n == 0 { 0 } else { pre.ends[n - 1] as int });
    assert forall|i: int, j: int, q: int|
        #![trigger post.ends[i], post.log_indices[j], post.log_indices[q]]
        0 <= i < post.ends.len() && post.start(i) <= j < q < post.ends[i] implies post.log_indices[j]
            < post.log_indices[q] by {
        if i < n {
            assert(post.ends[i] == pre.ends[i] && post.start(i) == pre.start(i)) by {
                if i > 0 {
                    assert(post.ends[i - 1] == pre.ends[i - 1]);
                }
            }
            assert(pre.ends[i] <= pre.ends[n - 1]);
            assert(post.log_indices.subrange(0, p)[j] == pre.log_indices[j]);
            assert(post.log_indices.subrange(0, p)[q] == pre.log_indices[q]);
            assert(pre.log_indices[j] < pre.log_indices[q]);
        } else {
            if n > 0 {
                assert(post.ends[n - 1] == pre.ends[n - 1]);
            }
            let (a, b) = (j - p, q - p);
            assert(appended_at(pre, post, before, a, block));
            assert(appended_at(pre, post, before, b, block));
            assert(s[bl - 1 - a] == before[bl - 1 - a] && s[bl - 1 - b] == before[bl - 1 - b]);
            assert(s[bl - 1 - a].0.number < s[bl - 1 - b].0.number || (s[bl - 1 - a].0 == s[bl - 1 - b].0
                && s[bl - 1 - a].1 < s[bl - 1 - b].1));
        }
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
