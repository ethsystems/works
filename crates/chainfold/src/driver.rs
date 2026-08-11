#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::vec::Vec;

use core::time::Duration;

use crate::{
    anchor::{
        Anchor,
        NoAnchor,
    },
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
    },
    sink::{
        NoSink,
        SnapshotSink,
    },
    source::{
        EventSource,
        ProbeSource,
        ReplayHorizon,
    },
};

/// Default poll cadence when the source has no error backlog.
const DEFAULT_POLL_INTERVAL: Duration = Duration::from_secs(1);
/// Default first backoff step after a source error.
const DEFAULT_BACKOFF_BASE: Duration = Duration::from_millis(200);
/// Default ceiling on exponential backoff.
const DEFAULT_BACKOFF_MAX: Duration = Duration::from_secs(30);
/// Default anchor divergence rollbacks tolerated before the typed terminal state.
const DEFAULT_MAX_DIVERGENCE_RETRIES: u32 = 1;

/// True when `block` has reached the next interval step past the last marked block.
fn due(last: Option<u64>, block: u64, interval: u64) -> bool {
    last.is_none_or(|last| block >= last.saturating_add(interval))
}

/// Poll loop state machine a harness drives; owns cadence, backoff, recovery.
pub trait Tickable {
    /// Advances the loop by one poll, apply, and recovery step.
    fn tick(&mut self) -> Tick;
    /// Forces a checkpoint now, followed by the anchor check.
    fn checkpoint(&mut self);
    /// Snapshots the current driver and engine state.
    fn status(&self) -> DriverStatus;
    /// Delay before the next tick: zero while catching up, the poll interval at
    /// the tip, or capped exponential backoff after a source error.
    fn next_delay(&self) -> Duration;
}

/// Outcome of one driver tick.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tick {
    /// Batch applied; the summary counts what the fold saw.
    Progressed(ApplySummary),
    /// Poll returned nothing new.
    Idle,
    /// Fork or anchor divergence rolled the engine back to a checkpoint.
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
    /// Cursor the sink reports a restart would recover; None without a sink or a
    /// flush. A resync lowers it, so it holds for the instant it was read.
    pub durable_cursor: Option<Position>,
    /// True once the sink refused an offer; folding continues unpersisted.
    pub durability_lost: bool,
    /// Increments once per tick; a level signal for wait primitives.
    pub generation: u64,
}

impl DriverStatus {
    /// True once the engine can no longer make automated progress.
    pub fn is_terminal(&self) -> bool {
        !self.engine.is_active()
    }
}

/// Poll cadence, backoff, and recovery tuning for a driver.
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
    /// Anchor divergence rollbacks tolerated before the typed terminal state.
    pub max_divergence_retries: u32,
}

impl Default for DriverConfig {
    fn default() -> Self {
        Self {
            start_block: 0,
            poll_interval: DEFAULT_POLL_INTERVAL,
            backoff_base: DEFAULT_BACKOFF_BASE,
            backoff_max: DEFAULT_BACKOFF_MAX,
            checkpoint_interval: None,
            snapshot_interval: None,
            max_divergence_retries: DEFAULT_MAX_DIVERGENCE_RETRIES,
        }
    }
}

/// Driver over a plain source; fork suspicion escalates straight to resync or terminal.
pub struct Driver<F, S, A = NoAnchor<<F as Fold>::View>, K = NoSink>
where
    F: Fold,
    S: EventSource<Event = F::Event>,
    A: Anchor<View = F::View>,
    K: SnapshotSink<F>,
{
    engine: Engine<F>,
    source: S,
    anchor: Option<A>,
    sink: K,
    config: DriverConfig,
    batch: Batch<F::Event>,
    initial: F,
    consecutive_errors: u32,
    caught_up: bool,
    generation: u64,
    divergence_retries: u32,
    last_checkpoint_block: Option<u64>,
    last_snapshot_block: Option<u64>,
    durability_lost: bool,
    advanced: bool,
}

impl<F, S> Driver<F, S>
where
    F: Fold + Clone,
    S: EventSource<Event = F::Event>,
{
    /// Builds a driver with no anchor; anchor divergence checks never fire.
    pub fn new(
        fold: F,
        source: S,
        engine: EngineConfig,
        config: DriverConfig,
    ) -> Result<Self, ConfigError> {
        Self::build(fold, source, None, NoSink, engine, config)
    }

    /// Resumes from a recovered engine, polling onward from its cursor.
    ///
    /// `genesis` is the fold a resync restarts from, so it is empty state rather than
    /// the recovered state.
    pub fn resume(
        engine: Engine<F>,
        source: S,
        genesis: F,
        config: DriverConfig,
    ) -> Result<Self, ConfigError> {
        Self::around(engine, source, None, NoSink, genesis, config)
    }
}

impl<F, S, K> Driver<F, S, NoAnchor<<F as Fold>::View>, K>
where
    F: Fold + Clone,
    S: EventSource<Event = F::Event>,
    K: SnapshotSink<F>,
{
    /// Builds a driver that offers durable snapshots to the sink.
    pub fn with_sink(
        fold: F,
        source: S,
        sink: K,
        engine: EngineConfig,
        config: DriverConfig,
    ) -> Result<Self, ConfigError> {
        Self::build(fold, source, None, sink, engine, config)
    }

    /// Resumes from a recovered engine, offering durable snapshots to the sink.
    pub fn resume_with_sink(
        engine: Engine<F>,
        source: S,
        sink: K,
        genesis: F,
        config: DriverConfig,
    ) -> Result<Self, ConfigError> {
        Self::around(engine, source, None, sink, genesis, config)
    }
}

impl<F, S, A> Driver<F, S, A, NoSink>
where
    F: Fold + Clone,
    S: EventSource<Event = F::Event>,
    A: Anchor<View = F::View>,
{
    /// Builds a driver with an anchor whose view is checked at every checkpoint.
    pub fn with_anchor(
        fold: F,
        source: S,
        anchor: A,
        engine: EngineConfig,
        config: DriverConfig,
    ) -> Result<Self, ConfigError> {
        Self::build(fold, source, Some(anchor), NoSink, engine, config)
    }
}

impl<F, S, A, K> Driver<F, S, A, K>
where
    F: Fold + Clone,
    S: EventSource<Event = F::Event>,
    A: Anchor<View = F::View>,
    K: SnapshotSink<F>,
{
    fn build(
        fold: F,
        source: S,
        anchor: Option<A>,
        sink: K,
        engine_config: EngineConfig,
        driver_config: DriverConfig,
    ) -> Result<Self, ConfigError> {
        let initial = fold.clone();
        let engine = Engine::new(fold, engine_config)?;
        Self::around(engine, source, anchor, sink, initial, driver_config)
    }

    /// Wraps an engine, checking the source horizon against the configured start block.
    fn around(
        engine: Engine<F>,
        source: S,
        anchor: Option<A>,
        sink: K,
        initial: F,
        driver_config: DriverConfig,
    ) -> Result<Self, ConfigError> {
        if let ReplayHorizon::FromBlock(horizon) = source.horizon()
            && horizon > driver_config.start_block
        {
            return Err(ConfigError::HorizonExceedsStart {
                start: driver_config.start_block,
                horizon,
            });
        }
        Ok(Self {
            engine,
            source,
            anchor,
            sink,
            config: driver_config,
            batch: Batch::new(),
            initial,
            consecutive_errors: 0,
            caught_up: false,
            generation: 0,
            divergence_retries: 0,
            last_checkpoint_block: None,
            last_snapshot_block: None,
            durability_lost: false,
            advanced: false,
        })
    }

    /// Builds an anchored driver that offers durable snapshots to the sink.
    pub fn with_anchor_and_sink(
        fold: F,
        source: S,
        anchor: A,
        sink: K,
        engine: EngineConfig,
        config: DriverConfig,
    ) -> Result<Self, ConfigError> {
        Self::build(fold, source, Some(anchor), sink, engine, config)
    }

    /// Resumes an anchored driver that offers durable snapshots to the sink.
    pub fn resume_with_anchor_and_sink(
        engine: Engine<F>,
        source: S,
        anchor: A,
        sink: K,
        genesis: F,
        config: DriverConfig,
    ) -> Result<Self, ConfigError> {
        Self::around(engine, source, Some(anchor), sink, genesis, config)
    }

    /// Borrows the durability sink.
    pub fn sink(&self) -> &K {
        &self.sink
    }

    /// Consumes the driver, returning the sink for joining or inspection.
    pub fn into_sink(self) -> K {
        self.sink
    }

    /// Borrows the underlying engine.
    pub fn engine(&self) -> &Engine<F> {
        &self.engine
    }

    /// Manual recovery access: rollback out of Halted or Poisoned, then keep ticking.
    pub fn engine_mut(&mut self) -> &mut Engine<F> {
        &mut self.engine
    }

    /// Mutable access to the underlying event source.
    pub fn source_mut(&mut self) -> &mut S {
        &mut self.source
    }

    /// True once the most recent poll returned no new blocks.
    pub fn is_caught_up(&self) -> bool {
        self.caught_up
    }

    /// Runs the interval-based checkpoint rule; returns the overriding tick, if any.
    fn auto_checkpoint(&mut self) -> Option<Tick> {
        let interval = self.config.checkpoint_interval?;
        let cursor = self.engine.cursor()?;
        if due(self.last_checkpoint_block, cursor.block, interval) {
            self.run_checkpoint()
        } else {
            None
        }
    }

    /// Stores a checkpoint, records its block, then runs the anchor check.
    fn run_checkpoint(&mut self) -> Option<Tick> {
        self.engine.checkpoint();
        if let Some(cursor) = self.engine.cursor() {
            self.last_checkpoint_block = Some(cursor.block);
        }
        self.check_anchor()
    }

    /// Runs the interval-based snapshot rule; returns the overriding tick, if any.
    fn offer_snapshot(&mut self) -> Option<Tick> {
        if self.durability_lost {
            return None;
        }
        let interval = self.config.snapshot_interval?;
        let point = self.engine.durable_point()?;
        if !due(self.last_snapshot_block, point.block, interval) {
            return None;
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
    #[cold]
    fn lose_durability(&mut self) -> Tick {
        self.durability_lost = true;
        Tick::DurabilityLost
    }

    /// Lowers the snapshot mark to the restore point so the next offer is not suppressed.
    #[cold]
    fn clamp_snapshot_mark(&mut self, to: Option<Position>) {
        self.last_snapshot_block = self
            .last_snapshot_block
            .zip(to)
            .map(|(last, point)| last.min(point.block));
    }

    /// Compares the fold view against the anchor's expectation at the last verified block.
    fn check_anchor(&mut self) -> Option<Tick> {
        let anchor = self.anchor.as_ref()?;
        let at = self.engine.last_verified()?;
        let expected = anchor.expected(&at)?;
        if self.engine.view() == expected {
            self.divergence_retries = 0;
            None
        } else {
            Some(self.handle_anchor_divergence(at))
        }
    }

    /// Rolls back to the block before the divergent anchor, or escalates.
    #[cold]
    fn handle_anchor_divergence(&mut self, at: BlockRef) -> Tick {
        if self.divergence_retries >= self.config.max_divergence_retries {
            self.engine
                .mark_unrecoverable(DivergenceCause::AnchorDivergence { at: at.number });
            return Tick::Terminal(self.engine.status());
        }
        let tick = self.roll_back_to(at.number.saturating_sub(1));
        if matches!(tick, Tick::RolledBack { .. }) {
            self.divergence_retries = self.divergence_retries.saturating_add(1);
        }
        tick
    }

    /// Rolls back to the newest checkpoint at or below the ancestor, else escalates.
    #[cold]
    fn roll_back_to(&mut self, ancestor: u64) -> Tick {
        match self.engine.rollback_at_or_below(ancestor) {
            Ok(to) => {
                self.caught_up = false;
                self.clamp_snapshot_mark(to);
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
    #[cold]
    fn resync_or_terminal(&mut self) -> Tick {
        match self.source.horizon() {
            // The same shortfall `around` rejects at construction, reached at runtime.
            ReplayHorizon::FromBlock(horizon) if horizon > self.config.start_block => {
                self.engine
                    .mark_unrecoverable(DivergenceCause::HorizonExceeded {
                        needed: self.config.start_block,
                        horizon,
                    });
                Tick::Terminal(self.engine.status())
            }
            _ => self.resync(),
        }
    }

    #[cold]
    fn resync(&mut self) -> Tick {
        self.engine.reset(self.initial.clone());
        self.caught_up = false;
        self.consecutive_errors = 0;
        self.divergence_retries = 0;
        self.last_checkpoint_block = None;
        self.last_snapshot_block = None;
        Tick::Resynced
    }

    /// Runs one poll-apply step, then records whether the cursor moved forward.
    fn step<Fork>(&mut self, on_fork: Fork) -> Tick
    where
        Fork: FnOnce(&mut Self) -> Tick,
    {
        let tick = self.poll_apply(on_fork);
        // Only forward cursor movement earns an immediate re-poll; a batch the
        // engine fully deduped leaves the loop on its poll interval.
        self.advanced = matches!(
            tick,
            Tick::Progressed(summary) if summary.applied > 0 || summary.skipped > 0
        );
        tick
    }

    /// Polls the source and applies the batch, deferring fork recovery to `on_fork`.
    fn poll_apply<Fork>(&mut self, on_fork: Fork) -> Tick
    where
        Fork: FnOnce(&mut Self) -> Tick,
    {
        self.generation = self.generation.wrapping_add(1);
        if !self.engine.status().is_active() {
            return Tick::Terminal(self.engine.status());
        }
        if self
            .source
            .next_batch(self.engine.cursor(), &mut self.batch)
            .is_err()
        {
            self.consecutive_errors = self.consecutive_errors.saturating_add(1);
            return Tick::SourceError;
        }
        self.consecutive_errors = 0;
        match self.engine.apply_batch(&self.batch) {
            Ok(summary) => {
                self.caught_up = self.batch.is_empty();
                // A checkpoint tick overrides a snapshot tick, which overrides progress.
                if let Some(tick) =
                    self.auto_checkpoint().or_else(|| self.offer_snapshot())
                {
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
            ) => on_fork(self),
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
}

impl<F, S, A, K> Tickable for Driver<F, S, A, K>
where
    F: Fold + Clone,
    S: EventSource<Event = F::Event>,
    A: Anchor<View = F::View>,
    K: SnapshotSink<F>,
{
    fn tick(&mut self) -> Tick {
        self.step(Self::resync_or_terminal)
    }

    fn checkpoint(&mut self) {
        self.run_checkpoint();
    }

    fn status(&self) -> DriverStatus {
        DriverStatus {
            cursor: self.engine.cursor(),
            last_verified: self.engine.last_verified(),
            engine: self.engine.status(),
            caught_up: self.caught_up,
            skips: self.engine.skip_count(),
            durable_cursor: self.sink.durable_cursor(),
            durability_lost: self.durability_lost,
            generation: self.generation,
        }
    }

    fn next_delay(&self) -> Duration {
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

impl<F, S, A, K> Driver<F, S, A, K>
where
    F: Fold + Clone,
    S: ProbeSource<Event = F::Event>,
    A: Anchor<View = F::View>,
    K: SnapshotSink<F>,
{
    /// Bisects the observed ring for the deepest still-canonical block, then rolls back.
    #[cold]
    fn recover_via_bisection(&mut self) -> Tick {
        let observed: Vec<BlockRef> = self.engine.observed().collect();
        let mut lo = 0usize;
        let mut hi = observed.len();
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            match self.source.header_at(observed[mid].number) {
                Ok(Some(header)) if header.hash == observed[mid].hash => lo = mid + 1,
                Ok(_) => hi = mid,
                Err(_) => {
                    self.consecutive_errors = self.consecutive_errors.saturating_add(1);
                    return Tick::SourceError;
                }
            }
        }
        if lo == 0 {
            return self.resync_or_terminal();
        }
        self.roll_back_to(observed[lo - 1].number)
    }
}

/// Probe-capable driver: fork suspicion bisects to the ancestor and rolls back.
pub struct Probed<F, S, A = NoAnchor<<F as Fold>::View>, K = NoSink>
where
    F: Fold,
    S: ProbeSource<Event = F::Event>,
    A: Anchor<View = F::View>,
    K: SnapshotSink<F>,
{
    inner: Driver<F, S, A, K>,
}

impl<F, S> Probed<F, S>
where
    F: Fold + Clone,
    S: ProbeSource<Event = F::Event>,
{
    /// Builds a probe-capable driver with no anchor.
    pub fn new(
        fold: F,
        source: S,
        engine: EngineConfig,
        config: DriverConfig,
    ) -> Result<Self, ConfigError> {
        Ok(Self {
            inner: Driver::new(fold, source, engine, config)?,
        })
    }

    /// Resumes from a recovered engine, polling onward from its cursor.
    ///
    /// `genesis` is the fold a resync restarts from, so it is empty state rather than
    /// the recovered state.
    pub fn resume(
        engine: Engine<F>,
        source: S,
        genesis: F,
        config: DriverConfig,
    ) -> Result<Self, ConfigError> {
        Ok(Self {
            inner: Driver::resume(engine, source, genesis, config)?,
        })
    }
}

impl<F, S, K> Probed<F, S, NoAnchor<<F as Fold>::View>, K>
where
    F: Fold + Clone,
    S: ProbeSource<Event = F::Event>,
    K: SnapshotSink<F>,
{
    /// Builds a probe-capable driver that offers durable snapshots to the sink.
    pub fn with_sink(
        fold: F,
        source: S,
        sink: K,
        engine: EngineConfig,
        config: DriverConfig,
    ) -> Result<Self, ConfigError> {
        Ok(Self {
            inner: Driver::with_sink(fold, source, sink, engine, config)?,
        })
    }
}

impl<F, S, A, K> Probed<F, S, A, K>
where
    F: Fold + Clone,
    S: ProbeSource<Event = F::Event>,
    A: Anchor<View = F::View>,
    K: SnapshotSink<F>,
{
    /// Borrows the durability sink.
    pub fn sink(&self) -> &K {
        self.inner.sink()
    }

    /// Consumes the driver, returning the sink for joining or inspection.
    pub fn into_sink(self) -> K {
        self.inner.into_sink()
    }

    /// Borrows the underlying engine.
    pub fn engine(&self) -> &Engine<F> {
        self.inner.engine()
    }

    /// Manual recovery access: rollback out of Halted or Poisoned, then keep ticking.
    pub fn engine_mut(&mut self) -> &mut Engine<F> {
        self.inner.engine_mut()
    }

    /// Mutable access to the underlying event source.
    pub fn source_mut(&mut self) -> &mut S {
        self.inner.source_mut()
    }

    /// True once the most recent poll returned no new blocks.
    pub fn is_caught_up(&self) -> bool {
        self.inner.is_caught_up()
    }
}

impl<F, S, A, K> Tickable for Probed<F, S, A, K>
where
    F: Fold + Clone,
    S: ProbeSource<Event = F::Event>,
    A: Anchor<View = F::View>,
    K: SnapshotSink<F>,
{
    fn tick(&mut self) -> Tick {
        self.inner.step(Driver::recover_via_bisection)
    }

    fn checkpoint(&mut self) {
        self.inner.checkpoint();
    }

    fn status(&self) -> DriverStatus {
        self.inner.status()
    }

    fn next_delay(&self) -> Duration {
        self.inner.next_delay()
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

    impl EventSource for Probe {
        type Event = u64;
        type Error = PollFailure;

        fn next_batch(
            &mut self,
            cursor: Option<Position>,
            out: &mut Batch<u64>,
        ) -> Result<(), PollFailure> {
            self.inner.next_batch(cursor, out)
        }

        fn horizon(&self) -> ReplayHorizon {
            self.inner.horizon()
        }
    }

    impl ProbeSource for Probe {
        fn header_at(&mut self, number: u64) -> Result<Option<BlockRef>, PollFailure> {
            self.calls += 1;
            if self.fail_next > 0 {
                self.fail_next -= 1;
                return Err(PollFailure);
            }
            self.inner.header_at(number)
        }
    }

    /// Source that re-serves the same one-event block on every poll.
    struct Stuck {
        block: BlockRef,
    }

    impl EventSource for Stuck {
        type Event = u64;
        type Error = PollFailure;

        fn next_batch(
            &mut self,
            cursor: Option<Position>,
            out: &mut Batch<u64>,
        ) -> Result<(), PollFailure> {
            out.clear();
            out.boundary = cursor.map(|_| self.block);
            out.push_block(self.block, [(0u32, 1u64)]);
            Ok(())
        }

        fn horizon(&self) -> ReplayHorizon {
            ReplayHorizon::Genesis
        }
    }

    /// Anchor matching a one-event-per-block chain folded from genesis in full.
    struct ExactAnchor;

    impl Anchor for ExactAnchor {
        type View = Vec<(Position, u64)>;

        fn expected(&self, at: &BlockRef) -> Option<Self::View> {
            Some((1..=at.number).map(|n| (Position::new(n, 0), n)).collect())
        }
    }

    /// Anchor whose expectation never matches, forcing divergence on every checkpoint.
    struct DisagreeingAnchor;

    impl Anchor for DisagreeingAnchor {
        type View = Vec<(Position, u64)>;

        fn expected(&self, _at: &BlockRef) -> Option<Self::View> {
            Some(Vec::new())
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

    fn run_to_idle<D: Tickable>(driver: &mut D) -> Tick {
        let mut outcome = driver.tick();
        while !matches!(outcome, Tick::Idle) {
            outcome = driver.tick();
        }
        outcome
    }

    fn collect_to_idle<D: Tickable>(driver: &mut D) -> Vec<Tick> {
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
        chain.set_batch_blocks(1);
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
    type SinkDriver = Driver<
        RecordingFold,
        ScriptedChain,
        NoAnchor<Vec<(Position, u64)>>,
        WatermarkSink,
    >;

    /// Probe-capable counterpart of `SinkDriver`, so a fork bisects before rolling back.
    type ProbedSinkDriver = Probed<
        RecordingFold,
        ScriptedChain,
        NoAnchor<Vec<(Position, u64)>>,
        WatermarkSink,
    >;

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

    fn probed_sink_driver(
        blocks: u64,
        slots: usize,
        config: DriverConfig,
    ) -> ProbedSinkDriver {
        Probed::with_sink(
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
        assert_eq!(driver.engine().view(), expected);
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
        assert_eq!(driver.engine().view(), expected);
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
        assert_eq!(driver.engine().view(), expected);
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
        chain.set_batch_blocks(1);
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
        chain.set_batch_blocks(1);
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
        chain.set_batch_blocks(1);
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
        chain.set_batch_blocks(1);
        let mut driver = Probed::new(
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
        assert_eq!(driver.engine().view(), expected);
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
        chain.set_batch_blocks(1);
        let mut driver = Probed::new(
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
        assert_eq!(driver.engine().view(), expected);
    }

    #[test]
    fn shorter_chain_fork_is_suspected_not_retried() {
        // given a reorg to a chain shorter than the cursor block
        let mut chain = ScriptedChain::new(1);
        for value in 1..=5u64 {
            chain.push_block(&[value]);
        }
        chain.set_batch_blocks(1);
        let mut driver = Probed::new(
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
        assert_eq!(driver.engine().view(), expected);
    }

    #[test]
    fn bisection_finds_deepest_canonical_block() {
        // given a ring of eight observed blocks and a fork at the sixth
        let mut chain = ScriptedChain::new(1);
        for value in 1..=8u64 {
            chain.push_block(&[value]);
        }
        chain.set_batch_blocks(1);
        let mut driver = Probed::new(
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
        fn build(horizon: ReplayHorizon) -> Probed<RecordingFold, ScriptedChain> {
            let mut chain = ScriptedChain::new(1);
            for value in 1..=6u64 {
                chain.push_block(&[value]);
            }
            chain.set_batch_blocks(1);
            let mut driver = Probed::new(
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
        fn build(horizon: ReplayHorizon) -> Probed<RecordingFold, ScriptedChain> {
            let mut chain = ScriptedChain::new(1);
            for value in 1..=8u64 {
                chain.push_block(&[value]);
            }
            chain.set_batch_blocks(1);
            let mut driver = Probed::new(
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
        chain.set_batch_blocks(1);
        let mut driver = Probed::new(
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
        assert_eq!(driver.engine().view(), expected);
    }

    #[test]
    fn anchor_match_resets_divergence_budget() {
        // given an anchor agreeing with the fold
        let mut chain = ScriptedChain::new(1);
        for value in 1..=5u64 {
            chain.push_block(&[value]);
        }
        let mut driver = Driver::with_anchor(
            RecordingFold::default(),
            chain,
            ExactAnchor,
            engine_config(2),
            DriverConfig::default(),
        )
        .unwrap();
        driver.tick();
        let cursor_before = driver.engine().cursor();
        // when checkpoints fire
        driver.checkpoint();
        driver.checkpoint();
        // then no rollback runs and the cursor, status, and checkpoint count hold steady
        assert_eq!(driver.engine().cursor(), cursor_before);
        assert_eq!(driver.engine().status(), EngineStatus::Active);
        assert_eq!(driver.engine().checkpoint_count(), 2);
    }

    #[test]
    fn anchor_divergence_rolls_back_then_terminates() {
        // given an anchor that always disagrees and max_divergence_retries 1
        let mut chain = ScriptedChain::new(1);
        for value in 1..=3u64 {
            chain.push_block(&[value]);
        }
        let mut driver = Driver::with_anchor(
            RecordingFold::default(),
            chain,
            DisagreeingAnchor,
            EngineConfig {
                ring_capacity: 8,
                checkpoint_slots: 4,
            },
            DriverConfig {
                max_divergence_retries: 1,
                ..DriverConfig::default()
            },
        )
        .unwrap();
        // when two checkpoints fire a mismatch each, with a re-fold between them
        driver.checkpoint();
        driver.tick();
        driver.checkpoint();
        let after_first_mismatch = (driver.engine().status(), driver.engine().cursor());
        driver.tick();
        driver.checkpoint();
        let after_second_mismatch = driver.engine().status();
        // then the first mismatch rolls back to the pre-fold checkpoint, the second terminates
        assert_eq!(after_first_mismatch, (EngineStatus::Active, None));
        assert_eq!(
            after_second_mismatch,
            EngineStatus::Unrecoverable {
                cause: DivergenceCause::AnchorDivergence { at: 3 },
            }
        );
    }
}
