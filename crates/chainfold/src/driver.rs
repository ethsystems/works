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

/// Default poll cadence when the source has no error backlog.
const DEFAULT_POLL_INTERVAL: Duration = Duration::from_secs(1);
/// Default first backoff step after a source error.
const DEFAULT_BACKOFF_BASE: Duration = Duration::from_millis(200);
/// Default ceiling on exponential backoff.
const DEFAULT_BACKOFF_MAX: Duration = Duration::from_secs(30);
/// Default blocks between checkpoints.
const DEFAULT_CHECKPOINT_INTERVAL: u64 = 64;
/// Most windows one tick reads; a longer walk goes on in the next tick.
const MAX_SPAN: u64 = 64;

/// True when `block` has reached the next interval step past the last marked block.
fn due(last: Option<u64>, block: u64, interval: u64) -> bool {
    last.is_none_or(|last| block >= last.saturating_add(interval))
}

/// Outcome of one driver tick.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tick {
    /// Batch applied; the summary counts what the fold saw. A zero summary means the walk
    /// stopped at its per-tick cap with nothing to fold yet; the next tick goes on from
    /// there.
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

/// What a scan leaves for the tick to act on.
enum Scan {
    /// `batch` is ready to apply; the walk ran under this head.
    Ready(BlockRef),
    /// The walk stopped at its cap with nothing to fold; `batch` holds only the boundary,
    /// `anchor` is the block the walk ended on, and the walk ran under `head`.
    Capped { anchor: BlockRef, head: BlockRef },
    /// The source's head trails the cursor, or the walked mark, on the chain the ring
    /// observed; nothing to do.
    Lagging,
    /// The source contradicted itself; its answer is dropped.
    Refused,
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
    /// True once the most recent poll reached the head and found no new blocks.
    pub caught_up: bool,
    /// Events the fold declared not its own.
    pub skips: u64,
    /// Cursor the sink reports a restart would recover; None without a sink, before a
    /// flush, and after a reset until an offer made since then commits. A resync clears
    /// it, so it holds for the instant it was read.
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
    seen_resets: u64,
    durability_lost: bool,
    advanced: bool,
    /// Windows the next tick may read, up to `MAX_SPAN`: halves after a source error,
    /// doubles after any other tick.
    span: u64,
    /// The block the last walk ended on when it stopped at its cap: the chain through it
    /// has nothing to fold above the cursor, up to that block.
    walked: Option<BlockRef>,
    /// The head a tick read before and after a walk that folded or stopped at its cap,
    /// once its boundary check passed. The chain it names holds the whole cursor block,
    /// so a tick that finds the same head need not read that block again.
    vouched: Option<BlockRef>,
    /// Cursor and reset count the last tick left the engine at; None when that tick left
    /// it halted or poisoned, or never ended. A different pair now means the caller moved
    /// the engine.
    left_at: Option<(Option<Position>, u64)>,
}

impl<F, S> Driver<F, S>
where
    F: Fold + Clone,
    S: Source<Event = F::Event>,
{
    /// Builds a driver that persists nothing.
    pub fn new(
        fold: F,
        source: S,
        engine: EngineConfig,
        config: DriverConfig,
    ) -> Result<Self, ConfigError> {
        Self::build(fold, source, NoSink, engine, config)
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
        Self::around(engine, source, NoSink, genesis, config)
    }
}

impl<F, S, K> Driver<F, S, K>
where
    F: Fold + Clone,
    S: Source<Event = F::Event>,
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
        Self::build(fold, source, sink, engine, config)
    }

    /// Resumes from a recovered engine, offering durable snapshots to the sink.
    pub fn resume_with_sink(
        engine: Engine<F>,
        source: S,
        sink: K,
        genesis: F,
        config: DriverConfig,
    ) -> Result<Self, ConfigError> {
        Self::around(engine, source, sink, genesis, config)
    }
}

impl<F, S, K> Driver<F, S, K>
where
    F: Fold + Clone,
    S: Source<Event = F::Event>,
    K: SnapshotSink<F>,
{
    fn build(
        fold: F,
        source: S,
        sink: K,
        engine_config: EngineConfig,
        driver_config: DriverConfig,
    ) -> Result<Self, ConfigError> {
        let initial = fold.clone();
        let engine = Engine::new(fold, engine_config)?;
        Self::around(engine, source, sink, initial, driver_config)
    }

    /// Wraps an engine, checking the source horizon against the configured start block.
    fn around(
        engine: Engine<F>,
        source: S,
        mut sink: K,
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
        // A sink ahead of the engine holds a cursor from a run this engine has not folded.
        if sink.durable_cursor() > engine.cursor() {
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
            seen_resets,
            durability_lost: false,
            advanced: false,
            span: MAX_SPAN,
            walked: None,
            vouched: None,
            left_at: None,
        };
        // A recovered engine holds no checkpoint. Its first poll would take one at the tip,
        // so a depth-1 reorg there would resync; keep one at the recovery point.
        if driver.engine.checkpoint_count() == 0 {
            driver.auto_checkpoint();
        }
        Ok(driver)
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
    ///
    /// A call drops the scan's progress, since the caller may change what it returns.
    pub fn source_mut(&mut self) -> &mut S {
        self.walked = None;
        self.vouched = None;
        &mut self.source
    }

    /// True once the most recent poll reached the head and found no new blocks.
    pub fn is_caught_up(&self) -> bool {
        self.caught_up
            && self.engine.status().is_active()
            && self.left_at == Some(self.engine_point())
    }

    /// The cursor and reset count, which change only when a tick or the caller moves the
    /// engine.
    fn engine_point(&self) -> (Option<Position>, u64) {
        (self.engine.cursor(), self.engine.resets())
    }

    /// Runs the interval-based checkpoint rule.
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
    fn run_checkpoint(&mut self) {
        self.engine.checkpoint();
        if let Some(cursor) = self.engine.cursor() {
            self.last_checkpoint_block = Some(cursor.block);
        }
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

    /// Lowers both cadence marks to the cursor block, and clears them without a cursor, so
    /// a rollback or a reset suppresses neither the next checkpoint nor the next offer.
    fn clamp_marks(&mut self) {
        let block = self.engine.cursor().map(|cursor| cursor.block);
        let clamp =
            |mark: Option<u64>| mark.zip(block).map(|(mark, block)| mark.min(block));
        self.last_checkpoint_block = clamp(self.last_checkpoint_block);
        self.last_snapshot_block = clamp(self.last_snapshot_block);
    }

    /// Rolls back to the newest checkpoint at or below the ancestor, else escalates.
    #[cold]
    fn roll_back_to(&mut self, ancestor: u64) -> Tick {
        match self.engine.rollback_at_or_below(ancestor) {
            Ok(to) => {
                self.caught_up = false;
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
        Tick::Resynced
    }

    /// Runs one poll-apply step, then records whether the cursor moved forward.
    fn step(&mut self) -> Tick {
        // The caller can roll back or reset through `engine_mut`, so both are caught here.
        self.clamp_marks();
        if self.seen_resets != self.engine.resets() {
            self.sink.reset();
            self.seen_resets = self.engine.resets();
        }
        // An engine away from where the last tick left it was moved by the caller, so
        // what was walked above its old cursor says nothing about the new one.
        if self.left_at.take() != Some(self.engine_point()) {
            self.walked = None;
            self.vouched = None;
        }
        let tick = self.poll_apply();
        // A tick that folded, or walked to its cap, earns an immediate re-poll.
        self.advanced = matches!(tick, Tick::Progressed(_));
        self.span = if tick == Tick::SourceError {
            (self.span / 2).max(1)
        } else {
            self.span.saturating_mul(2).min(MAX_SPAN)
        };
        self.left_at = self
            .engine
            .status()
            .is_active()
            .then(|| self.engine_point());
        tick
    }

    /// Scans the source and applies the batch, recovering from a fork by bisection.
    fn poll_apply(&mut self) -> Tick {
        self.generation = self.generation.wrapping_add(1);
        if !self.engine.status().is_active() {
            return Tick::Terminal(self.engine.status());
        }
        let mut capped_at = None;
        let head = match self.scan() {
            Ok(Scan::Ready(head)) => head,
            Ok(Scan::Capped { anchor, head }) => {
                capped_at = Some(anchor);
                head
            }
            Ok(Scan::Lagging) => {
                self.consecutive_errors = 0;
                self.caught_up = true;
                return Tick::Idle;
            }
            Ok(Scan::Refused) | Err(_) => {
                self.batch.clear();
                self.consecutive_errors = self.consecutive_errors.saturating_add(1);
                return Tick::SourceError;
            }
        };
        self.consecutive_errors = 0;
        // The mark survives only a tick that folds nothing and passes its boundary check.
        let walked = self.walked.take();
        match self.engine.apply_batch(&self.batch) {
            Ok(summary) => {
                let idle = self.batch.is_empty() && capped_at.is_none();
                if self.batch.is_empty() {
                    self.walked = capped_at.or(walked);
                }
                // An idle walk read the head only once, so it vouches for no new head.
                if !idle {
                    self.vouched = Some(head);
                }
                self.caught_up = idle;
                // A snapshot refusal overrides progress; a checkpoint is silent.
                self.auto_checkpoint();
                if let Some(tick) = self.offer_snapshot() {
                    return tick;
                }
                if idle {
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

    /// Fills `batch` with the events after the cursor, plus the cursor block's header, all
    /// as the chain `head` names reports them. A walk stops at `span` windows; when it
    /// has found nothing by then, the block it ended on is the mark the next walk starts
    /// above. A head the last folding or capped tick vouched for is the same chain, so
    /// the walk starts above the cursor block, and above the mark without checking it.
    fn scan(&mut self) -> Result<Scan, S::Error> {
        self.batch.clear();
        let head = self.source.head()?;
        let cursor = self.engine.cursor();
        // a node behind the mark, or behind the cursor without one, on the chain the ring
        // observed is lagging, not forked
        if let Some(floor) = self
            .walked
            .map(|walked| walked.number)
            .or(cursor.map(|cursor| cursor.block))
            && head.number < floor
            && self
                .engine
                .observed()
                .all(|seen| seen.number != head.number || seen.hash == head.hash)
        {
            return Ok(Scan::Lagging);
        }

        let window = self.source.window().max(1);
        let mut from = cursor.map_or(self.config.start_block, |cursor| cursor.block);
        // The same head names the same chain, which still holds the cursor block that
        // tick checked, so a walk can start above it.
        let vouched = self.vouched == Some(head);
        // A mark on the head's chain holds nothing to fold below it, and that chain holds
        // the cursor block the mark was set over. Any other mark is stale.
        let mut resumed = false;
        if let Some(walked) = self.walked {
            if vouched
                || head == walked
                || self.source.header_at(walked.number)? == Some(walked)
            {
                from = walked.number.saturating_add(1);
                resumed = true;
            } else {
                self.walked = None;
            }
        } else if vouched && let Some(cursor) = cursor {
            from = cursor.block.saturating_add(1);
            resumed = true;
        }
        let end = head
            .number
            .min(from.saturating_add(self.span.saturating_mul(window) - 1));
        while from <= end {
            let to = end.min(from.saturating_add(window - 1));
            self.scratch.clear();
            self.source.events_in(from, to, &mut self.scratch)?;
            if self
                .scratch
                .iter()
                .any(|(block, ..)| !(from..=to).contains(&block.number))
            {
                return Ok(Scan::Refused);
            }
            if let Some(cursor) = cursor
                && from == cursor.block
            {
                let mut at_cursor = self
                    .scratch
                    .iter()
                    .map(|(block, ..)| block)
                    .filter(|block| block.number == cursor.block);
                let boundary = at_cursor.next().copied();
                if at_cursor.any(|block| Some(*block) != boundary) {
                    return Ok(Scan::Refused);
                }
                self.batch.boundary = boundary;
                // the rest of a partly folded cursor block is still owed
                self.scratch.retain(|(block, log_index, _)| {
                    Position::new(block.number, u64::from(*log_index)) > cursor
                });
            }
            if !self.scratch.is_empty() {
                group_into(&mut self.batch, &mut self.scratch);
                break;
            }
            let Some(next) = to.checked_add(1) else {
                break;
            };
            from = next;
        }
        if let Some(cursor) = cursor
            && self.batch.boundary.is_none()
        {
            self.batch.boundary = if resumed {
                self.engine.observed().last()
            } else if head.number == cursor.block {
                Some(head)
            } else {
                self.source.header_at(cursor.block)?
            };
        }
        if end < head.number && self.batch.is_empty() {
            // The head reads before and after the anchor read bracket it, so the anchor
            // lies on the chain `head` names.
            let anchor = self.source.header_at(end)?;
            let unmoved = self.source.header_at(head.number)? == Some(head);
            return Ok(match anchor {
                Some(anchor) if unmoved && anchor.number == end => {
                    Scan::Capped { anchor, head }
                }
                _ => Scan::Refused,
            });
        }
        // What was read since `head` came from its chain only while the source still has
        // `head`. An answer that ends on `head` is no exception: it may still carry blocks
        // of another fork below it.
        if !self.batch.is_empty() && self.source.header_at(head.number)? != Some(head) {
            return Ok(Scan::Refused);
        }
        Ok(Scan::Ready(head))
    }

    /// Bisects the observed ring for the deepest still-canonical block, then rolls back.
    #[cold]
    fn recover_via_bisection(&mut self) -> Tick {
        // The engine is about to leave the cursor block the head vouched for.
        self.vouched = None;
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

    /// Advances the loop by one poll, apply, and recovery step.
    pub fn tick(&mut self) -> Tick {
        self.step()
    }

    /// Forces a checkpoint now.
    pub fn checkpoint(&mut self) {
        self.run_checkpoint();
    }

    /// Snapshots the current driver and engine state.
    pub fn status(&self) -> DriverStatus {
        DriverStatus {
            cursor: self.engine.cursor(),
            last_verified: self.engine.last_verified(),
            engine: self.engine.status(),
            caught_up: self.is_caught_up(),
            skips: self.engine.skip_count(),
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

/// Drains `entries` into `batch`
fn group_into<E>(batch: &mut Batch<E>, entries: &mut Vec<(BlockRef, u32, E)>) {
    entries.sort_by_key(|(block, log_index, _)| (block.number, *log_index));

    let mut span: Vec<(u32, E)> = Vec::new();
    let mut current: Option<BlockRef> = None;
    for (block, log_index, event) in entries.drain(..) {
        match current {
            Some(open) if open != block => {
                batch.push_block(open, span.drain(..));
                current = Some(block);
            }
            None => current = Some(block),
            _ => {}
        }
        span.push((log_index, event));
    }
    if let Some(open) = current {
        batch.push_block(open, span);
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
    use core::cell::{
        Cell,
        RefCell,
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

        fn head(&mut self) -> Result<BlockRef, PollFailure> {
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
    /// so every poll after the first finds it already applied.
    struct Stuck {
        block: BlockRef,
    }

    impl Source for Stuck {
        type Event = u64;
        type Error = PollFailure;

        fn head(&mut self) -> Result<BlockRef, PollFailure> {
            Ok(self.block)
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

    /// Scripted chain that misbehaves on cue: it reorgs just before a chosen read, and it
    /// appends `extra` to the next range answer.
    struct Hostile {
        inner: ScriptedChain,
        reads: u32,
        reorg: Option<(u32, usize, Vec<Vec<u64>>)>,
        extra: Vec<(BlockRef, u32, u64)>,
    }

    impl Hostile {
        fn new(inner: ScriptedChain) -> Self {
            Self {
                inner,
                reads: 0,
                reorg: None,
                extra: Vec::new(),
            }
        }

        /// Reorgs the chain just before the `nth` read from now, whichever method it is.
        fn reorg_before_read(
            &mut self,
            nth: u32,
            depth: usize,
            new_blocks: Vec<Vec<u64>>,
        ) {
            self.reorg = Some((self.reads + nth, depth, new_blocks));
        }

        fn read(&mut self) {
            self.reads += 1;
            assert!(self.reads < 1_000, "the scan never stopped reading");
            if self
                .reorg
                .as_ref()
                .is_some_and(|(at, ..)| *at == self.reads)
            {
                let (_, depth, new_blocks) = self.reorg.take().expect("a reorg is due");
                let new_blocks: Vec<&[u64]> =
                    new_blocks.iter().map(Vec::as_slice).collect();
                self.inner.reorg(depth, &new_blocks);
            }
        }
    }

    impl Source for Hostile {
        type Event = u64;
        type Error = PollFailure;

        fn head(&mut self) -> Result<BlockRef, PollFailure> {
            self.read();
            self.inner.head()
        }

        fn header_at(&mut self, number: u64) -> Result<Option<BlockRef>, PollFailure> {
            self.read();
            self.inner.header_at(number)
        }

        fn events_in(
            &mut self,
            from: u64,
            to: u64,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            self.read();
            self.inner.events_in(from, to, out)?;
            out.append(&mut self.extra);
            Ok(())
        }

        fn horizon(&self) -> ReplayHorizon {
            self.inner.horizon()
        }

        fn window(&self) -> u64 {
            self.inner.window()
        }
    }

    /// Scripted chain read through shared handles, so a test can move the chain between
    /// ticks without `source_mut`, which drops the walk's mark. `gate` is asked once per
    /// call and fails it by returning true; `hide` drops the events of one block; `lie_at`
    /// answers the header request for that block with the next block's header.
    struct Remote<'a, G> {
        chain: &'a RefCell<ScriptedChain>,
        calls: &'a Cell<u32>,
        gate: G,
        hide: Option<u64>,
        lie_at: Option<u64>,
    }

    impl<G: FnMut() -> bool> Remote<'_, G> {
        fn enter(&mut self) -> Result<(), PollFailure> {
            self.calls.set(self.calls.get() + 1);
            if (self.gate)() {
                Err(PollFailure)
            } else {
                Ok(())
            }
        }
    }

    impl<G: FnMut() -> bool> Source for Remote<'_, G> {
        type Event = u64;
        type Error = PollFailure;

        fn head(&mut self) -> Result<BlockRef, PollFailure> {
            self.enter()?;
            self.chain.borrow_mut().head()
        }

        fn header_at(&mut self, number: u64) -> Result<Option<BlockRef>, PollFailure> {
            self.enter()?;
            let asked = if self.lie_at == Some(number) {
                number + 1
            } else {
                number
            };
            self.chain.borrow_mut().header_at(asked)
        }

        fn events_in(
            &mut self,
            from: u64,
            to: u64,
            out: &mut Vec<(BlockRef, u32, u64)>,
        ) -> Result<(), PollFailure> {
            self.enter()?;
            self.chain.borrow_mut().events_in(from, to, out)?;
            if let Some(hidden) = self.hide {
                out.retain(|(block, ..)| block.number != hidden);
            }
            Ok(())
        }

        fn window(&self) -> u64 {
            self.chain.borrow().window()
        }
    }

    fn remote_driver<'a, G: FnMut() -> bool>(
        chain: &'a RefCell<ScriptedChain>,
        calls: &'a Cell<u32>,
        gate: G,
        engine: EngineConfig,
        config: DriverConfig,
    ) -> Driver<RecordingFold, Remote<'a, G>> {
        let source = Remote {
            chain,
            calls,
            gate,
            hide: None,
            lie_at: None,
        };
        Driver::new(RecordingFold::default(), source, engine, config).unwrap()
    }

    /// Runs one tick and returns it with the source calls it made.
    fn tick_counted<G: FnMut() -> bool>(
        driver: &mut Driver<RecordingFold, Remote<'_, G>>,
        calls: &Cell<u32>,
    ) -> (Tick, u32) {
        let before = calls.get();
        let tick = driver.tick();
        (tick, calls.get() - before)
    }

    /// Chain of `blocks` blocks read `window` at a time; the block numbered `n` carries
    /// the event `n` when `n` is listed and none otherwise.
    fn sparse_chain(blocks: u64, window: u64, events: &[u64]) -> ScriptedChain {
        let mut chain = ScriptedChain::new(1);
        for number in 1..=blocks {
            let carried: &[u64] = if events.contains(&number) {
                &[number]
            } else {
                &[]
            };
            chain.push_block(carried);
        }
        chain.set_window(window);
        chain
    }

    /// Replaces the blocks `first..` of `chain` with blocks up to `last`, carrying the
    /// listed events as `sparse_chain` does.
    fn replace_from(chain: &mut ScriptedChain, first: u64, last: u64, events: &[u64]) {
        let depth = chain.tip().map_or(0, |tip| tip.number) + 1 - first;
        let blocks: Vec<Vec<u64>> = (first..=last)
            .map(|number| {
                if events.contains(&number) {
                    vec![number]
                } else {
                    vec![]
                }
            })
            .collect();
        let blocks: Vec<&[u64]> = blocks.iter().map(Vec::as_slice).collect();
        chain.reorg(usize::try_from(depth).unwrap(), &blocks);
    }

    fn engine_config(checkpoint_slots: usize) -> EngineConfig {
        EngineConfig {
            ring_capacity: 8,
            checkpoint_slots,
        }
    }

    fn hostile_driver(
        chain: ScriptedChain,
        checkpoint_slots: usize,
        config: DriverConfig,
    ) -> Driver<RecordingFold, Hostile> {
        Driver::new(
            RecordingFold::default(),
            Hostile::new(chain),
            engine_config(checkpoint_slots),
            config,
        )
        .unwrap()
    }

    /// Every event the fold holds, in fold order.
    fn folded<S: Source<Event = u64>>(driver: &Driver<RecordingFold, S>) -> Vec<u64> {
        let applied = &driver.engine().fold().applied;
        applied.iter().map(|(_, event)| *event).collect()
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

    /// Ticks until the first `Idle`; a thousand ticks without one fail the test.
    fn settle<F, S, K>(driver: &mut Driver<F, S, K>)
    where
        F: Fold + Clone,
        S: Source<Event = F::Event>,
        K: SnapshotSink<F>,
    {
        for _ in 0..1_000 {
            if driver.tick() == Tick::Idle {
                return;
            }
        }
        panic!("the driver never went idle");
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
    fn a_reset_clears_the_durable_cursor_until_a_later_offer_commits() {
        // given two drivers that offered through block 8, so each sink holds block 5
        fn offered() -> SinkDriver {
            let mut driver = sink_driver(8, 4, cadence_config(1, 1));
            run_to_idle(&mut driver);
            assert_eq!(driver.status().durable_cursor, Some(Position::new(5, 0)));
            driver
        }
        let mut resynced = offered();
        let mut reset = offered();
        // when one resyncs after a reorg below its ring and the other is reset by hand
        resynced
            .source_mut()
            .reorg(8, &[&[10], &[20], &[30], &[40]]);
        let outcome = resynced.tick();
        reset.engine_mut().reset(RecordingFold::default());
        // then neither reports the durable cursor of the chain it left
        assert_eq!(outcome, Tick::Resynced);
        assert_eq!(resynced.status().durable_cursor, None);
        assert_eq!(reset.status().durable_cursor, None);
        for driver in [&mut resynced, &mut reset] {
            // and a poll that offers nothing leaves it None
            driver.source_mut().fail_next_polls(1);
            assert_eq!(driver.tick(), Tick::SourceError);
            assert_eq!(driver.status().durable_cursor, None);
            // until the first offer made after the reset commits
            driver.tick();
            assert_eq!(driver.status().durable_cursor, Some(Position::new(1, 0)));
        }
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
    fn rollback_replays_from_the_restored_cursor() {
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
        // then the scan restarted at the restored cursor, so the replacements folded
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
    fn an_applied_block_served_again_keeps_the_poll_interval() {
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
        // when the first tick applies the block and the second drops it as applied
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
        assert_eq!(deduping, Tick::Idle);
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

    /// Twenty one-event blocks folded with a checkpoint every 4, at blocks 1, 5, 9, 13, 17.
    fn cadence_driver() -> Driver<RecordingFold, ScriptedChain> {
        let config = DriverConfig {
            checkpoint_interval: Some(4),
            snapshot_interval: None,
            ..DriverConfig::from_block(1)
        };
        let engine = EngineConfig {
            ring_capacity: 64,
            checkpoint_slots: 16,
        };
        let mut driver = new_driver(one_event_chain(20), engine, config);
        run_to_idle(&mut driver);
        assert_eq!(driver.engine().checkpoint_count(), 5);
        driver
    }

    #[test]
    fn a_rollback_restarts_the_checkpoint_cadence_at_the_restore_point() {
        // given twenty blocks folded with a checkpoint every 4, the last at block 17
        let mut driver = cadence_driver();
        // when blocks 15 to 20 are replaced and the refold runs on to block 24
        driver.source_mut().reorg(
            6,
            &[
                &[91],
                &[92],
                &[93],
                &[94],
                &[95],
                &[96],
                &[97],
                &[98],
                &[99],
                &[100],
            ],
        );
        run_to_idle(&mut driver);
        // then the cadence restarted at the restore point, block 13, so the replaced 17
        // and the new 21 each got a checkpoint
        assert_eq!(driver.engine().checkpoint_count(), 6);
    }

    #[test]
    fn a_manual_rollback_restarts_the_cadence_at_the_restore_point() {
        // given twenty blocks folded with a checkpoint every 4, the last at block 17
        let mut driver = cadence_driver();
        // when the caller rolls back through engine_mut and the driver refolds
        let restored = driver.engine_mut().rollback_at_or_below(12).unwrap();
        run_to_idle(&mut driver);
        // then blocks 13 and 17 got their checkpoints again
        assert_eq!(restored, Some(Position::new(9, 0)));
        assert_eq!(driver.engine().checkpoint_count(), 5);
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
    fn a_terminal_tick_clears_caught_up() {
        // given a caught-up driver whose fold halts on the next block's event
        let mut chain = ScriptedChain::new(1);
        chain.push_block(&[1]);
        let halt_pos = Position::new(2, 0);
        let fold = RecordingFold {
            applied: Vec::new(),
            fail_at: Some((halt_pos, FailKind::Halt)),
        };
        let mut driver =
            Driver::new(fold, chain, engine_config(0), DriverConfig::default()).unwrap();
        run_to_idle(&mut driver);
        assert!(driver.is_caught_up());
        // when that block arrives and the next tick hits the halt
        driver.source_mut().push_block(&[2]);
        let outcome = driver.tick();
        // then the tick is Terminal and neither the driver nor its status claims caught up
        assert_eq!(
            outcome,
            Tick::Terminal(EngineStatus::Halted { at: halt_pos })
        );
        assert!(!driver.is_caught_up());
        assert!(!driver.status().caught_up);
        // and a manual recovery through engine_mut is not caught up before the next poll
        driver.engine_mut().reset(RecordingFold::default());
        assert!(!driver.is_caught_up());
    }

    #[cfg(feature = "std")]
    #[test]
    fn a_caught_fold_panic_clears_caught_up() {
        // given a caught-up driver whose fold panics on the next block's event
        let mut chain = ScriptedChain::new(1);
        chain.push_block(&[1]);
        let fold = RecordingFold {
            applied: Vec::new(),
            fail_at: Some((Position::new(2, 0), FailKind::Panic)),
        };
        let mut driver =
            Driver::new(fold, chain, engine_config(0), DriverConfig::default()).unwrap();
        run_to_idle(&mut driver);
        assert!(driver.is_caught_up());
        // when that block arrives and the panic out of the next tick is caught
        driver.source_mut().push_block(&[2]);
        let caught =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| driver.tick()));
        // then the engine is Poisoned and neither the driver nor its status claims caught up
        assert!(caught.is_err());
        assert_eq!(
            driver.engine().status(),
            EngineStatus::Poisoned {
                at: Position::new(1, 0),
            }
        );
        assert!(!driver.is_caught_up());
        assert!(!driver.status().caught_up);
    }

    #[test]
    fn fold_maintenance_between_ticks_keeps_caught_up() {
        // given a driver over five one-event blocks
        let mut chain = ScriptedChain::new(1);
        for value in 1..=5u64 {
            chain.push_block(&[value]);
        }
        let mut driver = new_driver(chain, engine_config(0), DriverConfig::default());
        // when it ticks and then touches the fold, as a loop that prunes it does, until
        // it reports caught up
        let mut ticks = 0;
        while !driver.is_caught_up() {
            driver.tick();
            driver.engine_mut().fold_mut();
            ticks += 1;
            assert!(ticks < 50, "the driver never reported caught up");
        }
        // then it gets there after one tick that folds and one that finds the head
        assert_eq!(ticks, 2);
        assert_eq!(folded(&driver), vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn a_halted_engine_rolled_back_to_its_own_cursor_is_not_caught_up() {
        // given a caught-up driver with a checkpoint at its cursor, whose fold halts on
        // the next block's event
        let mut chain = ScriptedChain::new(1);
        chain.push_block(&[1]);
        let fold = RecordingFold {
            applied: Vec::new(),
            fail_at: Some((Position::new(2, 0), FailKind::Halt)),
        };
        let mut driver =
            Driver::new(fold, chain, engine_config(1), DriverConfig::default()).unwrap();
        run_to_idle(&mut driver);
        assert!(driver.is_caught_up());
        // when that block arrives, the tick hits the halt, which leaves the cursor where
        // it was, and the caller rolls back to the checkpoint there
        driver.source_mut().push_block(&[2]);
        driver.tick();
        let restored = driver.engine_mut().rollback_at_or_below(1).unwrap();
        // then the cursor is as it was, and the driver does not call that caught up
        assert_eq!(restored, Some(Position::new(1, 0)));
        assert!(!driver.is_caught_up());
        assert!(!driver.status().caught_up);
    }

    #[cfg(feature = "std")]
    #[test]
    fn a_poisoned_engine_rolled_back_to_its_own_cursor_is_not_caught_up() {
        // given a caught-up driver with a checkpoint at its cursor, whose fold panics on
        // the next block's event
        let mut chain = ScriptedChain::new(1);
        chain.push_block(&[1]);
        let fold = RecordingFold {
            applied: Vec::new(),
            fail_at: Some((Position::new(2, 0), FailKind::Panic)),
        };
        let mut driver =
            Driver::new(fold, chain, engine_config(1), DriverConfig::default()).unwrap();
        run_to_idle(&mut driver);
        assert!(driver.is_caught_up());
        // when that block arrives, the panic out of the next tick is caught, and the
        // caller rolls back to the checkpoint at the cursor, which the panic left alone
        driver.source_mut().push_block(&[2]);
        let caught =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| driver.tick()));
        let restored = driver.engine_mut().rollback_at_or_below(1).unwrap();
        // then the cursor is as it was, and the driver does not call that caught up
        assert!(caught.is_err());
        assert_eq!(restored, Some(Position::new(1, 0)));
        assert!(!driver.is_caught_up());
        assert!(!driver.status().caught_up);
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
    fn a_flapping_head_does_not_wear_the_checkpoints_down_to_a_resync() {
        // given one event every 100 blocks, so each event block is a checkpoint, folded to
        // block 700 at the defaults: four slots, one checkpoint per 64 blocks
        let mut x = ScriptedChain::new(1);
        for number in 1..=700u64 {
            if number % 100 == 0 {
                x.push_block(&[number]);
            } else {
                x.push_block(&[]);
            }
        }
        x.set_window(1);
        // and a second view of it whose head Y is X's sibling, with an event of its own
        let mut y = x.clone();
        y.reorg(1, &[&[7001]]);
        let mut driver = new_driver(
            x.clone(),
            EngineConfig::default(),
            DriverConfig::from_block(1),
        );
        run_to_idle(&mut driver);
        assert_eq!(driver.engine().checkpoint_count(), 4);
        // when the head flaps between X and Y, and the driver settles after each flap
        let mut ticks = Vec::new();
        for flap in 0..6 {
            *driver.source_mut() = if flap % 2 == 0 { y.clone() } else { x.clone() };
            ticks.extend(collect_to_idle(&mut driver));
        }
        // then no flap resyncs, and the four checkpoints are all still there
        assert!(!ticks.contains(&Tick::Resynced), "{ticks:?}");
        assert_eq!(driver.engine().checkpoint_count(), 4);
    }

    /// Folds blocks `from..=to` of the chain, one event each, straight into the engine.
    fn fold_blocks(
        engine: &mut Engine<RecordingFold>,
        chain: &ScriptedChain,
        from: u64,
        to: u64,
    ) {
        let mut batch = Batch::new();
        batch.boundary = from.checked_sub(1).and_then(|number| chain.header(number));
        for number in from..=to {
            batch.push_block(chain.header(number).unwrap(), [(0, number)]);
        }
        engine.apply_batch(&batch).unwrap();
    }

    #[test]
    fn a_resumed_driver_rolls_back_a_reorg_of_its_first_tip() {
        // given an engine recovered at block 2 with no checkpoints, as a decode leaves it
        let mut chain = ScriptedChain::new(1);
        for value in 1..=6u64 {
            chain.push_block(&[value]);
        }
        let mut engine = Engine::new(RecordingFold::default(), engine_config(2)).unwrap();
        fold_blocks(&mut engine, &chain, 1, 2);
        let config = DriverConfig {
            checkpoint_interval: Some(2),
            ..DriverConfig::from_block(1)
        };
        // when the driver resumes, folds to the tip in one poll, and the tip is replaced
        let mut driver =
            Driver::resume(engine, chain, RecordingFold::default(), config).unwrap();
        driver.tick();
        driver.source_mut().reorg(1, &[&[60]]);
        let outcome = driver.tick();
        // then it rolls back to the recovery point instead of resyncing from genesis
        assert_eq!(
            outcome,
            Tick::RolledBack {
                to: Some(Position::new(2, 0)),
            }
        );
    }

    #[test]
    fn a_driver_takes_no_extra_checkpoint_over_an_engine_that_has_one() {
        // given an engine at block 4 whose one slot holds a checkpoint at block 2
        let mut chain = ScriptedChain::new(1);
        for value in 1..=4u64 {
            chain.push_block(&[value]);
        }
        let mut engine = Engine::new(RecordingFold::default(), engine_config(1)).unwrap();
        fold_blocks(&mut engine, &chain, 1, 2);
        engine.checkpoint();
        fold_blocks(&mut engine, &chain, 3, 4);
        // when a driver takes it over
        let driver = Driver::resume(
            engine,
            chain,
            RecordingFold::default(),
            DriverConfig::from_block(1),
        )
        .unwrap();
        // then the checkpoint at block 2 is still the only one
        assert_eq!(driver.engine().durable_point(), Some(Position::new(2, 0)));
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
        // the earlier ticks spent probes too; count only the bisection
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

    #[test]
    fn a_reorg_between_the_first_two_reads_leaves_no_orphan_in_the_fold() {
        // given a driver folded to block 3, one block per poll
        let mut chain = ScriptedChain::new(1);
        for value in 1..=3u64 {
            chain.push_block(&[value]);
        }
        chain.set_window(1);
        let config = DriverConfig {
            checkpoint_interval: Some(1),
            ..DriverConfig::default()
        };
        let mut driver = hostile_driver(chain, 4, config);
        run_to_idle(&mut driver);
        // when the chain replaces block 3 and adds a block right after the tick's first read
        driver
            .source_mut()
            .reorg_before_read(2, 1, vec![vec![30], vec![40]]);
        run_to_idle(&mut driver);
        // then the fold holds exactly the canonical events
        assert_eq!(folded(&driver), vec![1, 2, 30, 40]);
    }

    #[test]
    fn two_hashes_for_one_height_are_a_source_error() {
        // given a one-block chain whose first answer also lists a rival block 1
        let mut chain = ScriptedChain::new(1);
        chain.push_block(&[10]);
        let rival = BlockRef {
            number: 1,
            hash: [9; 32],
        };
        let mut source = Hostile::new(chain);
        source.extra = vec![(rival, 1, 11)];
        let mut driver = Driver::new(
            RecordingFold::default(),
            source,
            engine_config(0),
            DriverConfig::from_block(1),
        )
        .unwrap();
        // when ticked
        let tick = driver.tick();
        // then the answer is refused and nothing folds
        assert_eq!(tick, Tick::SourceError);
        assert!(folded(&driver).is_empty());
    }

    #[test]
    fn a_head_at_the_last_block_number_ends_the_walk() {
        // given three empty blocks ending at u64::MAX, read two blocks per query
        let first = u64::MAX - 2;
        let mut chain = ScriptedChain::new(first);
        for _ in 0..3 {
            chain.push_block(&[]);
        }
        chain.set_window(2);
        let mut driver = hostile_driver(chain, 0, DriverConfig::from_block(first));
        // when polled
        let tick = driver.tick();
        // then the walk stops after the last window instead of reading it forever
        assert_eq!(tick, Tick::Idle);
    }

    #[test]
    fn a_reorg_between_windows_does_not_skip_its_events() {
        // given a driver folded to the only event, at block 5 of ten, two blocks per query
        let mut chain = ScriptedChain::new(1);
        for block in 1..=10u64 {
            let events: &[u64] = if block == 5 { &[50] } else { &[] };
            chain.push_block(events);
        }
        chain.set_window(2);
        let mut driver = hostile_driver(chain, 0, DriverConfig::from_block(1));
        run_to_idle(&mut driver);
        // when blocks 6 to 10 are replaced after the scan read block 6 empty, with events
        // at the new blocks 6 and 8
        let new_blocks = vec![vec![60], vec![], vec![80], vec![], vec![]];
        driver.source_mut().reorg_before_read(3, 5, new_blocks);
        run_to_idle(&mut driver);
        // then both new events fold
        assert_eq!(folded(&driver), vec![50, 60, 80]);
    }

    #[test]
    fn a_torn_answer_is_not_folded() {
        // given a six-block chain with events at blocks 1, 3 and 6
        let mut chain = ScriptedChain::new(1);
        for events in [&[1][..], &[], &[30], &[], &[], &[60]] {
            chain.push_block(events);
        }
        let old_block_3 = chain.header(3).unwrap();
        let mut source = Hostile::new(chain);
        // when the chain reorgs after the head was read, and the one range answer still
        // carries block 3 from the old chain
        source.reorg_before_read(2, 4, vec![vec![], vec![], vec![], vec![61]]);
        source.extra = vec![(old_block_3, 0, 30)];
        let mut driver = Driver::new(
            RecordingFold::default(),
            source,
            engine_config(0),
            DriverConfig::from_block(1),
        )
        .unwrap();
        let first = driver.tick();
        run_to_idle(&mut driver);
        // then the tick is refused and the fold ends with the new chain's events only
        assert_eq!(first, Tick::SourceError);
        assert_eq!(folded(&driver), vec![1, 61]);
    }

    #[test]
    fn a_torn_answer_ending_on_the_head_is_not_folded() {
        // given a six-block chain with events at blocks 1, 3 and 6
        let mut chain = ScriptedChain::new(1);
        for events in [&[1][..], &[], &[30], &[], &[], &[60]] {
            chain.push_block(events);
        }
        let old_head = chain.header(6).unwrap();
        let mut source = Hostile::new(chain);
        // when the chain reorgs after the head was read, and the one range answer still
        // carries the old head block above a block of the new chain
        source.reorg_before_read(2, 4, vec![vec![31], vec![], vec![], vec![]]);
        source.extra = vec![(old_head, 0, 60)];
        let mut driver = Driver::new(
            RecordingFold::default(),
            source,
            engine_config(0),
            DriverConfig::from_block(1),
        )
        .unwrap();
        let first = driver.tick();
        let after_first = folded(&driver);
        run_to_idle(&mut driver);
        // then the tick is refused and the fold ends with the new chain's events only
        assert_eq!(first, Tick::SourceError);
        assert!(after_first.is_empty());
        assert_eq!(folded(&driver), vec![1, 31]);
    }

    #[test]
    fn an_entry_outside_the_window_is_a_source_error() {
        // given a three-block chain read two blocks per query, whose first answer also
        // lists a block above its window
        let mut chain = ScriptedChain::new(1);
        for value in 1..=3u64 {
            chain.push_block(&[value]);
        }
        chain.set_window(2);
        let above = BlockRef {
            number: 3,
            hash: [7; 32],
        };
        let mut source = Hostile::new(chain);
        source.extra = vec![(above, 0, 777)];
        let mut driver = Driver::new(
            RecordingFold::default(),
            source,
            engine_config(0),
            DriverConfig::from_block(1),
        )
        .unwrap();
        // when ticked
        let tick = driver.tick();
        // then the answer is refused and nothing folds
        assert_eq!(tick, Tick::SourceError);
        assert!(folded(&driver).is_empty());
    }

    #[test]
    fn an_entry_below_the_cursor_block_is_a_source_error() {
        // given a driver folded to block 3
        let mut chain = ScriptedChain::new(1);
        for value in 1..=3u64 {
            chain.push_block(&[value]);
        }
        let mut driver = hostile_driver(chain, 0, DriverConfig::default());
        driver.tick();
        // when the next answer also lists an older block
        let below = BlockRef {
            number: 2,
            hash: [7; 32],
        };
        driver.source_mut().extra = vec![(below, 0, 555)];
        let tick = driver.tick();
        // then the answer is refused
        assert_eq!(tick, Tick::SourceError);
        assert_eq!(folded(&driver), vec![1, 2, 3]);
    }

    #[test]
    fn a_head_below_the_cursor_on_the_same_chain_is_idle() {
        // given a driver folded to block 3 with a checkpoint there, over events at 1 and 3
        let mut chain = ScriptedChain::new(1);
        chain.push_block(&[1]);
        chain.push_block(&[]);
        chain.push_block(&[3]);
        let mut at_one = chain.clone();
        at_one.reorg(2, &[]);
        let mut at_two = chain.clone();
        at_two.reorg(1, &[]);
        let mut driver = new_driver(chain, engine_config(2), DriverConfig::default());
        driver.tick();
        driver.source_mut().fail_next_polls(1);
        driver.tick();
        // when polls land on a node still at block 1, which the ring holds, and on one at
        // block 2, which it does not
        *driver.source_mut() = at_one;
        let first = driver.tick();
        *driver.source_mut() = at_two;
        let second = driver.tick();
        // then nothing moves: no rollback and no resync, and the error backoff ends
        assert_eq!([first, second], [Tick::Idle; 2]);
        assert_eq!(driver.next_delay(), Duration::from_secs(1));
        assert!(driver.is_caught_up());
        assert_eq!(driver.engine().cursor(), Some(Position::new(3, 0)));
        assert_eq!(folded(&driver), vec![1, 3]);
    }

    #[test]
    fn a_cursor_inside_a_block_folds_the_rest_of_it() {
        // given an engine that took the first event of block 2 and no more
        let mut chain = ScriptedChain::new(1);
        chain.push_block(&[1]);
        chain.push_block(&[20, 21, 22]);
        let mut engine = Engine::new(RecordingFold::default(), engine_config(0)).unwrap();
        let mut partial = Batch::new();
        partial.push_block(chain.header(1).unwrap(), [(0, 1)]);
        partial.push_block(chain.header(2).unwrap(), [(0, 20)]);
        engine.apply_batch(&partial).unwrap();
        // when a driver resumes over the whole chain
        let mut driver = Driver::resume(
            engine,
            chain,
            RecordingFold::default(),
            DriverConfig::from_block(1),
        )
        .unwrap();
        run_to_idle(&mut driver);
        // then the rest of block 2 folds too
        assert_eq!(folded(&driver), vec![1, 20, 21, 22]);
    }

    #[test]
    fn two_hashes_at_the_cursor_block_are_a_source_error() {
        // given a driver folded to block 3
        let mut chain = ScriptedChain::new(1);
        for value in 1..=3u64 {
            chain.push_block(&[value]);
        }
        let mut driver = hostile_driver(chain, 0, DriverConfig::default());
        driver.tick();
        // when the next answer also lists a rival block 3 at an applied position
        let rival = BlockRef {
            number: 3,
            hash: [7; 32],
        };
        driver.source_mut().extra = vec![(rival, 0, 666)];
        let tick = driver.tick();
        // then the answer is refused
        assert_eq!(tick, Tick::SourceError);
        assert_eq!(folded(&driver), vec![1, 2, 3]);
    }

    #[test]
    fn only_a_poll_that_folds_re_reads_the_head_block() {
        // given a driver folded to the head of a chain with an event in every block
        let mut chain = ScriptedChain::new(1);
        for value in 1..=3u64 {
            chain.push_block(&[value]);
        }
        let mut driver = hostile_driver(chain, 0, DriverConfig::default());
        run_to_idle(&mut driver);
        let reads = |driver: &mut Driver<RecordingFold, Hostile>| {
            let before = driver.source_mut().reads;
            driver.tick();
            driver.source_mut().reads - before
        };
        // when polled with no change, after an empty block, and after a block with an event
        let idle = reads(&mut driver);
        driver.source_mut().inner.push_block(&[]);
        let empty_block = reads(&mut driver);
        driver.source_mut().inner.push_block(&[9]);
        let event = reads(&mut driver);
        // then a poll reads the head and one range, and a fold also re-reads the head block
        assert_eq!([idle, empty_block, event], [2, 2, 3]);
    }

    #[test]
    fn an_emptied_head_block_is_a_fork_found_without_reading_its_header() {
        // given a driver folded to block 3, the head, with a checkpoint at each block
        let config = DriverConfig {
            checkpoint_interval: Some(1),
            ..DriverConfig::default()
        };
        let mut driver = hostile_driver(one_event_chain(3), 4, config);
        run_to_idle(&mut driver);
        // when block 3 is replaced by an empty block
        driver.source_mut().inner.reorg(1, &[&[]]);
        let before = driver.source_mut().reads;
        let tick = driver.tick();
        // then the rollback costs the head, one range, and two bisection probes
        assert_eq!(
            tick,
            Tick::RolledBack {
                to: Some(Position::new(2, 0)),
            }
        );
        assert_eq!(driver.source_mut().reads - before, 4);
    }

    #[test]
    fn a_long_empty_walk_that_keeps_failing_still_finishes() {
        // given an event, 1,000 empty blocks read four at a time, and another event, from
        // a source that fails every 25th call, which is fewer calls than the walk needs
        let chain = RefCell::new(sparse_chain(1_002, 4, &[1, 1_002]));
        let calls = Cell::new(0);
        let mut seen = 0;
        let flaky = move || {
            seen += 1;
            seen % 25 == 0
        };
        let mut driver = remote_driver(
            &chain,
            &calls,
            flaky,
            engine_config(0),
            DriverConfig::from_block(1),
        );
        // when ticked until the second event folds
        for _ in 0..1_000 {
            driver.tick();
            if folded(&driver).len() == 2 {
                break;
            }
        }
        // then the walk got through the gap
        assert_eq!(folded(&driver), vec![1, 1_002]);
    }

    #[test]
    fn a_token_bucket_rate_limit_still_finishes() {
        // given 2,000 empty blocks read four at a time, then an event, from a source
        // that allows 10 calls a second with a burst of 20, takes 20 ms a call, and fails
        // the rest
        let chain = RefCell::new(sparse_chain(2_001, 4, &[2_001]));
        let calls = Cell::new(0);
        let clock = Cell::new(0u64);
        let (mut tokens, mut last) = (20_000u64, 0u64);
        let limiter = {
            let clock = &clock;
            move || {
                clock.set(clock.get() + 20);
                // a millisecond at 10 calls a second earns ten thousandths of a call
                tokens = (tokens + (clock.get() - last) * 10).min(20_000);
                last = clock.get();
                let refused = tokens < 1_000;
                if !refused {
                    tokens -= 1_000;
                }
                refused
            }
        };
        let mut driver = remote_driver(
            &chain,
            &calls,
            limiter,
            engine_config(0),
            DriverConfig::from_block(1),
        );
        // when ticked, sleeping each tick's delay, until the event folds
        for _ in 0..10_000 {
            driver.tick();
            if !folded(&driver).is_empty() {
                break;
            }
            let delay = driver.next_delay();
            clock.set(
                clock.get() + delay.as_secs() * 1_000 + u64::from(delay.subsec_millis()),
            );
        }
        // then the walk finished inside the limit
        assert_eq!(folded(&driver), vec![2_001]);
    }

    #[test]
    fn a_reorg_that_adds_events_below_the_mark_drops_it() {
        // given a driver folded to the event at block 1, whose next walk stopped at its
        // cap over 256 empty blocks of a 600-block chain read four at a time
        let chain = RefCell::new(sparse_chain(600, 4, &[1, 600]));
        let calls = Cell::new(0);
        let mut driver = remote_driver(
            &chain,
            &calls,
            || false,
            engine_config(0),
            DriverConfig::from_block(1),
        );
        driver.tick();
        let capped = driver.tick();
        assert_eq!(capped, Tick::Progressed(ApplySummary::default()));
        // when blocks 60 to 600 are replaced, with an event at 60 below the walk's end
        replace_from(&mut chain.borrow_mut(), 60, 600, &[60, 600]);
        settle(&mut driver);
        // then the new event folds with the rest
        assert_eq!(folded(&driver), vec![1, 60, 600]);
    }

    #[test]
    fn source_mut_drops_the_mark() {
        // given a driver folded to the event at block 1, whose next walk stopped at its
        // cap over a source that hides the event at block 60
        let chain = RefCell::new(sparse_chain(600, 4, &[1, 60, 600]));
        let calls = Cell::new(0);
        let mut driver = remote_driver(
            &chain,
            &calls,
            || false,
            engine_config(0),
            DriverConfig::from_block(1),
        );
        driver.source_mut().hide = Some(60);
        driver.tick();
        let capped = driver.tick();
        assert_eq!(capped, Tick::Progressed(ApplySummary::default()));
        // when the source starts to answer for block 60
        driver.source_mut().hide = None;
        settle(&mut driver);
        // then the walk starts again at the cursor and folds it
        assert_eq!(folded(&driver), vec![1, 60, 600]);
    }

    #[test]
    fn engine_mut_drops_the_mark() {
        // given a driver folded to block 3 one block per query, with a checkpoint at each
        // event, whose next walk stopped at its cap over empty blocks
        let chain = RefCell::new(sparse_chain(250, 1, &[1, 2, 3, 250]));
        let calls = Cell::new(0);
        let config = DriverConfig {
            checkpoint_interval: Some(1),
            ..DriverConfig::from_block(1)
        };
        let mut driver =
            remote_driver(&chain, &calls, || false, engine_config(4), config);
        for _ in 0..3 {
            driver.tick();
        }
        let capped = driver.tick();
        assert_eq!(capped, Tick::Progressed(ApplySummary::default()));
        // when the engine is rolled back to block 2 by hand
        driver.engine_mut().rollback_at_or_below(2).unwrap();
        settle(&mut driver);
        // then the walk starts again at the restored cursor and folds block 3 once more
        assert_eq!(folded(&driver), vec![1, 2, 3, 250]);
    }

    #[test]
    fn a_long_empty_walk_finishes_through_fold_maintenance_between_its_ticks() {
        // given an event, 600 empty blocks read four at a time, and another event
        let chain = RefCell::new(sparse_chain(602, 4, &[1, 602]));
        let calls = Cell::new(0);
        let mut driver = remote_driver(
            &chain,
            &calls,
            || false,
            engine_config(0),
            DriverConfig::from_block(1),
        );
        // when it ticks, touching the fold after each tick, until the second event folds
        for _ in 0..100 {
            driver.tick();
            driver.engine_mut().fold_mut();
            if folded(&driver).len() == 2 {
                break;
            }
        }
        // then the walk got through the gap, which takes more than one capped tick
        assert_eq!(folded(&driver), vec![1, 602]);
    }

    #[test]
    fn a_manual_rollback_clears_caught_up_and_the_mark() {
        // given a driver folded to block 3 one block per query, with a checkpoint at each
        // event, that went idle after walks over empty blocks left a mark
        let chain = RefCell::new(sparse_chain(250, 1, &[1, 2, 3]));
        let calls = Cell::new(0);
        let config = DriverConfig {
            checkpoint_interval: Some(1),
            ..DriverConfig::from_block(1)
        };
        let mut driver =
            remote_driver(&chain, &calls, || false, engine_config(4), config);
        settle(&mut driver);
        assert!(driver.is_caught_up());
        assert!(driver.walked.is_some());
        // when the engine is rolled back to block 2 by hand
        driver.engine_mut().rollback_at_or_below(2).unwrap();
        // then it is not caught up
        assert!(!driver.is_caught_up());
        assert!(!driver.status().caught_up);
        // and the walk starts again at the restored cursor and folds block 3 once more
        settle(&mut driver);
        assert_eq!(folded(&driver), vec![1, 2, 3]);
        assert!(driver.is_caught_up());
    }

    #[test]
    fn a_manual_reset_of_an_engine_with_no_cursor_is_not_caught_up() {
        // given a caught-up driver over an empty chain, so its engine has no cursor
        let mut driver = new_driver(
            ScriptedChain::new(1),
            engine_config(0),
            DriverConfig::default(),
        );
        driver.tick();
        assert!(driver.is_caught_up());
        // when the engine is reset by hand
        driver.engine_mut().reset(RecordingFold::default());
        // then the driver is not caught up before its next poll
        assert!(!driver.is_caught_up());
        driver.tick();
        assert!(driver.is_caught_up());
    }

    #[test]
    fn a_manual_reset_clears_caught_up_and_the_mark() {
        // given a driver folded to the event at block 1 of 250 blocks read one at a time,
        // that went idle after walks over empty blocks left a mark
        let chain = RefCell::new(sparse_chain(250, 1, &[1]));
        let calls = Cell::new(0);
        let mut driver = remote_driver(
            &chain,
            &calls,
            || false,
            engine_config(0),
            DriverConfig::from_block(1),
        );
        settle(&mut driver);
        assert!(driver.is_caught_up());
        assert!(driver.walked.is_some());
        // when the engine is reset by hand
        driver.engine_mut().reset(RecordingFold::default());
        // then it is not caught up
        assert!(!driver.is_caught_up());
        assert!(!driver.status().caught_up);
        // and it folds the chain again from the start instead of going on from the mark
        settle(&mut driver);
        assert_eq!(folded(&driver), vec![1]);
        assert!(driver.is_caught_up());
    }

    #[test]
    fn a_mark_off_the_head_chain_is_dropped_for_good() {
        // given a fresh driver whose first walk stopped at its cap at block 256 of a
        // 600-block chain with no events
        let chain = RefCell::new(sparse_chain(600, 4, &[]));
        let calls = Cell::new(0);
        let mut driver = remote_driver(
            &chain,
            &calls,
            || false,
            engine_config(0),
            DriverConfig::from_block(1),
        );
        driver.tick();
        // when blocks 2 and up are replaced by empty blocks up to 256, and the driver polls
        // twice
        replace_from(&mut chain.borrow_mut(), 2, 256, &[]);
        let first = tick_counted(&mut driver, &calls);
        let second = tick_counted(&mut driver, &calls);
        // then the first poll finds the mark off the head's chain and walks from the
        // start instead, 64 windows, and the second has no mark to check
        assert_eq!([first, second], [(Tick::Idle, 66), (Tick::Idle, 65)]);
    }

    #[test]
    fn a_head_below_the_mark_is_idle_and_changes_nothing() {
        // given a driver folded to the event at block 1, whose next walk stopped at its
        // cap at block 257 of a 600-block chain
        let chain = RefCell::new(sparse_chain(600, 4, &[1]));
        let calls = Cell::new(0);
        let mut driver = remote_driver(
            &chain,
            &calls,
            || false,
            engine_config(0),
            DriverConfig::from_block(1),
        );
        driver.tick();
        driver.tick();
        let mark = driver.walked;
        assert_eq!(mark, chain.borrow().header(257));
        // when the source answers from a node that is only at block 100
        let full = chain.borrow().clone();
        chain.borrow_mut().reorg(500, &[]);
        let (tick, read) = tick_counted(&mut driver, &calls);
        // then the tick reads the head and stops, and nothing it holds moves
        assert_eq!((tick, read), (Tick::Idle, 1));
        assert!(driver.is_caught_up());
        assert_eq!(driver.next_delay(), Duration::from_secs(1));
        assert_eq!(driver.engine().cursor(), Some(Position::new(1, 0)));
        assert_eq!(folded(&driver), vec![1]);
        assert_eq!(driver.walked, mark);
        // and the walk goes on from the mark once the node catches up, without a check of
        // the mark, since the head is the one the capped walk read twice
        *chain.borrow_mut() = full;
        let (tick, read) = tick_counted(&mut driver, &calls);
        assert_eq!(
            (tick, read),
            (Tick::Progressed(ApplySummary::default()), 67)
        );
    }

    #[test]
    fn a_first_sync_behind_the_mark_waits_for_the_node() {
        // given a fresh driver whose first walk stopped at its cap at block 256 of a
        // 600-block chain with no events
        let chain = RefCell::new(sparse_chain(600, 4, &[]));
        let calls = Cell::new(0);
        let mut driver = remote_driver(
            &chain,
            &calls,
            || false,
            engine_config(0),
            DriverConfig::from_block(1),
        );
        driver.tick();
        let mark = driver.walked;
        assert_eq!(mark, chain.borrow().header(256));
        // when the source answers from a node that is only at block 100
        chain.borrow_mut().reorg(500, &[]);
        let (tick, read) = tick_counted(&mut driver, &calls);
        // then the tick reads the head and stops, and the mark stays
        assert_eq!((tick, read), (Tick::Idle, 1));
        assert_eq!(driver.walked, mark);
    }

    #[test]
    fn a_head_that_contradicts_the_ring_is_a_fork_even_below_the_mark() {
        // given a driver folded to the event at block 1, whose next walk stopped at its
        // cap at block 257 of a 600-block chain
        let chain = RefCell::new(sparse_chain(600, 4, &[1]));
        let calls = Cell::new(0);
        let mut driver = remote_driver(
            &chain,
            &calls,
            || false,
            engine_config(0),
            DriverConfig::from_block(1),
        );
        driver.tick();
        driver.tick();
        // when the source answers from a one-block chain whose block 1 is another block
        let mut other = sparse_chain(1, 4, &[]);
        other.reorg(1, &[&[1]]);
        *chain.borrow_mut() = other;
        let tick = driver.tick();
        // then the tick is no wait for a node to catch up: the engine resyncs
        assert_eq!(tick, Tick::Resynced);
    }

    #[test]
    fn a_failed_tick_keeps_the_mark() {
        // given a driver whose first walk stopped at its cap at block 256 of a 600-block
        // chain with no events, and whose source fails its 70th call, the third of the
        // next tick
        let chain = RefCell::new(sparse_chain(600, 4, &[]));
        let calls = Cell::new(0);
        let mut seen = 0;
        let gate = move || {
            seen += 1;
            seen == 70
        };
        let mut driver = remote_driver(
            &chain,
            &calls,
            gate,
            engine_config(0),
            DriverConfig::from_block(1),
        );
        driver.tick();
        // when that tick fails, and the next one runs
        let failed = driver.tick();
        let mark = driver.walked;
        let next = tick_counted(&mut driver, &calls);
        // then the failure left the mark, and the next walk, half as long, goes on from it
        assert_eq!(failed, Tick::SourceError);
        assert_eq!(mark, chain.borrow().header(256));
        assert_eq!(next, (Tick::Progressed(ApplySummary::default()), 35));
        assert_eq!(driver.walked, chain.borrow().header(384));
    }

    #[test]
    fn a_fold_inside_the_cap_costs_what_it_did() {
        // given a fresh driver over a 600-block chain read four at a time, with an event
        // in block 10
        let chain = RefCell::new(sparse_chain(600, 4, &[10]));
        let calls = Cell::new(0);
        let mut driver = remote_driver(
            &chain,
            &calls,
            || false,
            engine_config(0),
            DriverConfig::from_block(1),
        );
        // when ticked once
        let (tick, read) = tick_counted(&mut driver, &calls);
        // then the walk stops at the window with the event, and the tick reads the head,
        // three windows, and the head block again
        let applied = ApplySummary {
            applied: 1,
            deduped: 0,
            skipped: 0,
        };
        assert_eq!((tick, read), (Tick::Progressed(applied), 5));
    }

    #[test]
    fn a_head_on_the_mark_costs_one_call() {
        // given a driver folded to the event at block 1, whose next walk stopped at its
        // cap at block 257 of a 600-block chain
        let chain = RefCell::new(sparse_chain(600, 4, &[1]));
        let calls = Cell::new(0);
        let mut driver = remote_driver(
            &chain,
            &calls,
            || false,
            engine_config(0),
            DriverConfig::from_block(1),
        );
        driver.tick();
        driver.tick();
        // when the source answers from a node whose head is that block
        chain.borrow_mut().reorg(343, &[]);
        let (tick, read) = tick_counted(&mut driver, &calls);
        // then the tick reads the head and nothing else
        assert_eq!((tick, read), (Tick::Idle, 1));
    }

    #[test]
    fn a_long_walk_goes_on_from_the_block_its_last_tick_ended_on() {
        // given a fresh driver over 600 blocks read four at a time, whose only event is
        // in the last block
        let chain = RefCell::new(sparse_chain(600, 4, &[600]));
        let calls = Cell::new(0);
        let mut driver = remote_driver(
            &chain,
            &calls,
            || false,
            engine_config(0),
            DriverConfig::from_block(1),
        );
        // when ticked four times, counting each tick's calls
        let mut ticks = vec![tick_counted(&mut driver, &calls)];
        let first_delay = driver.next_delay();
        let first_caught_up = driver.is_caught_up();
        ticks.extend((0..3).map(|_| tick_counted(&mut driver, &calls)));
        // then two ticks stop at 64 windows with nothing to fold, and ask for no delay
        // and no caught-up; each costs the head, its windows, the block it ended on and
        // the head block again, and the second starts above the mark without checking it,
        // since the head is the one the first read twice
        let empty = Tick::Progressed(ApplySummary::default());
        let applied = Tick::Progressed(ApplySummary {
            applied: 1,
            deduped: 0,
            skipped: 0,
        });
        assert_eq!(
            ticks,
            vec![(empty, 67), (empty, 67), (applied, 24), (Tick::Idle, 1)]
        );
        assert_eq!(first_delay, Duration::ZERO);
        assert!(!first_caught_up);
        assert_eq!(folded(&driver), vec![600]);
    }

    #[test]
    fn a_failed_walk_is_halved_and_a_good_one_doubles_the_next() {
        // given 400 empty blocks read one at a time, from a source that fails its first
        // eight calls
        let chain = RefCell::new(sparse_chain(400, 1, &[]));
        let calls = Cell::new(0);
        let mut seen = 0;
        let gate = move || {
            seen += 1;
            seen <= 8
        };
        let mut driver = remote_driver(
            &chain,
            &calls,
            gate,
            engine_config(0),
            DriverConfig::from_block(1),
        );
        // when ticked sixteen times
        let read: Vec<u32> = (0..16)
            .map(|_| tick_counted(&mut driver, &calls).1)
            .collect();
        // then the span runs 64 down to 1 and stays there, then 1 up to 64 and stays
        // there: a tick costs its windows, the head, the block it ended on and the head
        // block again, with no check of the mark, since the head is the one the tick
        // before read twice
        assert_eq!(
            read,
            vec![1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 7, 11, 19, 35, 67, 67]
        );
    }

    #[test]
    fn a_head_reorg_does_not_cost_a_walk_its_progress() {
        // given a driver whose two capped walks over 600 empty blocks read four at a time
        // ended at blocks 256 and 512
        let chain = RefCell::new(sparse_chain(600, 4, &[]));
        let calls = Cell::new(0);
        let mut driver = remote_driver(
            &chain,
            &calls,
            || false,
            engine_config(0),
            DriverConfig::from_block(1),
        );
        driver.tick();
        driver.tick();
        // when the head block is replaced by two blocks, and later one more block follows
        replace_from(&mut chain.borrow_mut(), 600, 601, &[]);
        let replaced = tick_counted(&mut driver, &calls);
        chain.borrow_mut().push_block(&[]);
        let followed = tick_counted(&mut driver, &calls);
        // then each walk starts above block 512 and reaches the head: the head, the check
        // of the mark, and 89 or 90 blocks in 23 windows
        assert_eq!([replaced, followed], [(Tick::Idle, 25); 2]);
    }

    #[test]
    fn a_walk_that_fails_its_boundary_check_leaves_no_mark() {
        // given a driver folded to the event at block 1 of a 600-block chain read four at
        // a time
        let chain = RefCell::new(sparse_chain(600, 4, &[1, 600]));
        let calls = Cell::new(0);
        let mut driver = remote_driver(
            &chain,
            &calls,
            || false,
            engine_config(0),
            DriverConfig::from_block(1),
        );
        driver.tick();
        // when the whole chain is replaced, so the next walk stops at its cap over empty
        // blocks and finds block 1 changed
        {
            let mut chain = chain.borrow_mut();
            let mut blocks = vec![vec![11]];
            blocks.resize(599, vec![]);
            blocks.push(vec![600]);
            let blocks: Vec<&[u64]> = blocks.iter().map(Vec::as_slice).collect();
            chain.reorg(600, &blocks);
        }
        let recovery = driver.tick();
        settle(&mut driver);
        // then the engine resyncs and folds the new chain from the start
        assert_eq!(recovery, Tick::Resynced);
        assert_eq!(folded(&driver), vec![11, 600]);
    }

    #[test]
    fn an_anchor_that_is_not_the_block_asked_for_is_a_source_error() {
        // given a source that answers the request for block 256 with block 257's header
        let chain = RefCell::new(sparse_chain(600, 4, &[]));
        let calls = Cell::new(0);
        let mut driver = remote_driver(
            &chain,
            &calls,
            || false,
            engine_config(0),
            DriverConfig::from_block(1),
        );
        driver.source_mut().lie_at = Some(256);
        // when a walk stops at its cap and asks for the block it ended on
        let tick = driver.tick();
        // then the answer is refused
        assert_eq!(tick, Tick::SourceError);
    }

    /// A driver over `chain`, which is read one block at a time, folded to the head, with
    /// a checkpoint at each block.
    fn head_cache_driver<'a>(
        chain: &'a RefCell<ScriptedChain>,
        calls: &'a Cell<u32>,
    ) -> Driver<RecordingFold, Remote<'a, impl FnMut() -> bool>> {
        let config = DriverConfig {
            checkpoint_interval: Some(1),
            ..DriverConfig::from_block(1)
        };
        let mut driver = remote_driver(chain, calls, || false, engine_config(8), config);
        settle(&mut driver);
        driver
    }

    #[test]
    fn an_unchanged_head_skips_the_read_of_the_cursor_block() {
        // given a driver over five one-event blocks read one at a time
        let chain = RefCell::new(sparse_chain(5, 1, &[1, 2, 3, 4, 5]));
        let calls = Cell::new(0);
        let mut driver = remote_driver(
            &chain,
            &calls,
            || false,
            engine_config(0),
            DriverConfig::from_block(1),
        );
        // when it ticks to the head and once more, counting each tick's calls
        let reads: Vec<u32> = (0..6)
            .map(|_| tick_counted(&mut driver, &calls).1)
            .collect();
        // then a tick that folds reads the head, the next block and the head block again,
        // and the poll after the last reads the head and nothing else
        assert_eq!(reads, vec![3, 3, 3, 3, 3, 1]);
    }

    #[test]
    fn a_reorg_below_the_cursor_block_is_caught_when_the_head_changes() {
        // given a driver folded to block 5 of five one-event blocks
        let chain = RefCell::new(sparse_chain(5, 1, &[1, 2, 3, 4, 5]));
        let calls = Cell::new(0);
        let mut driver = head_cache_driver(&chain, &calls);
        // when blocks 3 to 5 are replaced by blocks with other events, so the head is
        // another block at the same height
        chain.borrow_mut().reorg(3, &[&[30], &[40], &[50]]);
        let found = driver.tick();
        settle(&mut driver);
        // then the next poll finds the fork and rolls back, and the new events fold
        assert_eq!(
            found,
            Tick::RolledBack {
                to: Some(Position::new(2, 0)),
            }
        );
        assert_eq!(folded(&driver), vec![1, 2, 30, 40, 50]);
    }

    #[test]
    fn source_mut_drops_the_head_cache() {
        // given a driver folded to the head, whose poll with the head unchanged reads the
        // head and nothing else
        let chain = RefCell::new(sparse_chain(5, 1, &[1, 2, 3, 4, 5]));
        let calls = Cell::new(0);
        let mut driver = head_cache_driver(&chain, &calls);
        assert_eq!(tick_counted(&mut driver, &calls), (Tick::Idle, 1));
        // when the source is borrowed, which may change what it returns
        driver.source_mut();
        // then the next poll reads the cursor block again
        assert_eq!(tick_counted(&mut driver, &calls), (Tick::Idle, 2));
    }

    #[test]
    fn a_manual_rollback_drops_the_head_cache() {
        // given a driver folded to the head, whose poll with the head unchanged reads the
        // head and nothing else
        let chain = RefCell::new(sparse_chain(5, 1, &[1, 2, 3, 4, 5]));
        let calls = Cell::new(0);
        let mut driver = head_cache_driver(&chain, &calls);
        assert_eq!(tick_counted(&mut driver, &calls), (Tick::Idle, 1));
        // when the engine is rolled back to block 3 by hand
        driver.engine_mut().rollback_at_or_below(3).unwrap();
        let refold = tick_counted(&mut driver, &calls);
        // then the next tick reads the cursor block again, the next block, and the head
        // block, and folds block 4
        let applied = ApplySummary {
            applied: 1,
            deduped: 0,
            skipped: 0,
        };
        assert_eq!(refold, (Tick::Progressed(applied), 4));
    }

    #[test]
    fn a_rollback_drops_the_head_cache() {
        // given a driver folded to block 5 of five one-event blocks read one at a time,
        // with a checkpoint at each
        let chain = RefCell::new(sparse_chain(5, 1, &[1, 2, 3, 4, 5]));
        let calls = Cell::new(0);
        let mut driver = head_cache_driver(&chain, &calls);
        let original = chain.borrow().clone();
        // when block 5 is replaced, the next poll rolls back to block 4, and the chain
        // goes back to the original block 5
        chain.borrow_mut().reorg(1, &[&[50]]);
        let found = driver.tick();
        *chain.borrow_mut() = original;
        let refold = tick_counted(&mut driver, &calls);
        // then the poll after the rollback reads the cursor block again, the next block,
        // and the head block, though the head is the one the driver vouched for before it
        let applied = ApplySummary {
            applied: 1,
            deduped: 0,
            skipped: 0,
        };
        assert_eq!(
            found,
            Tick::RolledBack {
                to: Some(Position::new(4, 0)),
            }
        );
        assert_eq!(refold, (Tick::Progressed(applied), 4));
    }

    #[test]
    fn an_answer_that_fails_the_shape_check_vouches_for_no_head() {
        // given a driver folded to block 5 of five one-event blocks read two at a time,
        // with a checkpoint at each
        let mut chain = one_event_chain(5);
        chain.set_window(2);
        let config = DriverConfig {
            checkpoint_interval: Some(1),
            ..DriverConfig::from_block(1)
        };
        let mut driver = hostile_driver(chain, 8, config);
        run_to_idle(&mut driver);
        // when block 5 is replaced and a block 6 follows it, and the first answer from
        // that chain also lists a rival block 6
        let rival = BlockRef {
            number: 6,
            hash: [7; 32],
        };
        let source = driver.source_mut();
        source.inner.reorg(1, &[&[50], &[60]]);
        source.extra = vec![(rival, 0, 666)];
        let refused = driver.tick();
        // and the next answer is clean
        let found = driver.tick();
        // then the refused tick folded nothing, and the next one still checks the cursor
        // block against the new chain
        assert_eq!(refused, Tick::SourceError);
        assert_eq!(
            found,
            Tick::RolledBack {
                to: Some(Position::new(4, 0)),
            }
        );
    }

    #[test]
    fn an_idle_poll_on_a_new_head_does_not_vouch_for_it() {
        // given a driver folded to the head of five one-event blocks read one at a time
        let chain = RefCell::new(sparse_chain(5, 1, &[1, 2, 3, 4, 5]));
        let calls = Cell::new(0);
        let mut driver = head_cache_driver(&chain, &calls);
        // when a block with no events arrives and the driver polls twice
        chain.borrow_mut().push_block(&[]);
        let first = tick_counted(&mut driver, &calls);
        let second = tick_counted(&mut driver, &calls);
        // then each poll reads the head, the cursor block and the new block, since the
        // walk that found nothing read the head only once
        assert_eq!([first, second], [(Tick::Idle, 3); 2]);
    }

    #[test]
    fn a_resumed_driver_reads_the_rest_of_its_cursor_block() {
        // given an engine that took the first event of block 2 and no more, over a chain
        // read one block at a time
        let mut scripted = ScriptedChain::new(1);
        scripted.push_block(&[1]);
        scripted.push_block(&[20, 21, 22]);
        scripted.push_block(&[30]);
        scripted.set_window(1);
        let chain = RefCell::new(scripted);
        let mut engine = Engine::new(RecordingFold::default(), engine_config(0)).unwrap();
        let mut partial = Batch::new();
        partial.push_block(chain.borrow().header(1).unwrap(), [(0, 1)]);
        partial.push_block(chain.borrow().header(2).unwrap(), [(0, 20)]);
        engine.apply_batch(&partial).unwrap();
        let calls = Cell::new(0);
        let source = Remote {
            chain: &chain,
            calls: &calls,
            gate: || false,
            hide: None,
            lie_at: None,
        };
        let mut driver = Driver::resume(
            engine,
            source,
            RecordingFold::default(),
            DriverConfig::from_block(1),
        )
        .unwrap();
        // when it is ticked to the head and once more, counting each tick's calls
        let reads: Vec<u32> = (0..3)
            .map(|_| tick_counted(&mut driver, &calls).1)
            .collect();
        // then the first tick reads the cursor block and folds the rest of it, and only
        // the ticks after it find a head they have vouched for
        assert_eq!(folded(&driver), vec![1, 20, 21, 22, 30]);
        assert_eq!(reads, vec![3, 3, 1]);
    }
}
