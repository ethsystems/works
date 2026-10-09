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

/// True when `block` has reached the next interval step past the last marked block.
fn due(last: Option<u64>, block: u64, interval: u64) -> bool {
    last.is_none_or(|last| block >= last.saturating_add(interval))
}

/// Outcome of one driver tick.
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

/// What a scan leaves for the tick to act on.
enum Scan {
    /// `batch` is ready to apply.
    Ready,
    /// The source's head trails the cursor on the chain the ring observed; nothing to do.
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
    /// True once the most recent poll returned no new blocks.
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
    pub fn source_mut(&mut self) -> &mut S {
        &mut self.source
    }

    /// True once the most recent poll returned no new blocks.
    pub fn is_caught_up(&self) -> bool {
        self.caught_up && self.engine.status().is_active()
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
        match self.scan() {
            Ok(Scan::Ready) => {}
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

    /// Fills `batch` with the events after the cursor, plus the cursor block's header, all
    /// as the chain `head` names reports them.
    fn scan(&mut self) -> Result<Scan, S::Error> {
        self.batch.clear();
        let head = self.source.head()?;
        let cursor = self.engine.cursor();
        // a node behind the cursor on the chain the ring observed is lagging, not forked
        if let Some(cursor) = cursor
            && head.number < cursor.block
            && self
                .engine
                .observed()
                .all(|seen| seen.number != head.number || seen.hash == head.hash)
        {
            return Ok(Scan::Lagging);
        }

        let window = self.source.window().max(1);
        let mut from = cursor.map_or(self.config.start_block, |cursor| cursor.block);
        while from <= head.number {
            let to = head.number.min(from.saturating_add(window - 1));
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
            self.batch.boundary = if head.number == cursor.block {
                Some(head)
            } else {
                self.source.header_at(cursor.block)?
            };
        }
        // What was read since `head` came from its chain only while the source still has
        // `head`. An answer that ends on `head` is no exception: it may still carry blocks
        // of another fork below it.
        if !self.batch.is_empty() && self.source.header_at(head.number)? != Some(head) {
            return Ok(Scan::Refused);
        }
        Ok(Scan::Ready)
    }

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
}
