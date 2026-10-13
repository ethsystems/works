//! Tokio harness: runs a `Driver` on its own thread and publishes status into a watch.

use std::{
    panic::{
        AssertUnwindSafe,
        catch_unwind,
        resume_unwind,
    },
    sync::{
        Arc,
        Condvar,
        Mutex,
    },
    thread::JoinHandle,
};

use tokio::sync::watch;

use crate::{
    driver::{
        Driver,
        DriverStatus,
    },
    fold::Fold,
    position::Position,
    sink::SnapshotSink,
    source::Source,
};

/// Pending checkpoint requests and the stop signal shared with the loop thread.
struct HarnessState {
    checkpoint_requests: u64,
    stop: bool,
}

/// Runs a `Driver` on a dedicated thread, bridging its status into a tokio watch channel.
pub fn spawn<F, S, K>(mut driver: Driver<F, S, K>) -> Handle<Driver<F, S, K>>
where
    F: Fold + Clone + Send + 'static,
    F::Event: Send,
    S: Source<Event = F::Event> + Send + 'static,
    K: SnapshotSink<F> + Send + 'static,
{
    let initial = driver.status();
    let (status_tx, status_rx) = watch::channel(initial);
    let state = Arc::new((
        Mutex::new(HarnessState {
            checkpoint_requests: 0,
            stop: false,
        }),
        Condvar::new(),
    ));
    let loop_state = Arc::clone(&state);
    let thread = std::thread::spawn(move || {
        loop {
            let requests = {
                let mut guard =
                    loop_state.0.lock().expect("harness state mutex poisoned");
                std::mem::take(&mut guard.checkpoint_requests)
            };
            // A fold panic leaves the engine Poisoned: publish that terminal status and end
            // the loop. A panic that leaves the engine active is not the fold's, so rethrow.
            let outcome = catch_unwind(AssertUnwindSafe(|| {
                // Requests coalesce into one checkpoint, keeping the K slots at K cursors.
                if requests > 0 {
                    driver.checkpoint();
                }
                driver.tick();
            }));
            let status = driver.status();
            let _ = status_tx.send(status);
            if let Err(panic) = outcome
                && !status.is_terminal()
            {
                resume_unwind(panic);
            }
            let stop = loop_state
                .0
                .lock()
                .expect("harness state mutex poisoned")
                .stop;
            if status.is_terminal() || stop {
                break;
            }
            let delay = driver.next_delay();
            let guard = loop_state.0.lock().expect("harness state mutex poisoned");
            if guard.stop {
                break;
            }
            // A catch-up tick asks for no delay, so the next poll runs at once.
            if delay.is_zero() {
                drop(guard);
                continue;
            }
            // Both signals are level-checked under the lock, so a late request wakes the loop.
            let _ = loop_state.1.wait_timeout_while(guard, delay, |state| {
                !state.stop && state.checkpoint_requests == 0
            });
        }
        driver
    });
    Handle {
        status: status_rx,
        state,
        thread,
    }
}

/// Handle to a `Driver` running on its own thread.
pub struct Handle<T> {
    status: watch::Receiver<DriverStatus>,
    state: Arc<(Mutex<HarnessState>, Condvar)>,
    thread: JoinHandle<T>,
}

impl<T> Handle<T> {
    /// Reads the most recently published status without waiting.
    pub fn status(&self) -> DriverStatus {
        *self.status.borrow()
    }

    /// Returns the first published status the predicate accepts, or the last one
    /// published once the loop thread has dropped its sender.
    async fn settled(
        &mut self,
        accept: impl FnMut(&DriverStatus) -> bool,
    ) -> DriverStatus {
        self.status
            .wait_for(accept)
            .await
            .map(|status| *status)
            .unwrap_or_else(|_| *self.status.borrow())
    }

    /// Returns when caught up or terminal, regardless of when the transition happened.
    pub async fn wait_caught_up(&mut self) -> DriverStatus {
        self.settled(|s| s.caught_up || s.is_terminal()).await
    }

    /// Returns when the cursor reaches `pos` or the driver is terminal.
    pub async fn wait_past(&mut self, pos: Position) -> DriverStatus {
        self.settled(|s| s.is_terminal() || s.cursor.is_some_and(|c| c >= pos))
            .await
    }

    /// Returns when the durable cursor reaches `pos` or the driver is terminal.
    ///
    /// A later resync clears the durable cursor until an offer made after it commits, so
    /// the answer holds for the instant it resolves.
    pub async fn wait_durable(&mut self, pos: Position) -> DriverStatus {
        self.settled(|s| s.is_terminal() || s.durable_cursor.is_some_and(|c| c >= pos))
            .await
    }

    /// Asks the loop to checkpoint before its next tick.
    pub fn request_checkpoint(&self) {
        let mut guard = self.state.0.lock().expect("harness state mutex poisoned");
        guard.checkpoint_requests = guard.checkpoint_requests.saturating_add(1);
        drop(guard);
        self.state.1.notify_all();
    }
}

impl<T: Send + 'static> Handle<T> {
    /// Stops the loop and returns the driver for inspection or manual recovery.
    pub async fn shutdown(self) -> T {
        {
            let mut guard = self.state.0.lock().expect("harness state mutex poisoned");
            guard.stop = true;
        }
        self.state.1.notify_all();
        tokio::task::spawn_blocking(move || {
            self.thread.join().expect("harness loop thread panicked")
        })
        .await
        .expect("harness shutdown task panicked")
    }
}

#[cfg(test)]
mod tests {
    use std::{
        convert::Infallible,
        sync::atomic::{
            AtomicBool,
            Ordering,
        },
        time::Duration,
        vec,
        vec::Vec,
    };

    use super::*;
    use crate::{
        driver::{
            Driver,
            DriverConfig,
        },
        engine::EngineConfig,
        error::{
            EngineStatus,
            FoldError,
        },
        test_util::{
            FailKind,
            RecordingFold,
            ScriptedChain,
            WatermarkSink,
        },
    };

    /// Test-scale poll interval fast enough to finish inside the per-test timeout.
    const FAST_POLL: Duration = Duration::from_millis(5);
    /// Upper bound on how long any single wait may take before the test fails.
    const WAIT_TIMEOUT: Duration = Duration::from_secs(5);

    fn engine_config(checkpoint_slots: usize) -> EngineConfig {
        EngineConfig {
            ring_capacity: 8,
            checkpoint_slots,
        }
    }

    fn fast_config() -> DriverConfig {
        DriverConfig {
            poll_interval: FAST_POLL,
            ..DriverConfig::default()
        }
    }

    async fn timeout<F: std::future::Future>(fut: F) -> F::Output {
        tokio::time::timeout(WAIT_TIMEOUT, fut)
            .await
            .expect("operation timed out")
    }

    #[tokio::test]
    async fn wait_caught_up_after_transition_returns_immediately() {
        // given a spawned driver over an empty chain, so the first tick is already caught up,
        // with a poll interval longer than this test's own wait bound
        let chain = ScriptedChain::new(1);
        let config = DriverConfig {
            poll_interval: WAIT_TIMEOUT.saturating_mul(10),
            ..DriverConfig::default()
        };
        let driver =
            Driver::new(RecordingFold::default(), chain, engine_config(0), config)
                .unwrap();
        let mut handle = spawn(driver);
        let before = timeout(async {
            loop {
                let status = handle.status();
                if status.caught_up {
                    break status;
                }
                tokio::time::sleep(FAST_POLL).await;
            }
        })
        .await;
        // when awaiting wait_caught_up only after caught_up was already observed true
        let after = timeout(handle.wait_caught_up()).await;
        // then it resolves without a further tick, since a further tick would need the
        // poll interval to elapse, which exceeds this test's own wait bound
        assert_eq!(after.generation, before.generation);
    }

    #[tokio::test]
    async fn wait_caught_up_before_transition_wakes() {
        // given a spawned driver over a longer chain
        let mut chain = ScriptedChain::new(1);
        for value in 1..=20u64 {
            chain.push_block(&[value]);
        }
        let driver = Driver::new(
            RecordingFold::default(),
            chain,
            engine_config(0),
            fast_config(),
        )
        .unwrap();
        let mut handle = spawn(driver);
        // when awaiting first, before any status has been observed
        let status = timeout(handle.wait_caught_up()).await;
        // then the call resolves once folding finishes
        assert!(status.caught_up);
        assert_eq!(status.cursor, Some(Position::new(20, 0)));
    }

    #[tokio::test]
    async fn wait_past_observes_cursor_progress() {
        // given a chain with events at block 8
        let mut chain = ScriptedChain::new(1);
        for value in 1..=10u64 {
            chain.push_block(&[value]);
        }
        let driver = Driver::new(
            RecordingFold::default(),
            chain,
            engine_config(0),
            fast_config(),
        )
        .unwrap();
        let mut handle = spawn(driver);
        // when awaiting wait_past((8, 0))
        let status = timeout(handle.wait_past(Position::new(8, 0))).await;
        // then the returned status cursor is at or past it
        assert!(
            status
                .cursor
                .is_some_and(|cursor| cursor >= Position::new(8, 0))
        );
    }

    #[tokio::test]
    async fn wait_durable_resolves_when_the_watermark_passes() {
        // given a spawned driver over twelve one-event blocks offering to a watermark sink
        let mut chain = ScriptedChain::new(1);
        for value in 1..=12u64 {
            chain.push_block(&[value]);
        }
        chain.set_window(1);
        let driver = Driver::with_sink(
            RecordingFold::default(),
            chain,
            WatermarkSink::default(),
            engine_config(3),
            DriverConfig {
                checkpoint_interval: Some(2),
                snapshot_interval: Some(1),
                ..fast_config()
            },
        )
        .unwrap();
        let mut handle = spawn(driver);
        // when awaiting the durable cursor to reach (3, 0)
        let status = timeout(handle.wait_durable(Position::new(3, 0))).await;
        // then the returned status carries a durable cursor at or past it
        assert!(
            status
                .durable_cursor
                .is_some_and(|cursor| cursor >= Position::new(3, 0))
        );
    }

    #[tokio::test]
    async fn wait_returns_on_terminal() {
        // given a halting fold
        let mut chain = ScriptedChain::new(1);
        chain.push_block(&[1]);
        chain.push_block(&[2]);
        let fold = RecordingFold {
            applied: Vec::new(),
            fail_at: Some((Position::new(1, 0), FailKind::Halt)),
        };
        let driver = Driver::new(fold, chain, engine_config(0), fast_config()).unwrap();
        let mut handle = spawn(driver);
        // when awaiting caught up
        let status = timeout(handle.wait_caught_up()).await;
        // then the wait resolves with a terminal status instead of hanging
        assert!(status.is_terminal());
    }

    #[tokio::test]
    async fn a_fold_panic_publishes_a_poisoned_status_and_keeps_the_driver() {
        // given a driver whose fold panics on the second block's event
        let mut chain = ScriptedChain::new(1);
        chain.push_block(&[1]);
        chain.push_block(&[2]);
        let fold = RecordingFold {
            applied: Vec::new(),
            fail_at: Some((Position::new(2, 0), FailKind::Panic)),
        };
        let driver = Driver::new(fold, chain, engine_config(0), fast_config()).unwrap();
        let mut handle = spawn(driver);
        // when awaiting caught up
        let status = timeout(handle.wait_caught_up()).await;
        // then the wait resolves with the poisoned status instead of a stale active one
        assert!(matches!(status.engine, EngineStatus::Poisoned { .. }));
        assert!(status.is_terminal());
        // and shutdown returns the driver with each event folded once
        let driver = handle.shutdown().await;
        let expected = vec![(Position::new(1, 0), 1), (Position::new(2, 0), 2)];
        assert_eq!(driver.engine().fold().applied, expected);
    }

    /// Fold whose clone panics once armed, as a bug outside `apply` would.
    struct CloneBomb(Arc<AtomicBool>);

    impl Clone for CloneBomb {
        fn clone(&self) -> Self {
            assert!(!self.0.load(Ordering::Relaxed), "armed clone panicked");
            Self(Arc::clone(&self.0))
        }
    }

    impl Fold for CloneBomb {
        type Event = u64;
        type Error = Infallible;

        fn apply(
            &mut self,
            _pos: Position,
            _event: &u64,
        ) -> Result<(), FoldError<Infallible>> {
            Ok(())
        }
    }

    #[tokio::test]
    #[should_panic(expected = "harness shutdown task panicked")]
    async fn a_panic_outside_the_fold_still_unwinds_the_loop() {
        // given a caught-up driver whose fold clone panics once armed
        let armed = Arc::new(AtomicBool::new(false));
        let driver = Driver::new(
            CloneBomb(Arc::clone(&armed)),
            ScriptedChain::new(1),
            engine_config(2),
            fast_config(),
        )
        .unwrap();
        let mut handle = spawn(driver);
        timeout(handle.wait_caught_up()).await;
        // when a checkpoint request makes the loop clone the fold
        armed.store(true, Ordering::Relaxed);
        handle.request_checkpoint();
        timeout(async {
            while !handle.thread.is_finished() {
                tokio::time::sleep(FAST_POLL).await;
            }
        })
        .await;
        // then the panic was rethrown, so the loop thread is dead and shutdown says so
        handle.shutdown().await;
    }

    #[tokio::test]
    async fn request_checkpoint_is_executed_by_the_loop() {
        // given a spawned driver
        let mut chain = ScriptedChain::new(1);
        chain.push_block(&[1]);
        let driver = Driver::new(
            RecordingFold::default(),
            chain,
            engine_config(4),
            fast_config(),
        )
        .unwrap();
        let mut handle = spawn(driver);
        let start_generation = handle.status().generation;
        // when requesting a checkpoint and awaiting a later generation
        handle.request_checkpoint();
        timeout(async {
            handle
                .status
                .wait_for(|s| s.generation > start_generation)
                .await
                .expect("watch channel closed")
        })
        .await;
        let driver = handle.shutdown().await;
        // then checkpoint_count on the shut-down driver's engine is at least 1
        assert!(driver.engine().checkpoint_count() >= 1);
    }

    #[tokio::test]
    async fn shutdown_returns_the_driver() {
        // given a spawned driver over a two-block chain
        let mut chain = ScriptedChain::new(1);
        chain.push_block(&[1]);
        chain.push_block(&[2]);
        let driver = Driver::new(
            RecordingFold::default(),
            chain,
            engine_config(0),
            fast_config(),
        )
        .unwrap();
        let mut handle = spawn(driver);
        let status = timeout(handle.wait_caught_up()).await;
        // when shut down
        let driver = handle.shutdown().await;
        // then the returned driver's engine view matches the last published status
        assert_eq!(driver.engine().cursor(), status.cursor);
        let expected = vec![(Position::new(1, 0), 1), (Position::new(2, 0), 2)];
        assert_eq!(driver.engine().fold().applied, expected);
    }
}
