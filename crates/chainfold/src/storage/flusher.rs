//! Background fsync thread bridging the apply path to durable snapshot commits.

use std::{
    fmt,
    io,
    sync::{
        Arc,
        Condvar,
        Mutex,
        MutexGuard,
        atomic::{
            AtomicBool,
            Ordering,
        },
        mpsc,
    },
    thread,
    thread::JoinHandle,
};

use crate::{
    engine::Engine,
    error::DurabilityLost,
    position::Position,
    sink::SnapshotSink,
    snapshot::Persist,
    storage::{
        store::{
            SnapshotStore,
            StoreError,
        },
        vfs::Vfs,
    },
};

/// Failure completing a submitted snapshot flush.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FlushError {
    /// Flusher stopped after a prior failure or shutdown.
    Closed,
    /// Filesystem operation failed during the commit.
    Io {
        /// Kind of the underlying io error.
        kind: io::ErrorKind,
    },
    /// Store refused the durable state it found.
    Corrupt,
}

impl fmt::Display for FlushError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Closed => {
                write!(f, "flusher closed after a prior failure or shutdown")
            }
            Self::Io { kind } => write!(f, "flusher io error: {kind}"),
            Self::Corrupt => write!(f, "flusher rejected a corrupt durable state"),
        }
    }
}

impl core::error::Error for FlushError {}

impl From<StoreError> for FlushError {
    fn from(error: StoreError) -> Self {
        match error {
            StoreError::Io(io_error) => Self::Io {
                kind: io_error.kind(),
            },
            StoreError::CorruptManifest
            | StoreError::MissingSnapshot { .. }
            | StoreError::RetainZero => Self::Corrupt,
            StoreError::Poisoned => Self::Closed,
        }
    }
}

/// Locks past a poisoned mutex, since every mutex here guards plain settled state.
fn lock_recovering<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(|error| error.into_inner())
}

/// Counting gate bounding jobs admitted but not yet fully processed.
struct Admission {
    available: Mutex<usize>,
    ready: Condvar,
}

impl Admission {
    fn new(capacity: usize) -> Self {
        Self {
            available: Mutex::new(capacity),
            ready: Condvar::new(),
        }
    }

    /// Blocks until a slot is available, then takes it.
    fn acquire(&self) {
        let available = lock_recovering(&self.available);
        let mut available = self
            .ready
            .wait_while(available, |slots| *slots == 0)
            .unwrap_or_else(|error| error.into_inner());
        *available -= 1;
    }

    /// Returns a slot and wakes one waiter.
    fn release(&self) {
        let mut available = lock_recovering(&self.available);
        *available += 1;
        self.ready.notify_one();
    }
}

/// Shared cell one durability token waits on.
#[derive(Default)]
struct TokenState {
    result: Mutex<Option<Result<(), FlushError>>>,
    ready: Condvar,
}

impl TokenState {
    /// Settles the token, keeping the first outcome recorded.
    fn complete(&self, result: Result<(), FlushError>) {
        let mut guard = lock_recovering(&self.result);
        if guard.is_none() {
            *guard = Some(result);
            self.ready.notify_all();
        }
    }
}

/// One submitted snapshot's durability outcome.
#[derive(Clone)]
pub struct DurabilityToken {
    state: Arc<TokenState>,
}

impl DurabilityToken {
    /// Blocks until the flush completes or fails.
    pub fn wait(&self) -> Result<(), FlushError> {
        let guard = lock_recovering(&self.state.result);
        let guard = self
            .state
            .ready
            .wait_while(guard, |result| result.is_none())
            .unwrap_or_else(|error| error.into_inner());
        (*guard).expect("condvar wakes only after the result is set")
    }

    /// Non-blocking read of the flush outcome, if it has completed.
    pub fn try_result(&self) -> Option<Result<(), FlushError>> {
        *lock_recovering(&self.state.result)
    }
}

/// One snapshot handed from the apply thread to the flusher thread.
struct Job {
    snapshot: Vec<u8>,
    cursor: Option<Position>,
    token: Arc<TokenState>,
    admission: Arc<Admission>,
}

impl Drop for Job {
    fn drop(&mut self) {
        self.token.complete(Err(FlushError::Closed));
        self.admission.release();
    }
}

/// Marks the flusher poisoned and completes the failing job's own token with its error.
#[cold]
fn poison_and_report(poisoned: &AtomicBool, token: &TokenState, error: StoreError) {
    poisoned.store(true, Ordering::Release);
    token.complete(Err(FlushError::from(error)));
}

/// Drains jobs until the channel closes, committing each unless already poisoned.
fn run_flusher<V: Vfs>(
    mut store: SnapshotStore<V>,
    receiver: mpsc::Receiver<Job>,
    durable_cursor: Arc<Mutex<Option<Position>>>,
    poisoned: Arc<AtomicBool>,
) -> SnapshotStore<V> {
    while let Ok(job) = receiver.recv() {
        if poisoned.load(Ordering::Acquire) {
            continue;
        }
        match store.commit(&job.snapshot, job.cursor) {
            Ok(()) => {
                let committed = store.durable_cursor();
                let mut watermark = lock_recovering(&durable_cursor);
                // A commit supersedes whatever the store held, so the watermark
                // tracks it down as well as up and always names what a reopen
                // recovers. A resync commits older state and lowers it.
                *watermark = committed;
                drop(watermark);
                job.token.complete(Ok(()));
            }
            Err(error) => poison_and_report(&poisoned, &job.token, error),
        }
    }
    store
}

/// Background fsync thread; the commit point is the fsync return, not the write.
pub struct Flusher<V: Vfs + Send + 'static> {
    sender: mpsc::SyncSender<Job>,
    admission: Arc<Admission>,
    durable_cursor: Arc<Mutex<Option<Position>>>,
    poisoned: Arc<AtomicBool>,
    handle: JoinHandle<SnapshotStore<V>>,
}

impl<V: Vfs + Send + 'static> Flusher<V> {
    /// Spawns the background fsync thread over an opened store.
    pub fn spawn(store: SnapshotStore<V>, queue_depth: usize) -> Self {
        let (sender, receiver) = mpsc::sync_channel::<Job>(queue_depth);
        let durable_cursor = Arc::new(Mutex::new(store.durable_cursor()));
        let poisoned = Arc::new(AtomicBool::new(false));
        let admission = Arc::new(Admission::new(queue_depth));
        let thread_cursor = Arc::clone(&durable_cursor);
        let thread_poisoned = Arc::clone(&poisoned);
        let handle = thread::spawn(move || {
            run_flusher(store, receiver, thread_cursor, thread_poisoned)
        });
        Self {
            sender,
            admission,
            durable_cursor,
            poisoned,
            handle,
        }
    }

    /// Fails fast once a prior flush failed; the watermark never moves after that.
    pub fn submit(
        &self,
        snapshot: Vec<u8>,
        cursor: Option<Position>,
    ) -> Result<DurabilityToken, FlushError> {
        if self.poisoned.load(Ordering::Acquire) {
            return Err(FlushError::Closed);
        }
        self.admission.acquire();
        let token = Arc::new(TokenState::default());
        let job = Job {
            snapshot,
            cursor,
            token: Arc::clone(&token),
            admission: Arc::clone(&self.admission),
        };
        if self.sender.send(job).is_err() {
            return Err(FlushError::Closed);
        }
        Ok(DurabilityToken { state: token })
    }

    /// Cursor a reopen of the store would recover; falls when a resync commits
    /// older state.
    pub fn durable_cursor(&self) -> Option<Position> {
        *lock_recovering(&self.durable_cursor)
    }

    /// Stops the thread and returns the store; pending jobs complete first.
    pub fn join(self) -> Result<SnapshotStore<V>, FlushError> {
        let Self { sender, handle, .. } = self;
        drop(sender);
        handle.join().map_err(|_| FlushError::Closed)
    }
}

impl<V: Vfs + Send + 'static, F: Persist> SnapshotSink<F> for Flusher<V> {
    /// Encodes the oldest retained checkpoint and queues it; blocks only on a
    /// full queue, never on fsync.
    fn offer(&mut self, engine: &Engine<F>) -> Result<(), DurabilityLost> {
        let mut bytes = Vec::new();
        match engine.encode_durable_snapshot(&mut bytes) {
            Ok(None) => Ok(()),
            Ok(Some(point)) => {
                self.submit(bytes, Some(point))
                    .map_err(|_| DurabilityLost)?;
                Ok(())
            }
            Err(_) => Err(DurabilityLost),
        }
    }

    fn durable_cursor(&self) -> Option<Position> {
        Flusher::durable_cursor(self)
    }
}

#[cfg(test)]
mod tests {
    use std::{
        path::PathBuf,
        sync::{
            Arc,
            mpsc,
        },
        thread,
        time::Duration,
    };

    use super::super::{
        store::{
            SnapshotStore,
            StoreConfig,
        },
        vfs::Vfs,
    };
    use crate::{
        batch::{
            Batch,
            BlockSpan,
            LogEvent,
        },
        engine::{
            Engine,
            EngineConfig,
        },
        position::{
            BlockRef,
            Position,
        },
        sink::SnapshotSink,
        storage::flusher::{
            FlushError,
            Flusher,
        },
        test_util::{
            CrashVfs,
            RecordingFold,
        },
    };

    fn config(dir: PathBuf, retain: usize) -> StoreConfig {
        StoreConfig { dir, retain }
    }

    fn engine_config() -> EngineConfig {
        EngineConfig {
            ring_capacity: 8,
            checkpoint_slots: 2,
        }
    }

    /// Deterministic block header: the block number embedded directly in the hash bytes.
    fn block_ref(number: u64) -> BlockRef {
        let mut hash = [0u8; 32];
        hash[..8].copy_from_slice(&number.to_le_bytes());
        BlockRef { number, hash }
    }

    /// Advances the engine by one block carrying a single event.
    fn advance(engine: &mut Engine<RecordingFold>, number: u64) {
        let boundary = number.checked_sub(1).filter(|&n| n > 0).map(block_ref);
        let batch = Batch {
            boundary,
            spans: vec![BlockSpan {
                block: block_ref(number),
                start: 0,
                end: 1,
            }],
            events: vec![LogEvent {
                log_index: 0,
                event: number,
            }],
        };
        engine.apply_batch(&batch).unwrap();
    }

    #[test]
    fn sink_offer_submits_the_durable_point() {
        // given a flusher and an engine checkpointed at (2, 0) then folded to block 4
        let dir = PathBuf::from("/flusher-sink");
        let (store, _) =
            SnapshotStore::open(config(dir.clone(), 1), CrashVfs::new()).unwrap();
        let mut flusher = Flusher::spawn(store, 4);
        let mut engine = Engine::new(RecordingFold::default(), engine_config()).unwrap();
        advance(&mut engine, 1);
        advance(&mut engine, 2);
        engine.checkpoint();
        advance(&mut engine, 3);
        advance(&mut engine, 4);
        // when offered through the sink and the flusher is joined
        let offered = SnapshotSink::offer(&mut flusher, &engine);
        let store = flusher.join().unwrap();
        // then the durable cursor is the checkpoint's and the stored bytes decode to it
        assert_eq!(offered, Ok(()));
        assert_eq!(store.durable_cursor(), Some(Position::new(2, 0)));
        let (_, recovered) =
            SnapshotStore::open(config(dir, 1), store.into_vfs()).unwrap();
        let recovered = recovered.expect("the offered snapshot is durable");
        let decoded = Engine::<RecordingFold>::decode_snapshot(
            &recovered.snapshot,
            engine_config(),
        )
        .unwrap();
        assert_eq!(decoded.cursor(), Some(Position::new(2, 0)));
    }

    #[test]
    fn sink_offer_without_checkpoints_submits_nothing() {
        // given a flusher and an engine that never checkpointed
        let dir = PathBuf::from("/flusher-empty");
        let (store, _) = SnapshotStore::open(config(dir, 1), CrashVfs::new()).unwrap();
        let mut flusher = Flusher::spawn(store, 4);
        let mut engine = Engine::new(RecordingFold::default(), engine_config()).unwrap();
        advance(&mut engine, 1);
        // when offered through the sink and the flusher is joined
        let offered = SnapshotSink::offer(&mut flusher, &engine);
        let store = flusher.join().unwrap();
        // then the offer succeeded and the store holds no durable cursor
        assert_eq!(offered, Ok(()));
        assert_eq!(store.durable_cursor(), None);
    }

    #[test]
    fn token_completes_after_fsync() {
        // given a spawned flusher over a fresh store
        let dir = PathBuf::from("/flusher");
        let (store, _) = SnapshotStore::open(config(dir, 1), CrashVfs::new()).unwrap();
        let flusher = Flusher::spawn(store, 4);
        let cursor = Some(Position::new(5, 0));
        // when submitting a snapshot
        let token = flusher.submit(b"snapshot".to_vec(), cursor).unwrap();
        // then wait returns Ok and durable_cursor advances to the submitted cursor
        assert_eq!(token.wait(), Ok(()));
        assert_eq!(flusher.durable_cursor(), cursor);
    }

    #[test]
    fn watermark_tracks_the_last_committed_cursor() {
        // given three submits with strictly increasing cursors, each waited before the next
        let dir = PathBuf::from("/flusher");
        let (store, _) = SnapshotStore::open(config(dir, 1), CrashVfs::new()).unwrap();
        let flusher = Flusher::spawn(store, 4);
        let first_cursor = Some(Position::new(1, 0));
        let second_cursor = Some(Position::new(2, 0));
        let third_cursor = Some(Position::new(3, 0));
        // when each submit is waited on before the next one is issued, the last one
        // carrying an older cursor as a resync would
        let first = flusher.submit(b"one".to_vec(), first_cursor).unwrap();
        assert_eq!(first.wait(), Ok(()));
        let after_first = flusher.durable_cursor();
        let second = flusher.submit(b"two".to_vec(), second_cursor).unwrap();
        assert_eq!(second.wait(), Ok(()));
        let after_second = flusher.durable_cursor();
        let third = flusher.submit(b"three".to_vec(), third_cursor).unwrap();
        assert_eq!(third.wait(), Ok(()));
        let after_third = flusher.durable_cursor();
        let older = flusher.submit(b"resynced".to_vec(), first_cursor).unwrap();
        assert_eq!(older.wait(), Ok(()));
        let after_older = flusher.durable_cursor();
        // then durable_cursor names the cursor of the snapshot the store now holds
        assert_eq!(after_first, first_cursor);
        assert_eq!(after_second, second_cursor);
        assert_eq!(after_third, third_cursor);
        assert!(after_first < after_second);
        assert!(after_second < after_third);
        assert_eq!(after_older, first_cursor);
    }

    #[test]
    fn watermark_matches_what_a_reopen_recovers_after_older_state_commits() {
        // given a flusher that committed block 3 and then committed block 1 on top
        let dir = PathBuf::from("/flusher-resync");
        let (store, _) =
            SnapshotStore::open(config(dir.clone(), 1), CrashVfs::new()).unwrap();
        let flusher = Flusher::spawn(store, 4);
        let high = flusher
            .submit(b"folded".to_vec(), Some(Position::new(3, 0)))
            .unwrap();
        assert_eq!(high.wait(), Ok(()));
        let low = flusher
            .submit(b"resynced".to_vec(), Some(Position::new(1, 0)))
            .unwrap();
        assert_eq!(low.wait(), Ok(()));
        // when the watermark is read and the store is joined and reopened
        let watermark = flusher.durable_cursor();
        let store = flusher.join().unwrap();
        let (_, recovered) =
            SnapshotStore::open(config(dir, 1), store.into_vfs()).unwrap();
        // then the watermark equals the cursor and bytes the reopen recovers
        let recovered = recovered.expect("the resynced snapshot is durable");
        assert_eq!(watermark, Some(Position::new(1, 0)));
        assert_eq!(recovered.cursor, watermark);
        assert_eq!(recovered.snapshot.as_slice(), b"resynced".as_slice());
    }

    #[test]
    fn failed_fsync_freezes_watermark_and_poisons_tokens() {
        // given a CrashVfs budget that fails partway through the second commit
        let dir = PathBuf::from("/flusher");
        let (mut measure, _) =
            SnapshotStore::open(config(dir.clone(), 1), CrashVfs::new()).unwrap();
        measure.commit(b"first", Some(Position::new(1, 0))).unwrap();
        let after_first = measure.into_vfs().op_count();
        let vfs = CrashVfs::with_crash_budget(after_first, 0);
        let (store, _) = SnapshotStore::open(config(dir, 1), vfs).unwrap();
        let flusher = Flusher::spawn(store, 4);
        let first_cursor = Some(Position::new(1, 0));
        let second_cursor = Some(Position::new(2, 0));
        let first = flusher.submit(b"first".to_vec(), first_cursor).unwrap();
        let second = flusher.submit(b"second".to_vec(), second_cursor).unwrap();
        // when both tokens are waited
        let first_result = first.wait();
        let second_result = second.wait();
        // then the first is Ok, the second carries the error, watermark stays on the first
        assert_eq!(first_result, Ok(()));
        assert!(second_result.is_err());
        assert_eq!(flusher.durable_cursor(), first_cursor);
        // and a third submit returns Closed
        let third = flusher.submit(b"third".to_vec(), Some(Position::new(3, 0)));
        assert!(matches!(third, Err(FlushError::Closed)));
    }

    #[test]
    fn join_returns_store_after_draining() {
        // given a pending submit on a fresh flusher
        let dir = PathBuf::from("/flusher");
        let (store, _) = SnapshotStore::open(config(dir, 1), CrashVfs::new()).unwrap();
        let flusher = Flusher::spawn(store, 4);
        let cursor = Some(Position::new(7, 0));
        let token = flusher.submit(b"pending".to_vec(), cursor).unwrap();
        // when joined
        let store = flusher.join().unwrap();
        // then the returned store's durable_cursor reflects the drained job
        assert_eq!(token.wait(), Ok(()));
        assert_eq!(store.durable_cursor(), cursor);
    }

    /// Vfs wrapper that blocks one specific write call until the test releases it.
    ///
    /// `SnapshotStore::open` on a fresh directory issues the first `write` call
    /// (the blank manifest), so the commit under test is gated on the second.
    struct GatedVfs {
        inner: CrashVfs,
        gate: mpsc::Receiver<()>,
        gate_at_write: u32,
        writes_seen: u32,
    }

    impl GatedVfs {
        fn new(inner: CrashVfs, gate: mpsc::Receiver<()>, gate_at_write: u32) -> Self {
            Self {
                inner,
                gate,
                gate_at_write,
                writes_seen: 0,
            }
        }

        fn wait_if_gated(&mut self) {
            self.writes_seen += 1;
            if self.writes_seen == self.gate_at_write {
                self.gate
                    .recv()
                    .expect("gate sender dropped before releasing");
            }
        }
    }

    impl Vfs for GatedVfs {
        fn create_dir_all(&mut self, path: &std::path::Path) -> std::io::Result<()> {
            self.inner.create_dir_all(path)
        }

        fn read(&mut self, path: &std::path::Path) -> std::io::Result<Vec<u8>> {
            self.inner.read(path)
        }

        fn write(&mut self, path: &std::path::Path, bytes: &[u8]) -> std::io::Result<()> {
            self.wait_if_gated();
            self.inner.write(path, bytes)
        }

        fn write_at(
            &mut self,
            path: &std::path::Path,
            offset: u64,
            bytes: &[u8],
        ) -> std::io::Result<()> {
            self.inner.write_at(path, offset, bytes)
        }

        fn fsync_file(&mut self, path: &std::path::Path) -> std::io::Result<()> {
            self.inner.fsync_file(path)
        }

        fn rename(
            &mut self,
            from: &std::path::Path,
            to: &std::path::Path,
        ) -> std::io::Result<()> {
            self.inner.rename(from, to)
        }

        fn remove(&mut self, path: &std::path::Path) -> std::io::Result<()> {
            self.inner.remove(path)
        }

        fn list(&mut self, dir: &std::path::Path) -> std::io::Result<Vec<PathBuf>> {
            self.inner.list(dir)
        }

        fn fsync_dir(&mut self, path: &std::path::Path) -> std::io::Result<()> {
            self.inner.fsync_dir(path)
        }

        fn exists(&mut self, path: &std::path::Path) -> std::io::Result<bool> {
            self.inner.exists(path)
        }
    }

    #[test]
    fn bounded_queue_applies_backpressure() {
        // given queue_depth 1 and a first commit gated until the test releases it
        let dir = PathBuf::from("/flusher");
        let (release_tx, release_rx) = mpsc::channel();
        let vfs = GatedVfs::new(CrashVfs::new(), release_rx, 2);
        let (store, _) = SnapshotStore::open(config(dir, 1), vfs).unwrap();
        let flusher = Arc::new(Flusher::spawn(store, 1));
        let first = flusher
            .submit(b"first".to_vec(), Some(Position::new(1, 0)))
            .unwrap();

        // when a second submit is attempted from another thread while the first is gated
        let second_flusher = Arc::clone(&flusher);
        let handle = thread::spawn(move || {
            second_flusher.submit(b"second".to_vec(), Some(Position::new(2, 0)))
        });
        thread::sleep(Duration::from_millis(20));
        // then the second submit is still blocked, and releasing the first unblocks it
        assert!(!handle.is_finished());
        release_tx.send(()).unwrap();
        assert_eq!(first.wait(), Ok(()));
        let second = handle.join().unwrap().unwrap();
        assert_eq!(second.wait(), Ok(()));
    }
}
