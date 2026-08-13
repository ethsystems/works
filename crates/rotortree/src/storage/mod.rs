pub(crate) mod checkpoint;
mod config;
pub(crate) mod data;
mod error;
mod frame;
mod recovery;
mod token;
mod wal;

use std::{
    io::{
        Seek,
        SeekFrom,
        Write,
    },
    path::PathBuf,
    sync::{
        Arc,
        atomic::{
            AtomicBool,
            AtomicUsize,
            Ordering,
        },
    },
    time::Duration,
};

use arc_swap::ArcSwap;
use parking_lot::Mutex;

use crate::{
    Hash,
    Hasher,
    LeanIMT,
    chunked_level::{
        CHUNK_SIZE,
        Chunk,
    },
    tree::{
        TreeInner,
        TreeSnapshot,
    },
};

pub use checkpoint::{
    CheckpointPolicy,
    TieringConfig,
};
pub use config::{
    FlushPolicy,
    RotorTreeConfig,
};
pub use error::{
    RotorTreeError,
    StorageError,
};
pub use token::DurabilityToken;

use recovery::RecoveryResult;
use token::DurabilityTracker;

/// level ordered checkpoint during snapshot
struct LevelCheckpointData {
    /// unwritten
    new_chunks: Vec<Chunk>,
    /// start from
    from_chunk: usize,
    /// Complete chunks only: a partial last chunk is rewritten each checkpoint.
    total_chunks: usize,
}

/// checkpoint snapshot
struct CheckpointSnap {
    depth: usize,
    leaf_count: u64,
    last_seq: u64,
    root_hash: Hash,
    level_data: Vec<LevelCheckpointData>,
}

/// Internal mutable state
struct DurableState<const N: usize, const MAX_DEPTH: usize> {
    inner: TreeInner<N, MAX_DEPTH>,
    buffer: Vec<u8>,
    next_seq: u64,
    checkpointed_chunks: Vec<usize>,
}

struct CheckpointCoord {
    requested: bool,
    completed: u64,
}

/// Shared state
struct Shared<H: Hasher, const N: usize, const MAX_DEPTH: usize> {
    hasher: H,
    state: Mutex<DurableState<N, MAX_DEPTH>>,
    wal_file: Mutex<std::fs::File>,
    snapshot: ArcSwap<TreeSnapshot<N, MAX_DEPTH>>,
    durability: DurabilityTracker,
    closed: AtomicBool,
    bg_error: ArcSwap<Option<error::BackgroundError>>,
    data_dir: PathBuf,
    checkpoint_policy: CheckpointPolicy,
    tiering: TieringConfig,
    entries_since_checkpoint: AtomicUsize,
    uncheckpointed_memory_bytes: AtomicUsize,
    checkpoint: (Mutex<CheckpointCoord>, parking_lot::Condvar),
}

impl<H: Hasher, const N: usize, const MAX_DEPTH: usize> Shared<H, N, MAX_DEPTH> {
    fn flush_inner(&self) -> Result<(), StorageError> {
        let wal_file = self.wal_file.lock();
        let (buf, last_seq) = {
            let mut state = self.state.lock();
            if state.buffer.is_empty() {
                return Ok(());
            }
            let buf = std::mem::take(&mut state.buffer);
            let last_seq = state.next_seq.saturating_sub(1);
            (buf, last_seq)
        };

        let pos_before = (&*wal_file).stream_position().map_err(StorageError::Io)?;

        match (&*wal_file).write_all(&buf) {
            Ok(()) => {
                let sync_result = wal_file.sync_data();

                let mut state = self.state.lock();
                if state.buffer.is_empty() {
                    let mut returned = buf;
                    returned.clear();
                    state.buffer = returned;
                }

                match sync_result {
                    Ok(()) => {
                        self.durability.mark_flushed(last_seq);
                        Ok(())
                    }
                    Err(e) => {
                        let err = Arc::new(e);
                        self.bg_error.store(Arc::new(Some(
                            error::BackgroundError::FlushFailed(Arc::clone(&err)),
                        )));
                        Err(StorageError::FlushFailed(err))
                    }
                }
            }
            Err(e) => {
                let _ = (&*wal_file).seek(SeekFrom::Start(pos_before));
                let _ = wal_file.set_len(pos_before);

                let mut state = self.state.lock();
                if state.buffer.is_empty() {
                    state.buffer = buf;
                } else {
                    let mut combined = buf;
                    combined.extend_from_slice(&state.buffer);
                    state.buffer = combined;
                }
                let err = Arc::new(e);
                self.bg_error
                    .store(Arc::new(Some(error::BackgroundError::FlushFailed(
                        Arc::clone(&err),
                    ))));
                Err(StorageError::FlushFailed(err))
            }
        }
    }

    fn check_closed(&self) -> Result<(), StorageError> {
        if self.closed.load(Ordering::Acquire) {
            return Err(StorageError::Closed);
        }
        if let Some(ref err) = **self.bg_error.load() {
            return Err(match err {
                error::BackgroundError::FlushFailed(e) => {
                    StorageError::FlushFailed(Arc::clone(e))
                }
                error::BackgroundError::CheckpointFailed(s) => {
                    StorageError::CheckpointFailed(s.clone())
                }
            });
        }
        Ok(())
    }

    fn flush_buffer_locked(
        &self,
        mut wal_file: &std::fs::File,
        state: &mut DurableState<N, MAX_DEPTH>,
    ) -> Result<(), StorageError> {
        if !state.buffer.is_empty() {
            wal_file.write_all(&state.buffer)?;
            wal_file.sync_data()?;
            self.durability
                .mark_flushed(state.next_seq.saturating_sub(1));
            state.buffer.clear();
        }
        Ok(())
    }

    fn checkpoint_inner(&self) -> Result<(), StorageError> {
        let mut wal_file = self.wal_file.lock();

        let snap = {
            let mut state = self.state.lock();

            self.flush_buffer_locked(&wal_file, &mut state)?;

            let depth = state.inner.depth;
            let leaf_count = state.inner.size;
            let last_seq = state.next_seq.saturating_sub(1);

            if leaf_count == 0 {
                return Ok(());
            }

            let active_levels = depth.min(MAX_DEPTH - 1) + 1;
            let mut level_data = Vec::with_capacity(active_levels);

            for level_idx in 0..active_levels {
                // Count only whole chunks as done. The last chunk may be
                // partially filled and still growing
                let total_chunks = state.inner.levels[level_idx].len() / CHUNK_SIZE;
                let already = if level_idx < state.checkpointed_chunks.len() {
                    state.checkpointed_chunks[level_idx]
                } else {
                    0
                };

                let new_chunks: Vec<Chunk> =
                    state.inner.levels[level_idx].chunks_since(already);

                level_data.push(LevelCheckpointData {
                    new_chunks,
                    from_chunk: already,
                    total_chunks,
                });
            }

            let root_hash = state.inner.root.unwrap_or([0u8; 32]);

            CheckpointSnap {
                depth,
                leaf_count,
                last_seq,
                root_hash,
                level_data,
            }
        };

        std::fs::create_dir_all(&self.data_dir)?;
        #[allow(clippy::cast_possible_truncation)]
        checkpoint::write_header(&self.data_dir, N as u32, MAX_DEPTH as u32)?;

        let mut files_to_sync = Vec::new();

        for (level_idx, ld) in snap.level_data.iter().enumerate() {
            if !ld.new_chunks.is_empty() {
                std::fs::create_dir_all(checkpoint::level_dir_path(
                    &self.data_dir,
                    level_idx,
                ))?;
                let chunks_iter = ld.new_chunks.iter().map(|c| c.as_slice());
                let mut shard_files = checkpoint::append_chunks_to_level(
                    &self.data_dir,
                    level_idx,
                    ld.from_chunk,
                    chunks_iter,
                )?;
                files_to_sync.append(&mut shard_files);
            }
        }

        for file in &files_to_sync {
            file.sync_data()?;
        }

        #[allow(clippy::cast_possible_truncation)]
        checkpoint::write_meta(
            &self.data_dir,
            &checkpoint::CheckpointMeta {
                n: N as u32,
                max_depth: MAX_DEPTH as u32,
                last_wal_seq: snap.last_seq,
                leaf_count: snap.leaf_count,
                depth: snap.depth as u32,
                root_hash: snap.root_hash,
            },
        )?;

        {
            let mut state = self.state.lock();

            state.checkpointed_chunks.resize(snap.level_data.len(), 0);

            for (level_idx, ld) in snap.level_data.iter().enumerate() {
                let snapshot_total = ld.total_chunks;

                if snapshot_total > 0 && level_idx < self.tiering.pin_above_level {
                    let regions = checkpoint::mmap_level_shards(
                        &self.data_dir,
                        level_idx,
                        snapshot_total,
                    )?;
                    if !regions.is_empty() {
                        state.inner.levels[level_idx]
                            .remap_chunks(snapshot_total, &regions);
                    }
                }

                state.checkpointed_chunks[level_idx] = snapshot_total;
            }

            // truncate wal
            #[allow(clippy::cast_possible_truncation)]
            {
                let header_buf = wal::serialize_header(N as u32, MAX_DEPTH as u32);
                let wal = &mut *wal_file;
                wal.seek(SeekFrom::Start(0))?;
                wal.write_all(&header_buf)?;
                wal.set_len(header_buf.len() as u64)?;
                wal.sync_data()?;
            }

            self.entries_since_checkpoint.store(0, Ordering::Relaxed);
            self.uncheckpointed_memory_bytes.store(0, Ordering::Relaxed);

            self.flush_buffer_locked(&wal_file, &mut state)?;

            let new_snap = state.inner.snapshot();
            self.snapshot.store(Arc::new(new_snap));
        }

        {
            let (lock, cvar) = &self.checkpoint;
            let mut coord = lock.lock();
            coord.completed += 1;
            cvar.notify_all();
        }

        Ok(())
    }

    /// depends on configured checkpoint policy
    fn should_auto_checkpoint(&self) -> bool {
        match &self.checkpoint_policy {
            CheckpointPolicy::Manual | CheckpointPolicy::OnClose => false,
            CheckpointPolicy::EveryNEntries(n) => {
                self.entries_since_checkpoint.load(Ordering::Relaxed) as u64 >= *n
            }
            CheckpointPolicy::MemoryThreshold(bytes) => {
                self.uncheckpointed_memory_bytes.load(Ordering::Relaxed) >= *bytes
            }
        }
    }

    /// offload checkpoint request
    fn request_checkpoint(&self) {
        let (lock, cvar) = &self.checkpoint;
        let mut coord = lock.lock();
        coord.requested = true;
        cvar.notify_all();
    }
}

/// Handle for the background flush thread
struct FlushHandle {
    handle: std::thread::JoinHandle<()>,
    shutdown: Arc<(Mutex<bool>, parking_lot::Condvar)>,
}

/// Handle for the background checkpoint thread
struct CheckpointHandle {
    handle: std::thread::JoinHandle<()>,
}

/// Wraps the core tree with persistence via WAL and optional checkpointing.
///
/// Insertions go to an in-memory WAL buffer, but the state is available for
/// computing on immediately. When `flush()` is called (or triggered by
/// `FlushPolicy`), the buffer is written to disk. Checkpoints materialize
/// the tree state to data files, allowing WAL truncation and mmap-backed reads.
pub struct RotorTree<H: Hasher, const N: usize, const MAX_DEPTH: usize> {
    shared: Arc<Shared<H, N, MAX_DEPTH>>,
    flush_handle: Option<FlushHandle>,
    checkpoint_handle: Option<CheckpointHandle>,
}

impl<H: Hasher, const N: usize, const MAX_DEPTH: usize> RotorTree<H, N, MAX_DEPTH> {
    const _ASSERT_N: () = assert!(N >= 2, "branching factor must be at least 2");
    const _ASSERT_DEPTH: () = assert!(MAX_DEPTH >= 1, "max depth must be at least 1");

    /// Open or create a RotorTree at the given path.
    ///
    /// If data files from a previous checkpoint exist, loads state from them
    /// and replays only the WAL delta. Otherwise, replays the full WAL.
    pub fn open(hasher: H, config: RotorTreeConfig) -> Result<Self, RotorTreeError> {
        let () = Self::_ASSERT_N;
        let () = Self::_ASSERT_DEPTH;

        std::fs::create_dir_all(&config.path)?;

        let data_dir = config.path.join("data");
        let wal_path = config.path.join("wal");
        let file = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(&wal_path)?;

        use fs4::fs_std::FileExt;
        if !file
            .try_lock_exclusive()
            .map_err(|_| StorageError::FileLocked)?
        {
            return Err(StorageError::FileLocked.into());
        }

        if file.metadata()?.len() == 0
            && let Some(parent) = wal_path.parent()
        {
            let dir = std::fs::File::open(parent)?;
            dir.sync_all()?;
        }

        let mut file = file;

        // recover from checkpoint first
        let has_data_dir = data_dir.exists();
        let RecoveryResult { inner, next_seq } = if has_data_dir {
            recovery::recover_with_checkpoint::<H, _, N, MAX_DEPTH>(
                &mut file,
                &hasher,
                &data_dir,
                config.verify_checkpoint,
            )?
        } else {
            recovery::recover::<H, _, N, MAX_DEPTH>(&mut file, &hasher)?
        };

        // Compute initial level file state from checkpoint metadata
        let checkpointed_chunks = compute_initial_level_files::<N, MAX_DEPTH>(&data_dir)?;

        let snap = inner.snapshot();
        let durability = DurabilityTracker::new();

        if next_seq > 0 {
            durability.mark_flushed(next_seq.checked_sub(1).expect("next_seq > 0; qed"));
        }

        let state = DurableState {
            inner,
            buffer: Vec::new(),
            next_seq,
            checkpointed_chunks,
        };

        let shared = Arc::new(Shared {
            hasher,
            state: Mutex::new(state),
            wal_file: Mutex::new(file),
            snapshot: ArcSwap::from_pointee(snap),
            durability,
            closed: AtomicBool::new(false),
            bg_error: ArcSwap::from_pointee(None),
            data_dir,
            checkpoint_policy: config.checkpoint_policy,
            tiering: config.tiering,
            entries_since_checkpoint: AtomicUsize::new(0),
            uncheckpointed_memory_bytes: AtomicUsize::new(0),
            checkpoint: (
                Mutex::new(CheckpointCoord {
                    requested: false,
                    completed: 0,
                }),
                parking_lot::Condvar::new(),
            ),
        });

        let flush_handle = start_flush_thread(&shared, &config.flush_policy)?;
        let checkpoint_handle = start_checkpoint_thread(&shared)?;

        Ok(Self {
            shared,
            flush_handle,
            checkpoint_handle,
        })
    }

    /// Insert a single leaf
    pub fn insert(&self, leaf: Hash) -> Result<(Hash, DurabilityToken), RotorTreeError> {
        self.shared.check_closed()?;

        let (root, token) = {
            let mut state = self.shared.state.lock();
            let root = LeanIMT::<H, N, MAX_DEPTH>::_insert(
                &mut state.inner,
                &self.shared.hasher,
                leaf,
            )?;
            let seq = state.next_seq;
            wal::serialize_entry(&mut state.buffer, seq, wal::WalPayload::Single(leaf));
            state.next_seq = state.next_seq.checked_add(1).expect("seq overflow; qed");
            self.shared
                .entries_since_checkpoint
                .fetch_add(1, Ordering::Relaxed);
            self.shared
                .uncheckpointed_memory_bytes
                .fetch_add(32, Ordering::Relaxed);
            let snap = state.inner.snapshot();
            self.shared.snapshot.store(Arc::new(snap));
            let token = self.shared.durability.token(seq);
            (root, token)
        };

        self.maybe_auto_checkpoint();
        Ok((root, token))
    }

    /// Insert multiple leaves in a batch
    pub fn insert_many(
        &self,
        leaves: &[Hash],
    ) -> Result<(Hash, DurabilityToken), RotorTreeError> {
        self.shared.check_closed()?;

        let (root, token) = {
            let mut state = self.shared.state.lock();
            let root = LeanIMT::<H, N, MAX_DEPTH>::_insert_many(
                &mut state.inner,
                &self.shared.hasher,
                leaves,
            )?;
            let seq = state.next_seq;
            wal::serialize_entry(
                &mut state.buffer,
                seq,
                wal::WalPayload::Batch(wal::NewCow::Borrowed(leaves)),
            );
            state.next_seq = state.next_seq.checked_add(1).expect("seq overflow; qed");
            self.shared
                .entries_since_checkpoint
                .fetch_add(1, Ordering::Relaxed);
            self.shared
                .uncheckpointed_memory_bytes
                .fetch_add(leaves.len() * 32, Ordering::Relaxed);
            let snap = state.inner.snapshot();
            self.shared.snapshot.store(Arc::new(snap));
            let token = self.shared.durability.token(seq);
            (root, token)
        };

        self.maybe_auto_checkpoint();
        Ok((root, token))
    }

    /// Insert a single leaf and block until it is durable (fsynced)
    pub fn insert_durable(&self, leaf: Hash) -> Result<Hash, RotorTreeError> {
        let (root, token) = self.insert(leaf)?;
        self.flush().map_err(RotorTreeError::Storage)?;
        token.wait();
        Ok(root)
    }

    /// The current Merkle root, or `None` if the tree is empty
    pub fn root(&self) -> Option<Hash> {
        self.shared.snapshot.load().root
    }

    /// Number of leaves in the tree
    pub fn size(&self) -> u64 {
        self.shared.snapshot.load().size
    }

    /// Current depth (hash layers above the leaf level)
    pub fn depth(&self) -> usize {
        self.shared.snapshot.load().depth
    }

    /// Get a lock-free snapshot for proof generation
    pub fn snapshot(&self) -> Arc<TreeSnapshot<N, MAX_DEPTH>> {
        self.shared.snapshot.load_full()
    }

    /// Flush all buffered WAL entries to disk
    pub fn flush(&self) -> Result<(), StorageError> {
        self.shared.check_closed()?;
        self.shared.flush_inner()
    }

    /// Write a checkpoint
    pub fn checkpoint(&self) -> Result<(), StorageError> {
        self.shared.check_closed()?;
        self.shared.checkpoint_inner()
    }

    /// Block until a background checkpoint completes (or timeout)
    pub fn wait_for_checkpoint(&self, timeout: Duration) -> bool {
        let (lock, cvar) = &self.shared.checkpoint;
        let mut coord = lock.lock();
        let initial = coord.completed;
        let deadline = std::time::Instant::now() + timeout;
        loop {
            if coord.completed > initial {
                return true;
            }
            let remaining = deadline.saturating_duration_since(std::time::Instant::now());
            if remaining.is_zero() {
                return false;
            }
            cvar.wait_for(&mut coord, remaining);
        }
    }

    /// Close the tree
    pub fn close(mut self) -> Result<(), StorageError> {
        self.close_inner()
    }

    fn close_inner(&mut self) -> Result<(), StorageError> {
        if self.shared.closed.swap(true, Ordering::AcqRel) {
            return Ok(());
        }

        if self.checkpoint_handle.is_some() {
            self.shared.request_checkpoint(); // wake it so it sees `closed`
            if let Some(handle) = self.checkpoint_handle.take() {
                let _ = handle.handle.join();
            }
        }

        if let Some(handle) = self.flush_handle.take() {
            {
                let (lock, cvar) = &*handle.shutdown;
                let mut shutdown = lock.lock();
                *shutdown = true;
                cvar.notify_one();
            }
            let _ = handle.handle.join();
        }

        self.shared.flush_inner()?;

        // checkpoint on close if configured
        if matches!(self.shared.checkpoint_policy, CheckpointPolicy::OnClose) {
            self.shared.checkpoint_inner()?;
        }

        {
            let file = self.shared.wal_file.lock();
            let _ = fs4::fs_std::FileExt::unlock(&*file);
        }

        Ok(())
    }

    fn maybe_auto_checkpoint(&self) {
        if self.shared.should_auto_checkpoint() {
            self.shared.request_checkpoint();
        }
    }
}

fn compute_initial_level_files<const N: usize, const MAX_DEPTH: usize>(
    data_dir: &std::path::Path,
) -> Result<Vec<usize>, StorageError> {
    let meta = match checkpoint::read_meta(data_dir) {
        Ok(Some(m)) => m,
        Ok(None) => return Ok(Vec::new()),
        Err(e) => return Err(e),
    };

    let leaf_count =
        usize::try_from(meta.leaf_count).map_err(|_| StorageError::MathError)?;
    let depth = meta.depth as usize;

    if leaf_count == 0 {
        return Ok(Vec::new());
    }

    let active_levels = depth.min(MAX_DEPTH - 1) + 1;
    let mut result = Vec::with_capacity(active_levels);
    let mut level_len = leaf_count;

    for _ in 0..active_levels {
        let chunks = level_len / CHUNK_SIZE;
        result.push(chunks);
        level_len = level_len.div_ceil(N);
    }

    Ok(result)
}

fn start_flush_thread<H: Hasher, const N: usize, const MAX_DEPTH: usize>(
    shared: &Arc<Shared<H, N, MAX_DEPTH>>,
    policy: &FlushPolicy,
) -> Result<Option<FlushHandle>, RotorTreeError> {
    match policy {
        FlushPolicy::Manual => Ok(None),
        FlushPolicy::Interval(duration) => {
            let duration = *duration;
            let shared = Arc::clone(shared);
            spawn_flush_thread(move |shutdown| {
                let (lock, cvar) = &*shutdown;
                loop {
                    let mut stop = lock.lock();
                    cvar.wait_for(&mut stop, duration);
                    if *stop {
                        break;
                    }
                    drop(stop);
                    let _ = shared.flush_inner();
                }
            })
        }
    }
}

fn start_checkpoint_thread<H: Hasher, const N: usize, const MAX_DEPTH: usize>(
    shared: &Arc<Shared<H, N, MAX_DEPTH>>,
) -> Result<Option<CheckpointHandle>, RotorTreeError> {
    if matches!(
        shared.checkpoint_policy,
        CheckpointPolicy::Manual | CheckpointPolicy::OnClose
    ) {
        return Ok(None);
    }

    let shared = Arc::clone(shared);
    let handle = std::thread::Builder::new()
        .name("rotortree-checkpoint".to_string())
        .spawn(move || {
            let (lock, cvar) = &shared.checkpoint;
            loop {
                {
                    let mut coord = lock.lock();
                    while !coord.requested && !shared.closed.load(Ordering::Acquire) {
                        cvar.wait(&mut coord);
                    }
                    if shared.closed.load(Ordering::Acquire) {
                        break;
                    }
                    coord.requested = false;
                }

                if let Err(e) = shared.checkpoint_inner() {
                    shared.bg_error.store(Arc::new(Some(
                        error::BackgroundError::CheckpointFailed(e.to_string()),
                    )));
                    break;
                }
            }
        })
        .map_err(|e| RotorTreeError::Storage(StorageError::Io(e)))?;

    Ok(Some(CheckpointHandle { handle }))
}

fn spawn_flush_thread<F>(body: F) -> Result<Option<FlushHandle>, RotorTreeError>
where
    F: FnOnce(Arc<(Mutex<bool>, parking_lot::Condvar)>) + Send + 'static,
{
    let shutdown = Arc::new((Mutex::new(false), parking_lot::Condvar::new()));
    let shutdown_clone = Arc::clone(&shutdown);

    let handle = std::thread::Builder::new()
        .name("rotortree-flush".to_string())
        .spawn(move || {
            body(shutdown_clone);
        })
        .map_err(|e| RotorTreeError::Storage(StorageError::Io(e)))?;

    Ok(Some(FlushHandle { handle, shutdown }))
}

impl<H: Hasher, const N: usize, const MAX_DEPTH: usize> Drop
    for RotorTree<H, N, MAX_DEPTH>
{
    fn drop(&mut self) {
        if self.shared.closed.load(Ordering::Acquire) {
            return;
        }
        if std::thread::panicking() {
            self.shared.closed.store(true, Ordering::Release);
            self.shared.request_checkpoint();
            if let Some(handle) = self.checkpoint_handle.take() {
                let _ = handle.handle.join();
            }
            if let Some(handle) = self.flush_handle.take() {
                let (lock, cvar) = &*handle.shutdown;
                let mut shutdown = lock.lock();
                *shutdown = true;
                cvar.notify_one();
                drop(shutdown);
                let _ = handle.handle.join();
            }
            if let Some(file) = self.shared.wal_file.try_lock() {
                let _ = fs4::fs_std::FileExt::unlock(&*file);
            }
            return;
        }
        if let Err(e) = self.close_inner() {
            eprintln!("rotortree: error during drop: {e}");
        }
    }
}
