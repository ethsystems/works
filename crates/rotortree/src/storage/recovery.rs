use std::{
    io::{
        Read,
        Seek,
        SeekFrom,
        Write,
    },
    sync::Arc,
};

use crate::chunked_level::{
    CHUNK_SIZE,
    Chunk,
};

use super::checkpoint;

use crate::{
    Hash,
    Hasher,
    tree::TreeInner,
};

use super::{
    error::StorageError,
    wal::{
        WalPayload,
        deserialize_entry,
        deserialize_header,
        serialize_header,
    },
};

/// Result of WAL recovery
pub(crate) struct RecoveryResult<const N: usize, const MAX_DEPTH: usize> {
    pub inner: TreeInner<N, MAX_DEPTH>,
    pub next_seq: u64,
}

/// Abstraction over file-like objects for recovery
pub(crate) trait WalFile: Read + Write + Seek {
    fn file_len(&self) -> Result<u64, std::io::Error>;
    fn truncate_at(&self, len: u64) -> Result<(), std::io::Error>;
    fn sync(&self) -> Result<(), std::io::Error>;
}

impl WalFile for std::fs::File {
    fn file_len(&self) -> Result<u64, std::io::Error> {
        Ok(self.metadata()?.len())
    }

    fn truncate_at(&self, len: u64) -> Result<(), std::io::Error> {
        self.set_len(len)
    }

    fn sync(&self) -> Result<(), std::io::Error> {
        self.sync_data()
    }
}

/// Recover tree state from a WAL file.
///
/// If the file is empty, writes a fresh header. If it contains
/// entries, replays them into a new `TreeInner`. Truncates any
/// incomplete tail entries.
pub(crate) fn recover<H, F, const N: usize, const MAX_DEPTH: usize>(
    file: &mut F,
    hasher: &H,
) -> Result<RecoveryResult<N, MAX_DEPTH>, StorageError>
where
    H: Hasher,
    F: WalFile,
{
    let file_len = file.file_len()?;

    if file_len == 0 {
        #[allow(clippy::cast_possible_truncation)]
        let buf = serialize_header(N as u32, MAX_DEPTH as u32);
        file.write_all(&buf)?;
        file.sync()?;
        return Ok(RecoveryResult {
            inner: TreeInner::new(),
            next_seq: 0,
        });
    }

    let file_len_usize =
        usize::try_from(file_len).map_err(|_| StorageError::MathError)?;
    let mut all_data = vec![0u8; file_len_usize];
    file.seek(SeekFrom::Start(0))?;
    file.read_exact(&mut all_data)?;

    let (n, max_depth, header_size) = deserialize_header(&all_data)?;

    #[allow(clippy::cast_possible_truncation)]
    if n != N as u32 || max_depth != MAX_DEPTH as u32 {
        return Err(StorageError::ConfigMismatch {
            expected_n: N as u32,
            actual_n: n,
            expected_max_depth: MAX_DEPTH as u32,
            actual_max_depth: max_depth,
        });
    }

    let entry_data = &all_data[header_size..];
    let mut inner = TreeInner::<N, MAX_DEPTH>::new();
    let (last_seq, valid_offset) =
        replay_wal_entries::<H, N, MAX_DEPTH>(entry_data, hasher, &mut inner, None)?;

    let valid_end = (header_size as u64)
        .checked_add(valid_offset as u64)
        .ok_or(StorageError::MathError)?;
    if valid_end < file_len {
        file.truncate_at(valid_end)?;
        file.sync()?;
    }
    file.seek(SeekFrom::Start(valid_end))?;

    let next_seq = match last_seq {
        Some(s) => s.checked_add(1).ok_or(StorageError::MathError)?,
        None => 0,
    };
    Ok(RecoveryResult { inner, next_seq })
}

/// Recover from checkpoint data files, falling back to full wal replay
pub(crate) fn recover_with_checkpoint<H, F, const N: usize, const MAX_DEPTH: usize>(
    wal_file: &mut F,
    hasher: &H,
    data_dir: &std::path::Path,
    verify: bool,
) -> Result<RecoveryResult<N, MAX_DEPTH>, StorageError>
where
    H: Hasher,
    F: WalFile,
{
    let meta = match checkpoint::read_meta(data_dir)? {
        Some(m) => m,
        None => return recover(wal_file, hasher),
    };

    #[allow(clippy::cast_possible_truncation)]
    if meta.n != N as u32 || meta.max_depth != MAX_DEPTH as u32 {
        return recover(wal_file, hasher);
    }

    #[allow(clippy::cast_possible_truncation)]
    match checkpoint::read_header(data_dir)? {
        Some(h)
            if h.n == N as u32
                && h.max_depth == MAX_DEPTH as u32
                && h.chunk_size == CHUNK_SIZE as u32 =>
        {
            // valid
        }
        _ => return recover(wal_file, hasher),
    }

    let leaf_count =
        usize::try_from(meta.leaf_count).map_err(|_| StorageError::MathError)?;
    let depth = meta.depth as usize;

    let mut level_lens = [0usize; MAX_DEPTH];
    if leaf_count > 0 {
        level_lens[0] = leaf_count;
        for k in 1..=depth.min(MAX_DEPTH - 1) {
            level_lens[k] = level_lens[k - 1].div_ceil(N);
        }
    }

    let mut inner = TreeInner::<N, MAX_DEPTH>::new();

    let active = depth.min(MAX_DEPTH - 1) + 1;
    for (level_idx, &len) in level_lens.iter().enumerate().take(active) {
        if len == 0 {
            continue;
        }

        // Every chunk on disk, including a zero-padded partial last one.
        let num_chunks = len.div_ceil(CHUNK_SIZE);

        let regions = if num_chunks > 0 {
            checkpoint::mmap_level_shards(data_dir, level_idx, num_chunks)?
        } else {
            Vec::new()
        };

        let chunks: Vec<Chunk> = if regions.is_empty() {
            Vec::new()
        } else {
            (0..num_chunks)
                .map(|chunk_idx| {
                    let (shard_idx, offset_in_shard) =
                        checkpoint::shard_address(chunk_idx);
                    Chunk::new_mapped(Arc::clone(&regions[shard_idx]), offset_in_shard)
                })
                .collect()
        };

        inner.set_level_from_parts(level_idx, chunks, len);
    }

    inner.root = if leaf_count > 0 {
        Some(meta.root_hash)
    } else {
        None
    };
    inner.size = meta.leaf_count;
    inner.depth = depth;

    if verify && leaf_count > 0 {
        let computed = inner.recompute_root(hasher);
        if computed != inner.root {
            return Err(StorageError::DataCorruption {
                detail: format!(
                    "root mismatch: stored {:?}, recomputed {:?}",
                    inner.root, computed
                ),
            });
        }
    }

    let file_len = wal_file.file_len()?;

    let next_seq = if file_len == 0 {
        #[allow(clippy::cast_possible_truncation)]
        let buf = serialize_header(N as u32, MAX_DEPTH as u32);
        wal_file.write_all(&buf)?;
        wal_file.sync()?;
        meta.last_wal_seq
            .checked_add(1)
            .ok_or(StorageError::MathError)?
    } else {
        let file_len_usize =
            usize::try_from(file_len).map_err(|_| StorageError::MathError)?;
        let mut all_data = vec![0u8; file_len_usize];
        wal_file.seek(SeekFrom::Start(0))?;
        wal_file.read_exact(&mut all_data)?;

        let (n, max_depth, header_size) = deserialize_header(&all_data)?;
        #[allow(clippy::cast_possible_truncation)]
        if n != N as u32 || max_depth != MAX_DEPTH as u32 {
            return Err(StorageError::ConfigMismatch {
                expected_n: N as u32,
                actual_n: n,
                expected_max_depth: MAX_DEPTH as u32,
                actual_max_depth: max_depth,
            });
        }

        let entry_data = &all_data[header_size..];
        let (last_seq, valid_offset) = replay_wal_entries::<H, N, MAX_DEPTH>(
            entry_data,
            hasher,
            &mut inner,
            Some(meta.last_wal_seq),
        )?;

        let valid_end = (header_size as u64)
            .checked_add(valid_offset as u64)
            .ok_or(StorageError::MathError)?;
        if valid_end < file_len {
            wal_file.truncate_at(valid_end)?;
            wal_file.sync()?;
        }
        wal_file.seek(SeekFrom::Start(valid_end))?;

        match last_seq {
            Some(s) => s.checked_add(1).ok_or(StorageError::MathError)?,
            None => meta
                .last_wal_seq
                .checked_add(1)
                .ok_or(StorageError::MathError)?,
        }
    };

    Ok(RecoveryResult { inner, next_seq })
}

/// replay wal
fn replay_wal_entries<H: Hasher, const N: usize, const MAX_DEPTH: usize>(
    entry_data: &[u8],
    hasher: &H,
    inner: &mut TreeInner<N, MAX_DEPTH>,
    skip_until_seq: Option<u64>,
) -> Result<(Option<u64>, usize), StorageError> {
    let mut offset: usize = 0;
    let mut last_seq: Option<u64> = None;
    let mut pending_singles: Vec<Hash> = Vec::new();

    loop {
        match deserialize_entry(entry_data, offset, last_seq) {
            Ok(Some((entry, consumed))) => {
                let should_replay = match skip_until_seq {
                    Some(skip) => entry.seq > skip,
                    None => true,
                };
                if should_replay {
                    match entry.payload {
                        WalPayload::Single(leaf) => {
                            pending_singles.push(leaf);
                        }
                        WalPayload::Batch(cow) => {
                            flush_pending::<H, N, MAX_DEPTH>(
                                inner,
                                hasher,
                                &mut pending_singles,
                            )?;
                            crate::LeanIMT::<H, N, MAX_DEPTH>::_insert_many(
                                inner,
                                hasher,
                                cow.as_slice(),
                            )
                            .map_err(StorageError::Tree)?;
                        }
                    }
                }
                last_seq = Some(entry.seq);
                offset = offset
                    .checked_add(consumed)
                    .ok_or(StorageError::MathError)?;
            }
            Ok(None) => break,
            Err(e) => return Err(e),
        }
    }

    flush_pending::<H, N, MAX_DEPTH>(inner, hasher, &mut pending_singles)?;
    Ok((last_seq, offset))
}

/// Flush accumulated single-insert leaves as a batch
fn flush_pending<H: Hasher, const N: usize, const MAX_DEPTH: usize>(
    inner: &mut TreeInner<N, MAX_DEPTH>,
    hasher: &H,
    pending: &mut Vec<Hash>,
) -> Result<(), StorageError> {
    if pending.is_empty() {
        return Ok(());
    }
    crate::LeanIMT::<H, N, MAX_DEPTH>::_insert_many(inner, hasher, pending)
        .map_err(StorageError::Tree)?;
    pending.clear();
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{
        super::wal,
        *,
    };
    use crate::Hash;
    use std::{
        cell::RefCell,
        io::Cursor,
    };

    /// In-memory file for testing recovery without disk I/O
    struct MemFile {
        inner: RefCell<Cursor<Vec<u8>>>,
    }

    impl MemFile {
        fn new() -> Self {
            Self {
                inner: RefCell::new(Cursor::new(Vec::new())),
            }
        }

        fn from_bytes(bytes: Vec<u8>) -> Self {
            Self {
                inner: RefCell::new(Cursor::new(bytes)),
            }
        }

        fn data(&self) -> Vec<u8> {
            self.inner.borrow().get_ref().clone()
        }
    }

    impl Read for MemFile {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            self.inner.borrow_mut().read(buf)
        }
    }

    impl Write for MemFile {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            self.inner.borrow_mut().write(buf)
        }
        fn flush(&mut self) -> std::io::Result<()> {
            self.inner.borrow_mut().flush()
        }
    }

    impl Seek for MemFile {
        fn seek(&mut self, pos: SeekFrom) -> std::io::Result<u64> {
            self.inner.borrow_mut().seek(pos)
        }
    }

    impl WalFile for MemFile {
        fn file_len(&self) -> Result<u64, std::io::Error> {
            Ok(self.inner.borrow().get_ref().len() as u64)
        }

        fn truncate_at(&self, len: u64) -> Result<(), std::io::Error> {
            self.inner.borrow_mut().get_mut().truncate(len as usize);
            Ok(())
        }

        fn sync(&self) -> Result<(), std::io::Error> {
            Ok(())
        }
    }

    use crate::test_util::*;

    #[test]
    fn recover_empty_wal() {
        let mut file = MemFile::new();
        let result = recover::<XorHasher, _, 2, 32>(&mut file, &XorHasher).unwrap();
        assert_eq!(result.inner.size, 0);
        assert_eq!(result.inner.root, None);
        assert_eq!(result.next_seq, 0);

        let header_size = wal::serialize_header(2, 32).len();
        assert_eq!(file.data().len(), header_size);
    }

    #[test]
    fn recover_single_entries() {
        let mut buf = wal::serialize_header(2, 32);
        for i in 0..5u64 {
            wal::serialize_entry(&mut buf, i, wal::WalPayload::Single(leaf(i as u32)));
        }

        let mut file = MemFile::from_bytes(buf);
        let result = recover::<XorHasher, _, 2, 32>(&mut file, &XorHasher).unwrap();
        assert_eq!(result.inner.size, 5);
        assert_eq!(result.next_seq, 5);
        assert!(result.inner.root.is_some());
    }

    #[test]
    fn recover_batch_entry() {
        let leaves: Vec<Hash> = (0..10u32).map(leaf).collect();
        let mut buf = wal::serialize_header(2, 32);
        wal::serialize_entry(
            &mut buf,
            0,
            wal::WalPayload::Batch(wal::NewCow::Borrowed(&leaves)),
        );

        let mut file = MemFile::from_bytes(buf);
        let result = recover::<XorHasher, _, 2, 32>(&mut file, &XorHasher).unwrap();
        assert_eq!(result.inner.size, 10);
        assert_eq!(result.next_seq, 1);
    }

    #[test]
    fn recover_truncated_tail() {
        let mut buf = wal::serialize_header(2, 32);
        wal::serialize_entry(&mut buf, 0, wal::WalPayload::Single(leaf(1)));
        wal::serialize_entry(&mut buf, 1, wal::WalPayload::Single(leaf(2)));
        buf.truncate(buf.len() - 10);

        let mut file = MemFile::from_bytes(buf);
        let result = recover::<XorHasher, _, 2, 32>(&mut file, &XorHasher).unwrap();
        assert_eq!(result.inner.size, 1);
        assert_eq!(result.next_seq, 1);
    }

    #[test]
    fn recover_config_mismatch() {
        let buf = wal::serialize_header(4, 32);

        let mut file = MemFile::from_bytes(buf);
        let result = recover::<XorHasher, _, 2, 32>(&mut file, &XorHasher);
        assert!(matches!(result, Err(StorageError::ConfigMismatch { .. })));
    }

    #[test]
    fn recover_matches_sequential_inserts() {
        let mut buf = wal::serialize_header(2, 32);
        for i in 0..20u64 {
            wal::serialize_entry(&mut buf, i, wal::WalPayload::Single(leaf(i as u32)));
        }

        let mut file = MemFile::from_bytes(buf);
        let recovered = recover::<XorHasher, _, 2, 32>(&mut file, &XorHasher).unwrap();

        let mut inner = TreeInner::<2, 32>::new();
        for i in 0..20u32 {
            crate::LeanIMT::<XorHasher, 2, 32>::_insert(&mut inner, &XorHasher, leaf(i))
                .unwrap();
        }

        assert_eq!(recovered.inner.root, inner.root);
        assert_eq!(recovered.inner.size, inner.size);
        assert_eq!(recovered.inner.depth, inner.depth);
    }

    #[test]
    fn recover_header_only_wal() {
        let buf = wal::serialize_header(2, 32);

        let mut file = MemFile::from_bytes(buf);
        let result = recover::<XorHasher, _, 2, 32>(&mut file, &XorHasher).unwrap();
        assert_eq!(result.inner.size, 0);
        assert_eq!(result.inner.root, None);
        assert_eq!(result.next_seq, 0);
    }

    #[test]
    fn recover_mixed_single_and_batch() {
        let mut buf = wal::serialize_header(2, 32);

        for i in 0..3u64 {
            wal::serialize_entry(&mut buf, i, wal::WalPayload::Single(leaf(i as u32)));
        }
        let batch: Vec<Hash> = (3..8u32).map(leaf).collect();
        wal::serialize_entry(
            &mut buf,
            3,
            wal::WalPayload::Batch(wal::NewCow::Borrowed(&batch)),
        );
        for i in 4..6u64 {
            wal::serialize_entry(
                &mut buf,
                i,
                wal::WalPayload::Single(leaf((i + 4) as u32)),
            );
        }

        let mut file = MemFile::from_bytes(buf);
        let recovered = recover::<XorHasher, _, 2, 32>(&mut file, &XorHasher).unwrap();
        assert_eq!(recovered.inner.size, 10);
        assert_eq!(recovered.next_seq, 6);

        // Verify against reference
        let mut inner = TreeInner::<2, 32>::new();
        let all_leaves: Vec<Hash> = (0..10u32).map(leaf).collect();
        crate::LeanIMT::<XorHasher, 2, 32>::_insert_many(
            &mut inner,
            &XorHasher,
            &all_leaves,
        )
        .unwrap();
        assert_eq!(recovered.inner.root, inner.root);
    }
}
