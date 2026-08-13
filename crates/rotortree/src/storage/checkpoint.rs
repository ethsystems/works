use std::{
    fs,
    io::{
        self,
        Seek,
        Write,
    },
    path::{
        Path,
        PathBuf,
    },
    sync::Arc,
};

use crate::{
    Hash,
    chunked_level::CHUNK_SIZE,
};

use super::{
    data::MmapRegion,
    error::StorageError,
    frame,
};

const HEADER_MAGIC: [u8; 4] = *b"RTRD";
const META_MAGIC: [u8; 4] = *b"RTMD";

pub(crate) const CHUNK_BYTE_SIZE: usize = CHUNK_SIZE * 32;
pub(crate) const CHUNKS_PER_SHARD: usize = 65_536;

/// Returns `(shard_index, byte_offset_within_shard)` for a given chunk index.
#[inline]
pub(crate) fn shard_address(chunk_idx: usize) -> (usize, usize) {
    let shard_idx = chunk_idx / CHUNKS_PER_SHARD;
    let offset_in_shard = (chunk_idx % CHUNKS_PER_SHARD) * CHUNK_BYTE_SIZE;
    (shard_idx, offset_in_shard)
}

/// Controls when checkpoints are triggered
#[derive(Default)]
pub enum CheckpointPolicy {
    /// Caller calls `checkpoint()` explicitly
    #[default]
    Manual,
    /// Auto-checkpoint after every N WAL entries
    EveryNEntries(u64),
    /// Auto-checkpoint when in-memory chunks exceed N bytes
    MemoryThreshold(usize),
    /// Checkpoint only on graceful close
    OnClose,
}

/// Controls which tree levels are kept in memory vs mmap'd
pub struct TieringConfig {
    /// Levels below this value have their committed chunks mmap'd after checkpoint.
    /// Set to `usize::MAX` to mmap all levels (default), `0` to keep everything in memory
    pub pin_above_level: usize,
}

impl Default for TieringConfig {
    fn default() -> Self {
        Self {
            pin_above_level: usize::MAX,
        }
    }
}

/// Versioned header written once at data directory creation
#[derive(Debug, wincode::SchemaWrite, wincode::SchemaRead)]
enum HeaderFrame {
    V1 {
        magic: [u8; 4],
        n: u32,
        max_depth: u32,
        chunk_size: u32,
    },
}

/// Versioned checkpoint metadata (atomically written at each checkpoint)
#[derive(Debug, wincode::SchemaWrite, wincode::SchemaRead)]
enum MetaFrame {
    V1 {
        magic: [u8; 4],
        n: u32,
        max_depth: u32,
        last_wal_seq: u64,
        leaf_count: u64,
        depth: u32,
        root_hash: Hash,
    },
}

/// Deserialized header.bin contents
#[derive(Debug, Clone, Copy)]
pub(crate) struct HeaderData {
    pub(crate) n: u32,
    pub(crate) max_depth: u32,
    pub(crate) chunk_size: u32,
}

/// Deserialized checkpoint.meta contents
#[doc(hidden)]
#[derive(Debug, Clone, Copy)]
pub struct CheckpointMeta {
    pub n: u32,
    pub max_depth: u32,
    pub last_wal_seq: u64,
    pub leaf_count: u64,
    pub depth: u32,
    pub root_hash: Hash,
}

/// Write `header.bin`
pub(crate) fn write_header(data_dir: &Path, n: u32, max_depth: u32) -> io::Result<()> {
    #[allow(clippy::cast_possible_truncation)]
    let header = HeaderFrame::V1 {
        magic: HEADER_MAGIC,
        n,
        max_depth,
        chunk_size: CHUNK_SIZE as u32,
    };
    let buf = frame::serialize_frame(&header);
    atomic_write(&data_dir.join("header.bin"), &buf)
}

/// Read and validate `header.bin`. Returns `None` if missing or corrupt
pub(crate) fn read_header(data_dir: &Path) -> Result<Option<HeaderData>, StorageError> {
    let path = data_dir.join("header.bin");
    let header: HeaderFrame = match frame::read_frame_file(&path)? {
        Some(h) => h,
        None => return Ok(None),
    };

    let HeaderFrame::V1 {
        magic,
        n,
        max_depth,
        chunk_size,
    } = header;

    if magic != HEADER_MAGIC {
        return Ok(None);
    }

    Ok(Some(HeaderData {
        n,
        max_depth,
        chunk_size,
    }))
}

/// Write checkpoint metadata atomically
pub(crate) fn write_meta(data_dir: &Path, meta: &CheckpointMeta) -> io::Result<()> {
    let frame = MetaFrame::V1 {
        magic: META_MAGIC,
        n: meta.n,
        max_depth: meta.max_depth,
        last_wal_seq: meta.last_wal_seq,
        leaf_count: meta.leaf_count,
        depth: meta.depth,
        root_hash: meta.root_hash,
    };
    let buf = frame::serialize_frame(&frame);
    atomic_write(&data_dir.join("checkpoint.meta"), &buf)
}

/// Read and validate checkpoint metadata. Returns `None` if missing or corrupt
pub(crate) fn read_meta(data_dir: &Path) -> Result<Option<CheckpointMeta>, StorageError> {
    let path = data_dir.join("checkpoint.meta");
    let meta_frame: MetaFrame = match frame::read_frame_file(&path)? {
        Some(m) => m,
        None => return Ok(None),
    };

    let MetaFrame::V1 {
        magic,
        n,
        max_depth,
        last_wal_seq,
        leaf_count,
        depth,
        root_hash,
    } = meta_frame;

    if magic != META_MAGIC {
        return Ok(None);
    }

    Ok(Some(CheckpointMeta {
        n,
        max_depth,
        last_wal_seq,
        leaf_count,
        depth,
        root_hash,
    }))
}

pub(crate) fn level_dir_path(data_dir: &Path, level_idx: usize) -> PathBuf {
    data_dir.join(format!("level_{level_idx}"))
}

pub(crate) fn shard_file_path(
    data_dir: &Path,
    level_idx: usize,
    shard_idx: usize,
) -> PathBuf {
    data_dir.join(format!("level_{level_idx}/shard_{shard_idx:04}.dat"))
}

pub(crate) fn append_chunks_to_level<'a>(
    data_dir: &Path,
    level_idx: usize,
    from_chunk: usize,
    chunks: impl Iterator<Item = &'a [Hash; CHUNK_SIZE]>,
) -> io::Result<Vec<fs::File>> {
    let chunks: Vec<_> = chunks.collect();
    if chunks.is_empty() {
        return Ok(Vec::new());
    }

    let first_shard = from_chunk / CHUNKS_PER_SHARD;
    let last_shard = (from_chunk + chunks.len() - 1) / CHUNKS_PER_SHARD;

    (first_shard..=last_shard)
        .map(|shard_idx| {
            let shard_start = shard_idx * CHUNKS_PER_SHARD;
            let local_start = shard_start.saturating_sub(from_chunk);
            let local_end = ((shard_idx + 1) * CHUNKS_PER_SHARD)
                .saturating_sub(from_chunk)
                .min(chunks.len());
            let (_, offset) = shard_address(from_chunk + local_start);

            let path = shard_file_path(data_dir, level_idx, shard_idx);
            let mut file = fs::OpenOptions::new()
                .create(true)
                .write(true)
                .read(true)
                .truncate(false)
                .open(&path)?;
            file.seek(io::SeekFrom::Start(offset as u64))?;

            for chunk in &chunks[local_start..local_end] {
                file.write_all(chunk.as_flattened())?;
            }

            Ok(file)
        })
        .collect()
}

pub(crate) fn mmap_level_shards(
    data_dir: &Path,
    level_idx: usize,
    valid_chunks: usize,
) -> io::Result<Vec<Arc<MmapRegion>>> {
    if valid_chunks == 0 {
        return Ok(Vec::new());
    }

    let shard_count = valid_chunks.div_ceil(CHUNKS_PER_SHARD);
    let mut regions = Vec::with_capacity(shard_count);

    for shard_idx in 0..shard_count {
        let path = shard_file_path(data_dir, level_idx, shard_idx);
        let file = match fs::File::open(&path) {
            Ok(f) => f,
            Err(e) if e.kind() == io::ErrorKind::NotFound && shard_idx == 0 => {
                return Ok(Vec::new());
            }
            Err(e) if e.kind() == io::ErrorKind::NotFound => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "level_{level_idx}/shard_{shard_idx:04}.dat missing \
                         (shards 0..{shard_idx} exist)"
                    ),
                ));
            }
            Err(e) => return Err(e),
        };

        let chunks_in_shard =
            CHUNKS_PER_SHARD.min(valid_chunks - shard_idx * CHUNKS_PER_SHARD);
        let valid_len = chunks_in_shard * CHUNK_BYTE_SIZE;
        let file_len = usize::try_from(file.metadata()?.len()).unwrap_or(usize::MAX);

        if file_len < valid_len {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "level_{level_idx}/shard_{shard_idx:04}.dat too small: \
                     {file_len} bytes < {valid_len} expected"
                ),
            ));
        }

        let mmap = unsafe { memmap2::MmapOptions::new().len(file_len).map_copy(&file)? };
        regions.push(Arc::new(MmapRegion::new(mmap, valid_len)));
    }

    Ok(regions)
}

pub(crate) fn atomic_write(path: &Path, data: &[u8]) -> io::Result<()> {
    let mut s = path.as_os_str().to_owned();
    s.push(".tmp");
    let tmp = PathBuf::from(s);
    {
        let mut file = fs::File::create(&tmp)?;
        file.write_all(data)?;
        file.sync_all()?;
    }
    fs::rename(&tmp, path)?;
    if let Some(parent) = path.parent() {
        let dir = fs::File::open(parent)?;
        dir.sync_all()?;
    }
    Ok(())
}

#[doc(hidden)]
pub fn write_test_meta(data_dir: &Path, meta: &CheckpointMeta) -> io::Result<()> {
    write_meta(data_dir, meta)
}
