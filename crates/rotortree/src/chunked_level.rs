#[cfg(not(feature = "std"))]
use alloc::{
    boxed::Box,
    sync::Arc,
    vec::Vec,
};
#[cfg(feature = "std")]
use std::{
    sync::Arc,
    vec::Vec,
};

use core::mem::MaybeUninit;

use crate::{
    Hash,
    TreeError,
};

/// Number of hashes per chunk for structural sharing.
pub(crate) const CHUNK_SIZE: usize = 128;

/// Number of chunks per immutable segment
pub(crate) const CHUNKS_PER_SEGMENT: usize = 256;

#[cfg(not(feature = "storage"))]
#[derive(Clone)]
pub(crate) struct Chunk(Arc<[Hash; CHUNK_SIZE]>);

#[cfg(not(feature = "storage"))]
impl Chunk {
    #[inline(always)]
    pub(crate) fn as_slice(&self) -> &[Hash; CHUNK_SIZE] {
        &self.0
    }

    #[inline(always)]
    pub(crate) fn make_mut(&mut self) -> &mut [Hash; CHUNK_SIZE] {
        Arc::make_mut(&mut self.0)
    }

    /// Allocate a chunk and let `f` write its `CHUNK_SIZE` hashes in place.
    #[inline]
    pub(crate) fn from_fn(f: impl FnOnce(&mut [MaybeUninit<Hash>])) -> Self {
        Self(new_arc_from_fn(f))
    }

    #[cfg(test)]
    pub(crate) fn ptr_eq(a: &Self, b: &Self) -> bool {
        Arc::ptr_eq(&a.0, &b.0)
    }
}

/// Allocate a chunk and let `f` write its contents in place.
#[inline]
fn new_arc_from_fn(f: impl FnOnce(&mut [MaybeUninit<Hash>])) -> Arc<[Hash; CHUNK_SIZE]> {
    let mut arc = Arc::<[Hash; CHUNK_SIZE]>::new_uninit();
    // SAFETY: freshly allocated so uniquely owned, and `MaybeUninit<Hash>` has
    // the same layout as `Hash`.
    let out = unsafe {
        &mut *(Arc::get_mut(&mut arc).unwrap_unchecked().as_mut_ptr()
            as *mut [MaybeUninit<Hash>; CHUNK_SIZE])
    };
    f(out);
    // SAFETY: `f` is contracted to initialise all CHUNK_SIZE elements.
    unsafe { arc.assume_init() }
}

/// Minimum chunks to parallelize.
#[cfg(feature = "parallel")]
const PAR_MIN_CHUNKS: usize = 16;

#[inline]
fn build_chunks(n: usize, build: impl Fn(usize) -> Chunk + Send + Sync) -> Vec<Chunk> {
    #[cfg(feature = "parallel")]
    if n >= PAR_MIN_CHUNKS {
        use rayon::prelude::*;
        return (0..n).into_par_iter().map(build).collect();
    }
    (0..n).map(build).collect()
}

#[inline]
pub(crate) fn as_uninit_mut(s: &mut [Hash]) -> &mut [MaybeUninit<Hash>] {
    // SAFETY: `MaybeUninit<Hash>` has the same layout as `Hash`.
    unsafe { &mut *(s as *mut [Hash] as *mut [MaybeUninit<Hash>]) }
}

#[cfg(feature = "storage")]
#[derive(Clone)]
pub(crate) struct Chunk(ChunkInner);

#[cfg(feature = "storage")]
#[derive(Clone)]
enum ChunkInner {
    Memory(Arc<[Hash; CHUNK_SIZE]>),
    Mapped {
        region: Arc<crate::storage::data::MmapRegion>,
        offset: usize,
    },
}

#[cfg(feature = "storage")]
impl Chunk {
    #[inline(always)]
    pub(crate) fn as_slice(&self) -> &[Hash; CHUNK_SIZE] {
        match &self.0 {
            ChunkInner::Memory(arc) => arc,
            ChunkInner::Mapped { region, offset } => {
                // SAFETY: offset validated at construction
                unsafe { &*(region.as_ptr().add(*offset).cast::<[Hash; CHUNK_SIZE]>()) }
            }
        }
    }

    #[inline(always)]
    pub(crate) fn make_mut(&mut self) -> &mut [Hash; CHUNK_SIZE] {
        if matches!(&self.0, ChunkInner::Mapped { .. }) {
            let data = *self.as_slice();
            self.0 = ChunkInner::Memory(Arc::new(data));
        }
        match &mut self.0 {
            ChunkInner::Memory(arc) => Arc::make_mut(arc),
            ChunkInner::Mapped { .. } => unreachable!(),
        }
    }

    /// Allocate a chunk and let `f` write its `CHUNK_SIZE` hashes in place.
    #[inline]
    pub(crate) fn from_fn(f: impl FnOnce(&mut [MaybeUninit<Hash>])) -> Self {
        Self(ChunkInner::Memory(new_arc_from_fn(f)))
    }

    pub(crate) fn new_mapped(
        region: Arc<crate::storage::data::MmapRegion>,
        offset: usize,
    ) -> Self {
        const CHUNK_BYTE_SIZE: usize = CHUNK_SIZE * 32;
        assert!(
            offset + CHUNK_BYTE_SIZE <= region.valid_len(),
            "Chunk::new_mapped: offset {offset} + {CHUNK_BYTE_SIZE} exceeds valid_len {}",
            region.valid_len()
        );
        Self(ChunkInner::Mapped { region, offset })
    }

    #[cfg(test)]
    pub(crate) fn ptr_eq(a: &Self, b: &Self) -> bool {
        match (&a.0, &b.0) {
            (ChunkInner::Memory(a), ChunkInner::Memory(b)) => Arc::ptr_eq(a, b),
            _ => false,
        }
    }
}

/// A single level of the tree, stored as segmented chunks.
#[derive(Clone)]
pub(crate) struct ChunkedLevel {
    /// Immutable segments of committed chunks, shared with snapshots.
    segments: Vec<Arc<[Chunk; CHUNKS_PER_SEGMENT]>>,
    /// Mutable buffer of committed chunks not yet frozen into a segment.
    /// At most `CHUNKS_PER_SEGMENT - 1` items.
    pending: Vec<Chunk>,
    /// Total number of hashes in this level.
    len: usize,
}

impl ChunkedLevel {
    pub(crate) fn new() -> Self {
        Self {
            segments: Vec::new(),
            pending: Vec::new(),
            len: 0,
        }
    }

    /// Construct a level from checkpoint data, partitioning chunks into
    /// segments and pending.
    #[cfg(feature = "storage")]
    pub(crate) fn from_parts(chunks: Vec<Chunk>, len: usize) -> Self {
        let full_segments = chunks.len() / CHUNKS_PER_SEGMENT;
        let mut segments = Vec::with_capacity(full_segments);
        let mut drain = chunks.into_iter();
        for _ in 0..full_segments {
            let seg: Vec<Chunk> = drain.by_ref().take(CHUNKS_PER_SEGMENT).collect();
            let boxed: Box<[Chunk; CHUNKS_PER_SEGMENT]> = seg
                .into_boxed_slice()
                .try_into()
                .unwrap_or_else(|_| unreachable!());
            segments.push(Arc::from(boxed));
        }
        let pending: Vec<Chunk> = drain.collect();

        Self {
            segments,
            pending,
            len,
        }
    }

    /// Total number of hashes in this level.
    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.len
    }

    /// Total number of chunks, i.e. `len` rounded up to a whole chunk.
    #[cfg(any(feature = "storage", test))]
    #[inline]
    pub(crate) fn chunk_count(&self) -> usize {
        self.segments.len() * CHUNKS_PER_SEGMENT + self.pending.len()
    }

    /// The only place that knows chunks live in frozen segments below
    /// `committed` and in `pending` above it.
    #[inline(always)]
    pub(crate) fn chunk(&self, chunk_idx: usize) -> &Chunk {
        let committed = self.segments.len() * CHUNKS_PER_SEGMENT;
        if chunk_idx < committed {
            &self.segments[chunk_idx / CHUNKS_PER_SEGMENT][chunk_idx % CHUNKS_PER_SEGMENT]
        } else {
            &self.pending[chunk_idx - committed]
        }
    }

    #[inline(always)]
    fn chunk_slice(&self, chunk_idx: usize) -> &[Hash; CHUNK_SIZE] {
        self.chunk(chunk_idx).as_slice()
    }

    /// Read a hash at the given index.
    #[inline]
    pub(crate) fn get(&self, index: usize) -> Result<Hash, TreeError> {
        if index >= self.len {
            return Err(TreeError::IndexOutOfRange {
                index: index as u64,
                size: self.len as u64,
            });
        }
        Ok(self.chunk_slice(index / CHUNK_SIZE)[index % CHUNK_SIZE])
    }

    /// Copy `[start, start + count)` into `out`.
    #[inline(always)]
    pub(crate) fn get_group(&self, start: usize, count: usize, out: &mut [Hash]) {
        let mut at = 0;
        for run in self.runs(start, count) {
            out[at..at + run.len()].copy_from_slice(run);
            at += run.len();
        }
    }

    /// Borrow `[start, start + count)` as contiguous runs, one per chunk.
    #[inline]
    pub(crate) fn runs(
        &self,
        start: usize,
        count: usize,
    ) -> impl Iterator<Item = &[Hash]> {
        debug_assert!(
            start + count <= self.len,
            "runs: {start}+{count} > len {}",
            self.len
        );
        let mut done = 0;
        core::iter::from_fn(move || {
            if done == count {
                return None;
            }
            let idx = start + done;
            let offset = idx % CHUNK_SIZE;
            let take = (CHUNK_SIZE - offset).min(count - done);
            done += take;
            Some(&self.chunk_slice(idx / CHUNK_SIZE)[offset..offset + take])
        })
    }

    /// Write a hash at the given index
    #[inline]
    pub(crate) fn set(&mut self, index: usize, value: Hash) -> Result<(), TreeError> {
        if self.len <= index {
            self.ensure_len(index + 1)?;
        }
        self.set_preallocated(index, value);
        Ok(())
    }

    /// Caller must ensure `index < self.len`
    #[inline(always)]
    pub(crate) fn set_preallocated(&mut self, index: usize, value: Hash) {
        debug_assert!(
            index < self.len,
            "set_preallocated: index {index} >= len {}",
            self.len
        );
        self.chunk_slice_mut(index / CHUNK_SIZE)[index % CHUNK_SIZE] = value;
    }

    /// Resolve a chunk index to a mutable slice, copy-on-writing it.
    #[inline(always)]
    fn chunk_slice_mut(&mut self, chunk_idx: usize) -> &mut [Hash; CHUNK_SIZE] {
        let committed = self.segments.len() * CHUNKS_PER_SEGMENT;
        if chunk_idx < committed {
            let seg_idx = chunk_idx / CHUNKS_PER_SEGMENT;
            let seg_off = chunk_idx % CHUNKS_PER_SEGMENT;
            Arc::make_mut(&mut self.segments[seg_idx])[seg_off].make_mut()
        } else {
            self.pending[chunk_idx - committed].make_mut()
        }
    }

    /// Overwrite `[start, start + count)` with hashes produced by `fill`.
    pub(crate) fn write_with(
        &mut self,
        start: usize,
        count: usize,
        fill: impl Fn(usize, &mut [MaybeUninit<Hash>]),
    ) {
        debug_assert!(
            start + count <= self.len,
            "write_with: {start}+{count} > len {}",
            self.len
        );
        let mut done = 0;
        while done < count {
            let idx = start + done;
            let offset = idx % CHUNK_SIZE;
            let take = (CHUNK_SIZE - offset).min(count - done);
            let chunk = self.chunk_slice_mut(idx / CHUNK_SIZE);
            fill(done, as_uninit_mut(&mut chunk[offset..offset + take]));
            done += take;
        }
    }

    /// Append `count` hashes produced by `fill`, writing each chunk straight
    /// into its final allocation.
    pub(crate) fn extend_with<F>(
        &mut self,
        count: usize,
        fill: F,
    ) -> Result<(), TreeError>
    where
        F: Fn(usize, &mut [MaybeUninit<Hash>]) + Sync,
    {
        if count == 0 {
            return Ok(());
        }
        let new_len = self.len.checked_add(count).ok_or(TreeError::MathError)?;

        let offset = self.len % CHUNK_SIZE;
        let done = if offset > 0 {
            let take = (CHUNK_SIZE - offset).min(count);
            let chunk = self.chunk_slice_mut(self.len / CHUNK_SIZE);
            fill(0, as_uninit_mut(&mut chunk[offset..offset + take]));
            take
        } else {
            0
        };

        // fill into allocations
        if done < count {
            let n = (count - done).div_ceil(CHUNK_SIZE);
            self.pending.reserve(n.min(CHUNKS_PER_SEGMENT));
            let built = build_chunks(n, |ci| {
                let base = done + ci * CHUNK_SIZE;
                let take = (count - base).min(CHUNK_SIZE);
                Chunk::from_fn(|out| {
                    fill(base, &mut out[..take]);
                    out[take..].fill(MaybeUninit::new([0u8; 32]));
                })
            });
            for chunk in built {
                self.push_chunk(chunk);
            }
        }

        self.len = new_len;
        Ok(())
    }

    #[cfg(test)]
    #[inline]
    pub(crate) fn push(&mut self, value: Hash) -> Result<(), TreeError> {
        self.extend(&[value])
    }

    #[inline]
    pub(crate) fn extend(&mut self, values: &[Hash]) -> Result<(), TreeError> {
        self.extend_with(values.len(), |off, out| {
            // SAFETY: `extend_with` only ever asks for disjoint sub-ranges of
            // the `count` it was given, so `off + out.len() <= values.len()`;
            // `Hash` and `MaybeUninit<Hash>` share a layout; and `out` is either
            // a fresh allocation or `self.tail`, neither of which can overlap
            // the caller's `values`.
            unsafe {
                core::ptr::copy_nonoverlapping(
                    values.as_ptr().add(off),
                    out.as_mut_ptr().cast::<Hash>(),
                    out.len(),
                );
            }
        })
    }

    /// Grow to `target`, zero-filling the new slots.
    pub(crate) fn ensure_len(&mut self, target: usize) -> Result<(), TreeError> {
        if self.len >= target {
            return Ok(());
        }
        self.extend_with(target - self.len, |_, out| {
            out.fill(MaybeUninit::new([0u8; 32]));
        })
    }

    /// Push a chunk to pending, freezing into a segment when full
    fn push_chunk(&mut self, chunk: Chunk) {
        self.pending.push(chunk);
        if self.pending.len() == CHUNKS_PER_SEGMENT {
            self.freeze_pending();
        }
    }

    /// Freeze the full pending buffer into an immutable segment
    fn freeze_pending(&mut self) {
        debug_assert_eq!(self.pending.len(), CHUNKS_PER_SEGMENT);
        let pending = core::mem::take(&mut self.pending);
        let boxed_arr: Box<[Chunk; CHUNKS_PER_SEGMENT]> = pending
            .into_boxed_slice()
            .try_into()
            .unwrap_or_else(|_| unreachable!()); // qed
        self.segments.push(Arc::from(boxed_arr));
    }

    /// Collect chunks from index `already` onward
    #[cfg(feature = "storage")]
    pub(crate) fn chunks_since(&self, already: usize) -> Vec<Chunk> {
        (already..self.chunk_count())
            .map(|i| self.chunk(i).clone())
            .collect()
    }

    /// Remap the first `count` chunks to mmap-backed chunks (one region per shard)
    #[cfg(feature = "storage")]
    pub(crate) fn remap_chunks(
        &mut self,
        count: usize,
        regions: &[Arc<crate::storage::data::MmapRegion>],
    ) {
        use crate::storage::checkpoint::shard_address;

        let total = self.chunk_count();
        let remap_count = count.min(total);
        if remap_count == 0 || regions.is_empty() {
            return;
        }

        let unmapped: Vec<Chunk> = self.chunks_since(remap_count);

        self.segments.clear();
        self.pending.clear();

        (0..remap_count)
            .map(|chunk_idx| {
                let (shard_idx, offset_in_shard) = shard_address(chunk_idx);
                Chunk::new_mapped(Arc::clone(&regions[shard_idx]), offset_in_shard)
            })
            .chain(unmapped)
            .for_each(|chunk| self.push_chunk(chunk));
    }
}
