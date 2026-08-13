use crate::{
    Hash,
    Hasher,
    TreeError,
    chunked_level::{
        CHUNK_SIZE,
        ChunkedLevel,
    },
};

/// Parents gathered per `hash_many_into` call.
const PARENT_WINDOW: usize = 16;

/// Number of parents per rayon task in [`TreeInner::recompute_root`].
#[cfg(all(feature = "parallel", feature = "storage"))]
const PAR_CHUNK_SIZE: usize = 64;

#[cfg(feature = "parallel")]
pub(crate) fn parallel_threshold() -> usize {
    static THRESHOLD: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *THRESHOLD.get_or_init(|| {
        std::env::var("ROTORTREE_PARALLEL_THRESHOLD")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(1024)
    })
}

/// Returns the number of hash layers above the leaf level.
///
/// - `size <= 1` → 0 (root IS the leaf or tree is empty)
/// - `size == N` → 1
/// - `size == N^k` → k
#[allow(clippy::arithmetic_side_effects)]
#[inline(always)]
pub(crate) fn ceil_log_n(size: u64, n: usize) -> usize {
    if size <= 1 {
        return 0;
    }
    if n.is_power_of_two() {
        let radix_bits = n.trailing_zeros();
        let span_bits = u64::BITS - (size - 1).leading_zeros();
        return span_bits.div_ceil(radix_bits) as usize;
    }
    (size - 1).ilog(n as u64) as usize + 1
}

/// Convert `u64` to `usize`, returning `CapacityExceeded` on
/// failure (relevant on 32-bit platforms).
#[inline]
pub(crate) fn u64_to_usize(val: u64) -> Result<usize, TreeError> {
    usize::try_from(val).map_err(|_| TreeError::CapacityExceeded)
}

/// Immutable snapshot of the tree for lock-free reads and proof
/// generation.
pub struct TreeSnapshot<const N: usize, const MAX_DEPTH: usize> {
    pub(crate) levels: [ChunkedLevel; MAX_DEPTH],
    pub(crate) root: Option<Hash>,
    pub(crate) size: u64,
    pub(crate) depth: usize,
}

impl<const N: usize, const MAX_DEPTH: usize> TreeSnapshot<N, MAX_DEPTH> {
    /// The Merkle root, or `None` if the tree is empty.
    pub fn root(&self) -> Option<Hash> {
        self.root
    }

    /// Number of leaves in the snapshot.
    pub fn size(&self) -> u64 {
        self.size
    }

    /// Current depth (hash layers above the leaf level).
    pub fn depth(&self) -> usize {
        self.depth
    }

    /// Number of nodes at the given level.
    pub fn level_len(&self, level: usize) -> usize {
        if level > self.depth {
            return 0;
        }
        self.levels[level].len()
    }

    /// Retrieve the hash of a specific node by level and index.
    pub fn get_node(&self, level: usize, index: usize) -> Result<Hash, TreeError> {
        if level > self.depth {
            return Err(TreeError::IndexOutOfRange {
                index: index as u64,
                size: 0,
            });
        }
        self.levels[level].get(index)
    }
}

/// Mutable tree state.
pub(crate) struct TreeInner<const N: usize, const MAX_DEPTH: usize> {
    /// Levels 0..depth-1
    pub(crate) levels: [ChunkedLevel; MAX_DEPTH],
    /// The root hash
    pub(crate) root: Option<Hash>,
    pub(crate) size: u64,
    pub(crate) depth: usize,
}

impl<const N: usize, const MAX_DEPTH: usize> TreeInner<N, MAX_DEPTH> {
    pub(crate) fn new() -> Self {
        Self {
            levels: core::array::from_fn(|_| ChunkedLevel::new()),
            root: None,
            size: 0,
            depth: 0,
        }
    }

    /// Replace a level's contents from checkpoint data.
    #[cfg(feature = "storage")]
    pub(crate) fn set_level_from_parts(
        &mut self,
        level_idx: usize,
        chunks: Vec<crate::chunked_level::Chunk>,
        len: usize,
    ) {
        self.levels[level_idx] = ChunkedLevel::from_parts(chunks, len);
    }

    /// Recompute the root hash from level 0 data bottom-up
    #[cfg(feature = "storage")]
    pub(crate) fn recompute_root<H: Hasher>(&self, hasher: &H) -> Option<Hash> {
        use std::vec::Vec;
        if self.size == 0 {
            return None;
        }
        if self.size == 1 {
            return self.levels[0].get(0).ok();
        }

        let depth = self.depth;
        let level0_len = self.levels[0].len();
        let mut frontier: Vec<Hash> = Vec::with_capacity(level0_len);
        for i in 0..level0_len {
            frontier.push(self.levels[0].get(i).ok()?);
        }

        for _level in 0..depth {
            let len = frontier.len();
            let num_parents = len.div_ceil(N);

            #[cfg(feature = "parallel")]
            let parents = {
                use rayon::prelude::*;
                if num_parents >= parallel_threshold() {
                    let mut buf = vec![[0u8; 32]; num_parents];
                    buf.par_chunks_mut(PAR_CHUNK_SIZE).enumerate().for_each(
                        |(ci, chunk)| {
                            let base = ci * PAR_CHUNK_SIZE;
                            for (i, slot) in chunk.iter_mut().enumerate() {
                                *slot =
                                    Self::_hash_group(&frontier, base + i, len, hasher);
                            }
                        },
                    );
                    buf
                } else {
                    (0..num_parents)
                        .map(|parent_idx| {
                            Self::_hash_group(&frontier, parent_idx, len, hasher)
                        })
                        .collect()
                }
            };

            #[cfg(not(feature = "parallel"))]
            let parents: Vec<Hash> = (0..num_parents)
                .map(|parent_idx| Self::_hash_group(&frontier, parent_idx, len, hasher))
                .collect();

            frontier = parents;
        }

        frontier.first().copied()
    }

    #[cfg(feature = "storage")]
    #[inline]
    fn _hash_group<H: Hasher>(
        current: &[Hash],
        parent_idx: usize,
        len: usize,
        hasher: &H,
    ) -> Hash {
        let start = parent_idx * N;
        let end = core::cmp::min(start + N, len);
        let tally = end - start;
        if tally == 1 {
            current[start]
        } else {
            hasher.hash_children(&current[start..end])
        }
    }

    pub(crate) fn snapshot(&self) -> TreeSnapshot<N, MAX_DEPTH> {
        let mut levels = core::array::from_fn(|_| ChunkedLevel::new());
        let snap_count = core::cmp::min(self.depth.saturating_add(1), MAX_DEPTH);
        for (dst, src) in levels.iter_mut().zip(self.levels.iter()).take(snap_count) {
            *dst = src.clone();
        }
        TreeSnapshot {
            levels,
            root: self.root,
            size: self.size,
            depth: self.depth,
        }
    }
}

/// An N-ary Lean Incremental Merkle Tree.
///
/// # Type Parameters
///
/// - `H`: Hash function ([`Hasher`])
/// - `N`: Branching factor (compile-time, must be >= 2)
/// - `MAX_DEPTH`: Maximum tree depth (must be >= 1)
pub struct LeanIMT<H: Hasher, const N: usize, const MAX_DEPTH: usize> {
    hasher: H,
    #[cfg(not(feature = "concurrent"))]
    #[cfg_attr(docsrs, doc(cfg(not(feature = "concurrent"))))]
    inner: TreeInner<N, MAX_DEPTH>,
    #[cfg(feature = "concurrent")]
    #[cfg_attr(docsrs, doc(cfg(feature = "concurrent")))]
    inner: parking_lot::RwLock<TreeInner<N, MAX_DEPTH>>,
}

impl<H: Hasher, const N: usize, const MAX_DEPTH: usize> LeanIMT<H, N, MAX_DEPTH> {
    const _ASSERT_N: () = assert!(N >= 2, "branching factor must be at least 2");
    const _ASSERT_DEPTH: () = assert!(MAX_DEPTH >= 1, "max depth must be at least 1");

    /// Create a new empty tree.
    #[cfg(not(feature = "concurrent"))]
    pub fn new(hasher: H) -> Self {
        let () = Self::_ASSERT_N;
        let () = Self::_ASSERT_DEPTH;
        Self {
            hasher,
            inner: TreeInner::new(),
        }
    }

    /// Create a new empty tree
    #[cfg(feature = "concurrent")]
    #[cfg_attr(docsrs, doc(cfg(feature = "concurrent")))]
    pub fn new(hasher: H) -> Self {
        let () = Self::_ASSERT_N;
        let () = Self::_ASSERT_DEPTH;
        Self {
            hasher,
            inner: parking_lot::RwLock::new(TreeInner::new()),
        }
    }

    /// Insert a single leaf. Returns the new Merkle root.
    #[cfg(not(feature = "concurrent"))]
    pub fn insert(&mut self, leaf: Hash) -> Result<Hash, TreeError> {
        Self::_insert(&mut self.inner, &self.hasher, leaf)
    }

    /// Insert a single leaf. Returns the new Merkle root.
    #[cfg(feature = "concurrent")]
    #[cfg_attr(docsrs, doc(cfg(feature = "concurrent")))]
    pub fn insert(&self, leaf: Hash) -> Result<Hash, TreeError> {
        Self::_insert(&mut self.inner.write(), &self.hasher, leaf)
    }

    /// Insert multiple leaves in a batch. Returns the new root.
    #[cfg(not(feature = "concurrent"))]
    pub fn insert_many(&mut self, leaves: &[Hash]) -> Result<Hash, TreeError> {
        Self::_insert_many(&mut self.inner, &self.hasher, leaves)
    }

    /// Insert multiple leaves in a batch. Returns the new root.
    #[cfg(feature = "concurrent")]
    #[cfg_attr(docsrs, doc(cfg(feature = "concurrent")))]
    pub fn insert_many(&self, leaves: &[Hash]) -> Result<Hash, TreeError> {
        Self::_insert_many(&mut self.inner.write(), &self.hasher, leaves)
    }

    /// The current Merkle root, or `None` if the tree is empty.
    #[cfg(not(feature = "concurrent"))]
    pub fn root(&self) -> Option<Hash> {
        self.inner.root
    }

    /// The current Merkle root, or `None` if the tree is empty.
    #[cfg(feature = "concurrent")]
    #[cfg_attr(docsrs, doc(cfg(feature = "concurrent")))]
    pub fn root(&self) -> Option<Hash> {
        self.inner.read().root
    }

    /// Number of leaves in the tree.
    #[cfg(not(feature = "concurrent"))]
    pub fn size(&self) -> u64 {
        self.inner.size
    }

    /// Number of leaves in the tree.
    #[cfg(feature = "concurrent")]
    #[cfg_attr(docsrs, doc(cfg(feature = "concurrent")))]
    pub fn size(&self) -> u64 {
        self.inner.read().size
    }

    /// Current depth (hash layers above the leaf level).
    #[cfg(not(feature = "concurrent"))]
    pub fn depth(&self) -> usize {
        self.inner.depth
    }

    /// Current depth (hash layers above the leaf level).
    #[cfg(feature = "concurrent")]
    #[cfg_attr(docsrs, doc(cfg(feature = "concurrent")))]
    pub fn depth(&self) -> usize {
        self.inner.read().depth
    }

    /// Create an immutable snapshot for proof generation.
    #[cfg(not(feature = "concurrent"))]
    pub fn snapshot(&self) -> TreeSnapshot<N, MAX_DEPTH> {
        self.inner.snapshot()
    }

    /// Create an immutable snapshot for proof generation.
    #[cfg(feature = "concurrent")]
    #[cfg_attr(docsrs, doc(cfg(feature = "concurrent")))]
    pub fn snapshot(&self) -> TreeSnapshot<N, MAX_DEPTH> {
        self.inner.read().snapshot()
    }

    #[inline]
    pub(crate) fn _insert(
        inner: &mut TreeInner<N, MAX_DEPTH>,
        hasher: &H,
        leaf: Hash,
    ) -> Result<Hash, TreeError> {
        let new_size = inner
            .size
            .checked_add(1)
            .ok_or(TreeError::CapacityExceeded)?;
        let depth = ceil_log_n(new_size, N);
        if depth > MAX_DEPTH {
            return Err(TreeError::MaxDepthExceeded {
                max_depth: MAX_DEPTH,
            });
        }
        let index = u64_to_usize(inner.size)?;

        let mut rung = leaf;
        let mut locus = index;
        for level in 0..depth {
            inner.levels[level].set(locus, rung)?;

            let sibling_rank = locus % N;
            if sibling_rank != 0 {
                let group_start = locus - sibling_rank;
                let tally = sibling_rank + 1;
                let mut children = [[0u8; 32]; N];
                if sibling_rank > 0 {
                    inner.levels[level].get_group(
                        group_start,
                        sibling_rank,
                        &mut children,
                    );
                }
                children[sibling_rank] = rung;
                rung = hasher.hash_children(&children[..tally]);
            }
            locus /= N;
        }

        if depth < MAX_DEPTH {
            inner.levels[depth].set(0, rung)?;
        }
        inner.root = Some(rung);
        inner.size = new_size;
        inner.depth = depth;
        Ok(rung)
    }

    /// Compute the parent hash for a group at `parent_idx`
    /// within a single level.
    #[inline(always)]
    fn _compute_parent(
        child_level: &ChunkedLevel,
        parent_idx: usize,
        level_len: usize,
        hasher: &H,
    ) -> Result<Hash, TreeError> {
        let group_start = parent_idx * N;
        let group_end = core::cmp::min(group_start + N, level_len);
        let tally = group_end - group_start;
        if tally == 1 {
            child_level.get(group_start)
        } else {
            let mut children = [[0u8; 32]; N];
            child_level.get_group(group_start, tally, &mut children);
            Ok(hasher.hash_children(&children[..tally]))
        }
    }

    /// Sequential inner loop for one level of `_insert_many`.
    ///
    /// Consecutive FULL groups (each exactly `N` children) at an eligible
    /// arity are gathered into windows and hashed together via
    /// [`Hasher::hash_many_into`], which lets a SIMD-capable hasher hash
    /// several parents at once. The trailing partial group and the count==1
    /// lift fall back to the scalar [`Self::_compute_parent`] path. For
    /// hashers without a batch override this is identical to the old per-group
    /// loop (the default `hash_many_into` is a scalar loop).
    #[inline]
    #[allow(clippy::too_many_arguments)]
    fn _insert_many_level_seq(
        levels: &mut [ChunkedLevel],
        level: usize,
        start_parent: usize,
        num_parents: usize,
        level_len: usize,
        is_root_level: bool,
        hasher: &H,
        root: &mut Hash,
    ) -> Result<(), TreeError> {
        let next_level = level + 1;

        if next_level < levels.len() {
            levels[next_level].ensure_len(num_parents)?;
            // Split so the child level is borrowed immutably while the parent
            // level is written mutably.
            let (head, tail) = levels.split_at_mut(next_level);
            let child = &head[level];
            let parent = &mut tail[0];

            parent.write_with(start_parent, num_parents - start_parent, |off, out| {
                Self::_compute_parents_batched(
                    child,
                    start_parent + off,
                    level_len,
                    hasher,
                    out,
                );
            });

            // At the root level there is exactly one parent; it is the root.
            if is_root_level {
                *root = parent.get(num_parents - 1)?;
            }
        } else {
            // No parent level to write into: compute scalar, track root only.
            for parent_idx in start_parent..num_parents {
                let p =
                    Self::_compute_parent(&levels[level], parent_idx, level_len, hasher)?;
                if is_root_level {
                    *root = p;
                }
            }
        }
        Ok(())
    }

    /// Fill `out` with parents `start_parent .. start_parent + out.len()`,
    /// batching full groups through [`Hasher::hash_many_into`] and falling back
    /// to the scalar [`Self::_compute_parent`] for the trailing partial group
    /// and the lift.
    #[inline]
    fn _compute_parents_batched(
        child: &ChunkedLevel,
        start_parent: usize,
        level_len: usize,
        hasher: &H,
        out: &mut [core::mem::MaybeUninit<Hash>],
    ) {
        let full = if CHUNK_SIZE.is_multiple_of(N) {
            (level_len / N).saturating_sub(start_parent).min(out.len())
        } else {
            0
        };

        let mut refs: [&[Hash]; PARENT_WINDOW] = [&[]; PARENT_WINDOW];
        let mut staging: [Hash; PARENT_WINDOW] = [[0u8; 32]; PARENT_WINDOW];
        let mut i = 0;
        let mut win = 0;
        for run in child.runs(start_parent * N, full * N) {
            for group in run.chunks_exact(N) {
                refs[win] = group;
                win += 1;
                if win == PARENT_WINDOW {
                    hasher.hash_many_into(&refs, &mut staging);
                    for (k, &h) in staging.iter().enumerate() {
                        out[i + k].write(h);
                    }
                    i += win;
                    win = 0;
                }
            }
        }
        if win > 0 {
            hasher.hash_many_into(&refs[..win], &mut staging[..win]);
            for (k, &h) in staging[..win].iter().enumerate() {
                out[i + k].write(h);
            }
            i += win;
        }

        // remainder
        while i < out.len() {
            let p = Self::_compute_parent(child, start_parent + i, level_len, hasher)
                .expect("ensure_len guarantees valid indices");
            out[i].write(p);
            i += 1;
        }
    }

    pub(crate) fn _insert_many(
        inner: &mut TreeInner<N, MAX_DEPTH>,
        hasher: &H,
        leaves: &[Hash],
    ) -> Result<Hash, TreeError> {
        if leaves.is_empty() {
            return Err(TreeError::EmptyBatch);
        }

        let batch_len = u64::try_from(leaves.len()).unwrap_or(u64::MAX);
        let new_size = inner
            .size
            .checked_add(batch_len)
            .ok_or(TreeError::CapacityExceeded)?;
        let depth = ceil_log_n(new_size, N);
        if depth > MAX_DEPTH {
            return Err(TreeError::MaxDepthExceeded {
                max_depth: MAX_DEPTH,
            });
        }

        inner.levels[0].extend(leaves)?;

        let old_size_usize = u64_to_usize(inner.size)?;
        let mut start_parent = old_size_usize / N;

        let mut root = if depth == 0 {
            inner.levels[0].get(0)?
        } else {
            [0u8; 32]
        };

        #[cfg(feature = "parallel")]
        let par_threshold = parallel_threshold();

        for level in 0..depth {
            let level_len = inner.levels[level].len();
            let num_parents = level_len.div_ceil(N);
            let is_root_level = level + 1 == depth;

            #[cfg(feature = "parallel")]
            {
                let work = num_parents - start_parent;
                if work >= par_threshold && level + 1 < MAX_DEPTH {
                    let split_at = level + 1;
                    let (child_levels, parent_levels) =
                        inner.levels.split_at_mut(split_at);
                    let child_level = &child_levels[level];
                    let parent = &mut parent_levels[0];

                    let overlap = usize::from(start_parent < parent.len());
                    if overlap == 1 {
                        parent.write_with(start_parent, 1, |_, out| {
                            Self::_compute_parents_batched(
                                child_level,
                                start_parent,
                                level_len,
                                hasher,
                                out,
                            );
                        });
                    }

                    let appended = start_parent + overlap;
                    parent.extend_with(work - overlap, |off, out| {
                        Self::_compute_parents_batched(
                            child_level,
                            appended + off,
                            level_len,
                            hasher,
                            out,
                        );
                    })?;

                    if is_root_level {
                        root = parent.get(num_parents - 1)?;
                    }
                } else {
                    Self::_insert_many_level_seq(
                        &mut inner.levels,
                        level,
                        start_parent,
                        num_parents,
                        level_len,
                        is_root_level,
                        hasher,
                        &mut root,
                    )?;
                }
            }

            #[cfg(not(feature = "parallel"))]
            Self::_insert_many_level_seq(
                &mut inner.levels,
                level,
                start_parent,
                num_parents,
                level_len,
                is_root_level,
                hasher,
                &mut root,
            )?;

            start_parent /= N;
        }

        inner.root = Some(root);
        inner.size = new_size;
        inner.depth = depth;
        Ok(root)
    }
}

#[cfg(test)]
#[cfg_attr(feature = "concurrent", allow(unused_mut))]
mod tests {
    #[cfg(not(feature = "std"))]
    use alloc::vec::Vec;
    #[cfg(feature = "std")]
    use std::vec::Vec;

    use super::*;
    use crate::{
        chunked_level::{
            CHUNK_SIZE,
            Chunk,
        },
        test_util::*,
    };

    #[test]
    fn ceil_log_n_empty() {
        assert_eq!(ceil_log_n(0, 2), 0);
    }

    #[test]
    fn ceil_log_n_one() {
        assert_eq!(ceil_log_n(1, 2), 0);
    }

    #[test]
    fn ceil_log_n_binary_full() {
        assert_eq!(ceil_log_n(4, 2), 2);
    }

    #[test]
    fn ceil_log_n_binary_partial() {
        assert_eq!(ceil_log_n(3, 2), 2);
    }

    #[test]
    fn ceil_log_n_ternary() {
        assert_eq!(ceil_log_n(4, 3), 2);
    }

    #[test]
    fn ceil_log_n_ternary_exact() {
        assert_eq!(ceil_log_n(9, 3), 2);
    }

    #[test]
    fn ceil_log_n_quaternary() {
        assert_eq!(ceil_log_n(16, 4), 2);
        assert_eq!(ceil_log_n(17, 4), 3);
    }

    #[test]
    fn ceil_log_n_large_n() {
        assert_eq!(ceil_log_n(256, 16), 2);
        assert_eq!(ceil_log_n(257, 16), 3);
    }

    #[test]
    fn chunked_level_push_and_get() {
        let mut level = ChunkedLevel::new();
        for i in 0u32..10 {
            level.push(leaf(i)).unwrap();
        }
        assert_eq!(level.len(), 10);
        for i in 0u32..10 {
            assert_eq!(level.get(i as usize).unwrap(), leaf(i));
        }
    }

    #[test]
    fn chunked_level_pads_partial_chunk_with_zeros() {
        let mut level = ChunkedLevel::new();
        for i in 0..CHUNK_SIZE {
            level.push(leaf(i as u32)).unwrap();
        }
        assert_eq!(level.chunk_count(), 1);
        assert_eq!(level.len(), CHUNK_SIZE);

        // One more opens a second, partially filled chunk.
        level.push(leaf(0xFF)).unwrap();
        assert_eq!(level.chunk_count(), 2);
        assert_eq!(level.len(), CHUNK_SIZE + 1);
        assert!(
            level.chunk(1).as_slice()[1..]
                .iter()
                .all(|h| *h == [0u8; 32])
        );
    }

    #[test]
    fn chunked_level_clone_shares_arcs() {
        let mut level = ChunkedLevel::new();
        for i in 0..CHUNK_SIZE + 5 {
            level.push(leaf(i as u32)).unwrap();
        }
        let snap = level.clone();
        assert_eq!(snap.len(), level.len());
        // The completed chunk Arc is shared.
        assert!(Chunk::ptr_eq(level.chunk(0), snap.chunk(0)));
        // Data matches.
        for i in 0..level.len() {
            assert_eq!(level.get(i).unwrap(), snap.get(i).unwrap());
        }
    }

    #[test]
    fn empty_tree() {
        let tree = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
        assert_eq!(tree.root(), None);
        assert_eq!(tree.size(), 0);
        assert_eq!(tree.depth(), 0);
    }

    #[test]
    fn insert_single_leaf_binary() {
        let mut tree = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
        let l = leaf(1);
        let root = tree.insert(l).unwrap();
        assert_eq!(root, l); // single leaf stored as-is
        assert_eq!(tree.size(), 1);
        assert_eq!(tree.depth(), 0);
    }

    #[test]
    fn insert_two_leaves_binary() {
        let th = XorHasher;
        let mut tree = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
        let l0 = leaf(1);
        let l1 = leaf(2);
        tree.insert(l0).unwrap();
        let root = tree.insert(l1).unwrap();

        let expected = th.hash_children(&[l0, l1]);
        assert_eq!(root, expected);
        assert_eq!(tree.size(), 2);
        assert_eq!(tree.depth(), 1);
    }

    #[test]
    fn insert_three_leaves_binary() {
        let th = XorHasher;
        let mut tree = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
        let l0 = leaf(1);
        let l1 = leaf(2);
        let l2 = leaf(3);
        tree.insert(l0).unwrap();
        tree.insert(l1).unwrap();
        let root = tree.insert(l2).unwrap();

        // Level 0: [l0, l1, l2]
        // Level 1: [H(l0,l1), l2_lifted]
        // Level 2: [H(H(l0,l1), l2)]
        let h01 = th.hash_children(&[l0, l1]);
        let expected = th.hash_children(&[h01, l2]);
        assert_eq!(root, expected);
        assert_eq!(tree.depth(), 2);
    }

    #[test]
    fn insert_four_leaves_binary() {
        let th = XorHasher;
        let mut tree = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
        let leaves: Vec<Hash> = (1..=4).map(leaf).collect();
        for &l in &leaves {
            tree.insert(l).unwrap();
        }

        // Level 0: [l0, l1, l2, l3]
        // Level 1: [H(l0,l1), H(l2,l3)]
        // Level 2: [H(H(l0,l1), H(l2,l3))]
        let h01 = th.hash_children(&[leaves[0], leaves[1]]);
        let h23 = th.hash_children(&[leaves[2], leaves[3]]);
        let expected = th.hash_children(&[h01, h23]);
        assert_eq!(tree.root(), Some(expected));
        assert_eq!(tree.depth(), 2);
    }

    #[test]
    fn insert_four_leaves_ternary() {
        let th = XorHasher;
        let mut tree = LeanIMT::<XorHasher, 3, 32>::new(XorHasher);
        let leaves: Vec<Hash> = (1..=4).map(leaf).collect();
        for &l in &leaves {
            tree.insert(l).unwrap();
        }

        // Level 0: [l0, l1, l2, l3]
        // Level 1: [H(l0,l1,l2), l3_lifted]
        // Level 2: [H(H(l0,l1,l2), l3)]
        let h012 = th.hash_children(&[leaves[0], leaves[1], leaves[2]]);
        let expected = th.hash_children(&[h012, leaves[3]]);
        assert_eq!(tree.root(), Some(expected));
        assert_eq!(tree.depth(), 2);
    }

    #[test]
    fn insert_two_leaves_ternary() {
        let th = XorHasher;
        let mut tree = LeanIMT::<XorHasher, 3, 32>::new(XorHasher);
        let l0 = leaf(1);
        let l1 = leaf(2);
        tree.insert(l0).unwrap();
        let root = tree.insert(l1).unwrap();

        let expected = th.hash_children(&[l0, l1]);
        assert_eq!(root, expected);
        assert_eq!(tree.depth(), 1);
    }

    #[test]
    fn insert_five_leaves_quaternary() {
        let th = XorHasher;
        let mut tree = LeanIMT::<XorHasher, 4, 32>::new(XorHasher);
        let leaves: Vec<Hash> = (1..=5).map(leaf).collect();
        for &l in &leaves {
            tree.insert(l).unwrap();
        }

        // Level 0: [l0..l4]
        // Level 1: [H(l0,l1,l2,l3), l4_lifted]
        // Level 2: [H(H(l0,l1,l2,l3), l4)]
        let h0123 = th.hash_children(&[leaves[0], leaves[1], leaves[2], leaves[3]]);
        let expected = th.hash_children(&[h0123, leaves[4]]);
        assert_eq!(tree.root(), Some(expected));
        assert_eq!(tree.depth(), 2);
    }

    #[test]
    fn insert_many_matches_sequential_binary() {
        let h = XorHasher;
        let leaves: Vec<Hash> = (1..=7).map(leaf).collect();

        let mut seq = LeanIMT::<XorHasher, 2, 32>::new(h.clone());
        for &l in &leaves {
            seq.insert(l).unwrap();
        }

        let mut batch = LeanIMT::<XorHasher, 2, 32>::new(h.clone());
        batch.insert_many(&leaves).unwrap();

        assert_eq!(seq.root(), batch.root());
        assert_eq!(seq.size(), batch.size());
    }

    #[test]
    fn insert_many_matches_sequential_ternary() {
        let h = XorHasher;
        let leaves: Vec<Hash> = (1..=10).map(leaf).collect();

        let mut seq = LeanIMT::<XorHasher, 3, 32>::new(h.clone());
        for &l in &leaves {
            seq.insert(l).unwrap();
        }

        let mut batch = LeanIMT::<XorHasher, 3, 32>::new(h.clone());
        batch.insert_many(&leaves).unwrap();

        assert_eq!(seq.root(), batch.root());
    }

    #[test]
    fn insert_many_incremental() {
        let h = XorHasher;
        let leaves: Vec<Hash> = (1..=10).map(leaf).collect();

        let mut seq = LeanIMT::<XorHasher, 2, 32>::new(h.clone());
        for &l in &leaves {
            seq.insert(l).unwrap();
        }

        let mut mixed = LeanIMT::<XorHasher, 2, 32>::new(h.clone());
        for &l in &leaves[..3] {
            mixed.insert(l).unwrap();
        }
        mixed.insert_many(&leaves[3..]).unwrap();

        assert_eq!(seq.root(), mixed.root());
    }

    #[test]
    fn insert_many_empty_batch_error() {
        let mut tree = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
        assert_eq!(tree.insert_many(&[]), Err(TreeError::EmptyBatch));
    }

    #[test]
    fn insert_many_chunk_boundary() {
        let leaves: Vec<Hash> = (0..CHUNK_SIZE)
            .map(|i| {
                let mut h = [0u8; 32];
                let bytes = (i as u64).to_le_bytes();
                h[..8].copy_from_slice(&bytes);
                h
            })
            .collect();

        let mut seq = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
        for &l in &leaves {
            seq.insert(l).unwrap();
        }

        let mut batch = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
        batch.insert_many(&leaves).unwrap();

        assert_eq!(seq.root(), batch.root());
        assert_eq!(seq.size(), batch.size());
        assert_eq!(seq.size(), CHUNK_SIZE as u64);
    }

    #[test]
    fn max_depth_exceeded() {
        let mut tree = LeanIMT::<XorHasher, 2, 1>::new(XorHasher);
        let l = [0u8; 32];
        tree.insert(l).unwrap(); // size=1, depth=0
        tree.insert(l).unwrap(); // size=2, depth=1
        let err = tree.insert(l).unwrap_err();
        assert_eq!(err, TreeError::MaxDepthExceeded { max_depth: 1 });
    }

    #[cfg(feature = "blake3")]
    mod blake3_tests {
        use super::*;
        use crate::Blake3Hasher;

        fn blake3_leaf(n: u8) -> Hash {
            *::blake3::hash(&[n]).as_bytes()
        }

        #[test]
        fn binary_four_leaves_known_vector() {
            let th = Blake3Hasher;
            let mut tree = LeanIMT::<Blake3Hasher, 2, 32>::new(Blake3Hasher);

            let l0 = blake3_leaf(0);
            let l1 = blake3_leaf(1);
            let l2 = blake3_leaf(2);
            let l3 = blake3_leaf(3);

            let r1 = tree.insert(l0).unwrap();
            assert_eq!(r1, l0);

            let r2 = tree.insert(l1).unwrap();
            let h01 = th.hash_children(&[l0, l1]);
            assert_eq!(r2, h01);

            let r3 = tree.insert(l2).unwrap();
            let expected3 = th.hash_children(&[h01, l2]);
            assert_eq!(r3, expected3);

            let r4 = tree.insert(l3).unwrap();
            let h23 = th.hash_children(&[l2, l3]);
            let expected4 = th.hash_children(&[h01, h23]);
            assert_eq!(r4, expected4);
        }

        #[test]
        fn ternary_four_leaves_known_vector() {
            let th = Blake3Hasher;
            let mut tree = LeanIMT::<Blake3Hasher, 3, 32>::new(Blake3Hasher);

            let l0 = blake3_leaf(0);
            let l1 = blake3_leaf(1);
            let l2 = blake3_leaf(2);
            let l3 = blake3_leaf(3);

            tree.insert(l0).unwrap();

            let r2 = tree.insert(l1).unwrap();
            assert_eq!(r2, th.hash_children(&[l0, l1]));

            let r3 = tree.insert(l2).unwrap();
            assert_eq!(r3, th.hash_children(&[l0, l1, l2]));

            let r4 = tree.insert(l3).unwrap();
            let h012 = th.hash_children(&[l0, l1, l2]);
            assert_eq!(r4, th.hash_children(&[h012, l3]));
        }

        #[test]
        fn quaternary_five_leaves_known_vector() {
            let th = Blake3Hasher;
            let mut tree = LeanIMT::<Blake3Hasher, 4, 32>::new(Blake3Hasher);

            let leaves: Vec<Hash> = (0..5).map(blake3_leaf).collect();
            for &l in &leaves {
                tree.insert(l).unwrap();
            }

            let h0123 = th.hash_children(&[leaves[0], leaves[1], leaves[2], leaves[3]]);
            let expected = th.hash_children(&[h0123, leaves[4]]);
            assert_eq!(tree.root(), Some(expected));
        }
    }
}
