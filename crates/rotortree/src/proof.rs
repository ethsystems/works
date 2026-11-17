use crate::{
    Hash,
    Hasher,
    TreeError,
    tree::{
        TreeSnapshot,
        ceil_log_n,
        u64_to_usize,
    },
};

fn to_u8(v: usize) -> Result<u8, TreeError> {
    u8::try_from(v).map_err(|_| TreeError::MathError)
}

/// One level of an N-ary Merkle proof.
///
/// Uses a fixed-size `[Hash; N]` array (at most `N-1` siblings
/// are valid, indicated by `sibling_count`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "wincode", derive(wincode::SchemaWrite, wincode::SchemaRead))]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProofLevel<const N: usize> {
    /// Child position within the group (`0..N-1`)
    pub position: u8,
    /// Number of valid siblings in `siblings` (0 for lifted)
    pub sibling_count: u8,
    /// Sibling hashes
    #[cfg_attr(
        feature = "serde",
        serde(with = "serde_with::As::<[serde_with::Same; N]>")
    )]
    pub siblings: [Hash; N],
}

impl<const N: usize> ProofLevel<N> {
    const EMPTY: Self = Self {
        position: 0,
        sibling_count: 0,
        siblings: [[0u8; 32]; N],
    };
}

/// An N-ary Merkle inclusion proof
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "wincode", derive(wincode::SchemaWrite, wincode::SchemaRead))]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NaryProof<const N: usize, const MAX_DEPTH: usize> {
    /// The Merkle root this proof verifies against
    pub root: Hash,
    /// The leaf hash being proved
    pub leaf: Hash,
    /// The 0-based index of the leaf
    pub leaf_index: u64,
    /// Number of leaves in the tree this proof was generated from
    pub tree_size: u64,
    /// Number of valid levels in `levels`
    pub level_count: usize,
    /// Proof levels from leaf to root
    #[cfg_attr(
        feature = "serde",
        serde(with = "serde_with::As::<[serde_with::Same; MAX_DEPTH]>")
    )]
    pub levels: [ProofLevel<N>; MAX_DEPTH],
}

impl<const N: usize, const MAX_DEPTH: usize> NaryProof<N, MAX_DEPTH> {
    /// Verify this proof against the given hasher.
    pub fn verify<H: Hasher>(&self, hasher: &H) -> Result<bool, TreeError> {
        if self.tree_size == 0 || self.leaf_index >= self.tree_size {
            return Err(TreeError::MathError);
        }

        let expected_depth = ceil_log_n(self.tree_size, N);
        if self.level_count != expected_depth || expected_depth > MAX_DEPTH {
            return Err(TreeError::InvalidProofDepth {
                expected: expected_depth,
                actual: self.level_count,
            });
        }

        let mut expected_index = u64_to_usize(self.leaf_index)?;
        // u64, because the tree can outgrow a 32-bit usize when the leaf doesn't.
        let mut level_len = self.tree_size;
        let mut current = self.leaf;
        let mut children = [[0u8; 32]; N];

        for level in &self.levels[..self.level_count] {
            let pos = expected_index % N;
            let group_start = expected_index - pos;
            // The group size comes from the tree's shape, not from the proof.
            // A wrong count lets an internal node, or half of a leaf's
            // preimage, verify as a leaf.
            let remaining = level_len - group_start as u64;
            let group_size = usize::try_from(remaining).map_or(N, |r| r.min(N));
            if usize::from(level.position) != pos
                || usize::from(level.sibling_count) != group_size - 1
            {
                return Err(TreeError::MathError);
            }

            if group_size > 1 {
                children[..pos].copy_from_slice(&level.siblings[..pos]);
                children[pos] = current;
                children[pos + 1..group_size]
                    .copy_from_slice(&level.siblings[pos..group_size - 1]);
                current = hasher.hash_children(&children[..group_size]);
            }

            expected_index /= N;
            level_len = level_len.div_ceil(N as u64);
        }

        Ok(current == self.root)
    }

    /// Verify this inclusion proof against an externally-trusted root.
    ///
    /// A root does not commit to the leaf count, so also check `tree_size`
    /// against a size you trust.
    pub fn verify_against<H: Hasher>(
        &self,
        hasher: &H,
        trusted_root: Hash,
    ) -> Result<bool, TreeError> {
        if self.root != trusted_root {
            return Ok(false);
        }
        self.verify(hasher)
    }
}

/// Per-level data in a consistency proof
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "wincode", derive(wincode::SchemaWrite, wincode::SchemaRead))]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ConsistencyLevel<const N: usize> {
    /// Number of shared (left) siblings in `hashes`
    pub shared_count: u8,
    /// Number of new-only (right) siblings in `hashes`.
    pub new_count: u8,
    /// `[shared..., new...]` hashes
    #[cfg_attr(
        feature = "serde",
        serde(with = "serde_with::As::<[serde_with::Same; N]>")
    )]
    pub hashes: [Hash; N],
}

impl<const N: usize> ConsistencyLevel<N> {
    const EMPTY: Self = Self {
        shared_count: 0,
        new_count: 0,
        hashes: [[0u8; 32]; N],
    };

    fn new_hashes(&self) -> &[Hash] {
        let sc = self.shared_count as usize;
        let nc = self.new_count as usize;
        &self.hashes[sc..sc + nc]
    }
}

/// Consistency proof
///
/// Proves that a tree of `old_size` leaves is a prefix of a tree of
/// `new_size` leaves
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "wincode", derive(wincode::SchemaWrite, wincode::SchemaRead))]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ConsistencyProof<const N: usize, const MAX_DEPTH: usize> {
    /// Root of the old (smaller) tree
    pub old_root: Hash,
    /// Root of the new (larger) tree
    pub new_root: Hash,
    /// Number of leaves in the old tree
    pub old_size: u64,
    /// Number of leaves in the new tree
    pub new_size: u64,
    /// Number of valid levels in `levels`
    pub level_count: usize,
    /// Proof levels from leaves toward root
    #[cfg_attr(
        feature = "serde",
        serde(with = "serde_with::As::<[serde_with::Same; MAX_DEPTH]>")
    )]
    pub levels: [ConsistencyLevel<N>; MAX_DEPTH],
}

impl<const N: usize, const MAX_DEPTH: usize> ConsistencyProof<N, MAX_DEPTH> {
    /// Verify this consistency proof against the given hasher.
    ///
    /// Returns `Ok(true)` if both reconstructed roots match.
    pub fn verify<H: Hasher>(&self, hasher: &H) -> Result<bool, TreeError> {
        if self.old_size == 0
            || self.new_size == 0
            || self.old_size > self.new_size
            || self.level_count > MAX_DEPTH
        {
            return Err(TreeError::MathError);
        }

        if self.old_size == self.new_size {
            return Ok(self.old_root == self.new_root);
        }
        if self.level_count == 0 {
            return Ok(false);
        }

        let mut old_level_size = u64_to_usize(self.old_size)?;
        let mut new_level_size = u64_to_usize(self.new_size)?;

        let expected_depth = {
            let (mut os, mut ns) = (old_level_size, new_level_size);
            let mut d = 0usize;
            while os > 1 || ns > 1 {
                d += 1;
                os = os.div_ceil(N);
                ns = ns.div_ceil(N);
            }
            d
        };
        if self.level_count != expected_depth {
            return Err(TreeError::InvalidProofDepth {
                expected: expected_depth,
                actual: self.level_count,
            });
        }

        let mut old_hash = [0u8; 32];
        let mut new_hash = [0u8; 32];
        let mut children = [[0u8; 32]; N];

        for (i, level) in self.levels[..self.level_count].iter().enumerate() {
            let shared = level.shared_count as usize;
            let new_only = level.new_count as usize;
            let boundary = old_level_size - 1;
            let boundary_pos = boundary % N;
            let group_start = boundary - boundary_pos;

            let expected_shared = if i == 0 {
                boundary_pos + 1
            } else {
                boundary_pos
            };
            let expected_new_count = new_level_size.min(group_start + N) - boundary - 1;
            if shared != expected_shared || new_only != expected_new_count {
                return Err(TreeError::MathError);
            }

            let (old_mid, new_mid) = if i == 0 {
                (level.hashes[boundary_pos], level.hashes[boundary_pos])
            } else {
                (old_hash, new_hash)
            };

            let new_child_count = boundary_pos + 1 + new_only;
            children[..boundary_pos].copy_from_slice(&level.hashes[..boundary_pos]);
            children[boundary_pos] = old_mid;
            old_hash = if boundary_pos > 0 {
                hasher.hash_children(&children[..boundary_pos + 1])
            } else {
                old_mid
            };
            children[boundary_pos] = new_mid;
            children[boundary_pos + 1..new_child_count]
                .copy_from_slice(level.new_hashes());
            new_hash = if new_child_count > 1 {
                hasher.hash_children(&children[..new_child_count])
            } else {
                new_mid
            };

            old_level_size = old_level_size.div_ceil(N);
            new_level_size = new_level_size.div_ceil(N);
        }

        Ok(old_hash == self.old_root && new_hash == self.new_root)
    }

    /// Verify this consistency proof against externally-trusted roots.
    pub fn verify_against<H: Hasher>(
        &self,
        hasher: &H,
        trusted_old_root: Hash,
        trusted_new_root: Hash,
    ) -> Result<bool, TreeError> {
        if self.old_root != trusted_old_root || self.new_root != trusted_new_root {
            return Ok(false);
        }
        self.verify(hasher)
    }

    /// Verify this consistency proof against a trusted old root.
    ///
    /// If verification succeeds, the caller can trust `self.new_root`. A root
    /// does not commit to the leaf count, so also check `self.old_size`
    /// against the size you track.
    pub fn verify_transition<H: Hasher>(
        &self,
        hasher: &H,
        trusted_old_root: Hash,
    ) -> Result<bool, TreeError> {
        self.verify_against(hasher, trusted_old_root, self.new_root)
    }

    /// Update an existing inclusion proof from `old_root` to `new_root`.
    ///
    /// Given a valid `NaryProof` for some leaf against `old_root`, produces
    /// a valid `NaryProof` for the same leaf against `new_root` using only
    /// the data in this consistency proof. Returns an error if `old_proof`
    /// does not verify, or if its `tree_size` is not `old_size`.
    pub fn update_inclusion_proof<H: Hasher>(
        &self,
        old_proof: &NaryProof<N, MAX_DEPTH>,
        hasher: &H,
    ) -> Result<NaryProof<N, MAX_DEPTH>, TreeError> {
        // A root does not commit to the leaf count, so the sizes must match too.
        if old_proof.root != self.old_root || old_proof.tree_size != self.old_size {
            return Err(TreeError::MathError);
        }
        if !self.verify(hasher)? {
            return Err(TreeError::MathError);
        }
        if old_proof.leaf_index >= self.old_size {
            return Err(TreeError::IndexOutOfRange {
                index: old_proof.leaf_index,
                size: self.old_size,
            });
        }
        // The result reuses `old_proof`'s siblings. An invalid one could make
        // the loop below panic or return a proof that does not verify.
        if !old_proof.verify(hasher)? {
            return Err(TreeError::MathError);
        }

        if self.old_size == self.new_size {
            return Err(TreeError::NoUpdateNeeded);
        }

        let mut new_levels = [ProofLevel::<N>::EMPTY; MAX_DEPTH];
        let mut old_level_size = u64_to_usize(self.old_size)?;
        let mut member_idx = u64_to_usize(old_proof.leaf_index)?;
        let mut new_boundary_hash = [0u8; 32];
        let mut children = [[0u8; 32]; N];

        for (tree_level, level) in self.levels[..self.level_count].iter().enumerate() {
            let boundary = old_level_size - 1;
            let boundary_pos = boundary % N;
            let member_pos = member_idx % N;

            let new_only = level.new_count as usize;

            if member_idx / N != boundary / N {
                if tree_level < old_proof.level_count {
                    new_levels[tree_level] = old_proof.levels[tree_level];
                }
            } else {
                let mut group = [[0u8; 32]; N];
                let old_group_size = if tree_level < old_proof.level_count {
                    let old_level = &old_proof.levels[tree_level];
                    let group_size = (old_level.sibling_count as usize) + 1;
                    group[..member_pos]
                        .copy_from_slice(&old_level.siblings[..member_pos]);
                    if member_pos + 1 < group_size {
                        group[member_pos + 1..group_size].copy_from_slice(
                            &old_level.siblings[member_pos..group_size - 1],
                        );
                    }
                    group_size
                } else {
                    1
                };

                if tree_level > 0 && member_pos != boundary_pos {
                    group[boundary_pos] = new_boundary_hash;
                }

                let new_group_size = old_group_size + new_only;
                if new_only > 0 {
                    group[old_group_size..new_group_size]
                        .copy_from_slice(level.new_hashes());
                }

                let mut siblings = [[0u8; 32]; N];
                siblings[..member_pos].copy_from_slice(&group[..member_pos]);
                if member_pos + 1 < new_group_size {
                    siblings[member_pos..new_group_size - 1]
                        .copy_from_slice(&group[member_pos + 1..new_group_size]);
                }

                new_levels[tree_level] = ProofLevel {
                    position: to_u8(member_pos)?,
                    sibling_count: to_u8(new_group_size - 1)?,
                    siblings,
                };
            }

            let mid = if tree_level == 0 {
                level.hashes[boundary_pos]
            } else {
                new_boundary_hash
            };
            let child_count = boundary_pos + 1 + new_only;
            new_boundary_hash = if child_count == 1 {
                mid
            } else {
                children[..boundary_pos].copy_from_slice(&level.hashes[..boundary_pos]);
                children[boundary_pos] = mid;
                children[boundary_pos + 1..child_count]
                    .copy_from_slice(level.new_hashes());
                hasher.hash_children(&children[..child_count])
            };

            member_idx /= N;
            old_level_size = old_level_size.div_ceil(N);
        }

        Ok(NaryProof {
            root: self.new_root,
            leaf: old_proof.leaf,
            leaf_index: old_proof.leaf_index,
            tree_size: self.new_size,
            level_count: self.level_count,
            levels: new_levels,
        })
    }
}

impl<const N: usize, const MAX_DEPTH: usize> TreeSnapshot<N, MAX_DEPTH> {
    /// Generate an inclusion proof for the leaf at `leaf_index`
    pub fn generate_proof(
        &self,
        leaf_index: u64,
    ) -> Result<NaryProof<N, MAX_DEPTH>, TreeError> {
        if leaf_index >= self.size {
            return Err(TreeError::IndexOutOfRange {
                index: leaf_index,
                size: self.size,
            });
        }

        let leaf_idx = u64_to_usize(leaf_index)?;
        let mut index = leaf_idx;
        let mut levels = [ProofLevel::<N>::EMPTY; MAX_DEPTH];

        #[allow(clippy::needless_range_loop)]
        for level in 0..self.depth {
            let child_pos = index % N;
            let group_start = index - child_pos;
            let group_end = core::cmp::min(group_start + N, self.levels[level].len());
            let group_size = group_end - group_start;

            let mut group = [[0u8; 32]; N];
            self.levels[level].get_group(group_start, group_size, &mut group);
            let mut siblings = [[0u8; 32]; N];
            siblings[..child_pos].copy_from_slice(&group[..child_pos]);
            let rest = group_size - child_pos - 1;
            siblings[child_pos..child_pos + rest]
                .copy_from_slice(&group[child_pos + 1..group_size]);
            let sib_count = group_size - 1;
            levels[level] = ProofLevel {
                position: to_u8(child_pos)?,
                sibling_count: to_u8(sib_count)?,
                siblings,
            };

            index /= N;
        }

        Ok(NaryProof {
            root: self.root.expect("set prev; qed"),
            leaf: self.levels[0].get(leaf_idx)?,
            leaf_index,
            tree_size: self.size,
            level_count: self.depth,
            levels,
        })
    }

    /// Generate a consistency proof proving the tree at `old_size` is a prefix
    /// of the current tree
    pub fn generate_consistency_proof(
        &self,
        old_size: u64,
        old_root: Hash,
    ) -> Result<ConsistencyProof<N, MAX_DEPTH>, TreeError> {
        if old_size == 0 || self.size == 0 || old_size > self.size {
            return Err(TreeError::IndexOutOfRange {
                index: old_size,
                size: self.size,
            });
        }

        let new_root = self.root.expect("size > 0; qed");
        let mut levels = [ConsistencyLevel::<N>::EMPTY; MAX_DEPTH];

        if old_size == self.size {
            return Ok(ConsistencyProof {
                old_root,
                new_root,
                old_size,
                new_size: self.size,
                level_count: 0,
                levels,
            });
        }

        let mut old_level_size = u64_to_usize(old_size)?;
        let mut new_level_size = u64_to_usize(self.size)?;
        let mut depth = 0usize;

        while old_level_size > 1 || new_level_size > 1 {
            if depth >= MAX_DEPTH {
                return Err(TreeError::MathError);
            }

            let boundary = old_level_size - 1;
            let boundary_pos = boundary % N;
            let group_start = boundary - boundary_pos;
            let shared = if depth == 0 {
                boundary_pos + 1
            } else {
                boundary_pos
            };
            let new_count = new_level_size.min(group_start + N) - boundary - 1;

            let mut hashes = [[0u8; 32]; N];
            self.levels[depth].get_group(group_start, shared, &mut hashes[..shared]);
            self.levels[depth].get_group(
                boundary + 1,
                new_count,
                &mut hashes[shared..shared + new_count],
            );
            levels[depth] = ConsistencyLevel {
                shared_count: to_u8(shared)?,
                new_count: to_u8(new_count)?,
                hashes,
            };

            depth += 1;
            old_level_size = old_level_size.div_ceil(N);
            new_level_size = new_level_size.div_ceil(N);
        }

        Ok(ConsistencyProof {
            old_root,
            new_root,
            old_size,
            new_size: self.size,
            level_count: depth,
            levels,
        })
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
        LeanIMT,
        test_util::*,
    };

    fn build_snapshots<const N: usize, const MAX_DEPTH: usize>(
        leaves: &[Hash],
    ) -> Vec<(u64, Hash, TreeSnapshot<N, MAX_DEPTH>)> {
        let mut tree = LeanIMT::<XorHasher, N, MAX_DEPTH>::new(XorHasher);
        let mut snapshots = Vec::new();
        for &l in leaves {
            tree.insert(l).unwrap();
            let snap = tree.snapshot();
            let root = snap.root().unwrap();
            let size = snap.size();
            snapshots.push((size, root, snap));
        }
        snapshots
    }

    /// Verify generate + verify for every (old, new) pair up to `count` leaves.
    fn verify_consistency_all_pairs<const N: usize>(count: u32) {
        let leaves: Vec<Hash> = (1..=count).map(leaf).collect();
        let snaps = build_snapshots::<N, 32>(&leaves);
        for i in 0..snaps.len() {
            for j in i..snaps.len() {
                let proof = snaps[j]
                    .2
                    .generate_consistency_proof(snaps[i].0, snaps[i].1)
                    .unwrap();
                assert!(
                    proof.verify(&XorHasher).unwrap(),
                    "N={} consistency failed for {} -> {}",
                    N,
                    i + 1,
                    j + 1
                );
            }
        }
    }

    /// Verify update_inclusion_proof for every (old, new, member) triple,
    /// and assert the result equals a freshly generated proof.
    fn verify_update_all_pairs<const N: usize>(count: u32) {
        let leaves: Vec<Hash> = (1..=count).map(leaf).collect();
        let snaps = build_snapshots::<N, 32>(&leaves);
        for i in 0..snaps.len() {
            for j in i..snaps.len() {
                let cp = snaps[j]
                    .2
                    .generate_consistency_proof(snaps[i].0, snaps[i].1)
                    .unwrap();
                if i == j {
                    // Same-size update returns NoUpdateNeeded
                    let ip = snaps[i].2.generate_proof(0).unwrap();
                    let err = cp.update_inclusion_proof(&ip, &XorHasher).unwrap_err();
                    assert_eq!(err, TreeError::NoUpdateNeeded);
                    continue;
                }
                for m in 0..=i {
                    let old_ip = snaps[i].2.generate_proof(m as u64).unwrap();
                    let updated = cp.update_inclusion_proof(&old_ip, &XorHasher).unwrap();
                    assert!(
                        updated.verify(&XorHasher).unwrap(),
                        "N={} update failed: member {} from {} -> {}",
                        N,
                        m,
                        i + 1,
                        j + 1,
                    );
                    assert_eq!(updated.root, snaps[j].1);
                    assert_eq!(updated.leaf, old_ip.leaf);
                    assert_eq!(updated.leaf_index, old_ip.leaf_index);
                    let fresh = snaps[j].2.generate_proof(m as u64).unwrap();
                    assert_eq!(
                        updated,
                        fresh,
                        "N={} update mismatch: member {} from {} -> {}",
                        N,
                        m,
                        i + 1,
                        j + 1,
                    );
                }
            }
        }
    }

    #[test]
    fn proof_single_leaf() {
        let th = XorHasher;
        let mut tree = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
        let l = leaf(1);
        tree.insert(l).unwrap();
        let snap = tree.snapshot();

        let proof = snap.generate_proof(0).unwrap();
        assert_eq!(proof.leaf, l);
        assert_eq!(proof.root, l);
        assert_eq!(proof.leaf_index, 0);
        assert_eq!(proof.level_count, 0);
        assert!(proof.verify(&th).unwrap());
    }

    #[test]
    fn proof_two_leaves_binary() {
        let h = XorHasher;
        let th = XorHasher;
        let mut tree = LeanIMT::<XorHasher, 2, 32>::new(h.clone());
        let l0 = leaf(1);
        let l1 = leaf(2);
        tree.insert(l0).unwrap();
        tree.insert(l1).unwrap();
        let snap = tree.snapshot();

        let p0 = snap.generate_proof(0).unwrap();
        assert_eq!(p0.leaf, l0);
        assert_eq!(p0.level_count, 1);
        assert_eq!(p0.levels[0].position, 0);
        assert_eq!(p0.levels[0].sibling_count, 1);
        assert_eq!(p0.levels[0].siblings[0], l1);
        assert!(p0.verify(&th).unwrap());

        let p1 = snap.generate_proof(1).unwrap();
        assert_eq!(p1.leaf, l1);
        assert_eq!(p1.levels[0].position, 1);
        assert_eq!(p1.levels[0].sibling_count, 1);
        assert_eq!(p1.levels[0].siblings[0], l0);
        assert!(p1.verify(&th).unwrap());
    }

    #[test]
    fn proof_three_leaves_binary_lifted() {
        let h = XorHasher;
        let th = XorHasher;
        let mut tree = LeanIMT::<XorHasher, 2, 32>::new(h.clone());
        let l0 = leaf(1);
        let l1 = leaf(2);
        let l2 = leaf(3);
        tree.insert(l0).unwrap();
        tree.insert(l1).unwrap();
        tree.insert(l2).unwrap();
        let snap = tree.snapshot();

        let p = snap.generate_proof(2).unwrap();
        assert_eq!(p.level_count, 2);
        assert_eq!(p.levels[0].sibling_count, 0);
        let h01 = th.hash_children(&[l0, l1]);
        assert_eq!(p.levels[1].position, 1);
        assert_eq!(p.levels[1].sibling_count, 1);
        assert_eq!(p.levels[1].siblings[0], h01);
        assert!(p.verify(&th).unwrap());
    }

    #[test]
    fn proof_four_leaves_binary() {
        let h = XorHasher;
        let th = XorHasher;
        let mut tree = LeanIMT::<XorHasher, 2, 32>::new(h.clone());
        let leaves: Vec<Hash> = (1..=4).map(leaf).collect();
        for &l in &leaves {
            tree.insert(l).unwrap();
        }
        let snap = tree.snapshot();

        for i in 0..4u64 {
            let p = snap.generate_proof(i).unwrap();
            assert!(p.verify(&th).unwrap());
            assert_eq!(p.leaf, leaves[i as usize]);
        }
    }

    #[test]
    fn proof_ternary() {
        let h = XorHasher;
        let th = XorHasher;
        let mut tree = LeanIMT::<XorHasher, 3, 32>::new(h.clone());
        let leaves: Vec<Hash> = (1..=4).map(leaf).collect();
        for &l in &leaves {
            tree.insert(l).unwrap();
        }
        let snap = tree.snapshot();

        for i in 0..4u64 {
            let p = snap.generate_proof(i).unwrap();
            assert!(p.verify(&th).unwrap());
        }
    }

    #[test]
    fn proof_quaternary() {
        let h = XorHasher;
        let th = XorHasher;
        let mut tree = LeanIMT::<XorHasher, 4, 32>::new(h.clone());
        let leaves: Vec<Hash> = (1..=5).map(leaf).collect();
        for &l in &leaves {
            tree.insert(l).unwrap();
        }
        let snap = tree.snapshot();

        for i in 0..5u64 {
            let p = snap.generate_proof(i).unwrap();
            assert!(p.verify(&th).unwrap());
        }
    }

    #[test]
    fn verify_rejects_wrong_leaf() {
        let h = XorHasher;
        let th = XorHasher;
        let mut tree = LeanIMT::<XorHasher, 2, 32>::new(h.clone());
        tree.insert(leaf(1)).unwrap();
        tree.insert(leaf(2)).unwrap();
        let snap = tree.snapshot();

        let mut proof = snap.generate_proof(0).unwrap();
        proof.leaf = leaf(99);
        assert!(!proof.verify(&th).unwrap());
    }

    #[test]
    fn verify_rejects_wrong_root() {
        let h = XorHasher;
        let th = XorHasher;
        let mut tree = LeanIMT::<XorHasher, 2, 32>::new(h.clone());
        tree.insert(leaf(1)).unwrap();
        tree.insert(leaf(2)).unwrap();
        let snap = tree.snapshot();

        let mut proof = snap.generate_proof(0).unwrap();
        proof.root = [0xFF; 32];
        assert!(!proof.verify(&th).unwrap());
    }

    #[test]
    fn verify_rejects_wrong_sibling() {
        let h = XorHasher;
        let th = XorHasher;
        let mut tree = LeanIMT::<XorHasher, 2, 32>::new(h.clone());
        tree.insert(leaf(1)).unwrap();
        tree.insert(leaf(2)).unwrap();
        let snap = tree.snapshot();

        let mut proof = snap.generate_proof(0).unwrap();
        proof.levels[0].siblings[0] = [0xFF; 32];
        assert!(!proof.verify(&th).unwrap());
    }

    #[test]
    fn proof_index_out_of_range() {
        let mut tree = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
        tree.insert(leaf(1)).unwrap();
        let snap = tree.snapshot();

        let err = snap.generate_proof(1).unwrap_err();
        assert_eq!(err, TreeError::IndexOutOfRange { index: 1, size: 1 });
    }

    #[cfg(feature = "blake3")]
    #[test]
    fn proof_blake3_round_trip() {
        use crate::Blake3Hasher;
        let h = Blake3Hasher;
        let th = Blake3Hasher;
        let mut tree = LeanIMT::<Blake3Hasher, 2, 32>::new(h);

        for i in 0u8..20 {
            tree.insert(*::blake3::hash(&[i]).as_bytes()).unwrap();
        }
        let snap = tree.snapshot();

        for i in 0..20u64 {
            let proof = snap.generate_proof(i).unwrap();
            assert!(proof.verify(&th).unwrap());
        }
    }

    #[cfg(feature = "wincode")]
    fn verify_wincode_proof_round_trip<const N: usize>(count: u32) {
        let leaves: Vec<Hash> = (1..=count).map(leaf).collect();
        let mut tree = LeanIMT::<XorHasher, N, 32>::new(XorHasher);
        for &l in &leaves {
            tree.insert(l).unwrap();
        }
        let snap = tree.snapshot();
        for i in 0..count as u64 {
            let proof = snap.generate_proof(i).unwrap();
            let bytes = wincode::serialize(&proof).unwrap();
            let decoded: NaryProof<N, 32> = wincode::deserialize(&bytes).unwrap();
            assert_eq!(decoded, proof);
            assert!(decoded.verify(&XorHasher).unwrap());
        }
    }

    #[cfg(feature = "wincode")]
    #[test]
    fn wincode_round_trip_binary() {
        verify_wincode_proof_round_trip::<2>(10);
    }

    #[cfg(feature = "wincode")]
    #[test]
    fn wincode_round_trip_ternary() {
        verify_wincode_proof_round_trip::<3>(10);
    }

    #[cfg(feature = "wincode")]
    #[test]
    fn wincode_round_trip_quaternary() {
        verify_wincode_proof_round_trip::<4>(10);
    }

    #[test]
    fn consistency_same_size_trivial() {
        let mut tree = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
        tree.insert(leaf(1)).unwrap();
        tree.insert(leaf(2)).unwrap();
        let snap = tree.snapshot();
        let root = snap.root().unwrap();
        let proof = snap.generate_consistency_proof(2, root).unwrap();
        assert_eq!(proof.level_count, 0);
        assert!(proof.verify(&XorHasher).unwrap());
    }

    #[test]
    fn consistency_binary_all_pairs_small() {
        verify_consistency_all_pairs::<2>(8);
    }

    #[test]
    fn consistency_ternary_all_pairs_small() {
        verify_consistency_all_pairs::<3>(9);
    }

    #[test]
    fn consistency_quaternary_all_pairs_small() {
        verify_consistency_all_pairs::<4>(8);
    }

    #[test]
    fn consistency_rejects_wrong_old_root() {
        let leaves: Vec<Hash> = (1..=4).map(leaf).collect();
        let snaps = build_snapshots::<2, 32>(&leaves);
        let proof = snaps[3]
            .2
            .generate_consistency_proof(snaps[1].0, snaps[1].1)
            .unwrap();
        let mut tampered = proof;
        tampered.old_root = [0xFF; 32];
        assert!(!tampered.verify(&XorHasher).unwrap());
    }

    #[test]
    fn consistency_rejects_wrong_new_root() {
        let leaves: Vec<Hash> = (1..=4).map(leaf).collect();
        let snaps = build_snapshots::<2, 32>(&leaves);
        let proof = snaps[3]
            .2
            .generate_consistency_proof(snaps[1].0, snaps[1].1)
            .unwrap();
        let mut tampered = proof;
        tampered.new_root = [0xFF; 32];
        assert!(!tampered.verify(&XorHasher).unwrap());
    }

    #[test]
    fn consistency_rejects_tampered_hash() {
        let leaves: Vec<Hash> = (1..=4).map(leaf).collect();
        let snaps = build_snapshots::<2, 32>(&leaves);
        let proof = snaps[3]
            .2
            .generate_consistency_proof(snaps[1].0, snaps[1].1)
            .unwrap();
        let mut tampered = proof;
        if tampered.level_count > 0 {
            tampered.levels[0].hashes[0] = [0xFF; 32];
        }
        assert!(!tampered.verify(&XorHasher).unwrap());
    }

    #[test]
    fn consistency_rejects_invalid_sizes() {
        let mut tree = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
        tree.insert(leaf(1)).unwrap();
        let snap = tree.snapshot();
        assert!(snap.generate_consistency_proof(0, [0u8; 32]).is_err());
        assert!(snap.generate_consistency_proof(2, [0u8; 32]).is_err());
    }

    #[test]
    fn consistency_verify_rejects_zero_sizes() {
        let proof = ConsistencyProof::<2, 32> {
            old_root: [0u8; 32],
            new_root: [0u8; 32],
            old_size: 0,
            new_size: 1,
            level_count: 0,
            levels: [ConsistencyLevel::EMPTY; 32],
        };
        assert!(proof.verify(&XorHasher).is_err());
    }

    #[test]
    fn consistency_verify_rejects_old_gt_new() {
        let proof = ConsistencyProof::<2, 32> {
            old_root: [0u8; 32],
            new_root: [0u8; 32],
            old_size: 5,
            new_size: 3,
            level_count: 0,
            levels: [ConsistencyLevel::EMPTY; 32],
        };
        assert!(proof.verify(&XorHasher).is_err());
    }

    #[test]
    fn update_same_size() {
        let mut tree = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
        tree.insert(leaf(1)).unwrap();
        tree.insert(leaf(2)).unwrap();
        let snap = tree.snapshot();
        let root = snap.root().unwrap();
        let cp = snap.generate_consistency_proof(2, root).unwrap();
        let ip = snap.generate_proof(0).unwrap();
        let err = cp.update_inclusion_proof(&ip, &XorHasher).unwrap_err();
        assert_eq!(err, TreeError::NoUpdateNeeded);
    }

    #[test]
    fn update_binary_all_pairs() {
        verify_update_all_pairs::<2>(8);
    }

    #[test]
    fn update_ternary_all_pairs() {
        verify_update_all_pairs::<3>(9);
    }

    #[test]
    fn update_quaternary_all_pairs() {
        verify_update_all_pairs::<4>(8);
    }

    #[test]
    fn update_rejects_wrong_root() {
        let leaves: Vec<Hash> = (1..=4).map(leaf).collect();
        let snaps = build_snapshots::<2, 32>(&leaves);
        let cp = snaps[3]
            .2
            .generate_consistency_proof(snaps[1].0, snaps[1].1)
            .unwrap();
        let mut bad_proof = snaps[1].2.generate_proof(0).unwrap();
        bad_proof.root = [0xFF; 32];
        assert!(cp.update_inclusion_proof(&bad_proof, &XorHasher).is_err());
    }

    /// Regression: a transition from a smaller tree with the same root
    /// panicked while slicing the boundary group.
    #[test]
    fn update_rejects_size_mismatch() {
        // given a proof from a 2-leaf tree
        let mut tracked = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
        tracked.insert(leaf(1)).unwrap();
        tracked.insert(leaf(2)).unwrap();
        let root = tracked.root().unwrap();
        let proof = tracked.snapshot().generate_proof(0).unwrap();

        // when a 1-leaf tree whose leaf is that root grows by one leaf
        let mut other = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
        other.insert(root).unwrap();
        other.insert(leaf(99)).unwrap();
        let cp = other
            .snapshot()
            .generate_consistency_proof(1, root)
            .unwrap();
        assert!(cp.verify_transition(&XorHasher, root).unwrap());

        // then the update is rejected
        assert_eq!(
            cp.update_inclusion_proof(&proof, &XorHasher),
            Err(TreeError::MathError)
        );
    }

    /// Regression: an old proof with more siblings than `N - 1` panicked
    /// while copying its boundary group.
    #[test]
    fn update_rejects_malformed_old_proof() {
        // given a 2 -> 3 leaf transition and leaf 1's proof
        let leaves: Vec<Hash> = (1..=3).map(leaf).collect();
        let snaps = build_snapshots::<2, 32>(&leaves);
        let cp = snaps[2]
            .2
            .generate_consistency_proof(snaps[1].0, snaps[1].1)
            .unwrap();
        let mut proof = snaps[1].2.generate_proof(1).unwrap();

        // when the proof claims two siblings in a binary tree
        proof.levels[0].sibling_count = 2;

        // then the update is rejected
        assert_eq!(
            cp.update_inclusion_proof(&proof, &XorHasher),
            Err(TreeError::MathError)
        );
    }

    #[cfg(feature = "wincode")]
    fn verify_wincode_consistency_round_trip<const N: usize>() {
        let leaves: Vec<Hash> = (1..=6).map(leaf).collect();
        let snaps = build_snapshots::<N, 32>(&leaves);
        let proof = snaps[5]
            .2
            .generate_consistency_proof(snaps[2].0, snaps[2].1)
            .unwrap();
        let bytes = wincode::serialize(&proof).unwrap();
        let decoded: ConsistencyProof<N, 32> = wincode::deserialize(&bytes).unwrap();
        assert_eq!(decoded, proof);
        assert!(decoded.verify(&XorHasher).unwrap());
    }

    #[cfg(feature = "wincode")]
    #[test]
    fn consistency_wincode_binary() {
        verify_wincode_consistency_round_trip::<2>();
    }

    #[cfg(feature = "wincode")]
    #[test]
    fn consistency_wincode_ternary() {
        verify_wincode_consistency_round_trip::<3>();
    }

    #[cfg(feature = "wincode")]
    #[test]
    fn consistency_wincode_quaternary() {
        verify_wincode_consistency_round_trip::<4>();
    }

    #[test]
    fn verify_rejects_level_count_exceeds_max_depth() {
        let proof = NaryProof::<2, 4> {
            root: [0u8; 32],
            leaf: [0u8; 32],
            leaf_index: 0,
            tree_size: 2,
            level_count: 5,
            levels: [ProofLevel::EMPTY; 4],
        };
        assert!(proof.verify(&XorHasher).is_err());
    }

    #[test]
    fn verify_rejects_position_exceeds_n() {
        let mut tree = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
        tree.insert(leaf(1)).unwrap();
        tree.insert(leaf(2)).unwrap();
        let snap = tree.snapshot();
        let mut proof = snap.generate_proof(0).unwrap();
        proof.levels[0].position = 2;
        assert!(proof.verify(&XorHasher).is_err());
    }

    #[test]
    fn verify_rejects_sibling_count_exceeds_n() {
        let mut tree = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
        tree.insert(leaf(1)).unwrap();
        tree.insert(leaf(2)).unwrap();
        let snap = tree.snapshot();
        let mut proof = snap.generate_proof(0).unwrap();
        proof.levels[0].sibling_count = 2;
        assert!(proof.verify(&XorHasher).is_err());
    }

    #[test]
    fn consistency_verify_rejects_level_count_exceeds_max_depth() {
        let proof = ConsistencyProof::<2, 4> {
            old_root: [0u8; 32],
            new_root: [0u8; 32],
            old_size: 1,
            new_size: 2,
            level_count: 5,
            levels: [ConsistencyLevel::EMPTY; 4],
        };
        assert!(proof.verify(&XorHasher).is_err());
    }

    #[test]
    fn verify_rejects_spoofed_leaf_index() {
        let h = XorHasher;
        let th = XorHasher;
        let mut tree = LeanIMT::<XorHasher, 2, 32>::new(h.clone());
        tree.insert(leaf(1)).unwrap();
        tree.insert(leaf(2)).unwrap();
        let snap = tree.snapshot();

        let mut proof = snap.generate_proof(0).unwrap();
        proof.leaf_index = 1; // spoof: claim index 1 instead of 0
        assert!(proof.verify(&th).is_err());
    }

    #[test]
    fn verify_rejects_padded_levels() {
        let h = XorHasher;
        let th = XorHasher;
        let mut tree = LeanIMT::<XorHasher, 2, 32>::new(h.clone());
        tree.insert(leaf(1)).unwrap();
        tree.insert(leaf(2)).unwrap();
        let snap = tree.snapshot();

        let mut proof = snap.generate_proof(0).unwrap();
        // Pad with an extra zero-sibling level
        proof.level_count = 2;
        proof.levels[1] = ProofLevel::EMPTY;
        assert!(proof.verify(&th).is_err());
    }

    #[test]
    fn verify_rejects_truncated_levels() {
        let h = XorHasher;
        let th = XorHasher;
        let mut tree = LeanIMT::<XorHasher, 2, 32>::new(h.clone());
        for i in 1..=4u32 {
            tree.insert(leaf(i)).unwrap();
        }
        let snap = tree.snapshot();

        let mut proof = snap.generate_proof(2).unwrap();
        // Truncate: claim fewer levels than the tree requires
        proof.level_count = 1;
        assert!(proof.verify(&th).is_err());
    }

    /// Regression: a lift at level 0 let node (1, 0) verify as leaf 0.
    #[test]
    fn verify_rejects_internal_node_as_leaf() {
        // given a 4-leaf binary tree
        let mut tree = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
        for i in 1..=4 {
            tree.insert(leaf(i)).unwrap();
        }
        let snap = tree.snapshot();

        // when node (1, 0) claims leaf 0 with no sibling at level 0
        let mut levels = [ProofLevel::EMPTY; 32];
        levels[1] = ProofLevel {
            position: 0,
            sibling_count: 1,
            siblings: [snap.get_node(1, 1).unwrap(), [0u8; 32]],
        };
        let forged = NaryProof::<2, 32> {
            root: snap.root().unwrap(),
            leaf: snap.get_node(1, 0).unwrap(),
            leaf_index: 0,
            tree_size: 4,
            level_count: 2,
            levels,
        };

        // then the proof is rejected
        assert_eq!(forged.verify(&XorHasher), Err(TreeError::MathError));
    }

    /// Every level accepts only the sibling count that `leaf_index` and
    /// `tree_size` imply.
    fn verify_rejects_spoofed_sibling_count_up_to<const N: usize>(count: u32) {
        let leaves: Vec<Hash> = (1..=count).map(leaf).collect();
        for (size, _, snap) in build_snapshots::<N, 32>(&leaves) {
            for index in 0..size {
                let proof = snap.generate_proof(index).unwrap();
                for level in 0..proof.level_count {
                    let honest = proof.levels[level].sibling_count;
                    for spoofed in (0..=u8::MAX).filter(|&c| c != honest) {
                        let mut bad = proof.clone();
                        bad.levels[level].sibling_count = spoofed;
                        assert_eq!(
                            bad.verify(&XorHasher),
                            Err(TreeError::MathError),
                            "N={N} size={size} index={index} level={level} \
                             sibling_count={spoofed}",
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn verify_rejects_spoofed_sibling_count() {
        verify_rejects_spoofed_sibling_count_up_to::<2>(17);
        verify_rejects_spoofed_sibling_count_up_to::<3>(28);
        verify_rejects_spoofed_sibling_count_up_to::<4>(17);
    }

    #[test]
    fn verify_rejects_tree_size_zero() {
        let proof = NaryProof::<2, 4> {
            root: [0u8; 32],
            leaf: [0u8; 32],
            leaf_index: 0,
            tree_size: 0,
            level_count: 0,
            levels: [ProofLevel::EMPTY; 4],
        };
        assert!(proof.verify(&XorHasher).is_err());
    }

    #[test]
    fn verify_rejects_leaf_index_ge_tree_size() {
        let h = XorHasher;
        let th = XorHasher;
        let mut tree = LeanIMT::<XorHasher, 2, 32>::new(h.clone());
        tree.insert(leaf(1)).unwrap();
        tree.insert(leaf(2)).unwrap();
        let snap = tree.snapshot();

        let mut proof = snap.generate_proof(0).unwrap();
        proof.leaf_index = 2; // >= tree_size of 2
        assert!(proof.verify(&th).is_err());
    }

    #[test]
    fn verify_rejects_tree_size_exceeding_max_depth() {
        // tree_size=32 with N=2 requires depth 5, but MAX_DEPTH=4.
        // Must not panic on self.levels[..5] slice.
        let proof = NaryProof::<2, 4> {
            root: [0u8; 32],
            leaf: [0u8; 32],
            leaf_index: 0,
            tree_size: 32,
            level_count: 5,
            levels: [ProofLevel::EMPTY; 4],
        };
        match proof.verify(&XorHasher) {
            Err(TreeError::InvalidProofDepth {
                expected: 5,
                actual: 5,
            }) => {}
            other => panic!("expected InvalidProofDepth, got {other:?}"),
        }
    }
}
