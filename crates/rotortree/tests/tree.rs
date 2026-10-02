#![cfg_attr(feature = "concurrent", allow(unused_mut))]

use rotortree::{
    Hash,
    Hasher,
    LeanIMT,
    TreeError,
    test_util::*,
};

/// 130 leaves, N=3: group (126,127,128) spans chunk boundary → get_group slow path.
#[test]
fn cross_chunk_get_group_ternary() {
    // given
    let mut tree = LeanIMT::<XorHasher, 3, 32>::new(XorHasher);
    for i in 0..130u32 {
        tree.insert(leaf(i)).unwrap();
    }

    // when
    let snap = tree.snapshot();
    let proof = snap.generate_proof(127).unwrap();

    // then
    assert!(proof.verify(&XorHasher).unwrap());
}

/// 10 sequential + 300 batch exercises extend's 3-phase path (fill tail, full chunks, remainder).
#[test]
fn extend_three_phase_via_insert_many() {
    // given
    let mut seq = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
    let mut batch = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);

    let first: Vec<Hash> = (0..10u32).map(leaf).collect();
    let second: Vec<Hash> = (10..310u32).map(leaf).collect();
    let all: Vec<Hash> = (0..310u32).map(leaf).collect();

    for &l in &all {
        seq.insert(l).unwrap();
    }
    for &l in &first {
        batch.insert(l).unwrap();
    }

    // when
    batch.insert_many(&second).unwrap();

    // then
    assert_eq!(batch.root(), seq.root());
    assert_eq!(batch.size(), 310);
}

/// 33,000 leaves → 257 chunks → triggers freeze_pending at 256.
#[test]
fn segment_freeze_large_batch() {
    // given
    let leaves: Vec<Hash> = (0..33_000u32).map(leaf).collect();
    let mut seq = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
    for &l in &leaves {
        seq.insert(l).unwrap();
    }

    // when
    let mut batch = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
    batch.insert_many(&leaves).unwrap();

    // then
    assert_eq!(batch.root(), seq.root());
    assert_eq!(batch.size(), 33_000);

    let snap = batch.snapshot();
    for &idx in &[0u64, 1000, 16383, 32767, 32999] {
        let proof = snap.generate_proof(idx).unwrap();
        assert!(
            proof.verify(&XorHasher).unwrap(),
            "proof failed for idx {idx}"
        );
    }
}

/// Insert 200, snapshot, insert 200 more → CoW on Arc-shared chunks.
#[test]
fn snapshot_cow_on_shared_chunks() {
    // given
    let mut tree = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
    for i in 0..200u32 {
        tree.insert(leaf(i)).unwrap();
    }
    let snap = tree.snapshot();
    let snap_root = snap.root();
    let snap_size = snap.size();

    // when
    for i in 200..400u32 {
        tree.insert(leaf(i)).unwrap();
    }

    // then
    assert_eq!(snap.root(), snap_root);
    assert_eq!(snap.size(), snap_size);
    assert_eq!(tree.size(), 400);
    assert!(tree.root().is_some());

    let tree_snap = tree.snapshot();
    let p_old = snap.generate_proof(0).unwrap();
    assert!(p_old.verify(&XorHasher).unwrap());
    let p_new = tree_snap.generate_proof(399).unwrap();
    assert!(p_new.verify(&XorHasher).unwrap());
}

#[test]
fn snapshot_get_node_and_level_len() {
    // given
    let mut tree = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
    for i in 0..20u32 {
        tree.insert(leaf(i)).unwrap();
    }
    let snap = tree.snapshot();
    let depth = snap.depth();

    // then
    assert_eq!(snap.level_len(0), 20);
    assert_eq!(snap.level_len(1), 10);
    assert_eq!(snap.level_len(depth), 1);
    assert_eq!(snap.level_len(depth + 1), 0);

    let th = XorHasher;
    assert_eq!(snap.get_node(0, 0).unwrap(), leaf(0));
    assert_eq!(snap.get_node(0, 19).unwrap(), leaf(19));
    let expected = th.hash_children(&[leaf(0), leaf(1)]);
    assert_eq!(snap.get_node(1, 0).unwrap(), expected);

    match snap.get_node(depth + 1, 0) {
        Err(TreeError::IndexOutOfRange { .. }) => {}
        other => panic!("expected IndexOutOfRange, got {other:?}"),
    }
}

fn snapshots_at_max_depth<const N: usize, const DEPTH: usize>(
    mut check: impl FnMut(&rotortree::TreeSnapshot<N, DEPTH>),
) {
    let capacity = N.pow(DEPTH as u32);
    for batched in [false, true] {
        for count in (capacity / N + 1)..=capacity {
            let mut tree = LeanIMT::<XorHasher, N, DEPTH>::new(XorHasher);
            let leaves: Vec<Hash> = (0..count as u32).map(leaf).collect();
            if batched {
                tree.insert_many(&leaves).unwrap();
            } else {
                for hash in leaves {
                    tree.insert(hash).unwrap();
                }
            }
            let snapshot = tree.snapshot();
            assert_eq!(snapshot.depth(), DEPTH);
            check(&snapshot);
            // The root access must not change inclusion proof generation.
            for index in 0..count as u64 {
                assert!(
                    snapshot
                        .generate_proof(index)
                        .unwrap()
                        .verify(&XorHasher)
                        .unwrap()
                );
            }
        }
    }
}

#[test]
fn snapshot_level_len_returns_one_at_max_depth() {
    snapshots_at_max_depth::<2, 1>(|snapshot| {
        assert_eq!(snapshot.level_len(snapshot.depth()), 1);
    });
    snapshots_at_max_depth::<2, 3>(|snapshot| {
        assert_eq!(snapshot.level_len(snapshot.depth()), 1);
    });
    snapshots_at_max_depth::<3, 2>(|snapshot| {
        assert_eq!(snapshot.level_len(snapshot.depth()), 1);
    });
}

#[test]
fn snapshot_get_node_returns_root_at_max_depth() {
    fn check<const N: usize, const DEPTH: usize>(
        snapshot: &rotortree::TreeSnapshot<N, DEPTH>,
    ) {
        assert_eq!(
            snapshot.get_node(snapshot.depth(), 0),
            Ok(snapshot.root().unwrap())
        );
        assert_eq!(
            snapshot.get_node(snapshot.depth(), 1),
            Err(TreeError::IndexOutOfRange { index: 1, size: 1 })
        );
        assert_eq!(snapshot.level_len(snapshot.depth() + 1), 0);
        assert_eq!(
            snapshot.get_node(snapshot.depth() + 1, 0),
            Err(TreeError::IndexOutOfRange { index: 0, size: 0 })
        );
    }
    snapshots_at_max_depth::<2, 1>(check);
    snapshots_at_max_depth::<2, 3>(check);
    snapshots_at_max_depth::<3, 2>(check);
}

#[test]
fn snapshot_root_access_preserves_empty_and_single_leaf_behavior() {
    let mut tree = LeanIMT::<XorHasher, 2, 1>::new(XorHasher);
    let empty = tree.snapshot();
    assert_eq!(empty.level_len(0), 0);
    assert_eq!(
        empty.get_node(0, 0),
        Err(TreeError::IndexOutOfRange { index: 0, size: 0 })
    );
    tree.insert(leaf(7)).unwrap();
    let single = tree.snapshot();
    assert_eq!(single.depth(), 0);
    assert_eq!(single.level_len(0), 1);
    assert_eq!(single.get_node(0, 0), Ok(leaf(7)));
    assert_eq!(
        single.get_node(0, 1),
        Err(TreeError::IndexOutOfRange { index: 1, size: 1 })
    );
}

#[test]
fn proof_for_last_leaf() {
    // given
    let mut tree = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
    for i in 0..100u32 {
        tree.insert(leaf(i)).unwrap();
    }

    // when
    let snap = tree.snapshot();
    let proof = snap.generate_proof(99).unwrap();

    // then
    assert!(proof.verify(&XorHasher).unwrap());
    assert_eq!(proof.leaf, leaf(99));
}

/// 4 leaves (depth=2), 5th leaf increases depth to 3. All proofs must verify.
#[test]
fn proof_after_depth_increase() {
    // given
    let mut tree = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
    for i in 0..4u32 {
        tree.insert(leaf(i)).unwrap();
    }
    assert_eq!(tree.depth(), 2);

    // when
    tree.insert(leaf(4)).unwrap();

    // then
    assert_eq!(tree.depth(), 3);
    let snap = tree.snapshot();
    for i in 0..5u64 {
        let proof = snap.generate_proof(i).unwrap();
        assert!(
            proof.verify(&XorHasher).unwrap(),
            "proof failed for leaf {i}"
        );
    }
}

#[test]
fn proof_verify_rejects_bad_level_count() {
    // given
    let mut tree = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
    for i in 0..10u32 {
        tree.insert(leaf(i)).unwrap();
    }
    let snap = tree.snapshot();
    let mut proof = snap.generate_proof(0).unwrap();

    // when
    proof.level_count = 33; // > MAX_DEPTH

    // then
    match proof.verify(&XorHasher) {
        Err(TreeError::InvalidProofDepth { .. }) => {}
        other => panic!("expected InvalidProofDepth, got {other:?}"),
    }
}

#[test]
fn proof_verify_rejects_bad_sibling_count() {
    // given
    let mut tree = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
    for i in 0..10u32 {
        tree.insert(leaf(i)).unwrap();
    }
    let snap = tree.snapshot();
    let mut proof = snap.generate_proof(0).unwrap();

    // when
    for level in &mut proof.levels[..proof.level_count] {
        if level.sibling_count > 0 {
            level.sibling_count = 2;
            break;
        }
    }

    // then
    match proof.verify(&XorHasher) {
        Err(TreeError::MathError) => {}
        other => panic!("expected MathError, got {other:?}"),
    }
}

#[test]
fn proof_verify_rejects_bad_position() {
    // given
    let mut tree = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
    for i in 0..10u32 {
        tree.insert(leaf(i)).unwrap();
    }
    let snap = tree.snapshot();
    let mut proof = snap.generate_proof(0).unwrap();

    // when
    for level in &mut proof.levels[..proof.level_count] {
        if level.sibling_count > 0 {
            level.position = level.sibling_count + 1;
            break;
        }
    }

    // then
    match proof.verify(&XorHasher) {
        Err(TreeError::MathError) => {}
        other => panic!("expected MathError, got {other:?}"),
    }
}

#[test]
fn large_branching_factor_n16() {
    // given
    let mut tree = LeanIMT::<XorHasher, 16, 8>::new(XorHasher);
    for i in 0..300u32 {
        tree.insert(leaf(i)).unwrap();
    }

    // then
    assert_eq!(tree.size(), 300);
    assert!(tree.root().is_some());

    let snap = tree.snapshot();
    for &idx in &[0u64, 15, 16, 17, 255, 256, 299] {
        let proof = snap.generate_proof(idx).unwrap();
        assert!(
            proof.verify(&XorHasher).unwrap(),
            "proof failed for idx {idx}"
        );
    }
}

/// N=2, MAX_DEPTH=3 → capacity 8. Insert 8 (ok), 9th → MaxDepthExceeded.
#[test]
fn near_max_depth_binary() {
    // given
    let mut tree = LeanIMT::<XorHasher, 2, 3>::new(XorHasher);
    for i in 0..7u32 {
        tree.insert(leaf(i)).unwrap();
    }
    assert_eq!(tree.depth(), 3);

    // when
    tree.insert(leaf(7)).unwrap();
    assert_eq!(tree.depth(), 3);
    assert_eq!(tree.size(), 8);

    // then
    match tree.insert(leaf(8)) {
        Err(TreeError::MaxDepthExceeded { max_depth: 3 }) => {}
        other => panic!("expected MaxDepthExceeded {{ max_depth: 3 }}, got {other:?}"),
    }
}

#[test]
fn insert_many_single_leaf() {
    // given
    let mut single = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
    single.insert(leaf(42)).unwrap();

    // when
    let mut batch = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
    batch.insert_many(&[leaf(42)]).unwrap();

    // then
    assert_eq!(single.root(), batch.root());
    assert_eq!(single.size(), batch.size());
}

/// Two insert_many calls of exactly CHUNK_SIZE (128) each.
#[test]
fn insert_many_exact_chunk_size() {
    // given
    let chunk1: Vec<Hash> = (0..128u32).map(leaf).collect();
    let chunk2: Vec<Hash> = (128..256u32).map(leaf).collect();
    let all: Vec<Hash> = (0..256u32).map(leaf).collect();

    let mut seq = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
    for &l in &all {
        seq.insert(l).unwrap();
    }

    // when
    let mut batch = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
    batch.insert_many(&chunk1).unwrap();
    batch.insert_many(&chunk2).unwrap();

    // then
    assert_eq!(batch.root(), seq.root());
    assert_eq!(batch.size(), 256);
}

#[cfg(feature = "parallel")]
#[test]
fn parallel_threshold_boundary() {
    // given
    let small: Vec<Hash> = (0..9u32).map(leaf).collect();
    let large: Vec<Hash> = (0..500u32).map(leaf).collect();

    // when
    let mut seq_small = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
    for &l in &small {
        seq_small.insert(l).unwrap();
    }
    let mut batch_small = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
    batch_small.insert_many(&small).unwrap();

    let mut seq_large = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
    for &l in &large {
        seq_large.insert(l).unwrap();
    }
    let mut batch_large = LeanIMT::<XorHasher, 2, 32>::new(XorHasher);
    batch_large.insert_many(&large).unwrap();

    // then
    assert_eq!(batch_small.root(), seq_small.root());
    assert_eq!(batch_large.root(), seq_large.root());
}

/// 8 writers (100 inserts each) + 4 readers verifying snapshot proofs concurrently.
#[cfg(feature = "concurrent")]
#[test]
fn concurrent_snapshot_proof_stress() {
    use std::sync::{
        Arc,
        atomic::{
            AtomicBool,
            Ordering,
        },
    };

    // given
    let tree = Arc::new(LeanIMT::<XorHasher, 2, 32>::new(XorHasher));
    let done = Arc::new(AtomicBool::new(false));

    // when
    std::thread::scope(|s| {
        for t in 0..8u32 {
            let tree = Arc::clone(&tree);
            s.spawn(move || {
                for i in 0..100u32 {
                    tree.insert(leaf(t * 100 + i)).unwrap();
                }
            });
        }

        for _ in 0..4 {
            let tree = Arc::clone(&tree);
            let done = Arc::clone(&done);
            s.spawn(move || {
                while !done.load(Ordering::Relaxed) {
                    let snap = tree.snapshot();
                    let size = snap.size();
                    if size == 0 {
                        continue;
                    }
                    for idx in [0, size / 2, size - 1] {
                        let proof = snap.generate_proof(idx).unwrap();
                        assert!(proof.verify(&XorHasher).unwrap());
                    }
                    if size >= 800 {
                        break;
                    }
                }
            });
        }
    });

    // then
    assert_eq!(tree.size(), 800);
    let snap = tree.snapshot();
    for i in 0..800u64 {
        let proof = snap.generate_proof(i).unwrap();
        assert!(proof.verify(&XorHasher).unwrap());
    }
}

/// Internal nodes are the hash of the concatenation of their children.
#[cfg(feature = "blake3")]
#[test]
fn internal_nodes_hash_children() {
    use rotortree::Blake3Hasher;

    // given
    let leaves: Vec<Hash> = (0..4u32).map(leaf).collect();
    let mut tree = LeanIMT::<Blake3Hasher, 2, 32>::new(Blake3Hasher);
    tree.insert_many(&leaves).unwrap();

    let snap = tree.snapshot();
    let internal_left = snap.get_node(1, 0).unwrap();
    let internal_right = snap.get_node(1, 1).unwrap();

    // when
    let th = Blake3Hasher;
    let h01 = th.hash_children(&[leaves[0], leaves[1]]);
    let h23 = th.hash_children(&[leaves[2], leaves[3]]);

    // then
    assert_eq!(internal_left, h01);
    assert_eq!(internal_right, h23);
    assert_eq!(tree.root().unwrap(), th.hash_children(&[h01, h23]));
}
