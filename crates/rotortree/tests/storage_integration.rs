#![cfg(feature = "storage")]

use std::sync::Arc;

use rotortree::{
    CheckpointMeta,
    CheckpointPolicy,
    FlushPolicy,
    Hash,
    RotorTree,
    RotorTreeConfig,
    RotorTreeError,
    StorageError,
    TieringConfig,
    test_util::*,
    write_test_meta,
};

fn manual_config(dir: &std::path::Path) -> RotorTreeConfig {
    RotorTreeConfig {
        path: dir.to_path_buf(),
        flush_policy: FlushPolicy::Manual,
        checkpoint_policy: CheckpointPolicy::default(),
        tiering: TieringConfig::default(),
        verify_checkpoint: true,
    }
}

#[test]
fn open_empty_close_reopen() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    assert_eq!(tree.root(), None);
    assert_eq!(tree.size(), 0);
    tree.close().unwrap();

    // when
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    // then
    assert_eq!(tree.root(), None);
    assert_eq!(tree.size(), 0);
    tree.close().unwrap();
}

#[test]
fn insert_close_reopen() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    let (root, _token) = tree.insert(leaf(1)).unwrap();
    tree.flush().unwrap();
    let size = tree.size();
    // when
    tree.close().unwrap();

    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    // then
    assert_eq!(tree.root(), Some(root));
    assert_eq!(tree.size(), size);
    tree.close().unwrap();
}

#[test]
fn insert_many_close_reopen() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let leaves: Vec<Hash> = (0..10u32).map(leaf).collect();

    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    let (root, _token) = tree.insert_many(&leaves).unwrap();
    tree.flush().unwrap();
    // when
    tree.close().unwrap();

    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    // then
    assert_eq!(tree.root(), Some(root));
    assert_eq!(tree.size(), 10);
    tree.close().unwrap();
}

#[test]
fn many_inserts_close_reopen() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let n = 50u32;

    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    for i in 0..n {
        tree.insert(leaf(i)).unwrap();
    }
    tree.flush().unwrap();
    let root = tree.root();
    let snap = tree.snapshot();
    // Verify all proofs before close.
    for i in 0..n as u64 {
        let proof = snap.generate_proof(i).unwrap();
        assert!(proof.verify(&XorHasher).unwrap());
    }
    // when
    tree.close().unwrap();

    // Reopen and verify.
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    assert_eq!(tree.root(), root);
    assert_eq!(tree.size(), n as u64);
    let snap = tree.snapshot();
    for i in 0..n as u64 {
        let proof = snap.generate_proof(i).unwrap();
        // then
        assert!(proof.verify(&XorHasher).unwrap());
    }
    tree.close().unwrap();
}

#[test]
fn truncated_tail_recovery() {
    // given
    let dir = tempfile::tempdir().unwrap();

    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    for i in 0..5u32 {
        tree.insert(leaf(i)).unwrap();
    }
    tree.flush().unwrap();
    let root_after_5 = tree.root().unwrap();
    let size_after_5 = tree.size();

    tree.insert(leaf(5)).unwrap();
    tree.flush().unwrap();
    tree.close().unwrap();

    let wal_path = dir.path().join("wal");
    let data = std::fs::read(&wal_path).unwrap();
    // when: remove last few bytes
    std::fs::write(&wal_path, &data[..data.len() - 10]).unwrap();

    // then: recovery
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    assert_eq!(tree.size(), size_after_5);
    assert_eq!(tree.root(), Some(root_after_5));
    tree.close().unwrap();
}

#[test]
fn crc_corruption_mid_file() {
    // given
    let dir = tempfile::tempdir().unwrap();

    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    for i in 0..3u32 {
        tree.insert(leaf(i)).unwrap();
    }
    tree.flush().unwrap();
    tree.close().unwrap();

    let wal_path = dir.path().join("wal");
    let mut data = std::fs::read(&wal_path).unwrap();
    // when
    let corrupt_offset = data.len() / 2;
    data[corrupt_offset] ^= 0xFF;
    std::fs::write(&wal_path, &data).unwrap();

    // then: error
    let result =
        RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()));
    assert!(result.is_err());
}

#[test]
fn config_mismatch() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    tree.close().unwrap();

    // when, then
    let result =
        RotorTree::<XorHasher, 4, 10>::open(XorHasher, manual_config(dir.path()));
    match result {
        Err(RotorTreeError::Storage(StorageError::ConfigMismatch { .. })) => {}
        Err(e) => panic!("expected ConfigMismatch, got {e:?}"),
        Ok(_) => panic!("expected ConfigMismatch, got Ok"),
    }
}

#[test]
fn durability_token_lifecycle() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    let (_root, token) = tree.insert(leaf(1)).unwrap();

    assert!(!token.is_durable());

    // when
    tree.flush().unwrap();

    // then
    assert!(token.is_durable());

    tree.close().unwrap();
}

#[test]
fn concurrent_insert_recover() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let n_threads = 4;
    let inserts_per_thread = 25u32;
    let total = n_threads * inserts_per_thread as usize;

    let tree = Arc::new(
        RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
            .unwrap(),
    );

    std::thread::scope(|s| {
        for t in 0..n_threads {
            let tree = Arc::clone(&tree);
            // when
            s.spawn(move || {
                for i in 0..inserts_per_thread {
                    let val = (t as u32) * inserts_per_thread + i;
                    tree.insert(leaf(val)).unwrap();
                }
            });
        }
    });

    tree.flush().unwrap();
    // then
    assert_eq!(tree.size(), total as u64);

    let snap = tree.snapshot();
    for i in 0..total as u64 {
        let proof = snap.generate_proof(i).unwrap();
        assert!(proof.verify(&XorHasher).unwrap());
    }

    let root = tree.root();
    let tree = Arc::try_unwrap(tree)
        .ok()
        .expect("other Arc references still held");
    tree.close().unwrap();

    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    assert_eq!(tree.size(), total as u64);
    assert_eq!(tree.root(), root);
    tree.close().unwrap();
}

#[test]
fn recovery_continuation() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    for i in 0..5u32 {
        tree.insert(leaf(i)).unwrap();
    }
    tree.flush().unwrap();
    tree.close().unwrap();

    // when
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    assert_eq!(tree.size(), 5);
    for i in 5..10u32 {
        tree.insert(leaf(i)).unwrap();
    }
    tree.flush().unwrap();
    tree.close().unwrap();

    // then
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    assert_eq!(tree.size(), 10);
    let snap = tree.snapshot();
    for i in 0..10u64 {
        let proof = snap.generate_proof(i).unwrap();
        assert!(proof.verify(&XorHasher).unwrap());
    }
    tree.close().unwrap();
}

#[test]
fn depth_change_persistence() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    // when
    for i in 0..5u32 {
        tree.insert(leaf(i)).unwrap();
    }
    tree.flush().unwrap();
    let depth = tree.depth();
    let root = tree.root();
    assert!(
        depth >= 2,
        "depth should be at least 2 for 5 leaves with N=2"
    );
    tree.close().unwrap();

    // then
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    assert_eq!(tree.depth(), depth);
    assert_eq!(tree.root(), root);
    tree.close().unwrap();
}

#[test]
fn interleaved_single_and_batch() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    // when
    tree.insert(leaf(0)).unwrap();
    tree.insert(leaf(1)).unwrap();
    let batch: Vec<Hash> = (2..7u32).map(leaf).collect();
    tree.insert_many(&batch).unwrap();
    tree.insert(leaf(7)).unwrap();
    tree.insert(leaf(8)).unwrap();
    let batch2: Vec<Hash> = (9..15u32).map(leaf).collect();
    tree.insert_many(&batch2).unwrap();

    tree.flush().unwrap();
    let root = tree.root();
    let size = tree.size();
    assert_eq!(size, 15);
    tree.close().unwrap();

    // then
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    assert_eq!(tree.size(), size);
    assert_eq!(tree.root(), root);

    let snap = tree.snapshot();
    for i in 0..size {
        let proof = snap.generate_proof(i).unwrap();
        assert!(proof.verify(&XorHasher).unwrap());
    }
    tree.close().unwrap();
}

#[test]
fn first_insert_after_recovery() {
    // given
    let dir = tempfile::tempdir().unwrap();

    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    for i in 0..3u32 {
        tree.insert(leaf(i)).unwrap();
    }
    tree.flush().unwrap();
    tree.close().unwrap();

    // when
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    assert_eq!(tree.size(), 3);

    let (root, _) = tree.insert(leaf(3)).unwrap();
    tree.flush().unwrap();
    assert_eq!(tree.size(), 4);
    assert_eq!(tree.root(), Some(root));

    // then
    let snap = tree.snapshot();
    for i in 0..4u64 {
        let proof = snap.generate_proof(i).unwrap();
        assert!(proof.verify(&XorHasher).unwrap());
    }
    tree.close().unwrap();
}

#[test]
fn file_locking() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let _tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    // when, then
    let result =
        RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()));
    match result {
        Err(RotorTreeError::Storage(StorageError::FileLocked)) => {}
        Err(e) => panic!("expected FileLocked, got {e:?}"),
        Ok(_) => panic!("expected FileLocked, got Ok"),
    }
}

#[test]
fn insert_durable_round_trip() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    // when
    let root = tree.insert_durable(leaf(1)).unwrap();
    assert_eq!(tree.root(), Some(root));
    assert_eq!(tree.size(), 1);
    tree.close().unwrap();

    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    // then
    assert_eq!(tree.root(), Some(root));
    assert_eq!(tree.size(), 1);
    tree.close().unwrap();
}

#[test]
fn checkpoint_round_trip() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    let leaves: Vec<Hash> = (0..200u32).map(leaf).collect();
    let (root, _) = tree.insert_many(&leaves).unwrap();
    tree.flush().unwrap();
    // when
    tree.checkpoint().unwrap();

    assert!(dir.path().join("data").join("header.bin").exists());
    assert!(dir.path().join("data").join("checkpoint.meta").exists());

    tree.close().unwrap();

    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    assert_eq!(tree.root(), Some(root));
    assert_eq!(tree.size(), 200);
    let snap = tree.snapshot();
    // then
    for i in 0..200u64 {
        let proof = snap.generate_proof(i).unwrap();
        assert!(proof.verify(&XorHasher).unwrap());
    }
    tree.close().unwrap();
}

#[test]
fn checkpoint_then_more_inserts() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    let batch1: Vec<Hash> = (0..50u32).map(leaf).collect();
    tree.insert_many(&batch1).unwrap();
    tree.flush().unwrap();
    tree.checkpoint().unwrap();

    // when
    let batch2: Vec<Hash> = (50..100u32).map(leaf).collect();
    tree.insert_many(&batch2).unwrap();
    tree.flush().unwrap();

    let root = tree.root();
    tree.close().unwrap();

    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    assert_eq!(tree.root(), root);
    assert_eq!(tree.size(), 100);
    // then
    let snap = tree.snapshot();
    for i in 0..100u64 {
        let proof = snap.generate_proof(i).unwrap();
        assert!(proof.verify(&XorHasher).unwrap());
    }
    tree.close().unwrap();
}

#[test]
fn checkpoint_manual_explicit() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    for i in 0..20u32 {
        tree.insert(leaf(i)).unwrap();
    }
    tree.flush().unwrap();

    assert!(!dir.path().join("data").exists());

    // when
    tree.checkpoint().unwrap();

    assert!(dir.path().join("data").join("header.bin").exists());
    assert!(dir.path().join("data").join("checkpoint.meta").exists());

    let root = tree.root();
    tree.close().unwrap();

    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    // then
    assert_eq!(tree.root(), root);
    assert_eq!(tree.size(), 20);
    tree.close().unwrap();
}

#[test]
fn checkpoint_on_close_policy() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let config = RotorTreeConfig {
        path: dir.path().to_path_buf(),
        flush_policy: FlushPolicy::Manual,
        checkpoint_policy: CheckpointPolicy::OnClose,
        tiering: TieringConfig::default(),
        verify_checkpoint: true,
    };
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, config).unwrap();

    for i in 0..30u32 {
        tree.insert(leaf(i)).unwrap();
    }
    tree.flush().unwrap();

    assert!(!dir.path().join("data").exists());

    // when
    let root = tree.root();
    tree.close().unwrap();

    assert!(dir.path().join("data").join("checkpoint.meta").exists());

    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    assert_eq!(tree.root(), root);
    assert_eq!(tree.size(), 30);
    let snap = tree.snapshot();
    // then
    for i in 0..30u64 {
        let proof = snap.generate_proof(i).unwrap();
        assert!(proof.verify(&XorHasher).unwrap());
    }
    tree.close().unwrap();
}

#[test]
fn checkpoint_every_n_entries() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let config = RotorTreeConfig {
        path: dir.path().to_path_buf(),
        flush_policy: FlushPolicy::Manual,
        checkpoint_policy: CheckpointPolicy::EveryNEntries(10),
        tiering: TieringConfig::default(),
        verify_checkpoint: true,
    };
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, config).unwrap();

    // when
    for i in 0..15u32 {
        tree.insert(leaf(i)).unwrap();
    }

    assert!(tree.wait_for_checkpoint(std::time::Duration::from_secs(5)));

    let root = tree.root();
    tree.flush().unwrap();
    tree.close().unwrap();

    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    // then
    assert_eq!(tree.root(), root);
    assert_eq!(tree.size(), 15);
    tree.close().unwrap();
}

#[test]
fn checkpoint_memory_threshold() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let config = RotorTreeConfig {
        path: dir.path().to_path_buf(),
        flush_policy: FlushPolicy::Manual,
        checkpoint_policy: CheckpointPolicy::MemoryThreshold(1),
        tiering: TieringConfig::default(),
        verify_checkpoint: true,
    };
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, config).unwrap();

    // when
    let leaves: Vec<Hash> = (0..200u32).map(leaf).collect();
    tree.insert_many(&leaves).unwrap();

    assert!(tree.wait_for_checkpoint(std::time::Duration::from_secs(5)));

    let root = tree.root();
    tree.flush().unwrap();
    tree.close().unwrap();

    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    // then
    assert_eq!(tree.root(), root);
    assert_eq!(tree.size(), 200);
    tree.close().unwrap();
}

#[test]
fn checkpoint_empty_tree_noop() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    // when
    tree.checkpoint().unwrap();

    // then
    assert!(!dir.path().join("data").exists());

    tree.close().unwrap();
}

#[test]
fn checkpoint_idempotent() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    for i in 0..30u32 {
        tree.insert(leaf(i)).unwrap();
    }
    tree.flush().unwrap();

    // when
    tree.checkpoint().unwrap();
    let root_1 = tree.root();

    tree.checkpoint().unwrap();
    let root_2 = tree.root();

    assert_eq!(root_1, root_2);

    tree.close().unwrap();

    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    assert_eq!(tree.root(), root_1);
    assert_eq!(tree.size(), 30);
    let snap = tree.snapshot();
    // then
    for i in 0..30u64 {
        let proof = snap.generate_proof(i).unwrap();
        assert!(proof.verify(&XorHasher).unwrap());
    }
    tree.close().unwrap();
}

#[test]
fn checkpoint_after_recovery() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    for i in 0..30u32 {
        tree.insert(leaf(i)).unwrap();
    }
    tree.flush().unwrap();
    let root = tree.root();
    tree.close().unwrap();

    // when
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    assert_eq!(tree.size(), 30);

    tree.checkpoint().unwrap();
    assert!(dir.path().join("data").join("checkpoint.meta").exists());
    tree.close().unwrap();

    // then
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    assert_eq!(tree.root(), root);
    assert_eq!(tree.size(), 30);
    let snap = tree.snapshot();
    for i in 0..30u64 {
        let proof = snap.generate_proof(i).unwrap();
        assert!(proof.verify(&XorHasher).unwrap());
    }
    tree.close().unwrap();
}

#[test]
fn root_recomputation_catches_bit_rot() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    let leaves: Vec<Hash> = (0..200u32).map(leaf).collect();
    tree.insert_many(&leaves).unwrap();
    tree.flush().unwrap();
    tree.checkpoint().unwrap();
    tree.close().unwrap();

    // when
    let level_path = dir
        .path()
        .join("data")
        .join("level_0")
        .join("shard_0000.dat");
    let mut data = std::fs::read(&level_path).unwrap();
    data[16] ^= 0xFF;
    std::fs::write(&level_path, &data).unwrap();

    let result =
        RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()));
    // then
    match result {
        Err(RotorTreeError::Storage(StorageError::DataCorruption { .. })) => {}
        Err(e) => panic!("expected DataCorruption, got {e:?}"),
        Ok(_) => panic!("expected DataCorruption, got Ok"),
    }
}

#[test]
fn corrupt_checkpoint_meta_falls_back_to_wal() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    for i in 0..20u32 {
        tree.insert(leaf(i)).unwrap();
    }
    tree.flush().unwrap();
    let root = tree.root();
    tree.close().unwrap();

    // when
    let data_dir = dir.path().join("data");
    std::fs::create_dir_all(&data_dir).unwrap();
    std::fs::write(data_dir.join("checkpoint.meta"), b"garbage").unwrap();

    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    // then
    assert_eq!(tree.root(), root);
    assert_eq!(tree.size(), 20);
    tree.close().unwrap();
}

#[test]
fn cross_config_checkpoint_detection() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    for i in 0..10u32 {
        tree.insert(leaf(i)).unwrap();
    }
    tree.flush().unwrap();
    tree.checkpoint().unwrap();
    tree.close().unwrap();

    // when
    let result =
        RotorTree::<XorHasher, 4, 10>::open(XorHasher, manual_config(dir.path()));
    // then
    match result {
        Err(RotorTreeError::Storage(StorageError::ConfigMismatch { .. })) => {}
        Err(e) => panic!("expected ConfigMismatch, got {e:?}"),
        Ok(_) => panic!("expected ConfigMismatch, got Ok"),
    }
}

#[test]
fn inflated_leaf_count_meta() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    let leaves: Vec<Hash> = (0..200u32).map(leaf).collect();
    tree.insert_many(&leaves).unwrap();
    tree.flush().unwrap();
    tree.checkpoint().unwrap();
    tree.close().unwrap();

    // when
    let data_dir = dir.path().join("data");
    write_test_meta(
        &data_dir,
        &CheckpointMeta {
            n: 2,
            max_depth: 10,
            last_wal_seq: 0,
            leaf_count: 500,
            depth: 8,
            root_hash: [0u8; 32],
        },
    )
    .unwrap();

    // then
    let result =
        RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()));
    assert!(
        result.is_err(),
        "expected error from inflated leaf_count, got Ok"
    );
}

#[test]
fn level_pinning() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let config = RotorTreeConfig {
        path: dir.path().to_path_buf(),
        flush_policy: FlushPolicy::Manual,
        checkpoint_policy: CheckpointPolicy::default(),
        tiering: TieringConfig { pin_above_level: 1 },
        verify_checkpoint: true,
    };
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, config).unwrap();

    let leaves: Vec<Hash> = (0..200u32).map(leaf).collect();
    tree.insert_many(&leaves).unwrap();
    tree.flush().unwrap();
    // when
    tree.checkpoint().unwrap();

    let more: Vec<Hash> = (200..250u32).map(leaf).collect();
    tree.insert_many(&more).unwrap();
    tree.flush().unwrap();

    assert_eq!(tree.size(), 250);
    let snap = tree.snapshot();
    let proof_0 = snap.generate_proof(0).unwrap();
    assert!(proof_0.verify(&XorHasher).unwrap());
    let proof_last = snap.generate_proof(249).unwrap();
    assert!(proof_last.verify(&XorHasher).unwrap());

    let root = tree.root();
    tree.close().unwrap();

    let config2 = RotorTreeConfig {
        path: dir.path().to_path_buf(),
        flush_policy: FlushPolicy::Manual,
        checkpoint_policy: CheckpointPolicy::default(),
        tiering: TieringConfig { pin_above_level: 1 },
        verify_checkpoint: true,
    };
    // then
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, config2).unwrap();
    assert_eq!(tree.root(), root);
    assert_eq!(tree.size(), 250);
    tree.close().unwrap();
}

#[test]
fn mmap_snapshot_isolation() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    let leaves: Vec<Hash> = (0..200u32).map(leaf).collect();
    tree.insert_many(&leaves).unwrap();
    tree.flush().unwrap();
    tree.checkpoint().unwrap();

    // when
    let snap1 = tree.snapshot();
    let root1 = snap1.root();
    let size1 = snap1.size();

    let more: Vec<Hash> = (200..250u32).map(leaf).collect();
    tree.insert_many(&more).unwrap();
    tree.flush().unwrap();
    tree.checkpoint().unwrap();

    assert_eq!(tree.size(), 250);

    // then
    assert_eq!(snap1.root(), root1);
    assert_eq!(snap1.size(), size1);
    let proof_0 = snap1.generate_proof(0).unwrap();
    assert!(proof_0.verify(&XorHasher).unwrap());
    let proof_199 = snap1.generate_proof(199).unwrap();
    assert!(proof_199.verify(&XorHasher).unwrap());

    let snap2 = tree.snapshot();
    let proof_249 = snap2.generate_proof(249).unwrap();
    assert!(proof_249.verify(&XorHasher).unwrap());

    tree.close().unwrap();
}

#[test]
fn wal_truncated_after_checkpoint() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    for i in 0..50u32 {
        tree.insert(leaf(i)).unwrap();
    }
    tree.flush().unwrap();

    let wal_path = dir.path().join("wal");
    let wal_size_before = std::fs::metadata(&wal_path).unwrap().len();
    assert!(
        wal_size_before > 100,
        "WAL should have entries before checkpoint"
    );

    // when
    tree.checkpoint().unwrap();

    let wal_size_after = std::fs::metadata(&wal_path).unwrap().len();
    assert!(
        wal_size_after < 100,
        "WAL should be truncated to header after checkpoint, got {wal_size_after} bytes"
    );
    // then
    assert!(wal_size_after < wal_size_before);

    let root = tree.root();
    tree.close().unwrap();

    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    assert_eq!(tree.root(), root);
    assert_eq!(tree.size(), 50);
    tree.close().unwrap();
}

#[test]
fn max_depth_mismatch() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    tree.insert(leaf(1)).unwrap();
    tree.flush().unwrap();
    tree.close().unwrap();

    // when: reopen with different MAX_DEPTH
    let result =
        RotorTree::<XorHasher, 2, 20>::open(XorHasher, manual_config(dir.path()));

    // then
    match result {
        Err(RotorTreeError::Storage(StorageError::ConfigMismatch {
            expected_max_depth: 20,
            actual_max_depth: 10,
            ..
        })) => {}
        Err(e) => panic!("expected ConfigMismatch with max_depth 20 vs 10, got {e:?}"),
        Ok(_) => panic!("expected ConfigMismatch, got Ok"),
    }
}

#[test]
fn multiple_checkpoint_cycles() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    // Cycle 1: insert 50, flush, checkpoint
    let batch1: Vec<Hash> = (0..50u32).map(leaf).collect();
    tree.insert_many(&batch1).unwrap();
    tree.flush().unwrap();
    tree.checkpoint().unwrap();

    // Cycle 2: insert 50 more, flush, checkpoint
    let batch2: Vec<Hash> = (50..100u32).map(leaf).collect();
    tree.insert_many(&batch2).unwrap();
    tree.flush().unwrap();
    tree.checkpoint().unwrap();

    // Cycle 3: insert 50 more, flush, checkpoint
    let batch3: Vec<Hash> = (100..150u32).map(leaf).collect();
    tree.insert_many(&batch3).unwrap();
    tree.flush().unwrap();
    tree.checkpoint().unwrap();

    let root = tree.root();
    tree.close().unwrap();

    // when: reopen
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    // then
    assert_eq!(tree.size(), 150);
    assert_eq!(tree.root(), root);
    let snap = tree.snapshot();
    for &idx in &[0u64, 49, 50, 99, 100, 149] {
        let proof = snap.generate_proof(idx).unwrap();
        assert!(proof.verify(&XorHasher).unwrap());
    }
    tree.close().unwrap();
}

#[test]
fn file_lock_released_after_close() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    tree.insert(leaf(1)).unwrap();
    tree.flush().unwrap();
    tree.close().unwrap();

    // when: open again in same dir
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    // then: second open succeeded
    assert_eq!(tree.size(), 1);
    tree.close().unwrap();
}

#[test]
fn large_batch_storage_segment_freeze() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 20>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    // 33,000 leaves → 257 chunks → triggers freeze_pending at 256
    let leaves: Vec<Hash> = (0..33_000u32).map(leaf).collect();
    let (root, _) = tree.insert_many(&leaves).unwrap();
    tree.flush().unwrap();
    tree.checkpoint().unwrap();
    tree.close().unwrap();

    // when: reopen
    let tree = RotorTree::<XorHasher, 2, 20>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    // then
    assert_eq!(tree.size(), 33_000);
    assert_eq!(tree.root(), Some(root));
    let snap = tree.snapshot();
    for &idx in &[0u64, 1000, 16383, 32767, 32999] {
        let proof = snap.generate_proof(idx).unwrap();
        assert!(
            proof.verify(&XorHasher).unwrap(),
            "proof failed for idx {idx}"
        );
    }
    tree.close().unwrap();
}

#[test]
fn insert_many_after_checkpoint_recovery() {
    // given
    let dir = tempfile::tempdir().unwrap();
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();

    let batch1: Vec<Hash> = (0..100u32).map(leaf).collect();
    tree.insert_many(&batch1).unwrap();
    tree.flush().unwrap();
    tree.checkpoint().unwrap();
    tree.close().unwrap();

    // when: reopen and insert_many on recovered state
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    assert_eq!(tree.size(), 100);

    let batch2: Vec<Hash> = (100..200u32).map(leaf).collect();
    tree.insert_many(&batch2).unwrap();
    tree.flush().unwrap();

    let root = tree.root();
    tree.close().unwrap();

    // then: reopen and verify full state
    let tree = RotorTree::<XorHasher, 2, 10>::open(XorHasher, manual_config(dir.path()))
        .unwrap();
    assert_eq!(tree.size(), 200);
    assert_eq!(tree.root(), root);
    let snap = tree.snapshot();
    for &idx in &[0u64, 50, 99, 100, 150, 199] {
        let proof = snap.generate_proof(idx).unwrap();
        assert!(proof.verify(&XorHasher).unwrap());
    }
    tree.close().unwrap();
}
