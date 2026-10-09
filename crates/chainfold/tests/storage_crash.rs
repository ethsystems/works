#![cfg(feature = "storage")]
//! Multi-cycle crash fuzz plus resume: durable recovery converges to the last
//! acknowledged commit, and a reopened store carries a driver onward from its cursor.

use std::path::PathBuf;

use chainfold::{
    Batch,
    BlockRef,
    Driver,
    DriverConfig,
    Engine,
    EngineConfig,
    Position,
    storage::{
        Flusher,
        SnapshotStore,
        StoreConfig,
    },
    test_util::{
        CrashVfs,
        RecordingFold,
        ScriptedChain,
    },
};
use proptest::prelude::*;

/// Ring window for the reference engine that generates snapshot bytes to commit.
const RING_CAPACITY: usize = 8;
/// Above the largest schedule of 5 commits over 3 cycles, so open() keeps every file.
const RETAIN: usize = 32;
/// Snapshot jobs the flusher admits before an offer blocks on the queue.
const QUEUE_DEPTH: usize = 4;

fn test_config() -> EngineConfig {
    EngineConfig {
        ring_capacity: RING_CAPACITY,
        checkpoint_slots: 0,
    }
}

/// Engine window for the resume driver; two slots give the durable point its margin.
fn resume_engine_config() -> EngineConfig {
    EngineConfig {
        ring_capacity: RING_CAPACITY,
        checkpoint_slots: 2,
    }
}

fn store_config(dir: PathBuf) -> StoreConfig {
    StoreConfig {
        dir,
        retain: RETAIN,
    }
}

/// Deterministic block header: the block number embedded directly in the hash bytes.
fn block_ref(number: u64) -> BlockRef {
    let mut hash = [0u8; 32];
    hash[..8].copy_from_slice(&number.to_le_bytes());
    BlockRef { number, hash }
}

/// Advances the reference engine by one block carrying a single event.
fn advance(engine: &mut Engine<RecordingFold>, number: u64) {
    let boundary = number.checked_sub(1).filter(|&n| n > 0).map(block_ref);
    let mut batch = Batch::new();
    batch.boundary = boundary;
    batch.push_block(block_ref(number), [(0u32, number)]);
    engine.apply_batch(&batch).unwrap();
}

proptest! {
    #[test]
    fn crash_schedules_recover_a_committed_prefix(
        commits_per_cycle in 1usize..=5,
        cycles in 1usize..=3,
        extra_budget in 0u32..=64,
        torn_len in 0usize..=32,
    ) {
        // given a schedule of 1..=5 commits over 1..=3 cycles, an op budget, and a torn length
        let dir = PathBuf::from("/crash-fuzz");
        let total_commits = cycles * commits_per_cycle;
        let mut reference = Engine::new(RecordingFold::default(), test_config()).unwrap();
        let planned: Vec<(Vec<u8>, Option<Position>)> = (1..=total_commits as u64)
            .map(|number| {
                advance(&mut reference, number);
                let mut bytes = Vec::new();
                reference.encode_snapshot(&mut bytes).unwrap();
                (bytes, reference.cursor())
            })
            .collect();

        // The first commit runs unbudgeted to measure the ops a clean open plus commit
        // needs, so every fuzzed crash lands on a store with one acknowledged snapshot.
        let baseline = {
            let (mut store, _) =
                SnapshotStore::open(store_config(dir.clone()), CrashVfs::new()).unwrap();
            store.commit(&planned[0].0, planned[0].1).unwrap();
            store.into_vfs().op_count()
        };

        let vfs = CrashVfs::with_crash_budget(baseline + extra_budget, torn_len);
        let (mut store, _) = SnapshotStore::open(store_config(dir.clone()), vfs).unwrap();
        store.commit(&planned[0].0, planned[0].1).unwrap();
        let mut last_ok = planned[0].clone();
        let mut index = 1;

        for _ in 0..cycles {
            let end = (index + commits_per_cycle).min(planned.len());
            while index < end {
                let (bytes, cursor) = &planned[index];
                // durable_cursor() is authoritative: the active slot flips only after
                // the manifest fsync that made it durable.
                let _ = store.commit(bytes, *cursor);
                if store.durable_cursor() == *cursor {
                    last_ok = (bytes.clone(), *cursor);
                }
                index += 1;
            }

            // when the run crashes, the vfs crashes, and the store reopens
            let mut vfs = store.into_vfs();
            vfs.crash();
            let (reopened, recovered) =
                SnapshotStore::open(store_config(dir.clone()), vfs).unwrap();
            store = reopened;

            // then every open succeeds and recovers the last acknowledged commit
            let recovered = recovered.expect("the protected first commit is always durable");
            prop_assert_eq!(&recovered.snapshot, &last_ok.0);
            prop_assert_eq!(recovered.cursor, last_ok.1);
            let decoded =
                Engine::<RecordingFold>::decode_snapshot(&recovered.snapshot, test_config())
                    .unwrap();
            prop_assert_eq!(decoded.cursor(), last_ok.1);

            // reopening again with no further activity converges to the same state
            let vfs_again = store.into_vfs();
            let (reopened_again, recovered_again) =
                SnapshotStore::open(store_config(dir.clone()), vfs_again).unwrap();
            store = reopened_again;
            prop_assert_eq!(recovered_again.unwrap().snapshot, recovered.snapshot);
        }
    }
}

/// Builds a ten-block chain the driver reads four blocks at a time.
fn resume_chain() -> ScriptedChain {
    let mut chain = ScriptedChain::new(1);
    for value in 1..=10u64 {
        chain.push_block(&[value]);
    }
    chain.set_window(4);
    chain
}

#[test]
fn flusher_sink_persists_and_resumes() {
    // given a driver whose sink is a real flusher over a crash-accurate store
    let dir = PathBuf::from("/resume");
    let (store, _) =
        SnapshotStore::open(store_config(dir.clone()), CrashVfs::new()).unwrap();
    let mut driver = Driver::with_sink(
        RecordingFold::default(),
        resume_chain(),
        Flusher::spawn(store, QUEUE_DEPTH),
        resume_engine_config(),
        DriverConfig {
            checkpoint_interval: Some(2),
            snapshot_interval: Some(1),
            ..DriverConfig::from_block(1)
        },
    )
    .unwrap();

    // when driven to the tip, the flusher joined, and the reopened store resumes a driver
    while !driver.is_caught_up() {
        driver.tick();
    }
    let store = driver.into_sink().join().unwrap();
    let durable_cursor = store.durable_cursor();
    let (_, recovered) =
        SnapshotStore::open(store_config(dir), store.into_vfs()).unwrap();
    let recovered = recovered.expect("the offered snapshot is durable");
    let engine = Engine::<RecordingFold>::decode_snapshot(
        &recovered.snapshot,
        resume_engine_config(),
    )
    .unwrap();
    let mut resumed = Driver::resume(
        engine,
        resume_chain(),
        RecordingFold::default(),
        DriverConfig::from_block(1),
    )
    .unwrap();
    let resume_cursor = resumed.engine().cursor();
    while !resumed.is_caught_up() {
        resumed.tick();
    }

    // then the durable cursor trails the tip, the resume starts there, and the view converges
    assert_eq!(durable_cursor, Some(Position::new(8, 0)));
    assert_eq!(resume_cursor, Some(Position::new(8, 0)));
    assert_eq!(resumed.engine().cursor(), Some(Position::new(10, 0)));
    let expected: Vec<(Position, u64)> = (1..=10u64)
        .map(|value| (Position::new(value, 0), value))
        .collect();
    assert_eq!(resumed.engine().fold().applied, expected);
}
