#![cfg(feature = "std")]
//! Allocation guarantees proven by a counting global allocator: the steady-state
//! apply path allocates nothing, and decoding corrupt snapshots stays within the
//! bytes it was handed.

use std::{
    alloc::{
        GlobalAlloc,
        Layout,
        System,
    },
    sync::{
        Mutex,
        atomic::{
            AtomicU64,
            Ordering::Relaxed,
        },
    },
};

use chainfold::{
    Batch,
    BlockRef,
    Engine,
    EngineConfig,
    test_util::NoopFold,
};

static ALLOCATIONS: AtomicU64 = AtomicU64::new(0);
static ALLOCATED_BYTES: AtomicU64 = AtomicU64::new(0);
/// Serializes measured regions, since the counters are process wide.
static MEASURING: Mutex<()> = Mutex::new(());

struct Counting;

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOCATIONS.fetch_add(1, Relaxed);
        ALLOCATED_BYTES.fetch_add(layout.size() as u64, Relaxed);
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static GLOBAL: Counting = Counting;

/// Deterministic block header: the block number embedded directly in the hash bytes.
fn block_ref(number: u64) -> BlockRef {
    let mut hash = [0u8; 32];
    hash[..8].copy_from_slice(&number.to_le_bytes());
    BlockRef { number, hash }
}

/// Builds a single-span batch of `count` events over one block.
fn block_batch(boundary: Option<BlockRef>, number: u64, count: u32) -> Batch<u64> {
    let mut batch = Batch::new();
    batch.boundary = boundary;
    batch.push_block(
        block_ref(number),
        (0..count).map(|log_index| (log_index, u64::from(log_index))),
    );
    batch
}

#[test]
fn steady_state_apply_allocates_zero() {
    // given a pre-built engine warmed by one prior batch and a pre-built 1024-event batch
    let _measuring = MEASURING
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let mut engine = Engine::new(
        NoopFold,
        EngineConfig {
            ring_capacity: 64,
            checkpoint_slots: 4,
        },
    )
    .unwrap();
    engine.apply_batch(&block_batch(None, 1, 1)).unwrap();
    let batch = block_batch(Some(block_ref(1)), 2, 1024);

    // when apply_batch runs over the pre-built batch
    let before = ALLOCATIONS.load(Relaxed);
    engine.apply_batch(&batch).unwrap();
    let after = ALLOCATIONS.load(Relaxed);

    // then the allocation count delta is zero
    assert_eq!(after, before);
}

/// Bytes the allocator hands out while a decode of `bytes` fails.
#[cfg(feature = "wincode")]
fn failed_decode_bytes(bytes: &[u8]) -> u64 {
    use chainfold::test_util::RecordingFold;

    let config = EngineConfig {
        ring_capacity: 8,
        checkpoint_slots: 0,
    };
    let before = ALLOCATED_BYTES.load(Relaxed);
    let result = Engine::<RecordingFold>::decode_snapshot(bytes, config);
    let after = ALLOCATED_BYTES.load(Relaxed);
    assert!(result.is_err(), "corrupt input decoded successfully");
    after - before
}

#[cfg(feature = "wincode")]
#[test]
fn corrupt_snapshot_decode_allocates_within_the_input_length() {
    // given every truncation of a valid snapshot plus one bit-flipped copy
    use chainfold::test_util::RecordingFold;

    let _measuring = MEASURING
        .lock()
        .unwrap_or_else(|poison| poison.into_inner());
    let mut engine = Engine::new(
        RecordingFold::default(),
        EngineConfig {
            ring_capacity: 8,
            checkpoint_slots: 0,
        },
    )
    .unwrap();
    engine.apply_batch(&block_batch(None, 1, 4)).unwrap();
    let mut encoded = Vec::new();
    engine.encode_snapshot(&mut encoded).unwrap();
    let mut flipped = encoded.clone();
    flipped[10] ^= 0x01;

    // when each corrupt input is decoded
    let mut worst = 0u64;
    for len in 0..encoded.len() {
        worst = worst.max(failed_decode_bytes(&encoded[..len]));
    }
    let flipped_bytes = failed_decode_bytes(&flipped);

    // then no decode allocates more than the input it was handed
    assert!(
        worst <= encoded.len() as u64,
        "truncated decode allocated {worst} bytes"
    );
    assert!(
        flipped_bytes <= flipped.len() as u64,
        "bit-flipped decode allocated {flipped_bytes} bytes"
    );
}
