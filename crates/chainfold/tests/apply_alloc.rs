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
    cell::Cell,
};

use chainfold::{
    Batch,
    BlockRef,
    Driver,
    DriverConfig,
    Engine,
    EngineConfig,
    Tick,
    test_util::{
        NoopFold,
        ScriptedChain,
    },
};

thread_local! {
    // Per thread: the test harness allocates on its own threads while a test runs.
    // Const-initialized with no destructor, so the allocator can touch them.
    static ALLOCATIONS: Cell<u64> = const { Cell::new(0) };
    static ALLOCATED_BYTES: Cell<u64> = const { Cell::new(0) };
}

/// Allocations made so far by the calling thread.
fn allocations() -> u64 {
    ALLOCATIONS.with(Cell::get)
}

/// Bytes allocated so far by the calling thread.
#[cfg(feature = "wincode")]
fn allocated_bytes() -> u64 {
    ALLOCATED_BYTES.with(Cell::get)
}

struct Counting;

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let _ = ALLOCATIONS.try_with(|count| count.set(count.get() + 1));
        let _ = ALLOCATED_BYTES
            .try_with(|bytes| bytes.set(bytes.get() + layout.size() as u64));
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
    let before = allocations();
    engine.apply_batch(&batch).unwrap();
    let after = allocations();

    // then the allocation count delta is zero
    assert_eq!(after, before);
}

/// Blocks per poll, and events per block: 128 entries a poll, enough that a sort needing
/// scratch space would take it from the heap.
const WINDOW: u64 = 32;
const EVENTS_PER_BLOCK: u64 = 4;

/// Driver over `blocks` scripted blocks, checkpointing every window.
fn scripted_driver(blocks: u64) -> Driver<NoopFold, ScriptedChain> {
    let mut chain = ScriptedChain::new(1);
    for block in 1..=blocks {
        let events: Vec<u64> = (0..EVENTS_PER_BLOCK).map(|i| block * 8 + i).collect();
        chain.push_block(&events);
    }
    chain.set_window(WINDOW);
    Driver::new(
        NoopFold,
        chain,
        EngineConfig {
            ring_capacity: 256,
            checkpoint_slots: 4,
        },
        DriverConfig {
            checkpoint_interval: Some(WINDOW),
            snapshot_interval: None,
            ..DriverConfig::from_block(1)
        },
    )
    .unwrap()
}

/// Allocations made by one tick, with the tick it returned.
fn counted_tick(driver: &mut Driver<NoopFold, ScriptedChain>) -> (u64, Tick) {
    let before = allocations();
    let tick = driver.tick();
    (allocations() - before, tick)
}

#[test]
fn steady_state_catch_up_tick_allocates_zero() {
    // given a driver two full-window ticks into a long chain, its buffers warmed
    let mut driver = scripted_driver(8 * WINDOW);
    driver.tick();
    driver.tick();

    // when the next catch-up tick scans, groups and applies another full window
    let (allocations, tick) = counted_tick(&mut driver);

    // then it progressed without allocating
    assert!(matches!(tick, Tick::Progressed(_)), "{tick:?}");
    assert_eq!(allocations, 0);
}

#[test]
fn fork_recovery_tick_allocates_zero() {
    // given a driver caught up on a chain whose ring is full, then a one-block reorg
    let mut driver = scripted_driver(8 * WINDOW + 3);
    while driver.tick() != Tick::Idle {}
    driver
        .source_mut()
        .reorg(1, &[&[1, 2, 3, 4], &[5, 6, 7, 8]]);

    // when the next tick detects the fork, bisects the ring and rolls back
    let (allocations, tick) = counted_tick(&mut driver);

    // then it rolled back without allocating
    assert!(matches!(tick, Tick::RolledBack { .. }), "{tick:?}");
    assert_eq!(allocations, 0);
}

/// Bytes the allocator hands out while a decode of `bytes` fails.
#[cfg(feature = "wincode")]
fn failed_decode_bytes(bytes: &[u8]) -> u64 {
    use chainfold::test_util::RecordingFold;

    let config = EngineConfig {
        ring_capacity: 8,
        checkpoint_slots: 0,
    };
    let before = allocated_bytes();
    let result = Engine::<RecordingFold>::decode_snapshot(bytes, config);
    let after = allocated_bytes();
    assert!(result.is_err(), "corrupt input decoded successfully");
    after - before
}

#[cfg(feature = "wincode")]
#[test]
fn corrupt_snapshot_decode_allocates_within_the_input_length() {
    // given every truncation of a valid snapshot plus one bit-flipped copy
    use chainfold::test_util::RecordingFold;

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
