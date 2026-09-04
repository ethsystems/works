#![cfg(feature = "test-helpers")]
//! Zero-allocation guarantee for the scan miss path: a counting global
//! allocator turns "this hot path does not allocate" into an assertion.

use std::{
    alloc::{
        GlobalAlloc,
        Layout,
        System,
    },
    sync::{
        Mutex,
        MutexGuard,
        atomic::{
            AtomicUsize,
            Ordering::Relaxed,
        },
    },
};

use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;
use sealring::{
    Recipient,
    Scanner,
    test_util::{
        MockKem,
        TestDomain,
    },
};

static ALLOCATIONS: AtomicUsize = AtomicUsize::new(0);
static ANCHOR: AtomicUsize = AtomicUsize::new(0);
const STACK_WINDOW: usize = 64 * 1024;

struct Counting;

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let here = &layout as *const Layout as usize;
        if ANCHOR.load(Relaxed).wrapping_sub(here) < STACK_WINDOW {
            ALLOCATIONS.fetch_add(1, Relaxed);
        }
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static GLOBAL: Counting = Counting;

/// The counter is process-global but the tests in this file run on separate
/// threads, so one test's setup allocations would otherwise land inside
/// another's measured window and read as a leak. Measurements take turns.
static MEASURING: Mutex<()> = Mutex::new(());

/// Claims the counter, ignoring poisoning: a failed assertion elsewhere
/// should report itself rather than resurface here as an unrelated panic.
fn measuring() -> MutexGuard<'static, ()> {
    MEASURING
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

#[test]
fn scan_miss_path_allocates_nothing() {
    let _measuring = measuring();

    let recipient = [1u8; 32];
    let stranger = [2u8; 32];
    let aad = b"scan-alloc-aad";
    let mut rng = ChaCha20Rng::seed_from_u64(99);

    let envelopes: Vec<_> = (0..200)
        .map(|i| {
            sealring::seal::<MockKem, TestDomain>(
                &stranger,
                &vec![(i % 256) as u8],
                aad,
                &mut rng,
            )
            .unwrap()
        })
        .collect();
    let refs: Vec<_> = envelopes.iter().collect();

    let mut scanner = Scanner::<MockKem, TestDomain>::new(Recipient::new(recipient));

    let before = ALLOCATIONS.load(Relaxed);
    let results: Vec<_> = scanner.scan(refs, aad).collect();
    let after = ALLOCATIONS.load(Relaxed);

    assert!(results.is_empty());
    assert_eq!(after, before, "scan miss path must not allocate");
}

/// The k256 adapter overrides `decap_batch`, so it needs its own assertion
/// that the batched miss path stays allocation-free.
#[cfg(feature = "k256")]
#[test]
fn k256_scan_miss_path_allocates_nothing() {
    use k256::{
        SecretKey,
        elliptic_curve::Generate,
    };
    use sealring::K256;

    let _measuring = measuring();

    let aad = b"scan-alloc-k256-aad";
    let mut rng = ChaCha20Rng::seed_from_u64(77);

    let recipient = Recipient::<K256>::new(SecretKey::generate_from_rng(&mut rng));
    let stranger_pk = SecretKey::generate_from_rng(&mut rng).public_key();

    let envelopes: Vec<_> = (0..200)
        .map(|i| {
            sealring::seal::<K256, TestDomain>(
                &stranger_pk,
                &vec![(i % 256) as u8],
                aad,
                &mut rng,
            )
            .unwrap()
        })
        .collect();
    let refs: Vec<_> = envelopes.iter().collect();

    let mut scanner = Scanner::<K256, TestDomain>::new(recipient);

    let before = ALLOCATIONS.load(Relaxed);
    let results: Vec<_> = scanner.scan(refs.iter().copied(), aad).collect();
    let after = ALLOCATIONS.load(Relaxed);

    assert!(results.is_empty());
    assert_eq!(after, before, "k256 scan miss path must not allocate");
}
