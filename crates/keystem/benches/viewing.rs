use std::hint::black_box;

use criterion::{
    Criterion,
    criterion_group,
    criterion_main,
};
use keystem::{
    KemKeyOps,
    ViewingKey,
    ViewingPubkey,
    family::Incoming,
};
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;
use sealring::{
    K256,
    X25519,
};

/// Seed for the rng behind the one fixed keypair most benchmarks reuse.
const FIXED_KEY_SEED: u64 = 0x4242_4242_4242_4242;

/// Seed for the rng hoisted into the `random` benchmark's timed loop.
const RANDOM_SEED: u64 = 0x9009_9009_9009_9009;

fn bench_curve<K>(c: &mut Criterion, curve: &str)
where
    K: KemKeyOps,
    K::PublicKey: Clone,
{
    let mut group = c.benchmark_group(format!("keystem::viewing/curve={curve}"));

    let mut random_rng = ChaCha20Rng::seed_from_u64(RANDOM_SEED);

    let _ = black_box(ViewingKey::<K, Incoming>::random(&mut random_rng));

    group.bench_function("random", |b| {
        b.iter(|| black_box(ViewingKey::<K, Incoming>::random(&mut random_rng)));
    });

    let mut key_rng = ChaCha20Rng::seed_from_u64(FIXED_KEY_SEED);
    let fixed_key = ViewingKey::<K, Incoming>::random(&mut key_rng);

    group.bench_function("derive_pubkey", |b| {
        b.iter(|| black_box(black_box(&fixed_key).derive_pubkey()));
    });

    group.bench_function("to_sk_bytes", |b| {
        b.iter(|| black_box(black_box(&fixed_key).to_sk_bytes()));
    });

    let sk_bytes = fixed_key.to_sk_bytes();
    assert!(ViewingKey::<K, Incoming>::from_sk_bytes(sk_bytes.as_ref()).is_ok());

    group.bench_function("from_sk_bytes", |b| {
        b.iter(|| {
            black_box(ViewingKey::<K, Incoming>::from_sk_bytes(black_box(
                sk_bytes.as_ref(),
            )))
        });
    });

    let fixed_pubkey = fixed_key.derive_pubkey();

    group.bench_function("to_bytes", |b| {
        b.iter(|| black_box(black_box(&fixed_pubkey).to_bytes()));
    });

    let pk_bytes = fixed_pubkey.to_bytes();
    assert!(ViewingPubkey::<K, Incoming>::from_bytes(pk_bytes.as_ref()).is_ok());

    group.bench_function("from_bytes", |b| {
        b.iter(|| {
            black_box(ViewingPubkey::<K, Incoming>::from_bytes(black_box(
                pk_bytes.as_ref(),
            )))
        });
    });

    group.finish();
}

fn bench_k256(c: &mut Criterion) {
    bench_curve::<K256>(c, "k256");
}

fn bench_x25519(c: &mut Criterion) {
    bench_curve::<X25519>(c, "x25519");
}

criterion_group!(benches, bench_k256, bench_x25519);
criterion_main!(benches);
