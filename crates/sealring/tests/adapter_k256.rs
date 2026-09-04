#![cfg(all(feature = "k256", feature = "test-helpers"))]

use k256::{
    SecretKey,
    elliptic_curve::Generate,
};
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;
use sealring::{
    K256,
    Recipient,
    open,
    seal,
    test_util::{
        TestDomain,
        conformance_derive_pk_agrees,
        conformance_garbage_fails,
        conformance_low_order_fails,
        conformance_pk_codec_roundtrips,
        conformance_roundtrip,
    },
};

/// SEC1 encoding of the point at infinity; decap rejects it.
const IDENTITY_EPK: &[u8] = &[0x00];

#[test]
fn conformance_suite() {
    let mut rng = ChaCha20Rng::seed_from_u64(11);
    let sk = SecretKey::generate_from_rng(&mut rng);
    let pk = sk.public_key();

    conformance_garbage_fails::<K256>(&sk);
    conformance_low_order_fails::<K256>(&sk, &[IDENTITY_EPK]);
    conformance_roundtrip::<K256>(&mut rng, &pk, &sk);
    conformance_derive_pk_agrees::<K256>(&pk, &sk);
    conformance_pk_codec_roundtrips::<K256>(&pk);
}

#[test]
fn seal_open_round_trips() {
    let mut rng = ChaCha20Rng::seed_from_u64(22);
    let me = Recipient::<K256>::new(SecretKey::generate_from_rng(&mut rng));
    let note = vec![1u8, 2, 3, 4, 5];
    let aad = b"k256-adapter-aad";

    let envelope =
        seal::<K256, TestDomain>(me.public_key(), &note, aad, &mut rng).unwrap();
    let opened = open::<K256, TestDomain, _>(&me, &envelope, aad).unwrap();

    assert_eq!(opened, Some(note));
}
