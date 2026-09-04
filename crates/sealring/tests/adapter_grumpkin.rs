#![cfg(all(feature = "grumpkin", feature = "test-helpers"))]

use ark_ec::{
    AdditiveGroup,
    AffineRepr,
    CurveGroup,
};
use ark_ff::PrimeField;
use ark_grumpkin::{
    Affine,
    Fr,
};
use ark_serialize::CanonicalSerialize;
use rand_chacha::ChaCha20Rng;
use rand_core::{
    CryptoRng,
    SeedableRng,
};
use sealring::{
    Grumpkin,
    Kem,
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

/// Draws a Grumpkin keypair the same way the adapter draws an ephemeral
/// scalar: bytes from the caller's rng, reduced mod the scalar field order.
fn keypair(rng: &mut impl CryptoRng) -> (Fr, Affine) {
    let mut bytes = [0u8; 64];
    rng.fill_bytes(&mut bytes);
    let sk = Fr::from_le_bytes_mod_order(&bytes);
    let pk = (Affine::generator() * sk).into_affine();
    (sk, pk)
}

fn identity_epk() -> [u8; 32] {
    let mut bytes = [0u8; 32];
    Affine::identity()
        .serialize_compressed(&mut bytes[..])
        .unwrap();
    bytes
}

#[test]
fn garbage_epk_fails_decap() {
    let mut rng = ChaCha20Rng::seed_from_u64(1);
    let (sk, _pk) = keypair(&mut rng);
    conformance_garbage_fails::<Grumpkin>(&sk);
}

#[test]
fn identity_epk_fails_decap() {
    let mut rng = ChaCha20Rng::seed_from_u64(2);
    let (sk, _pk) = keypair(&mut rng);
    let identity = identity_epk();
    let cases: &[&[u8]] = &[&identity];
    conformance_low_order_fails::<Grumpkin>(&sk, cases);
}

#[test]
fn encap_decap_roundtrip_agrees() {
    let mut rng = ChaCha20Rng::seed_from_u64(3);
    let (sk, pk) = keypair(&mut rng);
    conformance_roundtrip::<Grumpkin>(&mut rng, &pk, &sk);
    conformance_derive_pk_agrees::<Grumpkin>(&pk, &sk);
    conformance_pk_codec_roundtrips::<Grumpkin>(&pk);
}

#[test]
fn sealing_to_the_identity_key_fails() {
    let mut rng = ChaCha20Rng::seed_from_u64(5);
    let note = vec![1u8, 2, 3];
    let aad = b"grumpkin-identity-aad";

    let result = seal::<Grumpkin, TestDomain>(&Affine::identity(), &note, aad, &mut rng);
    assert!(result.is_err(), "sealing to the identity key must fail");
}

#[test]
fn zero_secret_key_decaps_to_none() {
    let mut rng = ChaCha20Rng::seed_from_u64(6);
    let (_sk, pk) = keypair(&mut rng);
    let (epk, _shared) = Grumpkin::encap(&mut rng, &pk);

    assert!(
        Grumpkin::decap(&Fr::ZERO, &epk).is_none(),
        "a zero secret key must decap to None"
    );
}

#[test]
fn seal_open_round_trips_with_test_domain() {
    let mut rng = ChaCha20Rng::seed_from_u64(4);
    let (sk, _pk) = keypair(&mut rng);
    let me = Recipient::<Grumpkin>::new(sk);
    let note = vec![1u8, 2, 3, 4, 5];
    let aad = b"grumpkin-aad";

    let envelope =
        seal::<Grumpkin, TestDomain>(me.public_key(), &note, aad, &mut rng).unwrap();
    let opened = open::<Grumpkin, TestDomain, _>(&me, &envelope, aad).unwrap();

    assert_eq!(opened, Some(note));
}
