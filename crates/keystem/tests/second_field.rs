#![cfg(feature = "spend")]

use ark_bls12_381::Fr;
use ark_ff::{
    BigInteger,
    PrimeField,
    fields::{
        Fp64,
        MontBackend,
        MontConfig,
    },
};
use keystem::{
    OwnerPubkey,
    SecretScalar,
    SpendingKey,
};
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;

/// Seed for every generator drawn in this file, replayed on failure.
const SEED: u64 = 0xB151_2381;

#[test]
fn spending_key_random_over_bls12_381_yields_canonical_and_distinct_scalars() {
    // given a seeded generator
    let mut rng = ChaCha20Rng::seed_from_u64(SEED);
    // when two BLS12-381 spending keys are drawn from it
    let first = SpendingKey::<Fr>::random(&mut rng);
    let second = SpendingKey::<Fr>::random(&mut rng);
    // then both scalars re-encode canonically and the two draws differ
    let first_bytes = *first.scalar().expose_bytes();
    let second_bytes = *second.scalar().expose_bytes();
    assert!(SecretScalar::<Fr>::from_canonical_bytes(first_bytes).is_ok());
    assert!(SecretScalar::<Fr>::from_canonical_bytes(second_bytes).is_ok());
    assert_ne!(first_bytes, second_bytes);
}

#[test]
fn spending_key_from_canonical_bytes_over_bls12_381_accepts_the_modulus_minus_one() {
    // given the canonical encoding of BLS12-381's largest scalar, the modulus minus one
    let bytes = OwnerPubkey::<Fr>::from_field(-Fr::from(1u64)).to_bytes();
    // when it is decoded as a spending key
    let decoded = SpendingKey::<Fr>::from_canonical_bytes(bytes);
    // then it is accepted
    assert!(decoded.is_ok());
}

#[test]
fn spending_key_from_canonical_bytes_over_bls12_381_rejects_the_modulus() {
    // given the big-endian encoding of BLS12-381's scalar field modulus
    let bytes: [u8; 32] = Fr::MODULUS
        .to_bytes_be()
        .try_into()
        .expect("BLS12-381's scalar modulus is 32 bytes wide");
    // when it is decoded as a spending key
    let decoded = SpendingKey::<Fr>::from_canonical_bytes(bytes);
    // then the modulus comparison rejects it
    assert!(decoded.is_err());
}

#[test]
fn owner_pubkey_from_field_closes_the_external_derivation_seam_over_bls12_381() {
    // given a spending key's revealed scalar, squared as a stand-in for a caller-side hash
    let mut rng = ChaCha20Rng::seed_from_u64(SEED);
    let key = SpendingKey::<Fr>::random(&mut rng);
    let scalar = key.scalar();
    let transformed = scalar.expose_field() * scalar.expose_field();
    // when the transformed value is wrapped as an owner pubkey and re-decoded
    let pubkey = OwnerPubkey::<Fr>::from_field(transformed);
    let decoded = OwnerPubkey::<Fr>::from_canonical_bytes(pubkey.to_bytes());
    // then the seam closes: the re-decoded pubkey matches the one built from the transform
    assert_eq!(decoded, Ok(pubkey));
}

/// Goldilocks, `2^64 - 2^32 + 1`. Its integer form is one limb, so a 32-byte
/// encoding pads 24 bytes above it, the width a four-limb field never leaves.
#[derive(MontConfig)]
#[modulus = "18446744069414584321"]
#[generator = "7"]
pub struct GoldilocksConfig;

type Goldilocks = Fp64<MontBackend<GoldilocksConfig, 1>>;

/// Pad bytes in a Goldilocks encoding.
const GOLDILOCKS_PAD: usize = 24;

#[test]
fn encodings_over_a_one_limb_field_clear_the_pad_and_round_trip() {
    // given the largest Goldilocks element
    let value = -Goldilocks::from(1u64);
    // when it is encoded to the fixed width and decoded back
    let bytes = OwnerPubkey::<Goldilocks>::from_field(value).to_bytes();
    let decoded = SecretScalar::<Goldilocks>::from_canonical_bytes(bytes);
    // then the pad is clear and the element survives
    assert_eq!(bytes[..GOLDILOCKS_PAD], [0u8; GOLDILOCKS_PAD]);
    assert_eq!(decoded.map(|scalar| scalar.expose_field()), Ok(value));
}

#[test]
fn spending_key_from_canonical_bytes_over_a_one_limb_field_rejects_a_set_pad_byte() {
    // given a canonical Goldilocks encoding with its leading pad byte set
    let mut bytes =
        OwnerPubkey::<Goldilocks>::from_field(Goldilocks::from(7u64)).to_bytes();
    bytes[0] = 1;
    // when it is decoded as a spending key
    let decoded = SpendingKey::<Goldilocks>::from_canonical_bytes(bytes);
    // then the pad check rejects it instead of reading the low limb alone
    assert!(decoded.is_err());
}

#[test]
fn spending_key_from_canonical_bytes_over_a_one_limb_field_rejects_the_modulus() {
    // given the big-endian encoding of the Goldilocks modulus, pad clear
    let mut bytes = [0u8; 32];
    bytes[GOLDILOCKS_PAD..].copy_from_slice(&Goldilocks::MODULUS.to_bytes_be());
    // when it is decoded as a spending key
    let decoded = SpendingKey::<Goldilocks>::from_canonical_bytes(bytes);
    // then the modulus comparison rejects it
    assert!(decoded.is_err());
}
