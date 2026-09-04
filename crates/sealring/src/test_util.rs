//! Test helpers: a toy KEM and domain, and a conformance suite adapters
//! should run against their own keys.

use core::convert::Infallible;

#[cfg(not(feature = "std"))]
use alloc::{
    vec,
    vec::Vec,
};
#[cfg(feature = "std")]
use std::{
    vec,
    vec::Vec,
};

use rand_core::CryptoRng;
use zeroize::Zeroize;

use crate::{
    domain::Domain,
    kem::Kem,
};

/// Toy KEM: XORs a random 32-byte epk against the peer's 32-byte key.
/// Public and secret keys share a representation, so the same 32 bytes
/// used as `to` in `encap` must be passed as `sk` in `decap` to recover the
/// matching shared secret. Not cryptographically meaningful.
pub struct MockKem;

/// `MockKem`'s shared secret: the XOR of the epk and the peer's key.
pub struct MockSharedSecret([u8; 32]);

impl AsRef<[u8]> for MockSharedSecret {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl Zeroize for MockSharedSecret {
    fn zeroize(&mut self) {
        self.0.zeroize();
    }
}

impl Drop for MockSharedSecret {
    fn drop(&mut self) {
        self.zeroize();
    }
}

fn xor32(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = a[i] ^ b[i];
    }
    out
}

impl Kem for MockKem {
    type PublicKey = [u8; 32];
    type SecretKey = [u8; 32];
    type Epk = [u8; 32];
    type SharedSecret = MockSharedSecret;

    const KEM_ID: u8 = 0xFF;
    const EPK_LEN: usize = 32;

    fn encap(
        rng: &mut impl CryptoRng,
        to: &Self::PublicKey,
    ) -> (Self::Epk, Self::SharedSecret) {
        let mut epk = [0u8; 32];
        rng.fill_bytes(&mut epk);
        let shared = xor32(&epk, to);
        (epk, MockSharedSecret(shared))
    }

    fn decap(sk: &Self::SecretKey, epk: &[u8]) -> Option<Self::SharedSecret> {
        let epk: &[u8; 32] = epk.try_into().ok()?;
        Some(MockSharedSecret(xor32(epk, sk)))
    }

    fn derive_pk(sk: &Self::SecretKey) -> Self::PublicKey {
        *sk
    }

    fn encode_pk(pk: &Self::PublicKey) -> Self::Epk {
        *pk
    }

    fn decode_pk(bytes: &[u8]) -> Option<Self::PublicKey> {
        bytes.try_into().ok()
    }
}

/// Toy domain: notes are raw bytes, tag `"sealring-test"`.
pub struct TestDomain;

impl Domain for TestDomain {
    type Error = Infallible;
    type Note = Vec<u8>;

    const DOMAIN_TAG: &'static str = "sealring-test";

    fn encode_note(note: &Self::Note, out: &mut Vec<u8>) -> Result<(), Self::Error> {
        out.extend_from_slice(note);
        Ok(())
    }

    fn decode_note(bytes: &[u8]) -> Result<Self::Note, Self::Error> {
        Ok(bytes.to_vec())
    }
}

/// Asserts structurally invalid byte strings reach no key: the empty string,
/// and lengths shorter and longer than `K::EPK_LEN`. `decap` and `decode_pk`
/// read the same encoding, so both must reject all three.
pub fn conformance_garbage_fails<K: Kem>(sk: &K::SecretKey) {
    let too_short = vec![0xAAu8; K::EPK_LEN.saturating_sub(1)];
    let too_long = vec![0xAAu8; K::EPK_LEN + 1];

    for case in [[].as_slice(), &too_short, &too_long] {
        let len = case.len();
        assert!(
            K::decap(sk, case).is_none(),
            "garbage epk of {len} bytes must fail decap"
        );
        assert!(
            K::decode_pk(case).is_none(),
            "garbage of {len} bytes must decode to no public key"
        );
    }
}

/// Asserts `decode_pk` inverts `encode_pk`, the property a sender rests on
/// when it imports a counterparty's key from the wire. An adapter that gets
/// this wrong seals to a key nobody holds.
pub fn conformance_pk_codec_roundtrips<K: Kem>(pk: &K::PublicKey) {
    let encoded = K::encode_pk(pk);
    let decoded = K::decode_pk(encoded.as_ref()).expect("own pk encoding must decode");
    assert_eq!(
        K::encode_pk(&decoded).as_ref(),
        encoded.as_ref(),
        "decode_pk must invert encode_pk"
    );
}

/// Asserts every byte string in `cases` (known low-order, identity, or
/// otherwise non-contributory points) fails to decapsulate under `sk`.
pub fn conformance_low_order_fails<K: Kem>(sk: &K::SecretKey, cases: &[&[u8]]) {
    for case in cases {
        assert!(
            K::decap(sk, case).is_none(),
            "non-contributory epk must fail decap"
        );
    }
}

/// Asserts `encap`/`decap` agree: the shared secret produced by
/// encapsulating to `pk` matches the one produced by decapsulating under
/// the matching `sk`.
pub fn conformance_roundtrip<K: Kem>(
    rng: &mut impl CryptoRng,
    pk: &K::PublicKey,
    sk: &K::SecretKey,
) {
    let (epk, expected) = K::encap(rng, pk);
    let actual = K::decap(sk, epk.as_ref()).expect("matching sk must decap");
    assert_eq!(expected.as_ref(), actual.as_ref());
}

/// Asserts `derive_pk` reproduces `pk` from `sk`, the property
/// [`Recipient`](crate::Recipient) rests on: a keypair it builds binds the
/// same public key into the KDF that the sender sealed to. An adapter that
/// gets this wrong turns every note addressed to `sk` into a commit
/// mismatch, which the receive path reads as "not mine".
pub fn conformance_derive_pk_agrees<K: Kem>(pk: &K::PublicKey, sk: &K::SecretKey) {
    assert_eq!(
        K::encode_pk(&K::derive_pk(sk)).as_ref(),
        K::encode_pk(pk).as_ref(),
        "derive_pk must reproduce the public key belonging to sk"
    );
}
