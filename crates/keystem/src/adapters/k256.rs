//! secp256k1 key operations

use k256::{
    SecretKey,
    elliptic_curve::Generate,
};
use rand_core::CryptoRng;
use sealring::K256;

use crate::kem_ops::KemKeyOps;

/// Byte length of a secp256k1 scalar.
const K256_SK_LEN: usize = 32;

impl KemKeyOps for K256 {
    type SkBytes = [u8; K256_SK_LEN];

    fn generate_sk(rng: &mut impl CryptoRng) -> SecretKey {
        SecretKey::generate_from_rng(rng)
    }

    fn encode_sk(sk: &SecretKey) -> Self::SkBytes {
        sk.to_bytes().into()
    }

    /// Rejects zero and anything at or above the group order.
    fn decode_sk(bytes: &[u8]) -> Option<SecretKey> {
        let bytes: &Self::SkBytes = bytes.try_into().ok()?;
        SecretKey::from_slice(bytes).ok()
    }
}
