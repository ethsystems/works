//! X25519 key operations
//!
//! Building an incoming-viewing keypair and handing its credential to a
//! sender:
//!
//! ```
//! use keystem::{ViewingKey, family::Incoming};
//! use rand_chacha::ChaCha20Rng;
//! use rand_core::SeedableRng;
//! use sealring::X25519;
//!
//! fn seal_to_incoming(_: &keystem::ViewingPubkey<X25519, Incoming>) {}
//!
//! let mut rng = ChaCha20Rng::seed_from_u64(7);
//! let incoming: ViewingKey<X25519, Incoming> = ViewingKey::random(&mut rng);
//! seal_to_incoming(&incoming.derive_pubkey());
//! ```
//!
//! The compliance channel is a different type, so it cannot reach that sender
//! by accident. This is the correlation-risk rule, enforced by the compiler:
//!
//! ```compile_fail
//! use keystem::{ViewingKey, family::{Compliance, Incoming}};
//! use rand_chacha::ChaCha20Rng;
//! use rand_core::SeedableRng;
//! use sealring::X25519;
//!
//! fn seal_to_incoming(_: &keystem::ViewingPubkey<X25519, Incoming>) {}
//!
//! let mut rng = ChaCha20Rng::seed_from_u64(7);
//! let compliance: ViewingKey<X25519, Compliance> = ViewingKey::random(&mut rng);
//! seal_to_incoming(&compliance.derive_pubkey());
//! ```

use rand_core::CryptoRng;
use sealring::X25519;
use x25519_dalek::StaticSecret;

use crate::kem_ops::KemKeyOps;

/// Byte length of an X25519 scalar.
const X25519_KEY_LEN: usize = 32;

impl KemKeyOps for X25519 {
    type SkBytes = [u8; X25519_KEY_LEN];

    fn generate_sk(rng: &mut impl CryptoRng) -> StaticSecret {
        StaticSecret::random_from_rng(rng)
    }

    fn encode_sk(sk: &StaticSecret) -> Self::SkBytes {
        sk.to_bytes()
    }

    /// Every 32-byte string is a valid scalar once clamped, so only the length
    /// can fail.
    fn decode_sk(bytes: &[u8]) -> Option<StaticSecret> {
        Some(StaticSecret::from(
            <[u8; X25519_KEY_LEN]>::try_from(bytes).ok()?,
        ))
    }
}
