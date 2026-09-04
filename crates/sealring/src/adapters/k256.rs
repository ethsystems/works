use k256::elliptic_curve::{
    BatchNormalize,
    Generate,
};
use rand_core::CryptoRng;
use zeroize::Zeroize;

use crate::{
    kem::Kem,
    scan::SCAN_CHUNK,
};

/// Byte length of a SEC1-compressed secp256k1 point.
const K256_EPK_LEN: usize = 33;

/// secp256k1 ECDH KEM. Epk and encoded public key are SEC1-compressed
/// points; identity and off-curve points are rejected by SEC1 decoding.
pub struct K256;

/// secp256k1 ECDH output, reduced to a fixed-size byte string.
pub struct K256SharedSecret([u8; 32]);

impl AsRef<[u8]> for K256SharedSecret {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl Zeroize for K256SharedSecret {
    fn zeroize(&mut self) {
        self.0.zeroize();
    }
}

impl Drop for K256SharedSecret {
    fn drop(&mut self) {
        self.zeroize();
    }
}

impl Kem for K256 {
    type PublicKey = k256::PublicKey;
    type SecretKey = k256::SecretKey;
    type Epk = [u8; K256_EPK_LEN];
    type SharedSecret = K256SharedSecret;

    const KEM_ID: u8 = 0x01;
    const EPK_LEN: usize = K256_EPK_LEN;

    fn encap(
        rng: &mut impl CryptoRng,
        to: &Self::PublicKey,
    ) -> (Self::Epk, Self::SharedSecret) {
        let esk = k256::ecdh::EphemeralSecret::generate_from_rng(rng);
        let epk = Self::encode_pk(&esk.public_key());
        let shared = esk.diffie_hellman(to);
        let bytes: &[u8; 32] = shared.raw_secret_bytes().as_ref();
        (epk, K256SharedSecret(*bytes))
    }

    fn decap(sk: &Self::SecretKey, epk: &[u8]) -> Option<Self::SharedSecret> {
        let pk = Self::decode_pk(epk)?;
        let shared = k256::ecdh::diffie_hellman(sk.to_nonzero_scalar(), pk.as_affine());
        let bytes: &[u8; 32] = shared.raw_secret_bytes().as_ref();
        Some(K256SharedSecret(*bytes))
    }

    fn derive_pk(sk: &Self::SecretKey) -> Self::PublicKey {
        sk.public_key()
    }

    fn encode_pk(pk: &Self::PublicKey) -> Self::Epk {
        let sec1 = pk.to_sec1_bytes();
        let mut epk = [0u8; K256_EPK_LEN];
        epk.copy_from_slice(&sec1);
        epk
    }

    /// SEC1 decoding rejects the identity and off-curve points.
    fn decode_pk(bytes: &[u8]) -> Option<Self::PublicKey> {
        k256::PublicKey::from_sec1_bytes(bytes).ok()
    }

    fn decap_batch(
        sk: &Self::SecretKey,
        epks: &[&[u8]],
        out: &mut [Option<Self::SharedSecret>],
    ) {
        let scalar = sk.to_nonzero_scalar();
        for (epks, out) in epks.chunks(SCAN_CHUNK).zip(out.chunks_mut(SCAN_CHUNK)) {
            let mut indices = [0usize; SCAN_CHUNK];
            let mut points = PointScratch([k256::ProjectivePoint::IDENTITY; SCAN_CHUNK]);
            let mut valid = 0usize;

            for (i, (epk, slot)) in epks.iter().zip(out.iter_mut()).enumerate() {
                *slot = None;
                let Some(pk) = Self::decode_pk(epk) else {
                    continue;
                };
                indices[valid] = i;
                points.0[valid] =
                    k256::ProjectivePoint::from(*pk.as_affine()) * scalar.as_ref();
                valid += 1;
            }

            // One field inversion for the whole chunk instead of one per point.
            let affines =
                AffineScratch(k256::ProjectivePoint::batch_normalize(&points.0));
            for (idx, affine) in indices[..valid].iter().zip(&affines.0[..valid]) {
                let shared = k256::ecdh::SharedSecret::from(affine);
                let bytes: &[u8; 32] = shared.raw_secret_bytes().as_ref();
                out[*idx] = Some(K256SharedSecret(*bytes));
            }
        }
    }
}

/// Chunk-local projective shared points, overwritten with the identity on
/// drop.
struct PointScratch([k256::ProjectivePoint; SCAN_CHUNK]);

impl Drop for PointScratch {
    fn drop(&mut self) {
        self.0.fill(k256::ProjectivePoint::IDENTITY);
        core::hint::black_box(&self.0);
    }
}

/// Chunk-local normalized shared points, overwritten with the identity on
/// drop.
struct AffineScratch([k256::AffinePoint; SCAN_CHUNK]);

impl Drop for AffineScratch {
    fn drop(&mut self) {
        self.0.fill(k256::AffinePoint::IDENTITY);
        core::hint::black_box(&self.0);
    }
}
