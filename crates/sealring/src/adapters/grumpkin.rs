#[cfg(feature = "std")]
use std::sync::OnceLock;

#[cfg(feature = "std")]
use ark_ec::scalar_mul::BatchMulPreprocessing;
use ark_ec::{
    AffineRepr,
    CurveGroup,
};
use ark_ff::{
    AdditiveGroup,
    Field,
    PrimeField,
};
use ark_grumpkin::{
    Affine,
    Fq,
    Fr,
    Projective,
};
use ark_serialize::{
    CanonicalDeserialize,
    CanonicalSerialize,
};
use rand_core::CryptoRng;
use zeroize::Zeroize;

use crate::{
    kem::Kem,
    scan::SCAN_CHUNK,
};

/// Byte length of a compressed Grumpkin affine point. Its base field is 254
/// bits wide and serializes to 32 bytes with 2 spare bits, exactly enough to
/// carry the sign and infinity flags without an extra byte.
const GRUMPKIN_EPK_LEN: usize = 32;

/// Grumpkin ECDH KEM. Grumpkin's cofactor is 1, so a valid on-curve decode
/// needs no subgroup check; only the identity point is rejected.
pub struct Grumpkin;

/// Grumpkin shared-point x-coordinate, reduced to a fixed-size byte string.
pub struct GrumpkinSharedSecret([u8; 32]);

impl AsRef<[u8]> for GrumpkinSharedSecret {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl Zeroize for GrumpkinSharedSecret {
    fn zeroize(&mut self) {
        self.0.zeroize();
    }
}

impl Drop for GrumpkinSharedSecret {
    fn drop(&mut self) {
        self.zeroize();
    }
}

/// Draws a scalar from 64 bytes of caller-supplied randomness, reduced
/// modulo the Grumpkin scalar field order. The rng never enters arkworks:
/// only the reduced scalar does.
fn random_scalar(rng: &mut impl CryptoRng) -> Fr {
    let mut bytes = [0u8; 64];
    rng.fill_bytes(&mut bytes);
    let scalar = Fr::from_le_bytes_mod_order(&bytes);
    bytes.zeroize();
    scalar
}

/// Precomputed multiples of the generator, so deriving a public key walks a
/// window table instead of running a general scalar multiplication.
///
/// Grumpkin ships no equivalent of the basepoint tables x25519-dalek and k256
/// carry, so this builds one on first use. It needs somewhere to live for the
/// life of the process, which is what makes it `std` only.
#[cfg(feature = "std")]
fn generator_table() -> &'static BatchMulPreprocessing<Projective> {
    static TABLE: OnceLock<BatchMulPreprocessing<Projective>> = OnceLock::new();
    // Sized for one scalar at a time, which takes the narrowest window
    // arkworks offers and so the smallest table. Most of the distance from a
    // general multiplication is already covered at that width.
    TABLE.get_or_init(|| BatchMulPreprocessing::new(Affine::generator().into_group(), 1))
}

/// `scalar` times the generator.
fn mul_generator(scalar: &Fr) -> Affine {
    #[cfg(feature = "std")]
    {
        generator_table().batch_mul(&[*scalar])[0]
    }
    #[cfg(not(feature = "std"))]
    {
        (Affine::generator() * scalar).into_affine()
    }
}

/// Compressed encoding of an affine point.
fn compress(point: &Affine) -> [u8; GRUMPKIN_EPK_LEN] {
    let mut out = [0u8; GRUMPKIN_EPK_LEN];
    point
        .serialize_compressed(&mut out[..])
        .expect("grumpkin affine point compresses to GRUMPKIN_EPK_LEN bytes");
    out
}

/// Fixed-size byte string for a base field element, the form the shared
/// x-coordinate reaches the KDF in.
fn fq_bytes(x: &Fq) -> [u8; 32] {
    let mut out = [0u8; 32];
    x.serialize_compressed(&mut out[..])
        .expect("grumpkin base field element serializes to 32 bytes");
    out
}

/// x-coordinate of `point` as a fixed-size byte string, `None` for the
/// identity.
fn x_coordinate(point: &Affine) -> Option<[u8; 32]> {
    let (x, _) = point.xy()?;
    Some(fq_bytes(&x))
}

/// Replaces every element of `zs` with its inverse, spending one field
/// inversion on the whole slice instead of one each: Montgomery's trick.
///
/// `prefix` is scratch of the same length. Every element of `zs` must be
/// non-zero, since the trick inverts their product.
fn batch_invert(zs: &mut [Fq], prefix: &mut [Fq]) {
    debug_assert_eq!(zs.len(), prefix.len(), "scratch matches the slice");

    let mut running = Fq::ONE;
    for (z, slot) in zs.iter().zip(prefix.iter_mut()) {
        *slot = running;
        running *= z;
    }

    let mut inverse = running
        .inverse()
        .expect("a product of non-zero field elements is non-zero");
    for (z, before) in zs.iter_mut().zip(prefix.iter()).rev() {
        let this = *z;
        // `inverse` holds 1/(z_0 * .. * z_i), so scaling it by the product of
        // everything before i leaves 1/z_i.
        *z = inverse * before;
        inverse *= this;
    }
}

impl Kem for Grumpkin {
    type PublicKey = Affine;
    type SecretKey = Fr;
    type Epk = [u8; GRUMPKIN_EPK_LEN];
    type SharedSecret = GrumpkinSharedSecret;

    const KEM_ID: u8 = 0x03;
    const EPK_LEN: usize = GRUMPKIN_EPK_LEN;

    /// An identity recipient key yields the all-zero shared secret, which
    /// [`seal`](crate::seal) rejects.
    fn encap(
        rng: &mut impl CryptoRng,
        to: &Self::PublicKey,
    ) -> (Self::Epk, Self::SharedSecret) {
        let esk = random_scalar(rng);
        let epk = mul_generator(&esk);
        let shared = (*to * esk).into_affine();
        let secret = x_coordinate(&shared).unwrap_or([0u8; 32]);
        (compress(&epk), GrumpkinSharedSecret(secret))
    }

    fn decap(sk: &Self::SecretKey, epk: &[u8]) -> Option<Self::SharedSecret> {
        let shared = (Self::decode_pk(epk)? * *sk).into_affine();
        Some(GrumpkinSharedSecret(x_coordinate(&shared)?))
    }

    fn derive_pk(sk: &Self::SecretKey) -> Self::PublicKey {
        mul_generator(sk)
    }

    fn encode_pk(pk: &Self::PublicKey) -> Self::Epk {
        compress(pk)
    }

    /// Cofactor 1 means an on-curve decode needs no subgroup check, so only
    /// the identity is rejected. The length check is what stops a longer
    /// string from decoding through its first 32 bytes.
    fn decode_pk(bytes: &[u8]) -> Option<Self::PublicKey> {
        if bytes.len() != GRUMPKIN_EPK_LEN {
            return None;
        }
        let point = Affine::deserialize_compressed(bytes).ok()?;
        (!point.is_zero()).then_some(point)
    }

    /// Scalar-multiplies every epk in the chunk, then converts the whole
    /// batch out of Jacobian coordinates at once.
    ///
    /// One inversion covers the chunk rather than one per point, which is
    /// what [`CurveGroup::into_affine`] would spend. The affine y never
    /// reaches the KDF, so this derives x alone.
    fn decap_batch(
        sk: &Self::SecretKey,
        epks: &[&[u8]],
        out: &mut [Option<Self::SharedSecret>],
    ) {
        for (epks, out) in epks.chunks(SCAN_CHUNK).zip(out.chunks_mut(SCAN_CHUNK)) {
            let mut indices = [0usize; SCAN_CHUNK];
            let mut points = PointScratch([Projective::ZERO; SCAN_CHUNK]);
            let mut zs = FieldScratch([Fq::ZERO; SCAN_CHUNK]);
            let mut prefix = FieldScratch([Fq::ZERO; SCAN_CHUNK]);
            let mut valid = 0usize;

            for (i, (epk, slot)) in epks.iter().zip(out.iter_mut()).enumerate() {
                *slot = None;
                let Some(point) = Self::decode_pk(epk) else {
                    continue;
                };
                let shared = point * *sk;
                // An identity result has no x-coordinate to report, and
                // Montgomery's trick needs every element it inverts non-zero.
                if shared.z == Fq::ZERO {
                    continue;
                }
                indices[valid] = i;
                zs.0[valid] = shared.z;
                points.0[valid] = shared;
                valid += 1;
            }

            batch_invert(&mut zs.0[..valid], &mut prefix.0[..valid]);

            let normalized = indices[..valid]
                .iter()
                .zip(&points.0[..valid])
                .zip(&zs.0[..valid]);
            for ((index, point), z_inverse) in normalized {
                // Jacobian coordinates carry the affine x as `X / Z^2`.
                let x = point.x * z_inverse.square();
                out[*index] = Some(GrumpkinSharedSecret(fq_bytes(&x)));
            }
        }
    }
}

/// Chunk-local projective shared points, overwritten with the identity on
/// drop.
struct PointScratch([Projective; SCAN_CHUNK]);

impl Drop for PointScratch {
    fn drop(&mut self) {
        self.0.fill(Projective::ZERO);
        core::hint::black_box(&self.0);
    }
}

/// Chunk-local base field scratch, overwritten with zero on drop.
struct FieldScratch([Fq; SCAN_CHUNK]);

impl Drop for FieldScratch {
    fn drop(&mut self) {
        self.0.fill(Fq::ZERO);
        core::hint::black_box(&self.0);
    }
}

#[cfg(test)]
mod tests {
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

    use rand_chacha::ChaCha20Rng;
    use rand_core::SeedableRng;

    use super::*;

    #[test]
    fn epk_len_matches_compressed_size() {
        assert_eq!(GRUMPKIN_EPK_LEN, Affine::generator().compressed_size());
    }

    /// Spans more than one chunk and mixes in every epk the scalar path
    /// rejects, so the batch has to skip exactly the same inputs.
    #[test]
    fn decap_batch_agrees_with_decap() {
        let mut rng = ChaCha20Rng::seed_from_u64(5);
        let sk = random_scalar(&mut rng);
        let pk = Grumpkin::derive_pk(&sk);

        let count = SCAN_CHUNK + 5;
        let owned: Vec<Vec<u8>> = (0..count)
            .map(|i| match i % 8 {
                3 => vec![0xFFu8; GRUMPKIN_EPK_LEN],
                5 => compress(&Affine::identity()).to_vec(),
                6 => vec![1u8, 2, 3],
                _ => Grumpkin::encap(&mut rng, &pk).0.to_vec(),
            })
            .collect();
        let epks: Vec<&[u8]> = owned.iter().map(Vec::as_slice).collect();

        let mut batched: Vec<Option<GrumpkinSharedSecret>> =
            (0..count).map(|_| None).collect();
        Grumpkin::decap_batch(&sk, &epks, &mut batched);

        for (epk, batched) in epks.iter().zip(&batched) {
            let scalar = Grumpkin::decap(&sk, epk);
            assert_eq!(
                scalar.map(|shared| shared.0),
                batched.as_ref().map(|shared| shared.0),
            );
        }

        assert!(batched.iter().any(Option::is_some), "some epks decapsulate");
        assert!(
            batched.iter().any(Option::is_none),
            "some epks are rejected"
        );
    }

    #[test]
    fn batch_invert_matches_one_by_one() {
        let mut rng = ChaCha20Rng::seed_from_u64(9);
        let original: Vec<Fq> = (0..17)
            .map(|_| Fq::from(random_scalar(&mut rng).into_bigint()))
            .collect();

        let mut inverted = original.clone();
        let mut prefix = vec![Fq::ZERO; inverted.len()];
        batch_invert(&mut inverted, &mut prefix);

        for (value, batched) in original.iter().zip(&inverted) {
            assert_eq!(value.inverse().unwrap(), *batched);
        }
    }
}
