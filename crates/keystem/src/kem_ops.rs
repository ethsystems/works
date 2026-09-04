use rand_core::CryptoRng;
use sealring::Kem;
use zeroize::Zeroize;

/// Software-resident secret keys: generation and byte codecs.
///
/// A hardware KEM whose secret key is a device handle implements [`Kem`] alone
/// and skips this trait, so no impl is ever forced to stub out an operation its
/// custody cannot honor.
pub trait KemKeyOps: Kem {
    /// Secret-key encoding, fixed-size per curve, zeroizable so the
    /// persistence egress can wrap it.
    type SkBytes: AsRef<[u8]> + Zeroize;

    /// Draws a secret key from `rng`.
    fn generate_sk(rng: &mut impl CryptoRng) -> Self::SecretKey;

    /// Encodes `sk` for persistence.
    fn encode_sk(sk: &Self::SecretKey) -> Self::SkBytes;

    /// Decodes an encoding [`encode_sk`](Self::encode_sk) produced, returning
    /// `None` for byte strings that name no secret key.
    fn decode_sk(bytes: &[u8]) -> Option<Self::SecretKey>;
}
