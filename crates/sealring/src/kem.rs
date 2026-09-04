use rand_core::CryptoRng;
use zeroize::Zeroize;

/// Curve-generic key-encapsulation mechanism.
pub trait Kem {
    /// Recipient long-term public key.
    type PublicKey;

    /// Recipient long-term secret key. The crate borrows it; storage
    /// hygiene is the consumer's responsibility.
    type SecretKey;

    /// Ephemeral public key carried in the envelope alongside the ciphertext.
    type Epk: AsRef<[u8]>;

    /// Per-envelope KEM output fed into HKDF, viewed as the bytes the KDF
    /// extracts from. The crate calls [`Zeroize::zeroize`] on every value it
    /// owns once that value has been consumed.
    type SharedSecret: Zeroize + AsRef<[u8]>;

    /// Wire identifier for this KEM, carried in the envelope header.
    const KEM_ID: u8;

    /// Byte length of `Epk`.
    const EPK_LEN: usize;

    /// Encapsulates a fresh shared secret to `to`, returning the ephemeral
    /// public key and the shared secret.
    fn encap(
        rng: &mut impl CryptoRng,
        to: &Self::PublicKey,
    ) -> (Self::Epk, Self::SharedSecret);

    /// Decapsulates `epk` under `sk`.
    ///
    /// Returns `None` for invalid points and for non-contributory results,
    /// for example the all-zero X25519 output produced by a low-order point.
    fn decap(sk: &Self::SecretKey, epk: &[u8]) -> Option<Self::SharedSecret>;

    /// Derives the public key belonging to `sk`.
    ///
    /// [`Recipient`](crate::Recipient) calls this so the secret key that
    /// decapsulates and the public key bound into the KDF always come from
    /// the same keypair. An adapter proves its implementation with
    /// `conformance_derive_pk_agrees` from the `test-helpers` suite.
    fn derive_pk(sk: &Self::SecretKey) -> Self::PublicKey;

    /// Encodes `pk` in the same format as `Epk`.
    fn encode_pk(pk: &Self::PublicKey) -> Self::Epk;

    /// Decodes what [`encode_pk`](Self::encode_pk) produced, returning `None`
    /// for byte strings that name no public key.
    fn decode_pk(bytes: &[u8]) -> Option<Self::PublicKey>;

    /// Decapsulates a batch of ephemeral keys, one output slot per input.
    ///
    /// The default is a scalar loop over [`decap`](Self::decap); adapters
    /// that can batch field inversions override this.
    fn decap_batch(
        sk: &Self::SecretKey,
        epks: &[&[u8]],
        out: &mut [Option<Self::SharedSecret>],
    ) {
        for (epk, slot) in epks.iter().zip(out) {
            *slot = Self::decap(sk, epk);
        }
    }
}
