use core::{
    fmt,
    marker::PhantomData,
};

use rand_core::CryptoRng;
use sealring::{
    Kem,
    Recipient,
};
use zeroize::Zeroizing;

use crate::{
    error::InvalidKey,
    hex::write_hex,
    kem_ops::KemKeyOps,
};

/// Viewing keypair in disclosure family `F`.
pub struct ViewingKey<K: Kem, F> {
    recipient: Recipient<K>,
    family: PhantomData<fn() -> F>,
}

impl<K: Kem, F> ViewingKey<K, F> {
    /// Custody-agnostic constructor. Hardware ECDH enters here with a consumer
    /// [`Kem`] impl whose `SecretKey` is a device handle.
    pub fn from_recipient(recipient: Recipient<K>) -> Self {
        Self {
            recipient,
            family: PhantomData,
        }
    }

    /// The recipient sealring's open and scan paths consume.
    pub fn recipient(&self) -> &Recipient<K> {
        &self.recipient
    }

    /// The distributable read credential for this channel.
    pub fn derive_pubkey(&self) -> ViewingPubkey<K, F>
    where
        K::PublicKey: Clone,
    {
        ViewingPubkey {
            public_key: self.recipient.public_key().clone(),
            family: PhantomData,
        }
    }
}

impl<K: KemKeyOps, F> ViewingKey<K, F> {
    /// Draws a fresh keypair for this channel from `rng`.
    pub fn random(rng: &mut impl CryptoRng) -> Self {
        Self::from_recipient(Recipient::new(K::generate_sk(rng)))
    }

    /// Total decode of a persisted secret key.
    pub fn from_sk_bytes(bytes: &[u8]) -> Result<Self, InvalidKey> {
        let secret_key = K::decode_sk(bytes).ok_or(InvalidKey)?;
        Ok(Self::from_recipient(Recipient::new(secret_key)))
    }

    /// Persistence egress, in a wrapper that wipes the encoding on drop.
    pub fn to_sk_bytes(&self) -> Zeroizing<K::SkBytes> {
        Zeroizing::new(K::encode_sk(self.recipient.secret_key()))
    }
}

impl<K: Kem, F> fmt::Debug for ViewingKey<K, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("ViewingKey(REDACTED)")
    }
}

/// Distributable read credential in family `F`.
pub struct ViewingPubkey<K: Kem, F> {
    public_key: K::PublicKey,
    family: PhantomData<fn() -> F>,
}

impl<K: Kem, F> ViewingPubkey<K, F> {
    /// The seal-to handle `sealring::seal` consumes.
    pub fn public_key(&self) -> &K::PublicKey {
        &self.public_key
    }

    /// The wire encoding, in the same format the envelope carries its
    /// ephemeral key.
    pub fn to_bytes(&self) -> K::Epk {
        K::encode_pk(&self.public_key)
    }

    /// Counterparty import, the sender-side decode.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, InvalidKey> {
        let public_key = K::decode_pk(bytes).ok_or(InvalidKey)?;
        Ok(Self {
            public_key,
            family: PhantomData,
        })
    }
}

impl<K: Kem, F> Clone for ViewingPubkey<K, F>
where
    K::PublicKey: Clone,
{
    fn clone(&self) -> Self {
        Self {
            public_key: self.public_key.clone(),
            family: PhantomData,
        }
    }
}

impl<K: Kem, F> PartialEq for ViewingPubkey<K, F> {
    fn eq(&self, other: &Self) -> bool {
        self.to_bytes().as_ref() == other.to_bytes().as_ref()
    }
}

impl<K: Kem, F> Eq for ViewingPubkey<K, F> {}

impl<K: Kem, F> fmt::Debug for ViewingPubkey<K, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("ViewingPubkey(")?;
        write_hex(f, self.to_bytes().as_ref())?;
        f.write_str(")")
    }
}

#[cfg(feature = "serde")]
mod viewing_pubkey_serde {
    #[cfg(not(feature = "std"))]
    use alloc::vec::Vec;
    #[cfg(feature = "std")]
    use std::vec::Vec;

    use serde::{
        Deserialize,
        Deserializer,
        Serialize,
        Serializer,
        de::Error,
    };

    use super::*;

    #[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
    impl<K: Kem, F> Serialize for ViewingPubkey<K, F> {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serializer.serialize_bytes(self.to_bytes().as_ref())
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
    impl<'de, K: Kem, F> Deserialize<'de> for ViewingPubkey<K, F> {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            let bytes = Vec::<u8>::deserialize(deserializer)?;
            Self::from_bytes(&bytes).map_err(D::Error::custom)
        }
    }
}
