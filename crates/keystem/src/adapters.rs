//! Feature-gated key operations for sealring's shipped `Kem` adapters.

#[cfg(feature = "k256")]
#[cfg_attr(docsrs, doc(cfg(feature = "k256")))]
pub mod k256;

#[cfg(feature = "x25519")]
#[cfg_attr(docsrs, doc(cfg(feature = "x25519")))]
pub mod x25519;
