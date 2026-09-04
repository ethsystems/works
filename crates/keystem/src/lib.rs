#![cfg_attr(feature = "docs", doc = include_utils::include_md!("README.md:intro"))]
#![cfg_attr(feature = "docs", doc = include_utils::include_md!("README.md:design"))]
#![cfg_attr(feature = "docs", doc = include_utils::include_md!("README.md:usage"))]
#![cfg_attr(not(test), deny(clippy::cast_possible_truncation))]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![deny(unused_crate_dependencies)]
#![deny(warnings)]
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(all(not(feature = "std"), feature = "serde", feature = "viewing"))]
#[cfg_attr(docsrs, doc(cfg(not(feature = "std"))))]
extern crate alloc;

#[cfg(not(any(feature = "spend", feature = "viewing")))]
compile_error!(
    "keystem needs at least one of the `spend` and `viewing` features; \
     `default` enables `spend` through `poseidon`, and the viewing-only shape is \
     `default-features = false, features = [\"viewing\"]`"
);

// dev-only crates linked into the test harness build.
#[cfg(test)]
use {
    ark_bls12_381 as _,
    ark_serialize as _,
    criterion as _,
    proptest as _,
    rand_chacha as _,
    serde_json as _,
};

mod error;
#[cfg(any(feature = "spend", feature = "viewing"))]
mod hex;

#[cfg(feature = "spend")]
mod authority;
#[cfg(feature = "spend")]
mod encoding;
#[cfg(feature = "spend")]
mod spend;

#[cfg(feature = "viewing")]
mod kem_ops;
#[cfg(feature = "viewing")]
mod viewing;

pub mod adapters;
pub mod curves;

#[cfg(feature = "viewing")]
#[cfg_attr(docsrs, doc(cfg(feature = "viewing")))]
pub mod family;

#[cfg(any(test, feature = "test-helpers"))]
#[cfg_attr(docsrs, doc(cfg(feature = "test-helpers")))]
pub mod test_util;

#[cfg(feature = "spend")]
#[cfg_attr(docsrs, doc(cfg(feature = "spend")))]
pub use authority::SpendAuthority;
#[cfg(feature = "viewing")]
#[cfg_attr(docsrs, doc(cfg(feature = "viewing")))]
pub use error::InvalidKey;
#[cfg(feature = "spend")]
#[cfg_attr(docsrs, doc(cfg(feature = "spend")))]
pub use error::{
    NonCanonical,
    NotExportable,
};
#[cfg(feature = "viewing")]
#[cfg_attr(docsrs, doc(cfg(feature = "viewing")))]
pub use kem_ops::KemKeyOps;
#[cfg(feature = "spend")]
#[cfg_attr(docsrs, doc(cfg(feature = "spend")))]
pub use spend::{
    OwnerPubkey,
    SecretScalar,
    SpendingKey,
};
#[cfg(feature = "viewing")]
#[cfg_attr(docsrs, doc(cfg(feature = "viewing")))]
pub use viewing::{
    ViewingKey,
    ViewingPubkey,
};
