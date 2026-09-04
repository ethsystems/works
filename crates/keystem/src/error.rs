#[cfg(any(feature = "spend", feature = "viewing"))]
use core::fmt;

/// Bytes at or above the field modulus.
#[cfg(feature = "spend")]
#[cfg_attr(docsrs, doc(cfg(feature = "spend")))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NonCanonical;

#[cfg(feature = "spend")]
#[cfg_attr(docsrs, doc(cfg(feature = "spend")))]
impl fmt::Display for NonCanonical {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bytes are not a canonical field element")
    }
}

#[cfg(feature = "spend")]
#[cfg_attr(docsrs, doc(cfg(feature = "spend")))]
impl core::error::Error for NonCanonical {}

/// Returned or embedded by custody that refuses to reveal its scalar.
#[cfg(feature = "spend")]
#[cfg_attr(docsrs, doc(cfg(feature = "spend")))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NotExportable;

#[cfg(feature = "spend")]
#[cfg_attr(docsrs, doc(cfg(feature = "spend")))]
impl fmt::Display for NotExportable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "custody refuses to export the spending scalar")
    }
}

#[cfg(feature = "spend")]
#[cfg_attr(docsrs, doc(cfg(feature = "spend")))]
impl core::error::Error for NotExportable {}

/// Bytes that decode to no valid key for the chosen KEM.
#[cfg(feature = "viewing")]
#[cfg_attr(docsrs, doc(cfg(feature = "viewing")))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidKey;

#[cfg(feature = "viewing")]
#[cfg_attr(docsrs, doc(cfg(feature = "viewing")))]
impl fmt::Display for InvalidKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bytes are not a valid key for this kem")
    }
}

#[cfg(feature = "viewing")]
#[cfg_attr(docsrs, doc(cfg(feature = "viewing")))]
impl core::error::Error for InvalidKey {}

/// Bytes that decode to no owner-and-viewing credential pair.
#[cfg(all(feature = "spend", feature = "viewing"))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "spend", feature = "viewing"))))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidAddress;

#[cfg(all(feature = "spend", feature = "viewing"))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "spend", feature = "viewing"))))]
impl fmt::Display for InvalidAddress {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bytes are not an owner and viewing credential pair")
    }
}

#[cfg(all(feature = "spend", feature = "viewing"))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "spend", feature = "viewing"))))]
impl core::error::Error for InvalidAddress {}
