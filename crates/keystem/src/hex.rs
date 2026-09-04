use core::fmt;

/// Writes `bytes` as lowercase hex, the form every consumer already logs
/// public key material in.
pub(crate) fn write_hex(f: &mut fmt::Formatter<'_>, bytes: &[u8]) -> fmt::Result {
    for byte in bytes {
        write!(f, "{byte:02x}")?
    }
    Ok(())
}
