//! Disclosure-channel markers.
//!
//! Mixing a compliance-viewing branch with an ordinary incoming-viewing branch
//! is a correlation risk, so each channel is its own type and the compiler
//! keeps them apart. Consumers add channels by defining their own empty type;
//! nothing here is a closed set.

/// Ordinary incoming-viewing channel.
pub enum Incoming {}

/// Owner-side compliance channel.
pub enum Compliance {}

/// Audit-committee channel.
pub enum Audit {}
