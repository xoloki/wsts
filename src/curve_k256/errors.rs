//! Errors shared by the curve types.

use core::fmt::{Display, Formatter, Result as FmtResult};

#[derive(Debug, Clone, PartialEq, Eq)]
/// Errors decoding base58
pub enum Base58Error {
    /// The input was not valid base58
    Decode,
}

impl Display for Base58Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for Base58Error {}

#[derive(Debug, Clone, PartialEq, Eq)]
/// Errors converting between representations
pub enum ConversionError {
    /// The input had the wrong number of bytes
    WrongNumberOfBytes(usize),
    /// The input was not valid base58
    Base58(Base58Error),
}

impl Display for ConversionError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for ConversionError {}
