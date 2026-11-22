#![deny(missing_docs)]
#![doc = include_str!("../README.md")]
// Included so that the examples in USAGE.md are compiled as doctests;
// otherwise nothing keeps them in step with the API.
#![doc = include_str!("../USAGE.md")]

/// test bitcoin/taproot integration using libbitcoin_consensus
#[cfg(any(test, feature = "testing"))]
pub mod btc;
/// Types which are common to both v1 and v2
#[allow(clippy::op_ref)]
pub mod common;
/// Functions to perform various computations needed for v1 and v2
pub mod compute;
/// Errors which are returned from objects and functions
pub mod errors;
/// Network messages
pub mod net;
/// Schnorr utility types
#[allow(clippy::op_ref)]
pub mod schnorr;
/// State machines
#[allow(clippy::result_large_err)]
pub mod state_machine;
/// Functions for doing BIP-340 schnorr proofs and other taproot actions
pub mod taproot;
/// Traits which are used for v1 and v2
pub mod traits;
/// Utilities for hashing and encryption
pub mod util;
/// Version 1 of WSTS, which encapsulates a number of parties using vanilla FROST
#[cfg(feature = "with_v1")]
#[allow(clippy::op_ref)]
pub mod v1;
/// Version 2 of WSTS, in which each party holds one polynomial and one nonce but may control many keys
#[allow(clippy::op_ref)]
pub mod v2;
/// Shamir secret sharing, used in distributed key generation
pub mod vss;

/// secp256k1 arithmetic, backed by RustCrypto `k256`.
///
/// Named for its backend but reached as [`curve`]: `wsts::curve::...` is the public path and
/// stays that way regardless of what implements it. A second backend would be a sibling module
/// and a `cfg`-selected re-export below, changing nothing for callers. Hidden from the docs so
/// that there is one documented path rather than two spellings of it.
#[doc(hidden)]
pub mod curve_k256;

/// secp256k1 arithmetic. Currently [`curve_k256`], which is backed by RustCrypto `k256`.
pub use curve_k256 as curve;
