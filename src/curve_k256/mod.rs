//! secp256k1 arithmetic, backed by RustCrypto [`k256`].
//!
//! This replaces the `p256k1` crate, which wrapped libsecp256k1 through bindgen and so put a C
//! toolchain in the path of every downstream build. The motivating gap was multiscalar
//! multiplication: `k256` had no Pippenger implementation, so its cost per element stayed flat
//! while libsecp256k1's fell, and WSTS leans on MSM heavily for large key counts. That gap is
//! closed by the bucketed Pippenger work this crate's `k256` revision carries.
//!
//! The API deliberately mirrors `p256k1`'s rather than being idiomatic `k256`, so that the rest
//! of the crate is untouched by the switch. Byte and serde encodings match it exactly: scalars
//! are 32 big-endian bytes and points are SEC1 compressed, both serialized as `serialize_bytes`,
//! so keys, saved DKG state and network packets written by a `p256k1` build stay readable.

pub mod ecdsa;
pub mod errors;
pub mod field;
pub mod keys;
pub mod point;
pub mod scalar;
pub mod traits;

pub use errors::{Base58Error, ConversionError};
