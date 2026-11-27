//! Traits for working with the curve types.

use super::{point::Point, scalar::Scalar};

/// A trait which allows wrapping up types to be used in multimult without excessive copying
pub trait MultiMult {
    /// return the Scalar at index i
    fn get_scalar(&self, i: usize) -> &Scalar;

    /// return the Point at index i
    fn get_point(&self, i: usize) -> &Point;

    /// return the number of scalars and points to multimult
    fn get_size(&self) -> usize;

    /// return an optimum scratch size, or None if there is none
    ///
    /// Retained for compatibility with the libsecp256k1 backend, which sized a scratch arena
    /// for its multiexponentiation. The `k256` path allocates its own buckets, so this is
    /// ignored.
    fn get_scratch_size(&self) -> Option<usize> {
        Some(self.get_size() * 512)
    }
}
