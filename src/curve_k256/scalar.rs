//! Scalars: integers modulo the secp256k1 group order.

use core::{
    fmt::{Debug, Display, Formatter, Result as FmtResult},
    hash::{Hash, Hasher},
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use k256::{elliptic_curve::ops::Reduce, FieldBytes};
use num_traits::{One, Zero};
use rand_core::{CryptoRng, RngCore};
use serde::{
    de::{self, Deserialize, Deserializer, Visitor},
    ser::{Serialize, Serializer},
};

use super::errors::{Base58Error, ConversionError};

#[derive(Debug, Clone)]
/// Errors in scalar operations
pub enum Error {
    /// Error converting a scalar
    Conversion(ConversionError),
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for Error {}

/// A scalar modulo the secp256k1 group order.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct Scalar {
    pub(crate) scalar: k256::Scalar,
}

impl Scalar {
    /// Construct a zero scalar
    pub fn new() -> Self {
        Self {
            scalar: k256::Scalar::ZERO,
        }
    }

    /// Construct a random scalar
    ///
    /// Thirty-two random bytes reduced modulo the group order, which is how the libsecp256k1
    /// backend did it. The bias this leaves is bounded by the gap between `2^256` and the order,
    /// around `2^-128`. It deliberately avoids `ff::Field::random`, which would tie this
    /// signature to `k256`'s `rand_core`, a different major version from the one WSTS exposes.
    pub fn random<T: RngCore + CryptoRng>(rng: &mut T) -> Self {
        let mut bytes = [0u8; 32];
        rng.fill_bytes(&mut bytes);
        Self::from(bytes)
    }

    /// Set this scalar to a small integer
    pub fn set_int(&mut self, i: u32) {
        self.scalar = k256::Scalar::from(u64::from(i));
    }

    /// Return the low 32 bits of this scalar
    pub fn get_u32(&self) -> u32 {
        let bytes = self.to_bytes();
        u32::from_be_bytes([bytes[28], bytes[29], bytes[30], bytes[31]])
    }

    /// Invert this scalar, returning zero if it is zero
    ///
    /// The libsecp256k1 backend returned zero for a zero input rather than failing, and callers
    /// rely on that, so the `CtOption` is unwrapped to zero rather than panicking.
    pub fn invert(&self) -> Scalar {
        Self {
            scalar: Option::<k256::Scalar>::from(self.scalar.invert())
                .unwrap_or(k256::Scalar::ZERO),
        }
    }

    /// Return this scalar as 32 big-endian bytes
    pub fn to_bytes(&self) -> [u8; 32] {
        self.scalar.to_bytes().into()
    }

    /// Raise `x` to the power `n` by square and multiply
    pub fn square_and_multiply(x: &Scalar, n: &Scalar) -> Scalar {
        let mut result = Scalar::one();
        let mut base = *x;

        // Big-endian bytes, so walk them in reverse to go from the least significant bit up.
        for byte in n.to_bytes().iter().rev() {
            for bit in 0..8 {
                if byte & (1 << bit) != 0 {
                    result *= base;
                }
                base = base * base;
            }
        }

        result
    }

    /// Raise `x` to the power `n` by square and multiply
    pub fn square_and_multiply_usize(x: &Scalar, n: usize) -> Scalar {
        Self::square_and_multiply_u64(x, n as u64)
    }

    /// Raise `x` to the power `n` by square and multiply
    pub fn square_and_multiply_u32(x: &Scalar, n: u32) -> Scalar {
        Self::square_and_multiply_u64(x, u64::from(n))
    }

    fn square_and_multiply_u64(x: &Scalar, mut n: u64) -> Scalar {
        let mut result = Scalar::one();
        let mut base = *x;

        while n > 0 {
            if n & 1 == 1 {
                result *= base;
            }
            base = base * base;
            n >>= 1;
        }

        result
    }
}

impl Display for Scalar {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", bs58::encode(self.to_bytes()).into_string())
    }
}

impl Hash for Scalar {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_bytes().hash(state);
    }
}

impl Zero for Scalar {
    fn zero() -> Self {
        Self::new()
    }

    fn is_zero(&self) -> bool {
        bool::from(self.scalar.is_zero())
    }
}

impl One for Scalar {
    fn one() -> Self {
        Self {
            scalar: k256::Scalar::ONE,
        }
    }
}

impl From<u32> for Scalar {
    fn from(i: u32) -> Self {
        Self {
            scalar: k256::Scalar::from(u64::from(i)),
        }
    }
}

impl From<[u8; 32]> for Scalar {
    /// Reduce 32 big-endian bytes modulo the group order
    fn from(bytes: [u8; 32]) -> Self {
        let field_bytes = FieldBytes::from(bytes);
        Self {
            scalar: <k256::Scalar as Reduce<FieldBytes>>::reduce(&field_bytes),
        }
    }
}

impl TryFrom<&[u8]> for Scalar {
    type Error = Error;

    fn try_from(bytes: &[u8]) -> Result<Self, Error> {
        match bytes.len() {
            32 => {
                let mut data = [0u8; 32];
                data.clone_from_slice(bytes);
                Ok(Scalar::from(data))
            }
            n => Err(Error::Conversion(ConversionError::WrongNumberOfBytes(n))),
        }
    }
}

impl TryFrom<&str> for Scalar {
    type Error = Error;

    fn try_from(s: &str) -> Result<Self, Error> {
        match bs58::decode(s).into_vec() {
            Ok(bytes) => Scalar::try_from(&bytes[..]),
            Err(_) => Err(Error::Conversion(ConversionError::Base58(
                Base58Error::Decode,
            ))),
        }
    }
}

impl From<Scalar> for String {
    fn from(s: Scalar) -> String {
        bs58::encode(s.to_bytes()).into_string()
    }
}

impl Serialize for Scalar {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_bytes(&self.to_bytes())
    }
}

struct ScalarVisitor;

impl<'de> Visitor<'de> for ScalarVisitor {
    type Value = Scalar;

    fn expecting(&self, formatter: &mut Formatter) -> FmtResult {
        formatter.write_str("an array of bytes which represents a scalar for the secp256k1 curve")
    }

    fn visit_bytes<E: de::Error>(self, value: &[u8]) -> Result<Self::Value, E> {
        Scalar::try_from(value).map_err(|e| E::custom(format!("{:?}", e)))
    }

    fn visit_seq<A: de::SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
        let mut v = Vec::new();

        while let Ok(Some(x)) = seq.next_element() {
            v.push(x);
        }

        self.visit_bytes(&v)
    }
}

impl<'de> Deserialize<'de> for Scalar {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Scalar, D::Error> {
        deserializer.deserialize_bytes(ScalarVisitor)
    }
}

macro_rules! binop {
    ($trait:ident, $method:ident) => {
        impl $trait for Scalar {
            type Output = Scalar;
            fn $method(self, other: Scalar) -> Scalar {
                Scalar {
                    scalar: self.scalar.$method(other.scalar),
                }
            }
        }

        impl $trait<&Scalar> for Scalar {
            type Output = Scalar;
            fn $method(self, other: &Scalar) -> Scalar {
                Scalar {
                    scalar: self.scalar.$method(other.scalar),
                }
            }
        }

        impl $trait<Scalar> for &Scalar {
            type Output = Scalar;
            fn $method(self, other: Scalar) -> Scalar {
                Scalar {
                    scalar: self.scalar.$method(other.scalar),
                }
            }
        }

        impl $trait<&Scalar> for &Scalar {
            type Output = Scalar;
            fn $method(self, other: &Scalar) -> Scalar {
                Scalar {
                    scalar: self.scalar.$method(other.scalar),
                }
            }
        }
    };
}

binop!(Add, add);
binop!(Sub, sub);
binop!(Mul, mul);

impl AddAssign for Scalar {
    fn add_assign(&mut self, other: Scalar) {
        self.scalar += other.scalar;
    }
}

impl AddAssign<&Scalar> for Scalar {
    fn add_assign(&mut self, other: &Scalar) {
        self.scalar += other.scalar;
    }
}

impl SubAssign for Scalar {
    fn sub_assign(&mut self, other: Scalar) {
        self.scalar -= other.scalar;
    }
}

impl MulAssign for Scalar {
    fn mul_assign(&mut self, other: Scalar) {
        self.scalar *= other.scalar;
    }
}

impl MulAssign<&Scalar> for Scalar {
    fn mul_assign(&mut self, other: &Scalar) {
        self.scalar *= other.scalar;
    }
}

impl Neg for Scalar {
    type Output = Scalar;

    fn neg(self) -> Scalar {
        Scalar {
            scalar: -self.scalar,
        }
    }
}

/// Division is multiplication by the inverse, and a zero divisor yields zero, matching the
/// libsecp256k1 backend rather than panicking.
impl Div for Scalar {
    type Output = Scalar;

    #[allow(
        clippy::suspicious_arithmetic_impl,
        reason = "in a field, division is multiplication by the inverse"
    )]
    fn div(self, other: Scalar) -> Scalar {
        self * other.invert()
    }
}

impl Div<&Scalar> for Scalar {
    type Output = Scalar;

    #[allow(
        clippy::suspicious_arithmetic_impl,
        reason = "in a field, division is multiplication by the inverse"
    )]
    fn div(self, other: &Scalar) -> Scalar {
        self * other.invert()
    }
}

impl Div<Scalar> for &Scalar {
    type Output = Scalar;

    #[allow(
        clippy::suspicious_arithmetic_impl,
        reason = "in a field, division is multiplication by the inverse"
    )]
    fn div(self, other: Scalar) -> Scalar {
        *self * other.invert()
    }
}

impl Div<&Scalar> for &Scalar {
    type Output = Scalar;

    #[allow(
        clippy::suspicious_arithmetic_impl,
        reason = "in a field, division is multiplication by the inverse"
    )]
    fn div(self, other: &Scalar) -> Scalar {
        *self * other.invert()
    }
}

impl DivAssign for Scalar {
    fn div_assign(&mut self, other: Scalar) {
        *self = *self / other;
    }
}

impl Mul<super::point::Point> for Scalar {
    type Output = super::point::Point;

    fn mul(self, p: super::point::Point) -> super::point::Point {
        p * self
    }
}

impl Mul<&super::point::Point> for Scalar {
    type Output = super::point::Point;

    fn mul(self, p: &super::point::Point) -> super::point::Point {
        p * &self
    }
}

impl Mul<super::point::Point> for &Scalar {
    type Output = super::point::Point;

    fn mul(self, p: super::point::Point) -> super::point::Point {
        p * *self
    }
}

impl Mul<&super::point::Point> for &Scalar {
    type Output = super::point::Point;

    fn mul(self, p: &super::point::Point) -> super::point::Point {
        p * self
    }
}

#[cfg(test)]
mod tests {
    use super::Scalar;
    use num_traits::{One, Zero};
    use p256k1::scalar::Scalar as Ref;
    use rand_core::{RngCore, SeedableRng};

    /// Deterministic byte strings, including ones above the group order so the reduction in
    /// `From<[u8; 32]>` is exercised rather than just the identity path.
    fn samples() -> Vec<[u8; 32]> {
        let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(0x5c01_a125);
        let mut v = vec![[0u8; 32], [0xff; 32], {
            let mut b = [0u8; 32];
            b[31] = 1;
            b
        }];
        for _ in 0..64 {
            let mut b = [0u8; 32];
            rng.fill_bytes(&mut b);
            v.push(b);
        }
        v
    }

    /// Every operation must agree with the libsecp256k1 backend bit for bit, since serialized
    /// state written by one has to be readable by the other.
    #[test]
    fn agrees_with_p256k1() {
        assert_eq!(Scalar::zero().to_bytes(), Ref::zero().to_bytes(), "zero");
        assert_eq!(Scalar::one().to_bytes(), Ref::one().to_bytes(), "one");
        assert_eq!(Scalar::new().to_bytes(), Ref::new().to_bytes(), "new");

        for i in [0u32, 1, 2, 7, u32::MAX] {
            assert_eq!(
                Scalar::from(i).to_bytes(),
                Ref::from(i).to_bytes(),
                "From<u32>({i})"
            );
        }

        let bytes = samples();
        for (i, b) in bytes.iter().enumerate() {
            let (a, r) = (Scalar::from(*b), Ref::from(*b));
            assert_eq!(a.to_bytes(), r.to_bytes(), "From<[u8; 32]> at {i}");
            assert_eq!(a.get_u32(), r.get_u32(), "get_u32 at {i}");
            assert_eq!(
                a.invert().to_bytes(),
                r.invert().to_bytes(),
                "invert at {i}"
            );
            assert_eq!((-a).to_bytes(), (-r).to_bytes(), "neg at {i}");
            assert_eq!(a.to_string(), r.to_string(), "Display at {i}");
            assert_eq!(a.is_zero(), r.is_zero(), "is_zero at {i}");
        }

        for w in bytes.windows(2) {
            let (a0, a1) = (Scalar::from(w[0]), Scalar::from(w[1]));
            let (r0, r1) = (Ref::from(w[0]), Ref::from(w[1]));

            assert_eq!((a0 + a1).to_bytes(), (r0 + r1).to_bytes(), "add");
            assert_eq!((a0 - a1).to_bytes(), (r0 - r1).to_bytes(), "sub");
            assert_eq!((a0 * a1).to_bytes(), (r0 * r1).to_bytes(), "mul");
            assert_eq!((a0 / a1).to_bytes(), (r0 / r1).to_bytes(), "div");
            assert_eq!(
                Scalar::square_and_multiply(&a0, &a1).to_bytes(),
                Ref::square_and_multiply(&r0, &r1).to_bytes(),
                "square_and_multiply"
            );
        }

        for n in [0usize, 1, 2, 3, 17, 255, 256] {
            let a = Scalar::from(bytes[5]);
            let r = Ref::from(bytes[5]);
            assert_eq!(
                Scalar::square_and_multiply_usize(&a, n).to_bytes(),
                Ref::square_and_multiply_usize(&r, n).to_bytes(),
                "square_and_multiply_usize({n})"
            );
        }
    }

    /// The serde encoding has to be byte-identical, or saved state and network packets written
    /// by a `p256k1` build stop deserializing.
    #[test]
    fn serde_encoding_matches_p256k1() {
        for b in samples() {
            let mut mine = Vec::new();
            let mut theirs = Vec::new();
            ciborium::into_writer(&Scalar::from(b), &mut mine).unwrap();
            ciborium::into_writer(&Ref::from(b), &mut theirs).unwrap();
            assert_eq!(mine, theirs, "serialized form");

            let round: Scalar = ciborium::from_reader(&mine[..]).unwrap();
            assert_eq!(round.to_bytes(), Scalar::from(b).to_bytes(), "round trip");
        }
    }
}
