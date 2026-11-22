//! Elements of the secp256k1 base field.

use core::{
    fmt::{Display, Formatter, Result as FmtResult},
    hash::{Hash, Hasher},
    ops::{Add, AddAssign, BitXor, Mul, MulAssign, Neg, Sub, SubAssign},
};

use k256::elliptic_curve::bigint::{const_monty_params, modular::ConstMontyForm, U256};
use num_traits::{One, Zero};
use rand_core::{CryptoRng, RngCore};
use serde::{
    de::{self, Deserialize, Deserializer, Visitor},
    ser::{Serialize, Serializer},
};

use super::{
    errors::ConversionError,
    scalar::{Error as ScalarError, Scalar},
};

/// Errors in field operations
pub type Error = ScalarError;

/// The field modulus
pub const P: [u8; 32] = [
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE, 0xFF, 0xFF, 0xFC, 0x2F,
];

const P_UINT: U256 = U256::from_be_slice(&P);

const_monty_params!(
    Modulus,
    U256,
    "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"
);

type Monty = ConstMontyForm<Modulus, { U256::LIMBS }>;

/// An element of the secp256k1 base field, i.e. an integer modulo `p`.
///
/// `k256` does not export its own field type, and no sibling curve in that workspace does
/// either, so this is built on the Montgomery arithmetic in `crypto-bigint` that `k256`'s field
/// ultimately rests on. Arithmetic is needed, not decoration: lifting an x-coordinate to a point
/// is defined in terms of it.
///
/// Unlike the libsecp256k1 backend there is no non-normalized state, so [`Element::normalize`]
/// and [`Element::normalize_var`] are the identity. Values are always canonical, which is why
/// equality can be bytewise.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct Element {
    monty: Monty,
}

impl Element {
    /// Construct a zero element
    pub fn new() -> Self {
        Self { monty: Monty::ZERO }
    }

    /// Construct a random element
    pub fn random<T: RngCore + CryptoRng>(rng: &mut T) -> Self {
        // Rejection sampling: the modulus is within 2^-32 of 2^256, so this retries almost never,
        // and unlike reduction it is unbiased.
        loop {
            let mut bytes = [0u8; 32];
            rng.fill_bytes(&mut bytes);
            let candidate = U256::from_be_slice(&bytes);
            if candidate < P_UINT {
                return Self {
                    monty: Monty::new(&candidate),
                };
            }
        }
    }

    /// Set this element to a small integer
    pub fn set_int(&mut self, i: i32) {
        *self = Self::from(i);
    }

    /// Invert this element, returning zero if it is zero
    ///
    /// Zero has no inverse; the libsecp256k1 backend returned zero rather than failing and
    /// callers rely on that.
    pub fn invert(&self) -> Element {
        Self {
            monty: Option::<Monty>::from(self.monty.invert()).unwrap_or(Monty::ZERO),
        }
    }

    /// Return this element as 32 big-endian bytes
    pub fn to_bytes(&self) -> [u8; 32] {
        self.monty.retrieve().to_be_bytes().into()
    }

    /// Return true if this element is odd
    pub fn is_odd(&self) -> bool {
        self.to_bytes()[31] & 1 == 1
    }

    /// Return the normalized form of this element
    ///
    /// Values here are always canonical, so this is the identity. It exists because the
    /// libsecp256k1 backend carried unnormalized intermediates and callers normalized explicitly.
    pub fn normalize(&self) -> Self {
        *self
    }

    /// Return the normalized form of this element, in variable time
    pub fn normalize_var(&self) -> Self {
        *self
    }

    /// Raise `x` to the power `n`
    pub fn square_and_multiply(x: &Self, n: &Self) -> Self {
        let mut result = Self::one();
        let mut base = *x;

        // Big-endian exponent bytes, so walk them in reverse to go from the least significant
        // bit upward.
        for byte in n.to_bytes().iter().rev() {
            for bit in 0..8 {
                if byte & (1 << bit) != 0 {
                    result *= base;
                }
                base *= base;
            }
        }

        result
    }
}

impl Display for Element {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", bs58::encode(self.to_bytes()).into_string())
    }
}

impl PartialOrd for Element {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Element {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.to_bytes().cmp(&other.to_bytes())
    }
}

impl Hash for Element {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_bytes().hash(state);
    }
}

impl Zero for Element {
    fn zero() -> Self {
        Self::new()
    }

    fn is_zero(&self) -> bool {
        self.monty == Monty::ZERO
    }
}

impl One for Element {
    fn one() -> Self {
        Self { monty: Monty::ONE }
    }
}

impl From<i32> for Element {
    fn from(i: i32) -> Self {
        let magnitude = Self {
            monty: Monty::new(&U256::from_u32(i.unsigned_abs())),
        };

        if i < 0 {
            -magnitude
        } else {
            magnitude
        }
    }
}

impl From<[u8; 32]> for Element {
    /// Interpret 32 big-endian bytes as a field element, mapping anything at or above the field
    /// modulus to zero.
    ///
    /// This is a decoder, so it rejects rather than reduces, and that is load-bearing. Taproot
    /// proofs deserialize their `r` straight into this type. Reducing would make the encoding
    /// non-unique: for a small x-coordinate `x`, the bytes of `x + p` would decode to `x` and the
    /// proof would verify, since everything downstream works from the canonical bytes. The
    /// libsecp256k1 backend kept such input verbatim and then compared it bytewise against a
    /// canonical x-coordinate, so it rejected too, by a different route. Zero is not a valid
    /// x-coordinate, so mapping out-of-range input to it preserves that.
    fn from(bytes: [u8; 32]) -> Self {
        let value = U256::from_be_slice(&bytes);

        if value >= P_UINT {
            return Self::new();
        }

        Self {
            monty: Monty::new(&value),
        }
    }
}

impl From<Scalar> for Element {
    fn from(x: Scalar) -> Self {
        Self::from(x.to_bytes())
    }
}

impl TryFrom<&[u8]> for Element {
    type Error = Error;

    fn try_from(bytes: &[u8]) -> Result<Self, Error> {
        match bytes.len() {
            32 => {
                let mut data = [0u8; 32];
                data.clone_from_slice(bytes);
                Ok(Element::from(data))
            }
            n => Err(Error::Conversion(ConversionError::WrongNumberOfBytes(n))),
        }
    }
}

impl Serialize for Element {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_bytes(&self.to_bytes())
    }
}

struct ElementVisitor;

impl<'de> Visitor<'de> for ElementVisitor {
    type Value = Element;

    fn expecting(&self, formatter: &mut Formatter) -> FmtResult {
        formatter.write_str("an array of bytes which represents a secp256k1 field element")
    }

    fn visit_bytes<E: de::Error>(self, value: &[u8]) -> Result<Self::Value, E> {
        Element::try_from(value).map_err(|e| E::custom(format!("{:?}", e)))
    }

    fn visit_seq<A: de::SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
        let mut v = Vec::new();

        while let Ok(Some(x)) = seq.next_element() {
            v.push(x);
        }

        self.visit_bytes(&v)
    }
}

impl<'de> Deserialize<'de> for Element {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Element, D::Error> {
        deserializer.deserialize_bytes(ElementVisitor)
    }
}

macro_rules! element_binop {
    ($trait:ident, $method:ident, $op:tt) => {
        impl $trait for Element {
            type Output = Element;
            fn $method(self, other: Element) -> Element {
                Element { monty: self.monty $op other.monty }
            }
        }

        impl $trait<&Element> for Element {
            type Output = Element;
            fn $method(self, other: &Element) -> Element {
                Element { monty: self.monty $op other.monty }
            }
        }

        impl $trait<Element> for &Element {
            type Output = Element;
            fn $method(self, other: Element) -> Element {
                Element { monty: self.monty $op other.monty }
            }
        }

        impl $trait<&Element> for &Element {
            type Output = Element;
            fn $method(self, other: &Element) -> Element {
                Element { monty: self.monty $op other.monty }
            }
        }
    };
}

element_binop!(Add, add, +);
element_binop!(Sub, sub, -);
element_binop!(Mul, mul, *);

impl AddAssign for Element {
    fn add_assign(&mut self, other: Element) {
        self.monty = self.monty + other.monty;
    }
}

impl SubAssign for Element {
    fn sub_assign(&mut self, other: Element) {
        self.monty = self.monty - other.monty;
    }
}

impl MulAssign for Element {
    fn mul_assign(&mut self, other: Element) {
        self.monty = self.monty * other.monty;
    }
}

impl Neg for Element {
    type Output = Element;

    fn neg(self) -> Element {
        Element { monty: -self.monty }
    }
}

impl Neg for &Element {
    type Output = Element;

    fn neg(self) -> Element {
        -*self
    }
}

/// Exponentiation, spelled `^` as the libsecp256k1 backend spelled it.
impl BitXor for Element {
    type Output = Element;

    fn bitxor(self, rhs: Element) -> Element {
        Element::square_and_multiply(&self, &rhs)
    }
}

impl BitXor<Element> for &Element {
    type Output = Element;

    fn bitxor(self, rhs: Element) -> Element {
        Element::square_and_multiply(self, &rhs)
    }
}

impl BitXor<&Element> for Element {
    type Output = Element;

    fn bitxor(self, rhs: &Element) -> Element {
        Element::square_and_multiply(&self, rhs)
    }
}

impl BitXor<&Element> for &Element {
    type Output = Element;

    fn bitxor(self, rhs: &Element) -> Element {
        Element::square_and_multiply(self, rhs)
    }
}

#[cfg(test)]
mod tests {
    use super::{Element, P};
    use crate::curve::point::{Point, G};
    use num_traits::{One, Zero};
    use p256k1::field::Element as Ref;
    use rand_core::{RngCore, SeedableRng};

    /// Deterministic in-range field elements. Out-of-range bytes are skipped, since the two
    /// backends deliberately differ there.
    fn samples(n: usize) -> Vec<[u8; 32]> {
        let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(0xf1e1_d000);
        let mut v = vec![[0u8; 32], {
            let mut b = [0u8; 32];
            b[31] = 1;
            b
        }];
        while v.len() < n {
            let mut b = [0u8; 32];
            rng.fill_bytes(&mut b);
            if b < P {
                v.push(b);
            }
        }
        v
    }

    /// Field arithmetic must agree with libsecp256k1's, since the curve operations built on it do.
    #[test]
    fn arithmetic_agrees_with_p256k1() {
        assert_eq!(Element::zero().to_bytes(), Ref::zero().to_bytes(), "zero");
        assert_eq!(Element::one().to_bytes(), Ref::one().to_bytes(), "one");
        assert_eq!(Element::new().to_bytes(), Ref::new().to_bytes(), "new");

        // Only 0..=0x7FFF is compared: the reference passes its argument straight to
        // `secp256k1_fe_set_int`, which libsecp256k1 documents as requiring `0 <= a <= 0x7FFF`,
        // and in a release build there is no check. Outside that range it returns limb garbage,
        // so it is not an oracle there.
        for i in [0i32, 1, 2, 4, 7, 0x7fff] {
            assert_eq!(
                Element::from(i).to_bytes(),
                Ref::from(i).to_bytes(),
                "From<i32>({i})"
            );

            let (mut a, mut r) = (Element::new(), Ref::new());
            a.set_int(i);
            r.set_int(i);
            assert_eq!(a.to_bytes(), r.to_bytes(), "set_int({i})");
        }

        // Negative and large inputs are where the reference is unreliable. This backend gives the
        // mathematically correct answer instead, so the two deliberately differ.
        let mut minus_one = P;
        minus_one[31] -= 1;
        assert_eq!(Element::from(-1).to_bytes(), minus_one, "-1 is p - 1 here");
        assert_ne!(
            Ref::from(-1).to_bytes(),
            minus_one,
            "libsecp256k1 did not compute p - 1 for -1"
        );

        for (i, b) in samples(48).iter().enumerate() {
            let (a, r) = (Element::from(*b), Ref::from(*b));

            assert_eq!(a.to_bytes(), r.to_bytes(), "From<[u8; 32]> at {i}");
            assert_eq!(a.is_odd(), r.is_odd(), "is_odd at {i}");
            assert_eq!(a.is_zero(), r.is_zero(), "is_zero at {i}");
            assert_eq!(a.to_string(), r.to_string(), "Display at {i}");
            assert_eq!((-a).to_bytes(), (Ref::zero() - r).to_bytes(), "neg at {i}");
            assert_eq!(
                a.invert().to_bytes(),
                r.invert().to_bytes(),
                "invert at {i}"
            );
            assert_eq!(
                a.normalize().to_bytes(),
                r.normalize().to_bytes(),
                "normalize at {i}"
            );
            assert_eq!(
                a.normalize_var().to_bytes(),
                r.normalize_var().to_bytes(),
                "normalize_var at {i}"
            );
        }

        for w in samples(24).windows(2) {
            let (a0, a1) = (Element::from(w[0]), Element::from(w[1]));
            let (r0, r1) = (Ref::from(w[0]), Ref::from(w[1]));

            assert_eq!((a0 + a1).to_bytes(), (r0 + r1).to_bytes(), "add");
            assert_eq!((a0 - a1).to_bytes(), (r0 - r1).to_bytes(), "sub");
            assert_eq!((a0 * a1).to_bytes(), (r0 * r1).to_bytes(), "mul");
            assert_eq!(
                Element::square_and_multiply(&a0, &a1).to_bytes(),
                Ref::square_and_multiply(&r0, &r1).to_bytes(),
                "square_and_multiply"
            );
            assert_eq!((a0 ^ a1).to_bytes(), (r0 ^ r1).to_bytes(), "pow via ^");
            assert_eq!(
                a0.cmp(&a1),
                r0.to_bytes().cmp(&r1.to_bytes()),
                "ordering is numeric"
            );

            // The reference is normalized before comparing: its `+=` and `*=` leave the element
            // unnormalized, and its byte accessor then reports an unpropagated carry rather than
            // the value. Values here are always canonical, so there is nothing to normalize.
            let (mut acc, mut ref_acc) = (a0, r0);
            acc += a1;
            ref_acc += r1;
            assert_eq!(acc.to_bytes(), ref_acc.normalize().to_bytes(), "add_assign");

            let (mut acc, mut ref_acc) = (a0, r0);
            acc *= a1;
            ref_acc *= r1;
            assert_eq!(acc.to_bytes(), ref_acc.normalize().to_bytes(), "mul_assign");
        }
    }

    /// Serde output must be byte-identical, since taproot proofs carry an `Element`.
    #[test]
    fn serde_encoding_matches_p256k1() {
        for b in samples(16) {
            let (mut mine, mut theirs) = (Vec::new(), Vec::new());
            ciborium::into_writer(&Element::from(b), &mut mine).unwrap();
            ciborium::into_writer(&Ref::from(b), &mut theirs).unwrap();
            assert_eq!(mine, theirs, "serialized form");

            let round: Element = ciborium::from_reader(&mine[..]).unwrap();
            assert_eq!(round, Element::from(b), "round trip");
        }
    }

    /// Lifting an x-coordinate is field arithmetic, and this type has to be able to express it.
    ///
    /// [`Point::lift_x`] delegates to `k256`'s `decompress`, which is the audited, constant-time
    /// path and is what production uses. This recomputes it here the way the libsecp256k1 backend
    /// did, out of `Element` operations alone, and checks the two agree. It is both a cross-check
    /// of the square root and a standing demonstration that the public surface of this type is
    /// sufficient for the job.
    fn lift_x_in_field_arithmetic(x: &Element) -> Option<(Element, Element)> {
        // `P` reduces to zero, so this is the additive identity, exactly as it was there.
        let fp = Element::from(P);
        let f4 = Element::from(4);

        // 4 inverse is (p + 1) / 4, the square root exponent for p = 3 mod 4.
        let fp14 = (fp + Element::one()) * f4.invert();

        let c = x * x * x + Element::from(7);
        let y = c ^ fp14;

        if c != y * y {
            return None;
        }

        Some((*x, if y.is_odd() { fp - y } else { y }))
    }

    #[test]
    fn lift_x_matches_field_arithmetic() {
        let mut lifted = 0;
        let mut rejected = 0;

        // Real x-coordinates, which must lift, and arbitrary field elements, about half of which
        // are not on the curve and must not.
        let mut xs: Vec<Element> = vec![G.x()];
        for b in samples(24) {
            xs.push(Point::from(crate::curve::scalar::Scalar::from(b)).x());
            xs.push(Element::from(b));
        }

        for (i, x) in xs.iter().enumerate() {
            match (Point::lift_x(x), lift_x_in_field_arithmetic(x)) {
                (Ok(p), Some((fx, fy))) => {
                    assert_eq!(p.x(), fx, "x disagrees at {i}");
                    assert_eq!(p.y(), fy, "y disagrees at {i}");
                    assert!(p.has_even_y(), "lift must give even y at {i}");
                    lifted += 1;
                }
                (Err(_), None) => rejected += 1,
                (a, b) => panic!(
                    "lift_x disagrees at {i}: {:?} vs {:?}",
                    a.is_ok(),
                    b.is_some()
                ),
            }
        }

        // Both outcomes must actually occur, or the test proves nothing.
        assert!(
            lifted > 0 && rejected > 0,
            "lifted {lifted}, rejected {rejected}"
        );
    }
}
