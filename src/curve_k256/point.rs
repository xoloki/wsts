//! Points on the secp256k1 curve.

use core::{
    fmt::{Debug, Display, Formatter, Result as FmtResult},
    hash::{Hash, Hasher},
    iter::Sum,
    ops::{Add, AddAssign, Mul, Neg, Sub},
};

use k256::{
    elliptic_curve::{
        ops::LinearCombination,
        point::{AffineCoordinates, DecompressPoint},
        sec1::ToSec1Point,
        subtle::Choice,
        Group,
    },
    AffinePoint, FieldBytes, ProjectivePoint,
};
use num_traits::Zero;
use serde::{
    de::{self, Deserialize, Deserializer, Visitor},
    ser::{Serialize, Serializer},
    Deserialize as DeserializeDerive, Serialize as SerializeDerive,
};

use super::{errors::ConversionError, field, scalar::Scalar, traits::MultiMult};

/// The base point
pub const G: Point = Point {
    point: ProjectivePoint::GENERATOR,
};

/// Group order
pub const N: [u8; 32] = [
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE,
    0xBA, 0xAE, 0xDC, 0xE6, 0xAF, 0x48, 0xA0, 0x3B, 0xBF, 0xD2, 0x5E, 0x8C, 0xD0, 0x36, 0x41, 0x41,
];

#[derive(Debug, Clone, SerializeDerive, DeserializeDerive, PartialEq)]
/// Errors in point operations
pub enum Error {
    /// Error doing multi-exponentiation
    MultiMultFailed,
    /// Error decompressing a point
    Conversion(ConversionError),
    /// Error lifting a field element into an even_y point
    LiftFailed,
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for Error {}

/// A point on the secp256k1 curve.
#[derive(Copy, Clone)]
pub struct Point {
    pub(crate) point: ProjectivePoint,
}

impl Point {
    /// Construct a new point
    pub fn new() -> Self {
        Self::identity()
    }

    /// Construct an identity point
    pub fn identity() -> Self {
        Self {
            point: ProjectivePoint::IDENTITY,
        }
    }

    #[allow(non_snake_case)]
    /// Return the base point
    pub fn G() -> Point {
        G
    }

    /// Return the compressed SEC1 encoding of this point
    ///
    /// The identity has no SEC1 encoding, and the libsecp256k1 backend emitted an even-tagged
    /// zero x-coordinate for it rather than failing, so that is reproduced here: serialized
    /// identity points have to round-trip, and WSTS stores them.
    pub fn compress(&self) -> Compressed {
        let mut data = [0u8; 33];

        if self.is_zero() {
            data[0] = 0x02;
            return Compressed { data };
        }

        let affine = self.point.to_affine();
        data[0] = if bool::from(affine.y_is_odd()) {
            0x03
        } else {
            0x02
        };
        data[1..].clone_from_slice(&affine.x());

        Compressed { data }
    }

    /// Perform a multi-exponentiation operation on the passed scalars and points
    pub fn multimult(scalars: Vec<Scalar>, points: Vec<Point>) -> Result<Point, Error> {
        if scalars.len() != points.len() {
            return Err(Error::MultiMultFailed);
        }

        let terms: Vec<_> = points
            .iter()
            .zip(scalars.iter())
            .map(|(p, s)| (p.point, s.scalar))
            .collect();

        Ok(Point {
            point: ProjectivePoint::lincomb_vartime(terms.as_slice()),
        })
    }

    /// Perform a multi-exponentiation operation on the passed object which implements the
    /// MultiMult trait
    ///
    /// The libsecp256k1 backend read the terms through a callback, so a large multiexponentiation
    /// never had to be materialized. `k256` takes a slice, so the terms are gathered first. The
    /// copies are of `Scalar` and `ProjectivePoint`, which are plain data.
    pub fn multimult_trait<T: MultiMult>(mm: &mut T) -> Result<Point, Error> {
        let terms: Vec<_> = (0..mm.get_size())
            .map(|i| (mm.get_point(i).point, mm.get_scalar(i).scalar))
            .collect();

        Ok(Point {
            point: ProjectivePoint::lincomb_vartime(terms.as_slice()),
        })
    }

    /// Return true if the y-coordinate of this point is even
    pub fn has_even_y(&self) -> bool {
        // The identity has no y; the libsecp256k1 backend reported it as even, since its
        // coordinates were zero.
        self.is_zero() || !bool::from(self.point.to_affine().y_is_odd())
    }

    /// Return the x-coordinate of this point as a field element
    pub fn x(&self) -> field::Element {
        if self.is_zero() {
            return field::Element::new();
        }

        field::Element::from(<[u8; 32]>::from(self.point.to_affine().x()))
    }

    /// Return the y-coordinate of this point as a field element
    pub fn y(&self) -> field::Element {
        if self.is_zero() {
            return field::Element::new();
        }

        // `AffineCoordinates` exposes only x and the parity of y, so recover y from the
        // uncompressed encoding.
        match self.point.to_affine().to_sec1_point(false).y() {
            Some(y) => field::Element::from(<[u8; 32]>::from(*y)),
            None => field::Element::new(),
        }
    }

    /// Lift a field element to the point with that x-coordinate and an even y-coordinate
    pub fn lift_x(x: &field::Element) -> Result<Point, Error> {
        let bytes = FieldBytes::from(x.to_bytes());

        Option::<AffinePoint>::from(AffinePoint::decompress(&bytes, Choice::from(0)))
            .map(|affine| Point {
                point: ProjectivePoint::from(affine),
            })
            .ok_or(Error::LiftFailed)
    }
}

impl Default for Point {
    fn default() -> Self {
        Self::identity()
    }
}

impl Debug for Point {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self)
    }
}

impl Display for Point {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", bs58::encode(self.compress().data).into_string())
    }
}

impl PartialEq for Point {
    fn eq(&self, other: &Self) -> bool {
        self.point == other.point
    }
}

impl Eq for Point {}

impl Hash for Point {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.compress().data.hash(state);
    }
}

impl Zero for Point {
    fn zero() -> Self {
        Self::identity()
    }

    fn is_zero(&self) -> bool {
        bool::from(self.point.is_identity())
    }
}

impl From<Scalar> for Point {
    fn from(x: Scalar) -> Self {
        Self {
            point: ProjectivePoint::GENERATOR * x.scalar,
        }
    }
}

impl From<&Scalar> for Point {
    fn from(x: &Scalar) -> Self {
        Self::from(*x)
    }
}

impl From<(field::Element, field::Element)> for Point {
    /// Build a point from affine coordinates, yielding the identity if they are not on the curve
    ///
    /// The libsecp256k1 backend wrote the coordinates straight into its point without checking,
    /// so an off-curve pair produced a point that was not on the curve. This validates instead.
    fn from(ff: (field::Element, field::Element)) -> Self {
        let candidate = AffinePoint::from_coordinates(
            &FieldBytes::from(ff.0.to_bytes()),
            &FieldBytes::from(ff.1.to_bytes()),
        );

        Option::<AffinePoint>::from(candidate)
            .map(|affine| Point {
                point: ProjectivePoint::from(affine),
            })
            .unwrap_or_else(Point::identity)
    }
}

impl From<(Scalar, Scalar)> for Point {
    fn from(ss: (Scalar, Scalar)) -> Self {
        Self::from((field::Element::from(ss.0), field::Element::from(ss.1)))
    }
}

impl TryFrom<&Compressed> for Point {
    type Error = Error;

    fn try_from(c: &Compressed) -> Result<Self, Error> {
        // The all-zero x-coordinate is how the libsecp256k1 backend encoded the identity.
        if c.data[0] == 0x02 && c.data[1..] == [0u8; 32] {
            return Ok(Point::identity());
        }

        let y_is_odd = match c.data[0] {
            0x02 => Choice::from(0),
            0x03 => Choice::from(1),
            _ => return Err(Error::Conversion(ConversionError::WrongNumberOfBytes(33))),
        };

        let mut x = [0u8; 32];
        x.clone_from_slice(&c.data[1..]);

        Option::<AffinePoint>::from(AffinePoint::decompress(&FieldBytes::from(x), y_is_odd))
            .map(|affine| Point {
                point: ProjectivePoint::from(affine),
            })
            .ok_or(Error::Conversion(ConversionError::WrongNumberOfBytes(33)))
    }
}

impl Serialize for Point {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_bytes(self.compress().as_bytes())
    }
}

struct PointVisitor;

impl<'de> Visitor<'de> for PointVisitor {
    type Value = Point;

    fn expecting(&self, formatter: &mut Formatter) -> FmtResult {
        formatter.write_str("an array of bytes which represents a point on the secp256k1 curve")
    }

    fn visit_bytes<E: de::Error>(self, value: &[u8]) -> Result<Self::Value, E> {
        let c = Compressed::try_from(value).map_err(|e| E::custom(format!("{:?}", e)))?;

        Point::try_from(&c).map_err(|e| E::custom(format!("{:?}", e)))
    }

    fn visit_seq<A: de::SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
        let mut v = Vec::new();

        while let Ok(Some(x)) = seq.next_element() {
            v.push(x);
        }

        self.visit_bytes(&v)
    }
}

impl<'de> Deserialize<'de> for Point {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Point, D::Error> {
        deserializer.deserialize_bytes(PointVisitor)
    }
}

macro_rules! point_binop {
    ($trait:ident, $method:ident) => {
        impl $trait for Point {
            type Output = Point;
            fn $method(self, other: Point) -> Point {
                Point {
                    point: self.point.$method(other.point),
                }
            }
        }

        impl $trait<&Point> for Point {
            type Output = Point;
            fn $method(self, other: &Point) -> Point {
                Point {
                    point: self.point.$method(other.point),
                }
            }
        }

        impl $trait<Point> for &Point {
            type Output = Point;
            fn $method(self, other: Point) -> Point {
                Point {
                    point: self.point.$method(other.point),
                }
            }
        }

        impl $trait<&Point> for &Point {
            type Output = Point;
            fn $method(self, other: &Point) -> Point {
                Point {
                    point: self.point.$method(other.point),
                }
            }
        }
    };
}

point_binop!(Add, add);
point_binop!(Sub, sub);

impl AddAssign<Point> for Point {
    fn add_assign(&mut self, other: Point) {
        self.point += other.point;
    }
}

impl AddAssign<&Point> for Point {
    fn add_assign(&mut self, other: &Point) {
        self.point += other.point;
    }
}

impl Neg for Point {
    type Output = Point;

    fn neg(self) -> Point {
        Point { point: -self.point }
    }
}

impl Neg for &Point {
    type Output = Point;

    fn neg(self) -> Point {
        Point { point: -self.point }
    }
}

impl Sum<Point> for Point {
    fn sum<I: Iterator<Item = Point>>(iter: I) -> Self {
        iter.fold(Point::identity(), |acc, i| acc + i)
    }
}

impl<'a> Sum<&'a Point> for Point {
    fn sum<I: Iterator<Item = &'a Point>>(iter: I) -> Self {
        iter.fold(Point::identity(), |acc, i| acc + i)
    }
}

impl Mul<Scalar> for Point {
    type Output = Point;

    fn mul(self, x: Scalar) -> Point {
        Point {
            point: self.point * x.scalar,
        }
    }
}

impl Mul<&Scalar> for &Point {
    type Output = Point;

    fn mul(self, x: &Scalar) -> Point {
        Point {
            point: self.point * x.scalar,
        }
    }
}

/// A compressed SEC1 point encoding.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Compressed {
    /// The raw bytes of the compressed point
    pub data: [u8; 33],
}

impl Compressed {
    /// Return a byte slice of the data
    pub fn as_bytes(&self) -> &[u8] {
        &self.data
    }
}

impl From<[u8; 33]> for Compressed {
    fn from(bytes: [u8; 33]) -> Self {
        Self { data: bytes }
    }
}

impl From<Compressed> for String {
    fn from(c: Compressed) -> String {
        bs58::encode(c.data).into_string()
    }
}

impl TryFrom<&[u8]> for Compressed {
    type Error = Error;

    fn try_from(bytes: &[u8]) -> Result<Self, Error> {
        match bytes.len() {
            33 => {
                let mut data = [0u8; 33];
                data.clone_from_slice(bytes);
                Ok(Compressed { data })
            }
            n => Err(Error::Conversion(ConversionError::WrongNumberOfBytes(n))),
        }
    }
}

impl TryFrom<&str> for Compressed {
    type Error = Error;

    fn try_from(s: &str) -> Result<Self, Error> {
        match bs58::decode(s).into_vec() {
            Ok(bytes) => Compressed::try_from(&bytes[..]),
            Err(_) => Err(Error::Conversion(ConversionError::Base58(
                super::errors::Base58Error::Decode,
            ))),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Compressed, Error, Point, G, N};
    use crate::curve_k256::{field, scalar::Scalar, traits::MultiMult};
    use num_traits::Zero;
    use p256k1::{
        point::{Compressed as RefCompressed, Point as RefPoint, G as REF_G, N as REF_N},
        scalar::Scalar as RefScalar,
    };
    use rand_core::{RngCore, SeedableRng};

    fn seeds(n: usize) -> Vec<[u8; 32]> {
        let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(0x9017_2b3c);
        (0..n)
            .map(|_| {
                let mut b = [0u8; 32];
                rng.fill_bytes(&mut b);
                b
            })
            .collect()
    }

    /// Both backends must agree bit for bit, since serialized points have to round-trip across
    /// the switch.
    #[test]
    fn agrees_with_p256k1() {
        assert_eq!(N, REF_N, "group order");
        assert_eq!(G.compress().data, REF_G.compress().data, "generator");
        assert_eq!(
            Point::identity().compress().data,
            RefPoint::identity().compress().data,
            "identity"
        );
        assert_eq!(
            Point::zero().compress().data,
            RefPoint::zero().compress().data,
            "zero"
        );
        assert!(
            Point::zero().is_zero() && RefPoint::zero().is_zero(),
            "is_zero"
        );

        for (i, b) in seeds(32).iter().enumerate() {
            let (s, r) = (Scalar::from(*b), RefScalar::from(*b));
            let (p, q) = (Point::from(s), RefPoint::from(r));

            assert_eq!(p.compress().data, q.compress().data, "s * G at {i}");
            assert_eq!(p.x().to_bytes(), q.x().to_bytes(), "x at {i}");
            assert_eq!(p.y().to_bytes(), q.y().to_bytes(), "y at {i}");
            assert_eq!(p.has_even_y(), q.has_even_y(), "has_even_y at {i}");
            assert_eq!((-p).compress().data, (-q).compress().data, "neg at {i}");
            assert_eq!(p.to_string(), q.to_string(), "Display at {i}");

            let lifted = Point::lift_x(&p.x()).unwrap();
            let ref_lifted = RefPoint::lift_x(&q.x()).unwrap();
            assert_eq!(
                lifted.compress().data,
                ref_lifted.compress().data,
                "lift_x at {i}"
            );
            assert!(lifted.has_even_y(), "lift_x gives even y at {i}");
        }

        for w in seeds(16).windows(2) {
            let (s0, s1) = (Scalar::from(w[0]), Scalar::from(w[1]));
            let (r0, r1) = (RefScalar::from(w[0]), RefScalar::from(w[1]));
            let (p0, p1) = (Point::from(s0), Point::from(s1));
            let (q0, q1) = (RefPoint::from(r0), RefPoint::from(r1));

            assert_eq!((p0 + p1).compress().data, (q0 + q1).compress().data, "add");
            assert_eq!((p0 - p1).compress().data, (q0 - q1).compress().data, "sub");
            assert_eq!(
                (p0 * s1).compress().data,
                (q0 * r1).compress().data,
                "p * s"
            );
            assert_eq!(
                (s1 * p0).compress().data,
                (r1 * q0).compress().data,
                "s * p"
            );

            let mut acc = p0;
            let mut ref_acc = q0;
            acc += p1;
            ref_acc += q1;
            assert_eq!(acc.compress().data, ref_acc.compress().data, "add_assign");
        }
    }

    /// The multiexponentiation is the reason for the switch, so it is checked on both sides of
    /// the `k256` Pippenger dispatch threshold as well as at the degenerate sizes.
    #[test]
    fn multimult_agrees_with_p256k1() {
        for n in [0usize, 1, 2, 59, 60, 61, 128, 300] {
            let bytes = seeds(2 * n);
            let (mut scalars, mut points) = (Vec::new(), Vec::new());
            let (mut ref_scalars, mut ref_points) = (Vec::new(), Vec::new());

            for i in 0..n {
                scalars.push(Scalar::from(bytes[i]));
                ref_scalars.push(RefScalar::from(bytes[i]));
                points.push(Point::from(Scalar::from(bytes[n + i])));
                ref_points.push(RefPoint::from(RefScalar::from(bytes[n + i])));
            }

            let mine = Point::multimult(scalars.clone(), points.clone()).unwrap();
            let theirs = RefPoint::multimult(ref_scalars, ref_points).unwrap();
            assert_eq!(
                mine.compress().data,
                theirs.compress().data,
                "multimult at n={n}"
            );

            // And the same terms through the zero-copy trait entry point.
            struct Terms {
                scalars: Vec<Scalar>,
                points: Vec<Point>,
            }

            impl MultiMult for Terms {
                fn get_scalar(&self, i: usize) -> &Scalar {
                    &self.scalars[i]
                }
                fn get_point(&self, i: usize) -> &Point {
                    &self.points[i]
                }
                fn get_size(&self) -> usize {
                    self.scalars.len()
                }
            }

            let mut terms = Terms { scalars, points };
            let via_trait = Point::multimult_trait(&mut terms).unwrap();
            assert_eq!(
                via_trait.compress().data,
                mine.compress().data,
                "multimult_trait at n={n}"
            );
        }
    }

    /// A mismatched term count is an error rather than a panic or a wrong answer.
    #[test]
    fn multimult_rejects_mismatched_lengths() {
        let b = seeds(2);
        let err = Point::multimult(vec![Scalar::from(b[0])], vec![]).unwrap_err();
        assert_eq!(err, Error::MultiMultFailed);
    }

    /// Compressed encodings have to be interchangeable in both directions, or saved state and
    /// network packets stop crossing the switch.
    #[test]
    fn compressed_encoding_is_interchangeable() {
        let mut cases: Vec<(Point, RefPoint)> =
            vec![(Point::identity(), RefPoint::identity()), (G, REF_G)];
        for b in seeds(16) {
            cases.push((
                Point::from(Scalar::from(b)),
                RefPoint::from(RefScalar::from(b)),
            ));
        }

        for (i, (p, q)) in cases.iter().enumerate() {
            let mine = p.compress();
            let theirs = q.compress();
            assert_eq!(mine.data, theirs.data, "compress at {i}");

            // Their bytes, our parser.
            let back = Point::try_from(&Compressed::from(theirs.data)).unwrap();
            assert_eq!(back.compress().data, mine.data, "theirs -> ours at {i}");

            // Our bytes, their parser. The identity is the one case libsecp256k1 will not take
            // back: it compresses to an even-tagged zero x-coordinate, which its own decoder
            // rejects as a bad group element. This backend accepts what it emits.
            match RefPoint::try_from(&RefCompressed::from(mine.data)) {
                Ok(ref_back) => {
                    assert_eq!(
                        ref_back.compress().data,
                        theirs.data,
                        "ours -> theirs at {i}"
                    )
                }
                Err(e) => assert!(
                    p.is_zero(),
                    "ours -> theirs failed at {i} for non-identity: {e:?}"
                ),
            }

            // And through serde.
            let (mut ser, mut ref_ser) = (Vec::new(), Vec::new());
            ciborium::into_writer(p, &mut ser).unwrap();
            ciborium::into_writer(q, &mut ref_ser).unwrap();
            assert_eq!(ser, ref_ser, "serde encoding at {i}");

            let round: Point = ciborium::from_reader(&ser[..]).unwrap();
            assert_eq!(round.compress().data, mine.data, "serde round trip at {i}");
        }
    }

    /// Out-of-range x-coordinates are rejected rather than reduced, which the libsecp256k1
    /// backend did not do. See the note on `field::Element::from`.
    #[test]
    fn out_of_range_field_bytes_are_rejected() {
        // p itself, and an x-coordinate offset by p, both of which libsecp256k1 accepted.
        let p_bytes = [
            0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
            0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE,
            0xFF, 0xFF, 0xFC, 0x2F,
        ];

        assert!(
            field::Element::from(p_bytes).is_zero(),
            "p must not parse as a field element"
        );
        assert!(
            field::Element::from([0xff; 32]).is_zero(),
            "an all-ones x-coordinate is above p"
        );

        // The reference backend keeps those bytes verbatim rather than reducing them, and then
        // compares them bytewise against a canonical x-coordinate, so it rejects by a different
        // route. Pinned so the claim stays checked.
        assert_eq!(
            p256k1::field::Element::from(p_bytes).to_bytes(),
            p_bytes,
            "libsecp256k1 kept out-of-range bytes as they were"
        );

        // And in-range bytes are untouched by the rejection check.
        let x = G.x();
        assert_eq!(field::Element::from(x.to_bytes()), x, "in-range round trip");

        // Zero is not a valid x-coordinate, so the lift fails and a forged proof cannot verify.
        assert_eq!(
            Point::lift_x(&field::Element::from(p_bytes)).unwrap_err(),
            Error::LiftFailed
        );
    }
}
