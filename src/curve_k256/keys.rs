//! Public keys.

use core::{
    cmp::Ordering,
    fmt::{Debug, Display, Formatter, Result as FmtResult},
    hash::{Hash, Hasher},
};

use num_traits::Zero;
use serde::{
    de::{self, Deserialize, Deserializer, Visitor},
    ser::{Serialize, Serializer},
    Deserialize as DeserializeDerive, Serialize as SerializeDerive,
};

use super::{
    errors::{Base58Error, ConversionError},
    point::{Compressed, Point},
    scalar::Scalar,
};

#[derive(Debug, Clone, SerializeDerive, DeserializeDerive, PartialEq, Eq)]
/// Errors in key operations
pub enum Error {
    /// Error occurred due to invalid secret key
    InvalidSecretKey,
    /// Error occurred due to invalid public key
    InvalidPublicKey,
    /// Error occurred due to invalid xonly public key
    InvalidXOnlyPublicKey,
    /// Error occurred during a try from operation
    TryFrom(String),
    /// Error converting a scalar
    Conversion(ConversionError),
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for Error {}

/// A secp256k1 public key.
#[derive(Copy, Clone)]
pub struct PublicKey {
    pub(crate) point: Point,
}

impl PublicKey {
    /// Construct a public key from a given secret key
    pub fn new(sec_key: &Scalar) -> Result<Self, Error> {
        // The zero scalar has no public key. Every other value is in range, since `Scalar` is
        // always reduced modulo the group order.
        if sec_key.is_zero() {
            return Err(Error::InvalidSecretKey);
        }

        Ok(Self {
            point: Point::from(sec_key),
        })
    }

    /// Serialize the key to a compressed byte array
    pub fn to_bytes(&self) -> [u8; 33] {
        self.point.compress().data
    }
}

impl Debug for PublicKey {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self)
    }
}

impl Display for PublicKey {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", bs58::encode(self.to_bytes()).into_string())
    }
}

impl PartialEq for PublicKey {
    fn eq(&self, other: &Self) -> bool {
        self.point == other.point
    }
}

impl Eq for PublicKey {}

impl PartialOrd for PublicKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PublicKey {
    fn cmp(&self, other: &Self) -> Ordering {
        self.to_bytes().cmp(&other.to_bytes())
    }
}

impl Hash for PublicKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_bytes().hash(state);
    }
}

impl TryFrom<&Scalar> for PublicKey {
    type Error = Error;

    fn try_from(sec_key: &Scalar) -> Result<Self, Error> {
        Self::new(sec_key)
    }
}

impl TryFrom<&[u8]> for PublicKey {
    type Error = Error;

    fn try_from(bytes: &[u8]) -> Result<Self, Error> {
        let compressed = Compressed::try_from(bytes)
            .map_err(|_| Error::Conversion(ConversionError::WrongNumberOfBytes(bytes.len())))?;

        Point::try_from(&compressed)
            .map(|point| Self { point })
            .map_err(|_| Error::InvalidPublicKey)
    }
}

impl TryFrom<&str> for PublicKey {
    type Error = Error;

    fn try_from(s: &str) -> Result<Self, Error> {
        match bs58::decode(s).into_vec() {
            Ok(bytes) => PublicKey::try_from(&bytes[..]),
            Err(_) => Err(Error::Conversion(ConversionError::Base58(
                Base58Error::Decode,
            ))),
        }
    }
}

impl Serialize for PublicKey {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_bytes(&self.to_bytes())
    }
}

struct PublicKeyVisitor;

impl<'de> Visitor<'de> for PublicKeyVisitor {
    type Value = PublicKey;

    fn expecting(&self, formatter: &mut Formatter) -> FmtResult {
        formatter.write_str("an array of bytes which represents a secp256k1 public key")
    }

    fn visit_bytes<E: de::Error>(self, value: &[u8]) -> Result<Self::Value, E> {
        PublicKey::try_from(value).map_err(|e| E::custom(format!("{:?}", e)))
    }

    fn visit_seq<A: de::SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
        let mut v = Vec::new();

        while let Ok(Some(x)) = seq.next_element() {
            v.push(x);
        }

        self.visit_bytes(&v)
    }
}

impl<'de> Deserialize<'de> for PublicKey {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<PublicKey, D::Error> {
        deserializer.deserialize_bytes(PublicKeyVisitor)
    }
}

/// A secp256k1 public key without its y-coordinate, as BIP-340 uses.
#[derive(Copy, Clone)]
pub struct XOnlyPublicKey {
    bytes: [u8; 32],
}

impl XOnlyPublicKey {
    /// Construct an x-only public key from a given secret key
    pub fn new(sec_key: &Scalar) -> Result<Self, Error> {
        let key = PublicKey::new(sec_key)?;
        let mut bytes = [0u8; 32];
        bytes.clone_from_slice(&key.to_bytes()[1..]);

        Ok(Self { bytes })
    }

    /// Serialize the key to a byte array
    pub fn to_bytes(&self) -> [u8; 32] {
        self.bytes
    }
}

impl Debug for XOnlyPublicKey {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self)
    }
}

impl Display for XOnlyPublicKey {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", bs58::encode(self.bytes).into_string())
    }
}

impl PartialEq for XOnlyPublicKey {
    fn eq(&self, other: &Self) -> bool {
        self.bytes == other.bytes
    }
}

impl Eq for XOnlyPublicKey {}

impl PartialOrd for XOnlyPublicKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for XOnlyPublicKey {
    fn cmp(&self, other: &Self) -> Ordering {
        self.bytes.cmp(&other.bytes)
    }
}

impl Hash for XOnlyPublicKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bytes.hash(state);
    }
}

impl TryFrom<&[u8]> for XOnlyPublicKey {
    type Error = Error;

    fn try_from(bytes: &[u8]) -> Result<Self, Error> {
        match bytes.len() {
            32 => {
                let mut data = [0u8; 32];
                data.clone_from_slice(bytes);
                Ok(Self { bytes: data })
            }
            n => Err(Error::Conversion(ConversionError::WrongNumberOfBytes(n))),
        }
    }
}

impl Serialize for XOnlyPublicKey {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_bytes(&self.bytes)
    }
}

struct XOnlyPublicKeyVisitor;

impl<'de> Visitor<'de> for XOnlyPublicKeyVisitor {
    type Value = XOnlyPublicKey;

    fn expecting(&self, formatter: &mut Formatter) -> FmtResult {
        formatter.write_str("an array of bytes which represents an x-only secp256k1 public key")
    }

    fn visit_bytes<E: de::Error>(self, value: &[u8]) -> Result<Self::Value, E> {
        XOnlyPublicKey::try_from(value).map_err(|e| E::custom(format!("{:?}", e)))
    }

    fn visit_seq<A: de::SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
        let mut v = Vec::new();

        while let Ok(Some(x)) = seq.next_element() {
            v.push(x);
        }

        self.visit_bytes(&v)
    }
}

impl<'de> Deserialize<'de> for XOnlyPublicKey {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<XOnlyPublicKey, D::Error> {
        deserializer.deserialize_bytes(XOnlyPublicKeyVisitor)
    }
}
