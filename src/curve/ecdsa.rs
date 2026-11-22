//! ECDSA signatures, used to authenticate network packets.

use core::{
    cmp::Ordering,
    fmt::{Display, Formatter, Result as FmtResult},
    hash::{Hash, Hasher},
};

use k256::{
    ecdsa::{
        signature::hazmat::{PrehashSigner, PrehashVerifier},
        SigningKey, VerifyingKey,
    },
    FieldBytes,
};
use serde::{
    de::{self, Deserialize, Deserializer, Visitor},
    ser::{Serialize, Serializer},
    Deserialize as DeserializeDerive, Serialize as SerializeDerive,
};

use super::{errors::ConversionError, scalar::Scalar};

pub use super::keys::{Error as KeyError, PublicKey};

/// Length of the message digest these signatures are computed over.
const PREHASH_LEN: usize = 32;

#[derive(Debug, Clone, SerializeDerive, DeserializeDerive, PartialEq, Eq)]
/// Errors in ECDSA operations
pub enum Error {
    /// Error with key operations
    Key(KeyError),
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

/// An ECDSA signature over a 32-byte message digest.
#[derive(Copy, Clone, Debug)]
pub struct Signature {
    signature: k256::ecdsa::Signature,
}

impl Signature {
    /// Construct an ECDSA signature
    ///
    /// The nonce is derived deterministically per RFC 6979 with SHA-256, as the libsecp256k1
    /// backend's default nonce function did, so the same key and digest give the same signature
    /// under either backend.
    ///
    /// `hash` must be exactly 32 bytes. The libsecp256k1 backend took a slice but
    /// passed only its pointer to a function that reads 32 bytes unconditionally, so a shorter
    /// digest read past the end; this rejects it instead.
    pub fn new(hash: &[u8], sec_key: &Scalar) -> Result<Self, Error> {
        if hash.len() != PREHASH_LEN {
            return Err(Error::TryFrom(format!(
                "digest must be {PREHASH_LEN} bytes, got {}",
                hash.len()
            )));
        }

        let signing_key = SigningKey::from_bytes(&FieldBytes::from(sec_key.to_bytes()))
            .map_err(|_| Error::Key(KeyError::InvalidSecretKey))?;

        let signature: k256::ecdsa::Signature = signing_key
            .sign_prehash(hash)
            .map_err(|e| Error::TryFrom(e.to_string()))?;

        Ok(Self { signature })
    }

    /// Verify an ECDSA signature
    ///
    /// A high-`s` signature is rejected even though it is otherwise valid. ECDSA admits two `s`
    /// values for every signature, so accepting both would make the encoding malleable; the
    /// libsecp256k1 backend's verify rejected the high one, and generic ECDSA verification does
    /// not, so the check is explicit here.
    pub fn verify(&self, hash: &[u8], pub_key: &PublicKey) -> bool {
        if hash.len() != PREHASH_LEN {
            return false;
        }

        if self.signature.normalize_s() != self.signature {
            return false;
        }

        let Ok(verifying_key) = VerifyingKey::from_affine(pub_key.point.point.to_affine()) else {
            return false;
        };

        verifying_key.verify_prehash(hash, &self.signature).is_ok()
    }

    /// Returns the signature as 64 bytes, `r` then `s`, big-endian
    pub fn to_bytes(&self) -> [u8; 64] {
        self.signature.to_bytes().into()
    }
}

impl Display for Signature {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", bs58::encode(self.to_bytes()).into_string())
    }
}

impl PartialEq for Signature {
    fn eq(&self, other: &Self) -> bool {
        self.signature == other.signature
    }
}

impl Eq for Signature {}

impl PartialOrd for Signature {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Signature {
    fn cmp(&self, other: &Self) -> Ordering {
        self.to_bytes().cmp(&other.to_bytes())
    }
}

impl Hash for Signature {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_bytes().hash(state);
    }
}

impl TryFrom<&[u8]> for Signature {
    type Error = Error;

    fn try_from(bytes: &[u8]) -> Result<Self, Error> {
        k256::ecdsa::Signature::from_slice(bytes)
            .map(|signature| Self { signature })
            .map_err(|e| Error::TryFrom(e.to_string()))
    }
}

impl TryFrom<[u8; 64]> for Signature {
    type Error = Error;

    fn try_from(bytes: [u8; 64]) -> Result<Self, Error> {
        Self::try_from(&bytes[..])
    }
}

impl Serialize for Signature {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_bytes(&self.to_bytes())
    }
}

struct SignatureVisitor;

impl<'de> Visitor<'de> for SignatureVisitor {
    type Value = Signature;

    fn expecting(&self, formatter: &mut Formatter) -> FmtResult {
        formatter.write_str("an array of bytes which represents an ECDSA signature")
    }

    fn visit_bytes<E: de::Error>(self, value: &[u8]) -> Result<Self::Value, E> {
        Signature::try_from(value).map_err(|e| E::custom(format!("{:?}", e)))
    }

    fn visit_seq<A: de::SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
        let mut v = Vec::new();

        while let Ok(Some(x)) = seq.next_element() {
            v.push(x);
        }

        self.visit_bytes(&v)
    }
}

impl<'de> Deserialize<'de> for Signature {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Signature, D::Error> {
        deserializer.deserialize_bytes(SignatureVisitor)
    }
}

#[cfg(test)]
mod tests {
    use super::{Error, KeyError, PublicKey, Signature};
    use crate::curve::scalar::Scalar;
    use p256k1::{
        ecdsa::{PublicKey as RefPublicKey, Signature as RefSignature},
        scalar::Scalar as RefScalar,
    };
    use rand_core::{RngCore, SeedableRng};

    /// Deterministic (secret key, digest) pairs.
    fn cases() -> Vec<([u8; 32], [u8; 32])> {
        let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(0xec_d5a_000);
        (0..24)
            .map(|_| {
                let mut key = [0u8; 32];
                let mut digest = [0u8; 32];
                rng.fill_bytes(&mut key);
                rng.fill_bytes(&mut digest);
                (key, digest)
            })
            .collect()
    }

    /// Signatures must be byte-identical, not merely both valid.
    ///
    /// Both sides derive the nonce per RFC 6979 with SHA-256, so a given key and digest have one
    /// signature. If this ever diverges, packets signed by one build stop verifying under the
    /// other even though neither is wrong.
    #[test]
    fn signatures_match_p256k1() {
        for (i, (key, digest)) in cases().iter().enumerate() {
            let mine = Signature::new(digest, &Scalar::from(*key)).unwrap();
            let theirs = RefSignature::new(digest, &RefScalar::from(*key)).unwrap();

            assert_eq!(mine.to_bytes(), theirs.to_bytes(), "signature bytes at {i}");
            assert_eq!(mine.to_string(), theirs.to_string(), "Display at {i}");

            let (mut ser, mut ref_ser) = (Vec::new(), Vec::new());
            ciborium::into_writer(&mine, &mut ser).unwrap();
            ciborium::into_writer(&theirs, &mut ref_ser).unwrap();
            assert_eq!(ser, ref_ser, "serde encoding at {i}");

            let round: Signature = ciborium::from_reader(&ser[..]).unwrap();
            assert_eq!(round, mine, "serde round trip at {i}");
        }
    }

    /// Each backend must accept the other's signatures and public keys.
    #[test]
    fn verification_is_interchangeable() {
        for (i, (key, digest)) in cases().iter().enumerate() {
            let (s, r) = (Scalar::from(*key), RefScalar::from(*key));
            let (mine, theirs) = (
                Signature::new(digest, &s).unwrap(),
                RefSignature::new(digest, &r).unwrap(),
            );
            let (my_key, their_key) = (PublicKey::new(&s).unwrap(), RefPublicKey::new(&r).unwrap());

            assert_eq!(my_key.to_bytes(), their_key.to_bytes(), "pubkey at {i}");

            assert!(mine.verify(digest, &my_key), "mine under mine at {i}");
            assert!(
                theirs.verify(digest, &their_key),
                "theirs under theirs at {i}"
            );

            // Their signature, my verifier, and the reverse.
            let their_bytes = theirs.to_bytes();
            assert!(
                Signature::try_from(their_bytes)
                    .unwrap()
                    .verify(digest, &my_key),
                "theirs under mine at {i}"
            );
            assert!(
                RefSignature::try_from(mine.to_bytes())
                    .unwrap()
                    .verify(digest, &their_key),
                "mine under theirs at {i}"
            );

            // A different digest must not verify.
            let mut other = *digest;
            other[0] ^= 1;
            assert!(!mine.verify(&other, &my_key), "wrong digest at {i}");
        }
    }

    /// A high-`s` signature is rejected by both backends, so the explicit check matches rather
    /// than tightens behaviour.
    ///
    /// ECDSA admits `s` and `n - s` for the same message. libsecp256k1's verify refuses the high
    /// one; generic ECDSA verification accepts it, which is why `verify` checks explicitly.
    #[test]
    fn high_s_is_rejected_by_both() {
        let (key, digest) = cases()[0];
        let (s, r) = (Scalar::from(key), RefScalar::from(key));
        let low = Signature::new(&digest, &s).unwrap();
        let my_key = PublicKey::new(&s).unwrap();
        let their_key = RefPublicKey::new(&r).unwrap();

        assert!(low.verify(&digest, &my_key), "the low-s signature verifies");

        // Flip s to n - s, keeping r. Negating in the scalar field is exactly that.
        let mut flipped = low.to_bytes();
        let s_value = {
            let mut b = [0u8; 32];
            b.clone_from_slice(&flipped[32..]);
            Scalar::from(b)
        };
        flipped[32..].clone_from_slice(&(-s_value).to_bytes());

        // Whether the parser even admits it is worth recording: if it does not, the check in
        // `verify` is belt and braces rather than load-bearing.
        match Signature::try_from(flipped) {
            Ok(high) => {
                assert!(
                    !high.verify(&digest, &my_key),
                    "high-s must not verify here"
                );
                assert_ne!(high.to_bytes(), low.to_bytes(), "the flip changed s");
            }
            Err(e) => panic!("parser rejected high-s outright: {e:?} (check is then redundant)"),
        }

        match RefSignature::try_from(flipped) {
            Ok(high) => assert!(
                !high.verify(&digest, &their_key),
                "libsecp256k1 must not verify high-s either"
            ),
            Err(_) => { /* their parser refused it, which is also a rejection */ }
        }
    }

    /// The zero scalar has no public key, and signing with it fails.
    #[test]
    fn zero_secret_key_is_rejected() {
        let zero = Scalar::from([0u8; 32]);

        assert_eq!(
            PublicKey::new(&zero).unwrap_err(),
            KeyError::InvalidSecretKey
        );
        assert!(matches!(
            Signature::new(&[0u8; 32], &zero),
            Err(Error::Key(KeyError::InvalidSecretKey))
        ));
    }

    /// A digest of the wrong length is an error rather than a read past the end.
    ///
    /// The libsecp256k1 backend took a slice but handed only its pointer to a function that reads
    /// 32 bytes unconditionally, so a short digest read out of bounds. It is deliberately not
    /// called here with one.
    #[test]
    fn digest_length_is_checked() {
        let key = Scalar::from(cases()[0].0);

        for len in [0usize, 1, 31, 33, 64] {
            let digest = vec![7u8; len];
            assert!(
                matches!(Signature::new(&digest, &key), Err(Error::TryFrom(_))),
                "a {len}-byte digest must be refused"
            );
        }

        let good = Signature::new(&[9u8; 32], &key).unwrap();
        let pub_key = PublicKey::new(&key).unwrap();
        assert!(
            !good.verify(&[9u8; 31], &pub_key),
            "short digest fails verify"
        );
    }
}
