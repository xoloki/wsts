use rand_core::{CryptoRng, RngCore};
use std::{collections::BTreeMap, fmt::Debug};

use hashbrown::{HashMap, HashSet};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use tracing::warn;

use crate::{
    common::{MerkleRoot, PolyCommitment, PublicNonce, SignatureShare, TupleProof},
    curve::{
        ecdsa,
        point::{Point, G},
        scalar::Scalar,
    },
    schnorr,
    state_machine::PublicKeys,
    util::hash_to_scalar,
};

/// Trait to encapsulate sign/verify, users only need to impl hash
pub trait Signable {
    /// Hash this object in a consistent way so it can be signed/verified
    fn hash(&self, hasher: &mut Sha256);

    /// Sign a hash of this object using the passed private key
    fn sign(&self, private_key: &Scalar) -> Result<Vec<u8>, ecdsa::Error> {
        let mut hasher = Sha256::new();

        self.hash(&mut hasher);

        let hash = hasher.finalize();
        match ecdsa::Signature::new(hash.as_slice(), private_key) {
            Ok(sig) => Ok(sig.to_bytes().to_vec()),
            Err(e) => Err(e),
        }
    }

    /// Verify a hash of this object using the passed public key
    fn verify(&self, signature: &[u8], public_key: &ecdsa::PublicKey) -> bool {
        let mut hasher = Sha256::new();

        self.hash(&mut hasher);

        let hash = hasher.finalize();
        let sig = match ecdsa::Signature::try_from(signature) {
            Ok(sig) => sig,
            Err(_) => return false,
        };

        sig.verify(hash.as_slice(), public_key)
    }
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
/// A bad private share
pub struct BadPrivateShare {
    /// the DH shared key between these participants
    pub shared_key: Point,
    /// prooof that the shared key is a valid DH tuple as per chaum-pedersen
    pub tuple_proof: TupleProof,
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
/// Final DKG status after receiving public and private shares
pub enum DkgFailure {
    /// DKG threshold not met
    Threshold,
    /// Signer was in the wrong internal state to complete DKG
    BadState,
    /// DKG public shares were missing from these signer_ids
    MissingPublicShares(HashSet<u32>),
    /// DKG public shares were bad from these signer_ids
    BadPublicShares(HashSet<u32>),
    /// DKG private shares were missing from these signer_ids
    MissingPrivateShares(HashSet<u32>),
    /// DKG private shares were bad from these signer_ids
    BadPrivateShares(HashMap<u32, BadPrivateShare>),
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
/// Final DKG status after receiving public and private shares
pub enum DkgStatus {
    /// DKG completed successfully
    Success,
    /// DKG failed
    Failure(DkgFailure),
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
#[allow(clippy::large_enum_variant)]
/// Encapsulation of all possible network message types
pub enum Message {
    /// Tell signers to begin DKG by sending DKG public shares
    DkgBegin(DkgBegin),
    /// Send DKG public shares
    DkgPublicShares(DkgPublicShares),
    /// Tell signers the coordinator has received all expected public shares
    DkgPublicSharesDone(DkgPublicSharesDone),
    /// Acknowledge receipt of DkgPublicSharesDone
    DkgPublicSharesDoneAck(DkgPublicSharesDoneAck),
    /// Tell signers to send DKG private shares
    DkgPrivateBegin(DkgPrivateBegin),
    /// Send DKG private shares
    DkgPrivateShares(DkgPrivateShares),
    /// Tell signers the coordinator has received all expected private shares
    DkgPrivateSharesDone(DkgPrivateSharesDone),
    /// Acknowledge receipt of DkgPrivateSharesDone
    DkgPrivateSharesDoneAck(DkgPrivateSharesDoneAck),
    /// Tell signers to compute shares and send DKG end
    DkgEndBegin(DkgEndBegin),
    /// Tell coordinator that DKG is complete
    DkgEnd(DkgEnd),
    /// Tell signers to send signing nonces
    NonceRequest(NonceRequest),
    /// Tell coordinator signing nonces
    NonceResponse(NonceResponse),
    /// Tell signers to construct signature shares
    SignatureShareRequest(SignatureShareRequest),
    /// Tell coordinator signature shares
    SignatureShareResponse(SignatureShareResponse),
}

impl Signable for Message {
    fn hash(&self, hasher: &mut Sha256) {
        match self {
            Message::DkgBegin(msg) => msg.hash(hasher),
            Message::DkgPublicShares(msg) => msg.hash(hasher),
            Message::DkgPublicSharesDone(msg) => msg.hash(hasher),
            Message::DkgPublicSharesDoneAck(msg) => msg.hash(hasher),
            Message::DkgPrivateBegin(msg) => msg.hash(hasher),
            Message::DkgPrivateShares(msg) => msg.hash(hasher),
            Message::DkgPrivateSharesDone(msg) => msg.hash(hasher),
            Message::DkgPrivateSharesDoneAck(msg) => msg.hash(hasher),
            Message::DkgEndBegin(msg) => msg.hash(hasher),
            Message::DkgEnd(msg) => msg.hash(hasher),
            Message::NonceRequest(msg) => msg.hash(hasher),
            Message::NonceResponse(msg) => msg.hash(hasher),
            Message::SignatureShareRequest(msg) => msg.hash(hasher),
            Message::SignatureShareResponse(msg) => msg.hash(hasher),
        }
    }
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
/// DKG begin message from coordinator to signers
pub struct DkgBegin {
    /// DKG round ID
    pub dkg_id: u64,
}

impl Signable for DkgBegin {
    fn hash(&self, hasher: &mut Sha256) {
        hasher.update("DKG_BEGIN".as_bytes());
        hasher.update(self.dkg_id.to_be_bytes());
    }
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
/// DKG public shares message from signer to all signers and coordinator
pub struct DkgPublicShares {
    /// DKG round ID
    pub dkg_id: u64,
    /// Signer ID
    pub signer_id: u32,
    /// List of (party_id, commitment)
    pub comms: Vec<(u32, PolyCommitment)>,
    /// Ephemeral public key for key exchange
    pub kex_public_key: Point,
    /// Proof of knowledge of kex_private_key
    pub kex_proof: schnorr::Proof,
}

#[allow(non_snake_case)]
impl DkgPublicShares {
    /// construct a proof of knowledge of kex_private_key
    pub fn kex_prove<RNG: RngCore + CryptoRng>(
        dkg_id: u64,
        signer_id: u32,
        comms: &Vec<(u32, PolyCommitment)>,
        kex_private_key: &Scalar,
        rng: &mut RNG,
    ) -> schnorr::Proof {
        let r = Scalar::random(rng);
        let R = r * G;
        let kex_public_key = kex_private_key * G;
        let c = Self::kex_challenge(&R, dkg_id, signer_id, comms, &kex_public_key);
        let s = r + c * kex_private_key;

        schnorr::Proof { R, s }
    }

    /// verify a proof of knowledge of kex_private_key
    pub fn kex_verify(&self) -> bool {
        let c = Self::kex_challenge(
            &self.kex_proof.R,
            self.dkg_id,
            self.signer_id,
            &self.comms,
            &self.kex_public_key,
        );
        self.kex_proof.s * G == self.kex_proof.R + c * self.kex_public_key
    }

    /// construct a proof of knowledge of kex_private_key
    pub fn kex_challenge(
        R: &Point,
        dkg_id: u64,
        signer_id: u32,
        comms: &Vec<(u32, PolyCommitment)>,
        kex_public_key: &Point,
    ) -> Scalar {
        let mut hasher = Sha256::new();
        let tag = "WSTS/DKG_PUBLIC_SHARES/KEX_SCHNORR_PROOF";

        hasher.update(tag.as_bytes());
        hasher.update(R.compress().as_bytes());
        hasher.update(dkg_id.to_be_bytes());
        hasher.update(signer_id.to_be_bytes());
        hasher.update(kex_public_key.compress().as_bytes());
        for (party_id, comm) in comms {
            hasher.update(party_id.to_be_bytes());
            for a in &comm.poly {
                hasher.update(a.compress().as_bytes());
            }
        }

        hash_to_scalar(&mut hasher)
    }
}

impl Signable for DkgPublicShares {
    fn hash(&self, hasher: &mut Sha256) {
        hasher.update("DKG_PUBLIC_SHARES".as_bytes());
        hasher.update(self.dkg_id.to_be_bytes());
        hasher.update(self.signer_id.to_be_bytes());
        hasher.update(self.kex_public_key.compress().as_bytes());
        hasher.update(self.kex_proof.R.compress().as_bytes());
        hasher.update(self.kex_proof.s.to_bytes());
        for (party_id, comm) in &self.comms {
            hasher.update(party_id.to_be_bytes());
            for a in &comm.poly {
                hasher.update(a.compress().as_bytes());
            }
        }
    }
}

/// Domain separation tag for [`dkg_public_shares_digest`]
const DKG_PUBLIC_SHARES_DIGEST_TAG: &[u8] = b"WSTS/DKG_PUBLIC_SHARES_DIGEST";

/// Compute a digest over an accepted set of DKG public shares, keyed by signer ID.
///
/// Signers and the coordinator compare this value before any private shares are sent, so that a
/// signer who sent different public shares to different participants is caught before the round
/// can produce a group key that honest participants disagree about.  It covers every field of each
/// [`DkgPublicShares`], including the schnorr ID proofs and the key exchange public key and proof,
/// since private shares are encrypted to the latter.  Lists are length-prefixed so that the
/// encoding is unambiguous.  Signers are visited in ascending signer ID order.
pub fn dkg_public_shares_digest(
    dkg_id: u64,
    dkg_public_shares: &BTreeMap<u32, DkgPublicShares>,
) -> [u8; 32] {
    let mut hasher = Sha256::new();

    hasher.update(DKG_PUBLIC_SHARES_DIGEST_TAG);
    hasher.update(dkg_id.to_be_bytes());
    hasher.update((dkg_public_shares.len() as u64).to_be_bytes());
    for (signer_id, shares) in dkg_public_shares {
        hasher.update(signer_id.to_be_bytes());
        hasher.update(shares.dkg_id.to_be_bytes());
        hasher.update(shares.signer_id.to_be_bytes());
        hasher.update(shares.kex_public_key.compress().as_bytes());
        hasher.update(shares.kex_proof.R.compress().as_bytes());
        hasher.update(shares.kex_proof.s.to_bytes());
        hasher.update((shares.comms.len() as u64).to_be_bytes());
        for (party_id, comm) in &shares.comms {
            hasher.update(party_id.to_be_bytes());
            hasher.update(comm.id.id.to_bytes());
            hasher.update(comm.id.proof.R.compress().as_bytes());
            hasher.update(comm.id.proof.s.to_bytes());
            hasher.update((comm.poly.len() as u64).to_be_bytes());
            for a in &comm.poly {
                hasher.update(a.compress().as_bytes());
            }
        }
    }

    hasher.finalize().into()
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
/// DKG public shares done message from coordinator to signers
pub struct DkgPublicSharesDone {
    /// DKG round ID
    pub dkg_id: u64,
    /// Signer IDs that the coordinator received public shares from
    pub signer_ids: Vec<u32>,
}

impl Signable for DkgPublicSharesDone {
    fn hash(&self, hasher: &mut Sha256) {
        hasher.update("DKG_PUBLIC_SHARES_DONE".as_bytes());
        hasher.update(self.dkg_id.to_be_bytes());
        for signer_id in &self.signer_ids {
            hasher.update(signer_id.to_be_bytes());
        }
    }
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
/// DKG public shares done acknowledgment from signer to coordinator
pub struct DkgPublicSharesDoneAck {
    /// DKG round ID
    pub dkg_id: u64,
    /// Signer ID
    pub signer_id: u32,
    /// [`dkg_public_shares_digest`] of the public shares this signer accepted
    pub public_shares_digest: [u8; 32],
}

impl Signable for DkgPublicSharesDoneAck {
    fn hash(&self, hasher: &mut Sha256) {
        hasher.update("DKG_PUBLIC_SHARES_DONE_ACK".as_bytes());
        hasher.update(self.dkg_id.to_be_bytes());
        hasher.update(self.signer_id.to_be_bytes());
        hasher.update(self.public_shares_digest);
    }
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
/// DKG private begin message from signer to all signers and coordinator
pub struct DkgPrivateBegin {
    /// DKG round ID
    pub dkg_id: u64,
    /// Signer IDs who responded in time for this DKG round
    pub signer_ids: Vec<u32>,
    /// Key IDs who responded in time for this DKG round
    pub key_ids: Vec<u32>,
    /// [`dkg_public_shares_digest`] of the public shares the coordinator accepted, echoed so that
    /// signers need not trust the coordinator to have compared it against every ack
    pub public_shares_digest: [u8; 32],
}

impl Signable for DkgPrivateBegin {
    fn hash(&self, hasher: &mut Sha256) {
        hasher.update("DKG_PRIVATE_BEGIN".as_bytes());
        hasher.update(self.dkg_id.to_be_bytes());
        for key_id in &self.key_ids {
            hasher.update(key_id.to_be_bytes());
        }
        for signer_id in &self.signer_ids {
            hasher.update(signer_id.to_be_bytes());
        }
        hasher.update(self.public_shares_digest);
    }
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
/// DKG private shares message from signer to all signers and coordinator
pub struct DkgPrivateShares {
    /// DKG round ID
    pub dkg_id: u64,
    /// Signer ID
    pub signer_id: u32,
    /// List of (src_party_id, Map(dst_key_id, encrypted_share))
    pub shares: Vec<(u32, HashMap<u32, Vec<u8>>)>,
}

impl Signable for DkgPrivateShares {
    fn hash(&self, hasher: &mut Sha256) {
        hasher.update("DKG_PRIVATE_SHARES".as_bytes());
        hasher.update(self.dkg_id.to_be_bytes());
        hasher.update(self.signer_id.to_be_bytes());
        // make sure we hash consistently by sorting the keys
        for (src_id, share) in &self.shares {
            hasher.update(src_id.to_be_bytes());
            let mut dst_ids = share.keys().cloned().collect::<Vec<u32>>();
            dst_ids.sort();
            for dst_id in &dst_ids {
                hasher.update(dst_id.to_be_bytes());
                hasher.update(&share[dst_id]);
            }
        }
    }
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
/// DKG private shares done message from coordinator to signers
pub struct DkgPrivateSharesDone {
    /// DKG round ID
    pub dkg_id: u64,
    /// Signer IDs that the coordinator received private shares from
    pub signer_ids: Vec<u32>,
}

impl Signable for DkgPrivateSharesDone {
    fn hash(&self, hasher: &mut Sha256) {
        hasher.update("DKG_PRIVATE_SHARES_DONE".as_bytes());
        hasher.update(self.dkg_id.to_be_bytes());
        for signer_id in &self.signer_ids {
            hasher.update(signer_id.to_be_bytes());
        }
    }
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
/// DKG private shares done acknowledgment from signer to coordinator
pub struct DkgPrivateSharesDoneAck {
    /// DKG round ID
    pub dkg_id: u64,
    /// Signer ID
    pub signer_id: u32,
}

impl Signable for DkgPrivateSharesDoneAck {
    fn hash(&self, hasher: &mut Sha256) {
        hasher.update("DKG_PRIVATE_SHARES_DONE_ACK".as_bytes());
        hasher.update(self.dkg_id.to_be_bytes());
        hasher.update(self.signer_id.to_be_bytes());
    }
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
/// DKG end begin message from signer to all signers and coordinator
pub struct DkgEndBegin {
    /// DKG round ID
    pub dkg_id: u64,
    /// Signer IDs who responded in time for this DKG round
    pub signer_ids: Vec<u32>,
    /// Key IDs who responded in time for this DKG round
    pub key_ids: Vec<u32>,
}

impl Signable for DkgEndBegin {
    fn hash(&self, hasher: &mut Sha256) {
        hasher.update("DKG_END_BEGIN".as_bytes());
        hasher.update(self.dkg_id.to_be_bytes());
        for key_id in &self.key_ids {
            hasher.update(key_id.to_be_bytes());
        }
        for signer_id in &self.signer_ids {
            hasher.update(signer_id.to_be_bytes());
        }
    }
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
/// DKG end message from signers to coordinator
pub struct DkgEnd {
    /// DKG round ID
    pub dkg_id: u64,
    /// Signer ID
    pub signer_id: u32,
    /// DKG status for this Signer after receiving public/private shares
    pub status: DkgStatus,
}

impl Signable for DkgEnd {
    fn hash(&self, hasher: &mut Sha256) {
        hasher.update("DKG_END".as_bytes());
        hasher.update(self.dkg_id.to_be_bytes());
        hasher.update(self.signer_id.to_be_bytes());
    }
}

#[derive(Clone, Serialize, Deserialize, PartialEq)]
/// Nonce request message from coordinator to signers
pub struct NonceRequest {
    /// DKG round ID
    pub dkg_id: u64,
    /// Signing round ID
    pub sign_id: u64,
    /// Signing round iteration ID
    pub sign_iter_id: u64,
    /// The message to sign
    pub message: Vec<u8>,
    /// What type of signature to create
    pub signature_type: SignatureType,
}

impl Debug for NonceRequest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NonceRequest")
            .field("dkg_id", &self.dkg_id)
            .field("sign_id", &self.sign_id)
            .field("sign_iter_id", &self.sign_iter_id)
            .field("message", &hex::encode(&self.message))
            .field("signature_type", &self.signature_type)
            .finish()
    }
}

impl Signable for NonceRequest {
    fn hash(&self, hasher: &mut Sha256) {
        hasher.update("NONCE_REQUEST".as_bytes());
        hasher.update(self.dkg_id.to_be_bytes());
        hasher.update(self.sign_id.to_be_bytes());
        hasher.update(self.sign_iter_id.to_be_bytes());
        hasher.update(self.message.as_slice());
        match self.signature_type {
            SignatureType::Frost => hasher.update("SIGNATURE_TYPE_FROST".as_bytes()),
            SignatureType::Schnorr => hasher.update("SIGNATURE_TYPE_SCHNORR".as_bytes()),
            SignatureType::Taproot(merkle_root) => {
                hasher.update("SIGNATURE_TYPE_TAPROOT".as_bytes());
                if let Some(merkle_root) = merkle_root {
                    hasher.update(merkle_root);
                }
            }
        }
    }
}

#[derive(Clone, Serialize, Deserialize, PartialEq)]
/// Nonce response message from signers to coordinator
pub struct NonceResponse {
    /// DKG round ID
    pub dkg_id: u64,
    /// Signing round ID
    pub sign_id: u64,
    /// Signing round iteration ID
    pub sign_iter_id: u64,
    /// Signer ID
    pub signer_id: u32,
    /// Key IDs
    pub key_ids: Vec<u32>,
    /// Public nonces
    pub nonces: Vec<PublicNonce>,
    /// Bytes being signed
    pub message: Vec<u8>,
}

impl Debug for NonceResponse {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NonceResponse")
            .field("dkg_id", &self.dkg_id)
            .field("sign_id", &self.sign_id)
            .field("sign_iter_id", &self.sign_iter_id)
            .field("signer_id", &self.signer_id)
            .field("key_ids", &self.key_ids)
            .field(
                "nonces",
                &self
                    .nonces
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>(),
            )
            .field("message", &hex::encode(&self.message))
            .finish()
    }
}

impl Signable for NonceResponse {
    fn hash(&self, hasher: &mut Sha256) {
        hasher.update("NONCE_RESPONSE".as_bytes());
        hasher.update(self.dkg_id.to_be_bytes());
        hasher.update(self.sign_id.to_be_bytes());
        hasher.update(self.sign_iter_id.to_be_bytes());
        hasher.update(self.signer_id.to_be_bytes());

        for key_id in &self.key_ids {
            hasher.update(key_id.to_be_bytes());
        }

        for nonce in &self.nonces {
            hasher.update(nonce.D.compress().as_bytes());
            hasher.update(nonce.E.compress().as_bytes());
        }

        hasher.update(self.message.as_slice());
    }
}

#[derive(Clone, Copy, Serialize, Deserialize, Debug, PartialEq)]
/// Signature type
pub enum SignatureType {
    /// FROST signature
    Frost,
    /// BIP-340 Schnorr proof
    Schnorr,
    /// BIP-341 Taproot style schnorr proof with a merkle root
    Taproot(Option<MerkleRoot>),
}

#[derive(Clone, Serialize, Deserialize, PartialEq)]
/// Signature share request message from coordinator to signers
pub struct SignatureShareRequest {
    /// DKG round ID
    pub dkg_id: u64,
    /// Signing round ID
    pub sign_id: u64,
    /// Signing round iteration ID
    pub sign_iter_id: u64,
    /// Nonces responses used for this signature
    pub nonce_responses: Vec<NonceResponse>,
    /// Bytes to sign
    pub message: Vec<u8>,
    /// What type of signature to create
    pub signature_type: SignatureType,
}

impl Debug for SignatureShareRequest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SignatureShareRequest")
            .field("dkg_id", &self.dkg_id)
            .field("sign_id", &self.sign_id)
            .field("sign_iter_id", &self.sign_iter_id)
            .field("nonce_responses", &self.nonce_responses)
            .field("message", &hex::encode(&self.message))
            .field("signature_type", &self.signature_type)
            .finish()
    }
}

impl Signable for SignatureShareRequest {
    fn hash(&self, hasher: &mut Sha256) {
        hasher.update("SIGNATURE_SHARE_REQUEST".as_bytes());
        hasher.update(self.dkg_id.to_be_bytes());
        hasher.update(self.sign_id.to_be_bytes());

        for nonce_response in &self.nonce_responses {
            nonce_response.hash(hasher);
        }

        hasher.update(self.message.as_slice());
        match self.signature_type {
            SignatureType::Frost => hasher.update("SIGNATURE_TYPE_FROST".as_bytes()),
            SignatureType::Schnorr => hasher.update("SIGNATURE_TYPE_SCHNORR".as_bytes()),
            SignatureType::Taproot(merkle_root) => {
                hasher.update("SIGNATURE_TYPE_TAPROOT".as_bytes());
                if let Some(merkle_root) = merkle_root {
                    hasher.update(merkle_root);
                }
            }
        }
    }
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
/// Signature share response message from signers to coordinator
pub struct SignatureShareResponse {
    /// DKG round ID
    pub dkg_id: u64,
    /// Signing round ID
    pub sign_id: u64,
    /// Signing round iteration ID
    pub sign_iter_id: u64,
    /// Signer ID
    pub signer_id: u32,
    /// Signature shares from this Signer
    pub signature_shares: Vec<SignatureShare>,
}

impl Signable for SignatureShareResponse {
    fn hash(&self, hasher: &mut Sha256) {
        hasher.update("SIGNATURE_SHARE_RESPONSE".as_bytes());
        hasher.update(self.dkg_id.to_be_bytes());
        hasher.update(self.sign_id.to_be_bytes());
        hasher.update(self.signer_id.to_be_bytes());

        for signature_share in &self.signature_shares {
            hasher.update(signature_share.id.to_be_bytes());
            hasher.update(signature_share.z_i.to_bytes());
            for key_id in &signature_share.key_ids {
                hasher.update(key_id.to_be_bytes());
            }
        }
    }
}

#[derive(Serialize, Deserialize, Clone, PartialEq)]
/// Network packets need to be signed so they can be verified
pub struct Packet {
    /// The message to sign
    pub msg: Message,
    /// The bytes of the signature
    pub sig: Vec<u8>,
}

impl Debug for Packet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Packet")
            .field("msg", &self.msg)
            .field("sig", &hex::encode(&self.sig))
            .finish()
    }
}

impl Packet {
    /// This function verifies the packet's signature, returning true if the signature is valid,
    /// i.e. is appropriately signed by either the provided coordinator or one of the provided signer public keys
    pub fn verify(
        &self,
        signers_public_keys: &PublicKeys,
        coordinator_public_key: &ecdsa::PublicKey,
    ) -> bool {
        match &self.msg {
            Message::DkgBegin(msg) => {
                if !msg.verify(&self.sig, coordinator_public_key) {
                    warn!("Received a DkgBegin message with an invalid signature.");
                    return false;
                }
            }
            Message::DkgPrivateBegin(msg) => {
                if !msg.verify(&self.sig, coordinator_public_key) {
                    warn!("Received a DkgPrivateBegin message with an invalid signature.");
                    return false;
                }
            }
            Message::DkgEndBegin(msg) => {
                if !msg.verify(&self.sig, coordinator_public_key) {
                    warn!("Received a DkgEndBegin message with an invalid signature.");
                    return false;
                }
            }
            Message::DkgEnd(msg) => {
                if let Some(public_key) = signers_public_keys.signers.get(&msg.signer_id) {
                    if !msg.verify(&self.sig, public_key) {
                        warn!("Received a DkgPublicEnd message with an invalid signature.");
                        return false;
                    }
                } else {
                    warn!(
                        "Received a DkgPublicEnd message with an unknown id: {}",
                        msg.signer_id
                    );
                    return false;
                }
            }
            Message::DkgPublicShares(msg) => {
                if let Some(public_key) = signers_public_keys.signers.get(&msg.signer_id) {
                    if !msg.verify(&self.sig, public_key) {
                        warn!("Received a DkgPublicShares message with an invalid signature.");
                        return false;
                    }
                } else {
                    warn!(
                        "Received a DkgPublicShares message with an unknown id: {}",
                        msg.signer_id
                    );
                    return false;
                }
            }
            Message::DkgPublicSharesDone(msg) => {
                if !msg.verify(&self.sig, coordinator_public_key) {
                    warn!("Received a DkgPublicSharesDone message with an invalid signature.");
                    return false;
                }
            }
            Message::DkgPublicSharesDoneAck(msg) => {
                if let Some(public_key) = signers_public_keys.signers.get(&msg.signer_id) {
                    if !msg.verify(&self.sig, public_key) {
                        warn!(
                            "Received a DkgPublicSharesDoneAck message with an invalid signature."
                        );
                        return false;
                    }
                } else {
                    warn!(
                        "Received a DkgPublicSharesDoneAck message with an unknown id: {}",
                        msg.signer_id
                    );
                    return false;
                }
            }
            Message::DkgPrivateShares(msg) => {
                // Private shares have key IDs from [0, N) to reference IDs from [1, N]
                // in Frost V4 to enable easy indexing hence ID + 1
                // TODO: Once Frost V5 is released, this off by one adjustment will no longer be required
                if let Some(public_key) = signers_public_keys.signers.get(&msg.signer_id) {
                    if !msg.verify(&self.sig, public_key) {
                        warn!("Received a DkgPrivateShares message with an invalid signature from signer_id {} key {}", msg.signer_id, &public_key);
                        return false;
                    }
                } else {
                    warn!(
                        "Received a DkgPrivateShares message with an unknown id: {}",
                        msg.signer_id
                    );
                    return false;
                }
            }
            Message::DkgPrivateSharesDone(msg) => {
                if !msg.verify(&self.sig, coordinator_public_key) {
                    warn!("Received a DkgPrivateSharesDone message with an invalid signature.");
                    return false;
                }
            }
            Message::DkgPrivateSharesDoneAck(msg) => {
                if let Some(public_key) = signers_public_keys.signers.get(&msg.signer_id) {
                    if !msg.verify(&self.sig, public_key) {
                        warn!(
                            "Received a DkgPrivateSharesDoneAck message with an invalid signature."
                        );
                        return false;
                    }
                } else {
                    warn!(
                        "Received a DkgPrivateSharesDoneAck message with an unknown id: {}",
                        msg.signer_id
                    );
                    return false;
                }
            }
            Message::NonceRequest(msg) => {
                if !msg.verify(&self.sig, coordinator_public_key) {
                    warn!("Received a NonceRequest message with an invalid signature.");
                    return false;
                }
            }
            Message::NonceResponse(msg) => {
                if let Some(public_key) = signers_public_keys.signers.get(&msg.signer_id) {
                    if !msg.verify(&self.sig, public_key) {
                        warn!("Received a NonceResponse message with an invalid signature.");
                        return false;
                    }
                } else {
                    warn!(
                        "Received a NonceResponse message with an unknown id: {}",
                        msg.signer_id
                    );
                    return false;
                }
            }
            Message::SignatureShareRequest(msg) => {
                if !msg.verify(&self.sig, coordinator_public_key) {
                    warn!("Received a SignatureShareRequest message with an invalid signature.");
                    return false;
                }
            }
            Message::SignatureShareResponse(msg) => {
                if let Some(public_key) = signers_public_keys.signers.get(&msg.signer_id) {
                    if !msg.verify(&self.sig, public_key) {
                        warn!(
                            "Received a SignatureShareResponse message with an invalid signature."
                        );
                        return false;
                    }
                } else {
                    warn!(
                        "Received a SignatureShareResponse message with an unknown id: {}",
                        msg.signer_id
                    );
                    return false;
                }
            }
        }
        true
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::schnorr::ID;
    use crate::util::create_rng;
    use rand_core::{CryptoRng, RngCore};

    #[derive(Clone, Debug)]
    #[allow(dead_code)]
    pub struct TestConfig {
        pub coordinator_private_key: Scalar,
        pub coordinator_public_key: ecdsa::PublicKey,
        pub signer_private_key: Scalar,
        pub signer_public_key: ecdsa::PublicKey,
        pub public_keys: PublicKeys,
    }

    impl TestConfig {
        pub fn new<RNG: RngCore + CryptoRng>(rng: &mut RNG) -> Self {
            let coordinator_private_key = Scalar::random(rng);
            let coordinator_public_key = ecdsa::PublicKey::new(&coordinator_private_key).unwrap();
            let signer_private_key = Scalar::random(rng);
            let signer_public_key = ecdsa::PublicKey::new(&signer_private_key).unwrap();

            let mut signer_ids_map = HashMap::new();
            let mut signer_key_ids = HashMap::new();
            let mut key_ids_map = HashMap::new();
            let mut key_ids_set = HashSet::new();
            signer_ids_map.insert(0, signer_public_key);
            key_ids_map.insert(1, signer_public_key);
            key_ids_set.insert(1);
            signer_key_ids.insert(0, key_ids_set);

            let public_keys = PublicKeys {
                signers: signer_ids_map,
                key_ids: key_ids_map,
                signer_key_ids,
            };

            Self {
                coordinator_private_key,
                coordinator_public_key,
                signer_private_key,
                signer_public_key,
                public_keys,
            }
        }
    }

    impl Default for TestConfig {
        fn default() -> Self {
            let mut rng = create_rng();
            Self::new(&mut rng)
        }
    }

    #[test]
    fn dkg_begin_verify_msg() {
        let test_config = TestConfig::default();
        let dkg_begin = DkgBegin { dkg_id: 0 };
        let dkg_private_begin = DkgPrivateBegin {
            dkg_id: 0,
            key_ids: Default::default(),
            signer_ids: Default::default(),
            public_shares_digest: Default::default(),
        };
        let msg = Message::DkgBegin(dkg_begin.clone());
        let coordinator_packet_dkg_begin = Packet {
            sig: dkg_begin
                .sign(&test_config.coordinator_private_key)
                .expect("Failed to sign"),
            msg: msg.clone(),
        };
        let signer_packet_dkg_begin = Packet {
            sig: dkg_begin
                .sign(&test_config.signer_private_key)
                .expect("Failed to sign"),
            msg,
        };

        assert!(coordinator_packet_dkg_begin.verify(
            &test_config.public_keys,
            &test_config.coordinator_public_key
        ));
        assert!(!signer_packet_dkg_begin.verify(
            &test_config.public_keys,
            &test_config.coordinator_public_key
        ));

        let msg = Message::DkgPrivateBegin(dkg_private_begin.clone());
        let coordinator_packet_dkg_private_begin = Packet {
            sig: dkg_private_begin
                .sign(&test_config.coordinator_private_key)
                .expect("Failed to sign"),
            msg: msg.clone(),
        };
        let signer_packet_dkg_private_begin = Packet {
            sig: dkg_private_begin
                .sign(&test_config.signer_private_key)
                .expect("Failed to sign"),
            msg,
        };

        assert!(coordinator_packet_dkg_private_begin.verify(
            &test_config.public_keys,
            &test_config.coordinator_public_key
        ));
        assert!(!signer_packet_dkg_private_begin.verify(
            &test_config.public_keys,
            &test_config.coordinator_public_key
        ));
    }

    #[test]
    fn dkg_public_shares_verify_msg() {
        let ctx = 0u64.to_be_bytes();
        let mut rng = create_rng();
        let test_config = TestConfig::default();
        let public_shares = DkgPublicShares {
            dkg_id: 0,
            signer_id: 0,
            comms: vec![(
                0,
                PolyCommitment {
                    id: ID::new(&Scalar::new(), &Scalar::new(), &ctx, &mut rng),
                    poly: vec![],
                },
            )],
            kex_public_key: Point::from(Scalar::random(&mut rng)),
            kex_proof: schnorr::Proof {
                R: Point::new(),
                s: Scalar::new(),
            },
        };
        let msg = Message::DkgPublicShares(public_shares.clone());
        let coordinator_packet_dkg_public_shares = Packet {
            sig: public_shares
                .sign(&test_config.coordinator_private_key)
                .expect("Failed to sign"),
            msg: msg.clone(),
        };
        let signer_packet_dkg_public_shares = Packet {
            sig: public_shares
                .sign(&test_config.signer_private_key)
                .expect("Failed to sign"),
            msg,
        };

        assert!(!coordinator_packet_dkg_public_shares.verify(
            &test_config.public_keys,
            &test_config.coordinator_public_key
        ));
        assert!(signer_packet_dkg_public_shares.verify(
            &test_config.public_keys,
            &test_config.coordinator_public_key
        ));

        // change the kex_public_key but keep the previous signature
        let mitm_signer_packet_dkg_public_shares = Packet {
            sig: signer_packet_dkg_public_shares.sig,
            msg: Message::DkgPublicShares(DkgPublicShares {
                kex_public_key: Point::from(Scalar::random(&mut rng)),
                ..public_shares
            }),
        };
        // packet should no longer verify
        assert!(!mitm_signer_packet_dkg_public_shares.verify(
            &test_config.public_keys,
            &test_config.coordinator_public_key
        ));
    }

    #[test]
    fn dkg_private_shares_verify_msg() {
        let test_config = TestConfig::default();
        let private_shares = DkgPrivateShares {
            dkg_id: 0,
            signer_id: 0,
            shares: vec![(0, HashMap::new())],
        };
        let msg = Message::DkgPrivateShares(private_shares.clone());
        let coordinator_packet_dkg_private_shares = Packet {
            sig: private_shares
                .sign(&test_config.coordinator_private_key)
                .expect("Failed to sign"),
            msg: msg.clone(),
        };
        let signer_packet_dkg_private_shares = Packet {
            sig: private_shares
                .sign(&test_config.signer_private_key)
                .expect("Failed to sign"),
            msg,
        };

        assert!(!coordinator_packet_dkg_private_shares.verify(
            &test_config.public_keys,
            &test_config.coordinator_public_key
        ));
        assert!(signer_packet_dkg_private_shares.verify(
            &test_config.public_keys,
            &test_config.coordinator_public_key
        ));
    }

    #[test]
    fn dkg_end_verify_msg() {
        let test_config = TestConfig::default();
        let dkg_end = DkgEnd {
            dkg_id: 0,
            signer_id: 0,
            status: DkgStatus::Success,
        };
        let msg = Message::DkgEnd(dkg_end.clone());

        let coordinator_packet_dkg_end = Packet {
            sig: dkg_end
                .sign(&test_config.coordinator_private_key)
                .expect("Failed to sign"),
            msg: msg.clone(),
        };
        let signer_packet_dkg_end = Packet {
            sig: dkg_end
                .sign(&test_config.signer_private_key)
                .expect("Failed to sign"),
            msg,
        };
        assert!(!coordinator_packet_dkg_end.verify(
            &test_config.public_keys,
            &test_config.coordinator_public_key
        ));
        assert!(signer_packet_dkg_end.verify(
            &test_config.public_keys,
            &test_config.coordinator_public_key
        ));
    }
    #[test]
    fn nonce_request_verify_msg() {
        let test_config = TestConfig::default();
        let nonce_request = NonceRequest {
            dkg_id: 0,
            sign_id: 0,
            sign_iter_id: 0,
            message: vec![],
            signature_type: SignatureType::Frost,
        };
        let msg = Message::NonceRequest(nonce_request.clone());
        let coordinator_packet_nonce_request = Packet {
            sig: nonce_request
                .sign(&test_config.coordinator_private_key)
                .expect("Failed to sign"),
            msg: msg.clone(),
        };
        let signer_packet_nonce_request = Packet {
            sig: nonce_request
                .sign(&test_config.signer_private_key)
                .expect("Failed to sign"),
            msg,
        };
        assert!(coordinator_packet_nonce_request.verify(
            &test_config.public_keys,
            &test_config.coordinator_public_key
        ));
        assert!(!signer_packet_nonce_request.verify(
            &test_config.public_keys,
            &test_config.coordinator_public_key
        ));
    }
    #[test]
    fn nonce_response_verify_msg() {
        let test_config = TestConfig::default();

        let nonce_response = NonceResponse {
            dkg_id: 0,
            sign_id: 0,
            sign_iter_id: 0,
            signer_id: 0,
            key_ids: vec![],
            nonces: vec![],
            message: vec![],
        };
        let msg = Message::NonceResponse(nonce_response.clone());
        let coordinator_packet_nonce_response = Packet {
            sig: nonce_response
                .sign(&test_config.coordinator_private_key)
                .expect("Failed to sign"),
            msg: msg.clone(),
        };
        let signer_packet_nonce_response = Packet {
            sig: nonce_response
                .sign(&test_config.signer_private_key)
                .expect("Failed to sign"),
            msg,
        };
        assert!(!coordinator_packet_nonce_response.verify(
            &test_config.public_keys,
            &test_config.coordinator_public_key
        ));
        assert!(signer_packet_nonce_response.verify(
            &test_config.public_keys,
            &test_config.coordinator_public_key
        ));
    }

    #[test]
    fn signature_share_request_verify_msg() {
        let test_config = TestConfig::default();
        let signature_share_request = SignatureShareRequest {
            dkg_id: 0,
            sign_id: 0,
            sign_iter_id: 0,
            nonce_responses: vec![],
            message: vec![],
            signature_type: SignatureType::Frost,
        };
        let msg = Message::SignatureShareRequest(signature_share_request.clone());
        let coordinator_packet_signature_share_request = Packet {
            sig: signature_share_request
                .sign(&test_config.coordinator_private_key)
                .expect("Failed to sign"),
            msg: msg.clone(),
        };
        let signer_packet_signature_share_request = Packet {
            sig: signature_share_request
                .sign(&test_config.signer_private_key)
                .expect("Failed to sign"),
            msg,
        };
        assert!(coordinator_packet_signature_share_request.verify(
            &test_config.public_keys,
            &test_config.coordinator_public_key
        ));
        assert!(!signer_packet_signature_share_request.verify(
            &test_config.public_keys,
            &test_config.coordinator_public_key
        ));
    }

    #[test]
    fn signature_share_response_verify_msg() {
        let test_config = TestConfig::default();

        let signature_share_response = SignatureShareResponse {
            dkg_id: 0,
            sign_id: 0,
            sign_iter_id: 0,
            signer_id: 0,
            signature_shares: vec![],
        };
        let msg = Message::SignatureShareResponse(signature_share_response.clone());
        let coordinator_packet_signature_share_response = Packet {
            sig: signature_share_response
                .sign(&test_config.coordinator_private_key)
                .expect("Failed to sign"),
            msg: msg.clone(),
        };
        let signer_packet_signature_share_response = Packet {
            sig: signature_share_response
                .sign(&test_config.signer_private_key)
                .expect("Failed to sign"),
            msg,
        };
        assert!(!coordinator_packet_signature_share_response.verify(
            &test_config.public_keys,
            &test_config.coordinator_public_key
        ));
        assert!(signer_packet_signature_share_response.verify(
            &test_config.public_keys,
            &test_config.coordinator_public_key
        ));
    }

    #[test]
    fn signature_share_response_wrapped_verify_msg() {
        let test_config = TestConfig::default();

        let signature_share_response = SignatureShareResponse {
            dkg_id: 0,
            sign_id: 0,
            sign_iter_id: 0,
            signer_id: 0,
            signature_shares: vec![],
        };
        let msg = Message::SignatureShareResponse(signature_share_response.clone());
        let sig = msg
            .sign(&test_config.coordinator_private_key)
            .expect("Failed to sign");
        assert!(msg.verify(&sig, &test_config.coordinator_public_key));
    }

    fn digest_test_shares<RNG: RngCore + CryptoRng>(
        signer_id: u32,
        rng: &mut RNG,
    ) -> DkgPublicShares {
        let ctx = 0u64.to_be_bytes();
        let comms = (0..2u32)
            .map(|i| {
                let party_id = signer_id * 2 + i;
                (
                    party_id,
                    PolyCommitment {
                        id: ID::new(&Scalar::from(party_id), &Scalar::random(rng), &ctx, rng),
                        poly: vec![Point::from(Scalar::random(rng)); 2],
                    },
                )
            })
            .collect();
        DkgPublicShares {
            dkg_id: 7,
            signer_id,
            comms,
            kex_public_key: Point::from(Scalar::random(rng)),
            kex_proof: schnorr::Proof {
                R: Point::from(Scalar::random(rng)),
                s: Scalar::random(rng),
            },
        }
    }

    #[test]
    fn dkg_public_shares_digest_covers_every_field() {
        let mut rng = create_rng();
        let shares: BTreeMap<u32, DkgPublicShares> = (0..2u32)
            .map(|signer_id| (signer_id, digest_test_shares(signer_id, &mut rng)))
            .collect();
        let digest = dkg_public_shares_digest(7, &shares);
        assert_eq!(digest, dkg_public_shares_digest(7, &shares.clone()));

        let other_point = Point::from(Scalar::random(&mut rng));
        let other_scalar = Scalar::random(&mut rng);
        type Mutation = Box<dyn Fn(&mut BTreeMap<u32, DkgPublicShares>)>;
        let mutations: Vec<(&str, Mutation)> = vec![
            (
                "drop a signer",
                Box::new(|m| {
                    m.remove(&1);
                }),
            ),
            (
                "shares dkg_id",
                Box::new(|m| m.get_mut(&1).unwrap().dkg_id += 1),
            ),
            (
                "shares signer_id",
                Box::new(|m| m.get_mut(&1).unwrap().signer_id += 1),
            ),
            (
                "kex_public_key",
                Box::new(move |m| m.get_mut(&1).unwrap().kex_public_key = other_point),
            ),
            (
                "kex_proof R",
                Box::new(move |m| m.get_mut(&1).unwrap().kex_proof.R = other_point),
            ),
            (
                "kex_proof s",
                Box::new(move |m| m.get_mut(&1).unwrap().kex_proof.s = other_scalar),
            ),
            (
                "party_id",
                Box::new(|m| m.get_mut(&1).unwrap().comms[1].0 += 10),
            ),
            (
                "ID id",
                Box::new(move |m| m.get_mut(&1).unwrap().comms[1].1.id.id = other_scalar),
            ),
            (
                "ID proof R",
                Box::new(move |m| m.get_mut(&1).unwrap().comms[1].1.id.proof.R = other_point),
            ),
            (
                "ID proof s",
                Box::new(move |m| m.get_mut(&1).unwrap().comms[1].1.id.proof.s = other_scalar),
            ),
            (
                "poly point",
                Box::new(move |m| m.get_mut(&1).unwrap().comms[1].1.poly[1] = other_point),
            ),
            (
                "poly length",
                Box::new(|m| {
                    m.get_mut(&1).unwrap().comms[1].1.poly.pop();
                }),
            ),
            (
                "comms length",
                Box::new(|m| {
                    m.get_mut(&1).unwrap().comms.pop();
                }),
            ),
        ];
        for (name, mutate) in mutations {
            let mut mutated = shares.clone();
            mutate(&mut mutated);
            assert_ne!(
                digest,
                dkg_public_shares_digest(7, &mutated),
                "digest does not cover {name}"
            );
        }
        assert_ne!(
            digest,
            dkg_public_shares_digest(8, &shares),
            "digest does not cover dkg_id"
        );
    }

    #[test]
    fn public_shares_digest_is_signed() {
        let test_config = TestConfig::default();
        let public_key = &test_config.coordinator_public_key;

        let ack = DkgPublicSharesDoneAck {
            dkg_id: 0,
            signer_id: 0,
            public_shares_digest: [1u8; 32],
        };
        let sig = ack.sign(&test_config.coordinator_private_key).unwrap();
        assert!(ack.verify(&sig, public_key));
        let mut tampered = ack.clone();
        tampered.public_shares_digest[0] ^= 1;
        assert!(!tampered.verify(&sig, public_key));

        let begin = DkgPrivateBegin {
            dkg_id: 0,
            signer_ids: vec![0],
            key_ids: vec![1],
            public_shares_digest: [1u8; 32],
        };
        let sig = begin.sign(&test_config.coordinator_private_key).unwrap();
        assert!(begin.verify(&sig, public_key));
        let mut tampered = begin.clone();
        tampered.public_shares_digest[0] ^= 1;
        assert!(!tampered.verify(&sig, public_key));
    }
}
