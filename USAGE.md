# Usage

Applications which use `WSTS` will typically run both `Signer` and `Coordinator` state machines, in order to be able to handle all parts of the protocol.

## Packet verification

Both state machines verify the signature on each incoming `Packet`, and do so by default. The coordinator is controlled by `Config::verify_packet_sigs` and the signer by the public `Signer::verify_packet_sigs` field, which is persisted in `SavedState`; both are `true` unless you set them otherwise.

Verification needs the state machine to know two things: the signer public keys, via `public_keys`, and the active coordinator's public key, via `coordinator_public_key`. Without the latter, `process` and `process_message` return `Error::MissingCoordinatorPublicKey`; a packet whose signature does not check out returns `Error::InvalidPacketSignature`.

Set the flag to `false` if the calling application has already verified the packet, so the work is not done twice — an application running both state machines over the same packet stream would otherwise verify each packet twice. **If you disable verification, the application `must` verify packets itself before calling `process_message` on them.**

This is what addresses the audit critical issues [CR-01](https://github.com/xoloki/wsts/issues/66) and [CR-02](https://github.com/xoloki/wsts/issues/67). Verification moved into the library in [#153](https://github.com/xoloki/wsts/pull/153); before that it was the application's responsibility in every case.

## Random number generation

To ensure flexibility, these state machines require the user to provide a random number generator (RNG) that implements the `RngCore` and `CryptoRng` traits.

### Providing an RNG

You can use the following RNG implementations:

- **Operating System RNG (`OsRng`)**
  
  ```rust
  use rand_core::OsRng;

  let mut rng = OsRng;
  ```

- **ChaCha20 RNG**
  
  ```rust
  use rand_chacha::ChaCha20Rng;
  use rand_core::SeedableRng;

  let mut rng = ChaCha20Rng::from_entropy();
  ```

- **Custom RNGs**

  Implement your own RNG by adhering to the `RngCore` and `CryptoRng` traits.

### Example Usage

```rust
use wsts::util::create_rng;
use wsts::v2::Party;

// Protocol parameters
let num_parties: u32 = 5;
let num_keys: u32 = 10;
let threshold: u32 = 7;

// This party's id, and the key ids it controls
let party_id: u32 = 0;
let key_ids = [0, 1];

// Initialize your RNG
let mut rng = create_rng();

// Create a party
let party = Party::new(party_id, &key_ids, num_parties, num_keys, threshold, &mut rng);
```

The `v1` module is behind the `with_v1` feature and is not built by default; `use wsts::v1::Signer` requires `--features with_v1`.

### Do not replay RNG state

`WSTS` derives signing nonces with the hedged construction from [RFC 9591 section 4.1](https://datatracker.ietf.org/doc/rfc9591): each nonce is the hash of fresh RNG output together with the signer's secret key. The secret key is mixed in so that a poor RNG does not immediately yield a predictable nonce, but the nonce is still a function of the bytes your RNG produces.

So never reuse or replay RNG state across signing rounds. Two rounds that draw the same bytes produce the same nonce, and two Schnorr signatures sharing a nonce reveal the signing key. This is why `create_rng` returns `OsRng` and why the example above seeds from entropy: neither is reproducible, deliberately. If you want a reproducible run, keep it to tests.
