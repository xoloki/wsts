# Usage

Applications which use `WSTS` will typically run both `Signer` and `Coordinator` state machines, in order to be able to handle all parts of the protocol. Because of this, these state machines do not verify packets as they come in; this would lead to duplicate work, and require the state machines to have all keys in their configs, including knowing who is the active coordinator. This is out of scope for the library. Thus applications `must` verify packets before calling `process_message` on them.

This addresses the audit critical issues [CR-01](https://github.com/xoloki/wsts/issues/66) and [CR-02](https://github.com/xoloki/wsts/issues/67).


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

Ensure that you pass the RNG to all functions that require randomness.