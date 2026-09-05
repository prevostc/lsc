# Trusted Computing Base

What an end-to-end theorem of this project relies on beyond its own proof.

## Trusted

- Lean 4 kernel and the standard axioms `propext`, `Classical.choice`, `Quot.sound`. No
  `native_decide`, `bv_decide`, `sorry` or project axioms in the proof chain (they may appear in
  tests only). CI pins the axiom footprint of every end-to-end theorem.
- **The language specification**: `Tx` semantics and `Core.denote` (`Lsc/Lang/Tx.lean`,
  `Core.lean`). Reviewed, not proved. A theorem about `Tx.run f` means what these files say it
  means.
- **EVM ground truth**: powdr `evm-semantics` (relational, conformance-tested with zero failures
  against `ethereum/tests` GeneralStateTests and EEST Osaka) and powdr `yul-semantics` (adequacy
  proved by its authors). Pinned commits.
- **Deployment interface**: the layout relation `R` (storage slots, ABI encoding, error encoding)
  in `Lsc/Compiler/Layout.lean` defines how bytecode state is read back as contract state.
- **Keccak**: powdr's keccak oracle, assumed injective on the storage keys used; KeccakEngine
  assumed to agree with it for the selectors computed at compile time.
- Ethereum clients implement the specification.

## Hypotheses stated in every end-to-end theorem

- Sufficient gas for each call (powdr's gas bound is existential).
- `ExternalsRealized`: external call responses are realised by complete EVM executions.
- `Conforms I addr` for each declared external address (code realises the interface model and
  does not modify our account).
- Fork = Osaka.
- Adversary model scope (`SECURITY_MODEL.md`): any call sequence from any addresses; excludes
  private-key compromise, block-producer ordering/MEV, gas griefing, non-conforming tokens unless
  modelled.

## Untrusted (checked or irrelevant to soundness)

- The reifier (`Lsc/Lang/Reify.lean`): every run emits a kernel-checked `rfl` certificate.
- `toYul` codegen: covered by `toYul_correct`.
- powdr's compiler and optimisers: covered by `compileObject_correct`.
- The differential harness (revm/anvil): defence in depth only.

## Removed from the TCB by the September 2026 review

Home-grown EVM machine (~1.4k lines), home-grown codegen/encoder (~1.3k lines), EvmYulLean and
its C FFI (keccak, sha256), the two v2 axioms in `Lsc/Compile/Bytecode/EvmYulTrust.lean`.
