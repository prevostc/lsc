# Trusted Computing Base

What an end-to-end theorem of this project relies on beyond its own proof.

## Trusted

- Lean 4 kernel and the standard axioms `propext`, `Classical.choice`, `Quot.sound`. No
  `native_decide`, `bv_decide`, `sorry` or project axioms in the proof chain (they may appear in
  tests only). CI pins the axiom footprint of every end-to-end theorem.
- **The language specification**: `Tx` semantics, `Tx.call`, and `Core.denote`
  (`Lsc/Lang/Tx.lean`, `Interface.lean`, `Core.lean`). Reviewed, not proved. A theorem about
  `Tx.run f` means what these files say it means.
- **EVM ground truth**: powdr `evm-semantics` (relational, conformance-tested with zero failures
  against `ethereum/tests` GeneralStateTests and EEST Osaka) and powdr `yul-semantics` (adequacy
  proved by its authors). Pinned commits.
- **Deployment interface**: the layout relation `R` (storage slots, ABI encoding, error encoding)
  in `Lsc/Compiler/Correctness.lean` defines how bytecode state is read back as contract state.
- **Keccak**: powdr's keccak oracle (`targetKeccakOracle` / `evmKeccak` in the glue), assumed
  injective on the storage keys used (`KeccakSep`); KeccakEngine assumed to agree with it for
  the selectors computed at compile time.
- Ethereum clients implement the specification.

## Hypotheses stated in every end-to-end theorem

- Sufficient gas for each call (powdr's gas bound is existential; `EvmCallRun` quantifies `∃ b`).
- `FrameOK` on the assembled bytecode (fork = Osaka, not a precompile, empty call stack).
- `compile rt = some is` and `runtimeBlock c = some rt`: the compiler accepted this program.
- `KeccakSep c evmKeccak` with `evmKeccak := YulEvmCompiler.targetKeccakOracle`.
- `WorldWF`, `CtxWF`, ABI args `< 2^256`, and (for Token balance reads) the address `< 2^256`.
- S1 call-free glue uses a closed external model (`calls := .none`, `creates := .none`) and
  `ExternalsRealized.none`. Unrestricted programs still need `ExternalsRealized` / `Conforms`
  as below.
- `ExternalsRealized`: external call responses are realised by complete EVM executions
  (S2 / programs with `Op.call`).
- Per binding `b` of interface `I`: `Conforms I self σ₀.addr_b ext` — refinement of powdr
  `ExternalCalls` through `α_b`, including non-interference with our storage/transient and no
  cross-binding effect (`INTERFACE_MODEL.md`). Non-interference is **assumed**, justified
  informally by the `tload`/`tstore` lock (reentrant entry hits the dispatcher and reverts; views
  revert while locked). A bytecode-level proof from the lock is deferred.
- `RelyEnv`: between two of our calls, `I.Rely self (α_b st) (α_b st')`.
- Fault oracle: `toYul_correct` existentially chooses `faults ncalls := ¬resp.success` so Core
  and Yul agree on each external outcome; security theorems remain `∀ w` and the glue instantiates
  them at that oracle. A failing `call` reverts both sides with empty data and needs no `Conforms`
  success clause.
- Fork = Osaka.
- Adversary model scope (`SECURITY_MODEL.md`): any call sequence from any addresses, `env` steps
  under `RelyEnv`, `sender ≠ self`; excludes private-key compromise, block-producer ordering/MEV,
  gas griefing of our execution, and token behaviours excluded by `Conforms`/`Rely`.
- **Top-level revert rollback** (`EvmCallRun` / `EvmTraceRun`): if the compiled call halts
  `.Reverted`, post-storage is the pre-storage. Raw powdr `Run`/`Steps` do **not** roll back;
  Yul `RunCommitted`/`committedState` does. The EVM trace model restores storage on revert to
  match `Tx`'s `Except.error`. This is a modelling assumption, not a lemma about `Steps`.
- Each `mkEvmState` used in transport starts from empty logs (`R` tracks `.self` only across
  a trace). Token `.self` is proved independent of the log.
- Forward direction only: a Security/Core trace is realized by some `EvmTraceRun`. The converse
  (every halted `Steps` sequence is predicted) is open; `StepDeterminism` is per-`Step`.

## Untrusted (checked or irrelevant to soundness)

- The reifier (`Lsc/Lang/Reify.lean`): every run emits a kernel-checked `rfl` certificate.
- `toYul` codegen: covered by `toYul_correct`.
- powdr's compiler and optimisers: covered by `compile_correct` (runtime) /
  `compileObject_correct` (deploy).
- The differential harness (revm/anvil): defence in depth only.

## Removed from the TCB by the September 2026 review

Home-grown EVM machine (~1.4k lines), home-grown codegen/encoder (~1.3k lines), EvmYulLean and
its C FFI (keccak, sha256), the two v2 axioms in `Lsc/Compile/Bytecode/EvmYulTrust.lean`.
