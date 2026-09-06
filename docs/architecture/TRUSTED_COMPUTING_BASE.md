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
- `α : Abs I.Ghost` maps an EVM/`CallWorld` snapshot at a bound address to `I.Ghost`. Foreign
  token layout is not proved; `α` is a TCB parameter.
- `Conforms I self addr calls α`: every **successful** Yul/EVM call from `self` to `addr`
  decodes to some method of `I`, matches `I.model`, satisfies `decodeRet` (ABI-false / short
  `boolOpt` cannot be a success), and `NoInterfere`. Failed responses (`success = false`) are
  unconstrained.
- `NoInterfere`: our storage and transient are unchanged, ETH balances are unchanged
  (`value = 0`), other addresses' `α` are unchanged, and callee logs are not attributed to
  `self`. Reentrancy is excluded by this hypothesis, **not** by an emitted `tload`/`tstore`
  lock. A bytecode-level lock proof is not part of S2.
- `Realizes`: inhabitation only; used solely by a forward `_exists` companion, **not** by the
  backward `toYulFn_correct_ext`. Glue may set `faults n := ¬resp.success`.
- `ExternalsRealized { calls, creates := .none, gas := .none }` / `CallsRealized` stays TCB
  for later bytecode glue; M0 has no `compile_correct` over `yulD`.
- Fault oracle: backward `toYulFn_correct_ext` existentially chooses `fo` via
  `composeFault ncalls (¬resp.success) rest` so Core and Yul agree on each external outcome;
  security theorems remain `∀ w` and transport along the backward theorem. A failing `call`
  reverts both sides with empty data and needs no `Conforms` success clause. Core failure
  does not bump `ncalls`; a successful call's continuation sees indices `≥ ncalls + 1`.
- `RelyEnv`: between two of our calls, `I.Rely self (α_b st) (α_b st')`.
- Keccak: existing `KeccakSep`; `logsRel` ignores `address ≠ self`; top-level revert rollback
  unchanged; constructor `decimals` is deploy, not the runtime S2 theorem.
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
- `EvmCallRun` / `EvmTraceRunAll` quantify over matching start states (`FrameOK`,
  `StateMatch`, `pc = 0`, empty stack) with gas at least the existential bound from
  `compile_correct`. A matching `EvmStartOK` witness is part of `EvmTraceRunAll` so
  post-storage uniqueness is not vacuous; `*_exists` theorems keep the `∀ s0` shape of
  `compile_correct` (no constructed `State`). The converse (every EVM calldata sequence is
  a Security trace) remains open.

## Untrusted (checked or irrelevant to soundness)

- The reifier (`Lsc/Lang/Reify.lean`): every run emits a kernel-checked `rfl` certificate.
- `toYul` codegen: covered by `toYul_correct`.
- powdr's compiler and optimisers: covered by `compile_correct` (runtime) /
  `compileObject_correct` (deploy).
- The differential harness (revm/anvil): defence in depth only.

## Removed from the TCB by the September 2026 review

Home-grown EVM machine (~1.4k lines), home-grown codegen/encoder (~1.3k lines), EvmYulLean and
its C FFI (keccak, sha256), the two v2 axioms in `Lsc/Compile/Bytecode/EvmYulTrust.lean`.
