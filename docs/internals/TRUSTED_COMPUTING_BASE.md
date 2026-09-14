# Trusted Computing Base

What an end-to-end theorem of this project relies on beyond its own proof.

## What is proved

Spec → Core → Yul → EVM bytecode. Axiom footprint of the chain is `propext`,
`Classical.choice`, `Quot.sound`, pinned by `#guard_msgs` in `Checks.lean`.

Example security (pinned in `Checks.lean`):

- Token (S1, call-free): `token_no_unauthorized_extraction`, `token_solvent`,
  `erc20` (`Examples/Token/Theorems.lean`).
- Vault (S2, one `IERC20.Ref`): `vault_no_unauthorized_extraction`,
  `vault_solvent` (`Examples/Vault/Theorems.lean`).
- Cpamm (S2, two `IERC20.Ref`): `cpamm_no_unauthorized_extraction`,
  `cpamm_solvent`, `swap0for1_k` (`Examples/Cpamm/Theorems.lean`).

Compiler / glue (also pinned): `toYulFn_correct_callFree`,
`toYulFn_correct_ext`, `core_sim_ext_callFree`,
`runtimeBlock_correct_callFree`, `runtimeBlock_correct_ext`,
`bytecode_call_correct`, `bytecode_call_correct_ext`, `yul_progress`,
`evmCallRunExtAll_of_progress`, `constructor_correct`,
`bytecode_deploy_correct`.

A trace fact on a contract that CALLs out lifts to bytecode with
`transport_claim_ext` / `transport_exists_claim_ext`
(`Lsc/Compiler/TransportTheorems.lean`). Examples do not ship
`*_bytecode_*` theorems (DECISIONS 2026-09-12). Counter is compiler-level
only.

## Trusted foundations

- Lean 4 kernel and the standard axioms above. No `native_decide`, `bv_decide`,
  `sorry`, or project axioms in the chain.
- Language spec: `Tx`, `Oracle`, `Core.denote`, `Interface`
  (`Lsc/Lang/{Tx,Interface,Core}.lean`). Reviewed, not proved.
- powdr `evm-semantics` (relational, conformance-tested on GeneralStateTests and
  EEST Osaka) and powdr `yul-semantics` (adequacy proved by its authors). Pinned
  in `lake-manifest.json`.
- Yul→EVM compiler: fork `prevostc/yul-compiler` at `30230e1`, which differs from
  upstream powdr `330923e0` only by the classic `switch` lowering (jump-on-match,
  out-of-line bodies). Verified in the fork's own `Checks.lean` with the same
  axiom footprint. Pinned in `lake-manifest.json`.
- Layout relation `R` (`Lsc/Compiler/Correctness.lean`): how bytecode storage is
  read back as contract state.
- Keccak: powdr `targetKeccakOracle` (`evmKeccak`), injective on the storage keys
  used (`KeccakSep`); KeccakEngine agrees on compile-time selectors.
- Ethereum clients implement the specification.

## Hypotheses of the end-to-end theorems

**(a) EVM frame.** `FrameOK` on the assembled bytecode (fork = Osaka, not a
precompile, empty call stack). Gas is existential (`∃ b` from `compile_correct`).
`EvmStartOK` is `FrameOK`, `StateMatch`, `pc = 0`, empty stack.

**(b) Compiler acceptance.** `runtimeBlock c = some rt` and
`compileBlock rt = some is` (erase path or powdr spill).

**(c) Well-formedness.** `WorldWF`, `CtxWF`, ABI args and addresses used as keys
`< 2^256`, `KeccakSep`, field/param length bounds.

**(d) External calls (S2 only).** The CALL oracle is an `ExtOracle`
(`CallRequest → ExtView → CallResponse`): memory-free by construction.
Other contracts cannot see this contract's private memory or `msize`,
which is true of the EVM. Wrapping with `toCalls` yields `ExternalCalls`
that is scratch-insensitive on every reservation interval (needed by
powdr's spill theorem) and total (`toCalls_total`). The oracle is a
function of the request and the observable world. `NoReentry` (`hNR`) is
still the only callee hypothesis of the S2/transport theorems (slice 8C
drops it). Example theorems that mention the token take `IERC20.Spec`.
S1 uses a closed model instead.

**(e) Adversary scope** (`SECURITY_MODEL.md`): any call sequence from any
addresses, `env` steps under `RelyAlong`, `sender ≠ self`. Ordering of
*our* entrypoints (including sandwich of those calls) is the trace
quantifier. Excludes private-key compromise, block-producer ordering
across other contracts, gas griefing of our execution, and token
behaviours excluded by `IERC20.Spec`.

## Modelling assumptions

Not derived from powdr:

- **Top-level revert rollback.** If a compiled call halts `.Reverted`,
  post-storage is the pre-storage. Raw powdr `Run`/`Steps` do not roll back; Yul
  `RunCommitted` does. The EVM trace model restores storage on revert to match
  `Tx`'s `Except.error`.
- **Fresh per-call `EvmState`.** Each `mkEvmState` / `mkEvmStateExt` starts from
  `EvmState.init` with empty logs (`R` tracks `.self` only across a trace).
- **Universality.** `EvmCallRun` / `EvmTraceRunAll` (S1) and `EvmCallRunExtAll` /
  `EvmTraceRunExtAll` (S2) quantify over **every halted matching EVM run of an
  arbitrary calldata list**. Unknown selectors are no-ops. `Wf` and
  `NoAuthAlong` are hypotheses on the decoded calls. powdr `compile_correct` is
  forward (`Yul Run → ∃ EVM Steps`). Progress (`toCalls_total` + `yul_progress`)
  supplies a Yul run and `steps_halted_unique` identifies every halted matching
  EVM run with it.

## Not covered

- Deploy / constructor: Yul `constructor_correct` (Solidity CREATE suffix args in
  `env.code`). `compileObject_correct` / `bytecode_deploy_correct` start from
  `L.initState` (`env.code = L.code`, empty calldata) with `FrameOK` requiring
  that exact code — appended ABI args are **not** in the EVM theorem.
  Runtime theorems exclude constructors (`hctor`). Vault/Cpamm constructors
  with `call` are out of scope.

- Reentrancy: lock emitted (`runtimeBlock` / `lockCheckStmt`; `locks f`
  acquire/release). Held lock ⇒ revert, empty returndata, committed
  storage/transient/logs unchanged (`lock_held_reverts_yul` /
  `lock_held_reverts_yul_open` / `lock_held_reverts_evm`; no oracle).
  `hNR : ExtOracle.NoReentry` remains on S2/transport until 8C
  (nested-frame `compile_correct`, code-at-self pin, isolation lemma).
- Core outside `S2Frag` (e.g. wrapping `letPure` other than `id`, nested pair
  returns, `require`/`revert`/`emit` arities other than 0/1/3/4).
- Amount-typed compiler in general: bytecode glue is `Core.denote` (Nat).

## Non-vacuity

- `*_exists` companions keep a predicted `EvmTraceRun` / `EvmTraceRunExt`.
- Differential harness (`scripts/difftest.sh`) is defence in depth, not a proof.

## Untrusted (checked)

Reifier certificates (`Lsc/Lang/Reify.lean`, kernel-checked `rfl` or `Tx` monad
laws), `toYul`
(`toYulFn_correct_callFree` / `toYulFn_correct_ext`), the forked Yul→EVM compiler
(`compile_correct`; `compileObject_correct` / `bytecode_deploy_correct` for
init code without appended args; Yul `constructor_correct` for the CREATE
suffix convention).
