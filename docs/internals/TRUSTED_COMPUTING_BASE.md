# Trusted Computing Base

What an end-to-end theorem of this project relies on beyond its own proof.

## What is proved

Spec → Core → Yul → EVM bytecode. Axiom footprint of the chain is `propext`,
`Classical.choice`, `Quot.sound`, pinned by `#guard_msgs` in `Checks.lean`.

- Token (S1, call-free): `token_bytecode_no_unauthorized_extraction` /
  `token_bytecode_solvent` (`Examples/Token/EndToEndTheorems.lean`).
- Vault (S2, one external binding): `vault_bytecode_no_unauthorized_extraction` /
  `vault_bytecode_solvent` (`Examples/Vault/EndToEndTheorems.lean`).
- AMM (S2, two `IERC20` bindings): `amm_bytecode_no_unauthorized_extraction`
  (`Examples/Amm/EndToEndTheorems.lean`).
- Glue: `bytecode_call_correct` (`EndToEndTheorems.lean`), `bytecode_call_correct_ext`
  (`EndToEndExtTheorems.lean`). AMM bytecode: `amm_bytecode_no_unauthorized_extraction`.
  Counter is compiler-level only.

## Trusted foundations

- Lean 4 kernel and the standard axioms above. No `native_decide`, `bv_decide`,
  `sorry`, or project axioms in the chain.
- Language spec: `Tx`, `Tx.call`, `Core.denote`, `Interface`
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

**(b) Compiler acceptance.** `runtimeBlock c = some rt` and `compile rt = some is`.

**(c) Well-formedness.** `WorldWF`, `CtxWF`, ABI args and addresses used as keys
`< 2^256`, `KeccakSep`, field/param length bounds.

**(d) External calls (S2 only).** `α : Abs I.Ghost` maps an EVM snapshot at a bound
address to `I.Ghost` (foreign layout is not proved in general). `Conforms`: every
**successful** call from `self` to `addr` decodes to a method of `I`, matches
`I.model`, passes `decodeRet`, and `NoInterfere`. Failed responses unconstrained.
`NoInterfere`: our storage and transient unchanged, ETH balances unchanged
(`value = 0`), other addresses' `α` unchanged, callee logs not attributed to
`self`. Reentrancy is excluded by this hypothesis; no `tload`/`tstore` lock is
emitted. `CallsRealized` (powdr inhabitation) and `CallsTotal` (EVM CALL always
returns). `ignoresLocal` is foreign-address only. Foreign state `ξ` (`storageOf`)
is threaded through S2 traces; post-call `ξ'` is read from the halted EVM state.
A family `bs : List (BindEnv I S X)` carries per-package `RX`/`Conforms`/`neSelf`
(conjunction `RXs`, `BindEnvs.conforms`, `BindEnvs.neSelf`). Extra family
hypotheses: `sameAbs` (shared `α`, so `NoInterfere` frames other callees),
`orthogonal` (distinct addresses have independent ghosts), `addrInj` (colliding
addresses imply the same `α` and `get`; AMM needs `token0 ≠ token1` at `w.self`),
`lookupWF` (each well-formed `Op.call` indexes some package), `avoids` (runtime
does not store binding address slots). S1 uses a closed model (`calls := .none`,
`ExternalsRealized.none`) instead.

**(e) Fault oracle.** Backward S2 existentially chooses a fault oracle `fo` so
Core and Yul agree on each external outcome. Security theorems remain `∀ w`.
A failing `call` reverts both sides with empty data.

**(f) Adversary scope** (`SECURITY_MODEL.md`): any call sequence from any
addresses, `env` steps under `RelyAlong`, `sender ≠ self`. Excludes private-key
compromise, block-producer ordering/MEV, gas griefing of our execution, and
token behaviours excluded by `Conforms`/`Rely`.

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
  arbitrary calldata list** (`Lsc/Compiler/Transport.lean`): each call either fails
  the dispatcher (an EVM no-op, dropped from the trace) or decodes to the Security
  step `decodeTrace` assigns to it. `Wf` (`sender ≠ self`, `CtxWF`) and `NoAuthAlong`
  are hypotheses on the decoded calls (`CallsWF`), and the initial world has empty
  logs. An `EvmStartOK` witness keeps uniqueness non-vacuous; `*_exists` companions
  use the ABI-encoded Security trace. powdr `compile_correct` is forward (`Yul Run → ∃ EVM
  Steps`). Progress (`CallsTotal` + `yul_progress`) supplies a Yul run and
  `steps_halted_unique` identifies every halted matching EVM run with it, so powdr
  adequacy (every EVM execution is a Yul run) is not needed.

## Not covered

- Deploy / constructor: Yul `constructor_correct` (Solidity CREATE suffix args in
  `env.code`). `compileObject_correct` / `bytecode_deploy_correct` start from
  `L.initState` (`env.code = L.code`, empty calldata) with `FrameOK` requiring
  that exact code — appended ABI args are **not** in the EVM theorem.
  `FrameOK` fork = Osaka; CREATE-shaped empty call stack. Nested `"runtime"`
  subobject offsets are compiler artifacts (`Layout.Consistent` is data segments
  only). Runtime theorems exclude constructors (`hctor`). Vault/AMM constructors
  with `call` are out of scope.

- Bytecode-level reentrancy lock (not emitted).
- Core outside `S2Frag` (e.g. wrapping `letPure` other than `id`, nested pair
  returns, `require`/`revert`/`emit` arities other than 0/1/3/4).
- Amount-typed compiler in general: bytecode glue is `Core.denote` (Nat). Vault
  Amount ABI is identified via `deposit.core_denote` / `withdraw.core_denote`.

## Non-vacuity

- `vaultAbsSolidity`: a concrete `Abs` reading Solidity ERC20 layout
  (`balances[o]` at `mapSlot1 evmKeccak 0 o`, `decimals` at slot 1). Shared by
  Vault and both AMM token bindings (per-address via `evmForeign`).
- `*_exists` companions keep a predicted `EvmTraceRun` / `EvmTraceRunExt`.
- Differential harness (`scripts/difftest.sh`) is defence in depth, not a proof.

## Untrusted (checked)

Reifier certificates (`Lsc/Lang/Reify.lean`, kernel-checked `rfl`), `toYul`
(`toYulFn_correct_callFree` / `toYulFn_correct_ext`), the forked Yul→EVM compiler
(`compile_correct`; `compileObject_correct` / `bytecode_deploy_correct` for
init code without appended args; Yul `constructor_correct` for the CREATE
suffix convention), and the

harness. A former home-grown EVM/codegen/FFI stack was removed from this TCB.
