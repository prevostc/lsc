# Trusted Computing Base

What an end-to-end theorem of this project relies on beyond its own proof.

## What is proved

Spec → Core → Yul → EVM bytecode. Axiom footprint of the chain is `propext`,
`Classical.choice`, `Quot.sound`, pinned by `#guard_msgs` in `Checks.lean`.
Agents update `Checks.lean` when a pinned theorem is added or renamed; the
commit message records what moved.

Example security (pinned in `Checks.lean`):

- Token (S1, call-free): `token_no_unauthorized_extraction`, `token_solvent`,
  `erc20` (`Examples/Token/Theorems.lean`).
- Vault (S2, one `IERC20.Ref`): `vault_no_unauthorized_extraction`,
  `vault_solvent` (`Examples/Vault/Theorems.lean`).
- Cpamm (S2, two `IERC20.Ref`): `cpamm_no_unauthorized_extraction`,
  `cpamm_solvent`, `swap0for1_k` (`Examples/Cpamm/Theorems.lean`).
- WETH (payable wrap/unwrap): `weth_exact`, `weth_backed`, `deposit_delta`,
  `withdraw_delta` (`Examples/WETH/Theorems.lean`).

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
`compileBlock rt = some is` (erase path or powdr spill). CREATE installs
exactly those `compileRuntime` bytes (`deploy_installs_runtime`), so
every runtime theorem covers the deployed code.

**(c) Well-formedness.** `WorldWF`, `CtxWF`, ABI args and addresses used as keys
`< 2^256`, `KeccakSep`, field/param length bounds.

**(d) External calls (S2 only).** The CALL oracle is an `ExtOracle`
(`CallRequest → ExtView → CallResponse`): memory-free by construction.
Other contracts cannot see this contract's private memory or `msize`,
which is true of the EVM. Wrapping with `toCalls` yields `ExternalCalls`
that is scratch-insensitive on every reservation interval (needed by
powdr's spill theorem) and total (`toCalls_total`). The oracle is a
function of the request and the observable world. The oracle model
restores `self`'s storage, transient storage, and self-attributed logs
after every external CALL. This is justified because (i) in the EVM
only a frame executing at address `self` can write `self`'s storage or
emit `self`'s logs (no EXTSLOAD/EXTSSTORE; CALLCODE/DELEGATECALL by
others run at *their* address) — an EVM fact not mechanized here — and
(ii) such a frame is a CALL/STATICCALL into our runtime, which reverts in
the 11-step lock prefix with the parent snapshot restored
(`nested_lock_reverts`, mechanized in 8C-1 against evm-semantics). ETH
balances are not restored: a callee can credit `self` via `SELFDESTRUCT`
without running our code, and `balanceOf` of other accounts is a real
CALL effect. Example theorems that mention the token take `IERC20.Spec`.
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
- **Native-balance bound.** Well-formed traces target `self`, are not self-calls, and
  never overflow a 256-bit native balance — true on every chain since total native
  supply < `2^256`. `creditValue` still wraps (EVM `BitVec`); `Wf` is what rules
  wrapping out of attack traces.

## Not covered

- Deploy / constructor: Yul `constructor_correct` (Solidity CREATE suffix args in
  `env.code`). `compileObject_correct` / `bytecode_deploy_correct` start from
  `L.initState` (`env.code = L.code`, empty calldata) with `FrameOK` requiring
  that exact code — appended ABI args are **not** in the EVM theorem.
  Runtime theorems exclude constructors (`hctor`). Vault/Cpamm constructors
  with `call` are out of scope.

- Reentrancy: lock emitted (`runtimeBlock` / `lockCheckStmt`; `locks f`
  acquire/release when `¬f.reentrant`). Held lock ⇒ revert, empty
  returndata, committed storage/transient/logs unchanged
  (`lock_held_reverts_yul` / `lock_held_reverts_yul_open` /
  `lock_held_reverts_evm`; no oracle). Nested CALL/STATICCALL into the
  compiled runtime with the lock held reverts in the prefix and restores
  the parent snapshot (`nested_lock_reverts`, `nested_lock_restores_self`).
  S2/transport theorems do not take `hNR`; isolation of `self`'s
  storage/transient/self-logs is the `toCall` restore
  (`ExtOracle.noReentry`). ETH balances are not covered (`SELFDESTRUCT`
  to `self`, foreign `balanceOf`). `[Reentrant]` skips acquire/release
  (prologue still checks); store-after-call is rejected unless
  `[Reentrant.Unsafe]`. CALLCODE/DELEGATECALL are not emitted. The EVM fact
  that only a `self` frame can write `self` storage/logs is not
  mechanized (TCB §(d)).
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
