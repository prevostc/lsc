# Module Map

Every module exposes an API (definitions, theorem statements, assumptions) and keeps proofs in
`*Proof.lean` files. Tasks should read APIs, not proofs.

## `Lsc/Lang` — the language

- `Tx.lean` — `Tx S X E ε`, `World S X E` (`self`, `ext : X`, `log`, `faults`, `ncalls`), `Ctx`,
  `Err` (including `callFailed`), primitives, the `run_*` simp normal form. This file is the
  language specification.
- `Interface.lean` — `Interface`, `Binding`, `Tx.call` / `Tx.callUnit`, `run_call`. Bindings are
  explicit constants (no `bind` macro yet).
- `Amount.lean` — `Amount τ s` (structure), `Flag`, `Price`, rounding-explicit ops, `toNat` simp
  normal form, ℚ cast pack. External scales are opaque symbols; `rescale` / `Amount.one` take
  runtime scale words. No IERC20 shim.
- `Core.lean` — `Core` (`Op.call`, `Stmt.call`), `Core.denote` (Nat, compiler), `Core.denoteAWord`
  / `Core.denoteAUnit` (Amount surface certificates), `Core.effects` (including `calls`).
  `ContractSchema.ext` supplies `call : Nat → Nat → List Nat → Tx`.
- `CoreProof.lean` — `effects_frame` (stated; proof is a remaining structural induction).
- `Spec.lean` — `Entry`, `Spec` (a contract as a finite family of `Tx` entrypoints with their own
  argument/return types). Language-level so that `Reify` can generate it without depending on
  `Lsc/Security`.
- `Reify.lean` — `lsc_schema`, `lsc_reify`, `lsc_contract` (MetaM, untrusted). Exports
  `f.core`, `f.core_denote`, `C.contract`, `C.Fn`/`C.entry`/`C.spec` with `spec_exec_*` simp
  lemmas, and `#lsc_obligations C` listing the theorem statements to prove.
- `Contract.lean` — `ContractDef` (including `bindings : List BindingDef`), `FnDef`, ABI
  signatures, keccak selectors.

## `Lsc/Security` — the security model

- `Trace.lean` — `Call`, `Step` (`call`/`env`), `Wf` (`target = self` and `sender ≠ self`),
  `run`, adversary sets, revert-frame lemmas.
- `Invariant.lean` — `Inv : World S X E → Prop`, `RelyAlong`, `PreservesInv`/`PreservesInvEnv`,
  `inv_run`.
- `Wealth.lean` — `claim`, `Auth`, `holdings`, `no_unauthorized_extraction`, `solvency`.

Depends only on `Lsc/Lang`.

## `Lsc/Stdlib` — verified components

`ERC20.lean` (`Ghost`, `Method`, `model`, `Rely`, `IERC20`, `IERC20.Ref`, `Binding.*` aliases),
`Vault.lean`, `AMM.lean`, `Math.lean`, `AccessControl.lean`: each ships a component and its
proved invariants/laws.

## `Lsc/Compiler` — Core → Yul

- `Layout.lean` — storage slots, keccak mapping slots, ABI encoding, the relation `R`.
- `Yul.lean` — `toYulFn`, `runtimeBlock`, `deployObject` (powdr yul-semantics AST), `printYul`.
- `YulExec.lean`, `YulTests.lean` — executable harness on powdr's Yul interpreter and the
  differential tests against `Tx.run`.
- `Bytecode.lean` — `compileRuntime`/`compileDeploy` through powdr's verified compiler.
- `Correctness.lean` — `R` and the `toYul_correct` statement; proofs under `Proof/`.
- `Proof/{Words,Memory,Env,Layout,Ops,OpsMore,Emit,Core,Counter}.lean` — `M1Frag` simulation
  (`load`/`addChecked`/`subChecked`/`pure`, `store`/`emit`/`require`, `ite`/`opTail` word
  return, params); `counter_correct` for every Counter runtime function. General
  `toYulFn_correct` / `runtimeBlock_correct` remain `sorry` in `Correctness.lean`.
- `EndToEnd.lean` — glue: `bytecode_call_correct`, `EvmCallRun` (unique halted post-storage),
  `bytecode_trace_transport` / `bytecode_trace_all`. The only
  compiler module that imports `Security`.
- `Proof/Calldata.lean` — `decodeArgs_fnCalldata` / `selectedFn_fnCalldata`.
- `Proof/Lift.lean` — `RunCommitted` → `Run (evmWithExternal …)`.
- `Proof/EvmDet.lean` — `Halted`, `steps_halted_unique`.

Depends on `Lsc/Lang` (`Core`, `Interface`) and powdr; never on `Lsc/Security` except
`EndToEnd.lean`.

## `Lsc/Tools`

ABI JSON (`AbiJson.lean`). EVM differential harness: `scripts/difftest.sh` (Lean `Tx.run`
vs anvil/revm on `compileRuntime` / `compileDeploy` bytecode).

## `Lsc/Examples`

`Token`, `Vault`, `AMM`: contract source, proofs, end-to-end instance (`TokenEndToEnd.lean`).

## Deleted in S0

`Lsc/` v2 (23k lines), `examples/` (v2), `Lsc3/Compile/*`, `Lsc3/EVM/*`, Counter certificates and
`*EndToEnd.lean` `#eval` harnesses, `evmyul` dependency, v2 CI scripts.
