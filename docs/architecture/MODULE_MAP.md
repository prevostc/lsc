# Module Map

Every module exposes an API (definitions, theorem statements, assumptions) and keeps proofs in
`*Proof.lean` files. Tasks should read APIs, not proofs.

## `Lsc/Lang` — the language

- `Tx.lean` — `Tx S X E ε`, `World S X E` (`self`, `ext : X`, `log`, `faults`, `ncalls`), `Ctx`,
  `Err` (including `callFailed`), primitives, the `run_*` simp normal form. This file is the
  language specification.
- `Interface.lean` — `Interface`, `Binding`, `Tx.call` / `Tx.callUnit`, `run_call`, `bind` macro.
- `Amount.lean` — `Amount τ s` (structure), `Flag`, `Price`, rounding-explicit ops, `toNat` simp
  normal form, ℚ cast pack. External scales are opaque symbols; `rescale` / `Amount.one` take
  runtime scale words. No IERC20 shim.
- `Core.lean` — `Core` (`Op.call`, `Stmt.call`), `Core.denote`, `Core.effects` (including
  `calls`), `effects_frame`. `ContractSchema.ext` supplies `call : Nat → Nat → List Nat → Tx`.
- `Spec.lean` — `Entry`, `Spec` (a contract as a finite family of `Tx` entrypoints with their own
  argument/return types). Language-level so that `Reify` can generate it without depending on
  `Lsc/Security`.
- `Reify.lean` — `lsc_schema`, `lsc_reify`, `lsc_contract` (MetaM, untrusted). Exports
  `f.core`, `f.core_denote`, `C.contract`, `C.Fn`/`C.entry`/`C.spec` with `spec_exec_*` simp
  lemmas, and `#lsc_obligations C` listing the theorem statements to prove.
- `Contract.lean` — `ContractDef`, `FnDef`, ABI signatures, keccak selectors.

## `Lsc/Security` — the security model

- `Trace.lean` — `Call`, `call`/`env` steps, `RelyAlong`, `Call.sender ≠ target`, `run`,
  adversary sets, revert-frame lemmas.
- `Invariant.lean` — `Inv : World S X E → Prop`, obligations (including preservation by `Rely`)
  and trace induction.
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
- `EndToEnd.lean` — generic glue from a `Security` theorem to a bytecode-level theorem via
  `core_denote`, `toYul_correct`, powdr `compileObject_correct`. States `Conforms` against powdr.

Depends on `Lsc/Lang` (`Core`, `Interface`) and powdr; never on `Lsc/Security`.

## `Lsc/Tools`

Deploy hex, ABI JSON, revm/anvil differential harness.

## `Lsc/Examples`

`Token`, `Vault`, `AMM`: contract source, proofs, end-to-end instance.

## Deleted in S0

`Lsc/` v2 (23k lines), `examples/` (v2), `Lsc3/Compile/*`, `Lsc3/EVM/*`, Counter certificates and
`*EndToEnd.lean` `#eval` harnesses, `evmyul` dependency, v2 CI scripts.
