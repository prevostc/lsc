# Module Map

Every module exposes an API (definitions, theorem statements, assumptions) and keeps proofs in
`*Proof.lean` files. Tasks should read APIs, not proofs.

## `Lsc/Lang` — the language

- `Tx.lean` — `Tx`, `World`, `Ctx`, `Err`, primitives, the `run_*` simp normal form. This file is
  the language specification.
- `Amount.lean` — `Amount τ s` (structure), `Flag`, `Price`, rounding-explicit ops, `toNat` simp
  normal form, ℚ cast pack.
- `Core.lean` — `Core`, `Core.denote`, `Core.effects`, `effects_frame`.
- `Reify.lean` — `lsc_schema`, `lsc_reify`, `lsc_contract` (MetaM, untrusted). Exports
  `f.core`, `f.core_denote`, `C.contract`, generated obligation statements.
- `Contract.lean` — `ContractDef`, `FnDef`, ABI signatures, keccak selectors.

## `Lsc/Security` — the security model

- `Trace.lean` — `Call`, `step`, `run`, adversary sets, revert-frame lemmas.
- `Invariant.lean` — `Inv` obligations and trace induction.
- `Wealth.lean` — `claim`, `Auth`, `holdings`, `no_unauthorized_extraction`, `solvency`.
- `Interface.lean` — `Interface`, `Ext`, `Tx.call`, `Conforms`, `Implements`.

Depends only on `Lsc/Lang`.

## `Lsc/Stdlib` — verified components

`ERC20.lean`, `Vault.lean`, `AMM.lean`, `Math.lean`, `AccessControl.lean`: each ships a component
and its proved invariants/laws.

## `Lsc/Compiler` — Core → Yul

- `Layout.lean` — storage slots, keccak mapping slots, ABI encoding, the relation `R`.
- `ToYul.lean` — `toYul : ContractDef → Yul object` (powdr yul-semantics AST).
- `ToYulCorrect.lean` — `toYul_correct`.
- `EndToEnd.lean` — generic glue from a `Security` theorem to a bytecode-level theorem via
  `core_denote`, `toYul_correct`, powdr `compileObject_correct`.

Depends on `Lsc/Lang/Core` and powdr; never on `Lsc/Security`.

## `Lsc/Tools`

Deploy hex, ABI JSON, revm/anvil differential harness.

## `Lsc/Examples`

`Token`, `Vault`, `AMM`: contract source, proofs, end-to-end instance.

## Deleted in S0

`Lsc/` v2 (23k lines), `examples/` (v2), `Lsc3/Compile/*`, `Lsc3/EVM/*`, Counter certificates and
`*EndToEnd.lean` `#eval` harnesses, `evmyul` dependency, v2 CI scripts.
