# Lsc guide

For people who write or audit contracts in Lsc. The sources of truth for
syntax are `Examples/Counter/Contract.lean`, `Examples/Token/Contract.lean`,
`Examples/Vault/Contract.lean`, and `Examples/Cpamm/Contract.lean`.

- [Writing a contract](CONTRACTS.md) — `lsc_schema`, `lsc_contract`, `Amount`
- [Security model](SECURITY.md) — unauthorised extraction, solvency, the adversary
- [External calls](EXTERNAL_CALLS.md) — `IERC20.Ref` / `I.Impl` / `I.Spec`
- [What is trusted](TRUST.md) — foundations and hypotheses, in words
- [Audit coverage](AUDIT_COVERAGE.md) — SWC/OWASP cut: proved, assumed, open
- [Cpamm walkthrough](AMM.md) — constant-product AMM with LP fee and protocol-fee switch

Compile with `Lsc.Compiler.compileContract` (`Lsc/Compiler/Pipeline.lean`) →
`Artifacts {runtimeHex, deployHex, abi, yul, …}`;
`scripts/export_bytecode.lean` writes `Examples/*/compiled/`.

Every guarantee's `*Theorems.lean` file — and each `Examples/<Name>/Theorems.lean` —
is readable top to bottom because each theorem is explained in prose first.

Language developers: [`docs/internals/`](../internals/). Product intent:
[`docs/PROJECT_GOAL.md`](../PROJECT_GOAL.md).
