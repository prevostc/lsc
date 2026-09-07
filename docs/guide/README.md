# Lsc guide

For people who write or audit contracts in Lsc. The sources of truth for
syntax are `Examples/Counter/Contract.lean`, `Examples/Token/Contract.lean`,
`Examples/Vault/Contract.lean`, and `Examples/Amm/Contract.lean`.

- [Writing a contract](CONTRACTS.md) — `lsc_schema`, `lsc_reify`, `lsc_contract`
- [Security model](SECURITY.md) — unauthorised extraction, solvency, the adversary
- [External calls](EXTERNAL_CALLS.md) — `IERC20` bindings and what is assumed
- [What is trusted](TRUST.md) — foundations and hypotheses, in words
- [AMM walkthrough](AMM.md) — a constant-product pool with two tokens

Every guarantee's `*Theorems.lean` file — and each `Examples/<Name>/Theorems.lean` —
is readable top to bottom because each theorem is explained in prose first.

Language developers: [`docs/internals/`](../internals/). Product intent:
[`docs/PROJECT_GOAL.md`](../PROJECT_GOAL.md).
