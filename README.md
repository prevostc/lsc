# Lsc

Lsc is a DeFi smart-contract language hosted in Lean 4 and compiled to EVM
bytecode. You write ordinary Lean functions; the compiler emits bytecode. The
product goal is a checked anti-exploit claim under explicit assumptions, not
exhaustive functional correctness. See `docs/PROJECT_GOAL.md`.

## What you get

Under the assumptions in `docs/guide/TRUST.md` and `docs/guide/EXTERNAL_CALLS.md`,
compiled **runtime** bytecode cannot reduce an account's protocol claim unless
that account authorised the call, and the contract stays solvent relative to
the assets it controls. Token and Vault have both facts at bytecode. AMM has
unauthorised-extraction at bytecode and solvency at the spec. Counter is a
compiler demo. Constructors that call out, and CREATE with appended constructor
arguments, are outside the EVM deploy theorem.

## Writing a contract

A contract is a storage structure, events, errors, and `do` blocks using
`read` / `write`, checked arithmetic (`+?`, `-?`, …), and `Binding` calls to a
declared `IERC20` when the contract talks to an external token. `lsc_schema`,
`lsc_reify`, and `lsc_contract` assemble the schema and the contract object.
Start from `Examples/Counter/Contract.lean`, then Token, Vault, Amm.

## Build

One Lean process at a time, always through the lock:

```text
scripts/lean lake build Checks
```

## Docs

- Language users (write, audit, assumptions): [`docs/guide/`](docs/guide/)
- Language developers (proof chain, modules, TCB): [`docs/internals/`](docs/internals/)
