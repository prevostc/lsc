# Lsc

Lsc is a DeFi smart-contract language hosted in Lean 4 and compiled to EVM
bytecode. You write ordinary Lean functions; the compiler emits bytecode. The
product goal is a checked anti-exploit claim under explicit assumptions, not
exhaustive functional correctness. See `docs/PROJECT_GOAL.md`.

## What you get

Under the assumptions in `docs/guide/TRUST.md` and `docs/guide/EXTERNAL_CALLS.md`,
a well-formed trace cannot reduce an account's protocol claim unless that account
authorised the call, and the contract stays solvent relative to the assets it
controls. Token, Vault, and Cpamm prove those facts at `Tx.run` / trace level
(`token_no_unauthorized_extraction`, `vault_no_unauthorized_extraction`,
`cpamm_no_unauthorized_extraction`, and the matching solvency theorems, pinned
in `Checks.lean`). The compiler lifts a trace fact onto bytecode with
`transport_claim_ext` / `transport_exists_claim_ext`
(`Lsc/Compiler/TransportTheorems.lean`); examples do not ship per-contract
`*_bytecode_*` theorems. Counter is a compiler demo. Constructors that call out,
and CREATE with appended constructor arguments, are outside the EVM deploy
theorem.

## Writing a contract

A contract is a storage structure, events, errors, and `do` blocks using
`read` / `write`, checked arithmetic, named scales (`Wad`/`Ray`/`Bps`), and
typed `I.Ref` calls when the contract talks to an external token (`let tok ←
read asset; tok.balanceOf me`, `safeTransferFrom`).

| Surface | Meaning |
|---|---|
| `x +? y`, `x -? y` | same-asset add/sub |
| `x *? k`, `x /? k` | scale by a `Word` |
| `x mulDiv↓ y / z`, `x mulDiv↑ y / z` | fused `⌊x·y/z⌋` / `⌈x·y/z⌉`; `y`/`z` may be two `Amount`s or two `Word`s |
| `x *?↓ r`, `x *?↑ r` | scale `x : Amount a` by `r : Fixed d` (`⌊x·r/10^d⌋` / ceil) |
| `x.as b` | 1:1 retag to asset `b` (same raw word) |

`lsc_schema` and `lsc_contract` assemble the schema and the contract object.
`lsc_contract … implements IERC20 …` emits `C.impl`; Token proves
`theorem erc20 : IERC20.Spec Token.impl`, WETH proves
`theorem weth_exact : IERC20.Exact WETH.impl`. The native asset comes from
the `Chain` profile, so the same contract is a wrapped-native token on
any profile. Start from `Examples/Counter/Contract.lean`, then Token,
Vault, Cpamm, and WETH.

Compile with `Lsc.Compiler.compileContract` (`Lsc/Compiler/Pipeline.lean`): it
returns `Artifacts` (`runtimeHex`, `deployHex`, `abi`, `yul`, `asm`,
`deployYul`, `selectors`). `scripts/export_bytecode.lean` writes those into
`Examples/*/compiled/`.

## Build

One Lean process at a time, always through the lock:

```text
scripts/lean lake build Checks
```

## Layout

LscSemantics = what programs mean (Tx monad, World, Core and its denotation, security trace framework); Lsc = how they compile and why that is correct.

## Docs

- Language users (write, audit, assumptions): [`docs/guide/`](docs/guide/)
- Language developers (proof chain, modules, TCB): [`docs/internals/`](docs/internals/)
