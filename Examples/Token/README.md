# Token

Closed ERC-20: `transfer`, `approve`, `transferFrom`, owner-gated `mint`,
`burn`, and the views. Storage `extends ERC20.Storage` plus `owner`. The
six IERC20 entrypoints are one-line re-exports of the ERC20 base;
constructor and owner-`mint` call `ERC20.mint`.

`lsc_contract Token … implements IERC20 Token.tokenAsset` checks names and signatures
against `IERC20` and emits `Token.impl`. `Token.erc20` proves every field of
`IERC20.Spec` of that implementation: transfers conserve the two balances and
never change supply; `transferFrom` spends allowance when the caller is not
the source; `approve` writes the allowance; nobody can drop your balance except
you or a spender you approved. Self-spend (`sender = src`) still requires and
decrements allowance — the spec hypothesises `sender ≠ src`, so that policy
is compatible.

**Proved:** a successful transfer or `transferFrom` conserves the two balances.
A successful `approve` sets the allowance. In any reachable `State`, any
finite set of accounts together holds at most `totalSupply`
(`token_solvent`). No sequence of calls by other parties lowers `a`'s
balance except by the amount `a` itself authorised
(`token_no_unauthorized_extraction`: `a`'s own `transfer`/`burn`, or a
`transferFrom` of `a`'s tokens). Only accepted calls count.

| File | Role |
|------|------|
| `Contract.lean` | Token surface + schema + `lsc_contract` (`implements IERC20`) |
| `Spec.lean` | `claim`, `Auth`, `Inv`, `spentCall` |
| `Theorems.lean` | Exported Tx, IERC20, and security theorems |
| `Tests.lean` | Smoke `#guard`s |
| `Proofs/Tx.lean` | `Tx.run` lemmas and deltas |
| `Proofs/Implements.lean` | `IERC20.Spec Token.impl` (`Token.erc20`) |
| `Proofs/Security.lean` | Auth/conservation/invariant instances |
| `Proofs/Compile.lean` | Runtime `compileRuntime` witness |
| `compiled/` | Yul, labelled Asm, bytecode, ABI, heimdall decompile |
