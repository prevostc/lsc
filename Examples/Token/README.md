# Token

Closed ERC-20: `transfer`, `approve`, `transferFrom`, `mint`, `burn`, and the
views `totalSupply`, `balanceOf`, `allowance`. No external CALLs. Storage: owner,
totalSupply, balances, and nested `allowances : Mapping Address (Mapping Address
(Amount tokenAsset))` — the language supports that `map2` shape directly.

`lsc_contract Token … implements IERC20 tokenAsset` checks names and signatures
against `IERC20` and emits `Token.impl`. `Token.erc20` proves every field of
`IERC20.Spec` of that implementation: transfers conserve the two balances and
never change supply; `transferFrom` spends allowance when the caller is not
the source; `approve` writes the allowance; nobody can drop your balance except
you or a spender you approved. Self-spend (`sender = src`) still requires and
decrements allowance — the spec hypothesises `sender ≠ src`, so that policy
is compatible.

**Proved:** a successful transfer or `transferFrom` conserves the two balances.
A successful `approve` sets the allowance. Nobody's balance falls unless they
authorised the call. Recorded balances still sum to `totalSupply` after any
well-formed trace. The compiled Yul of each runtime function matches the
high-level model. Per-contract bytecode theorems are not stated.

| File | Role |
|------|------|
| `Contract.lean` | Token surface + `implements IERC20` |
| `Spec.lean` | `claim`, `Auth`, `Inv`, codec |
| `Theorems.lean` | Exported Tx, IERC20, security, and compiler theorems |
| `Tests.lean` | Smoke `#guard`s |
| `Proofs/Tx.lean` | `Tx.run` lemmas and deltas |
| `Proofs/Implements.lean` | `IERC20.Spec Token.impl` (`Token.erc20`) |
| `Proofs/Security.lean` | Auth/conservation/invariant instances |
| `Proofs/Compile.lean` | Call-free compiler instance + runtime `#guard` |
| `Proofs/EndToEnd.lean` | No per-contract bytecode theorems |
| `compiled/` | Yul, labelled Asm, bytecode, ABI, heimdall decompile |
