# Token

Closed ERC-20: `transfer`, `approve`, `transferFrom`, `mint`, `burn`, and the
views `totalSupply`, `balanceOf`, `allowance`. No external calls. Storage: owner,
total supply, balances, and nested allowances.

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
authorised the call. Recorded balances still sum to total supply after any
well-formed trace.

| File | Role |
|------|------|
| `Contract.lean` | Token surface + `implements IERC20` |
| `Spec.lean` | `claim`, `Auth`, `Inv` |
| `Theorems.lean` | Exported Tx, IERC20, and security theorems |
| `Tests.lean` | Smoke `#guard`s |
| `Proofs/Tx.lean` | `Tx.run` lemmas and deltas |
| `Proofs/Implements.lean` | `IERC20.Spec Token.impl` (`Token.erc20`) |
| `Proofs/Security.lean` | Auth/conservation/invariant instances |
| `Proofs/Compile.lean` | Runtime `compileRuntime` witness |
| `compiled/` | Yul, labelled Asm, bytecode, ABI, heimdall decompile |
