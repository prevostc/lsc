# Opt-in interface calls / `HonestERC20` (Escrow v1)

**Status: partially implemented** — see [`decisions/0009`](../decisions/0009-ierc20-interface-honest-assumptions.md)
and [`reference/ESCROW.md`](../reference/ESCROW.md).

## Implemented today

| Piece | Location |
|-------|----------|
| `token : IERC20` storage fields | `Lsc/Lib/Interfaces/IERC20.lean`, `Lsc/Lang/Derive.lean` |
| `exec σ.token.transfer(..)` / `read σ.token.balanceOf(..)` | `Lsc/Lang/Syntax.lean` |
| `checkBoolReturn` for IERC20 `transfer` | `Lsc/Lang/Syntax.lean` → `IR.externalCall` |
| `ContractDef.interfaces` from storage field types | `Lsc/Deriving.contractInterfacesExt` |
| `HonestERC20` typeclass + compositional lemmas | `Lsc/Lib/Interfaces/IERC20.lean` |
| Reference instance | `examples/escrow/test/TokenHonest.lean` |
| Escrow proof tiers A/B | `examples/escrow/test/EscrowProofs.lean`, `EscrowTheorem.lean` |

Black-box `exec Token.fn(..)` (module call, no interface field) remains for co-developed LSC callees.

## Still backlog

* Call-site cast for secondary interfaces on the same address (e.g. `(σ.token : IERC2612).permit`)
* Rich `interface` declarations (events, callee errors, attached theorems) beyond `HonestERC20`
* N-contract dispatch registry / `HonestWorld`
* Mechanically checking `[HonestERC20]` for arbitrary Solidity tokens (operational: allowlist/audit)

## Trust model

An interface-typed storage field is an **assumption** the author vouches for. When the callee is
another LSC contract in-repo (`Token`), the assumption is proved (`TokenHonest`). For external
mainnet tokens, the author must separately argue the token is standard/honest ERC20 — LSC does not
verify Solidity bytecode today.

## Call syntax

```lean
structure EscrowStorage where
  token : IERC20 := default
  ...

exec σ.token.transfer(recipient, amount);   -- mutating; bool return check
read σ.token.balanceOf(owner);              -- read-only STATICCALL
exec Token.transfer(recipient, amount);     -- black-box LSC module call (reference tests)
```

Lean lexes `σ.token.transfer` as one dotted ident; elaboration splits it into receiver + method.

## Original sketch (broader vision)

The black-box model is the right *default* for composability. Interface-typed fields recover
conditional proofs ("if transfer succeeds, balances moved correctly") without forcing every caller
to know the callee's full error/event taxonomy.

Richer `interface` declarations (events, error shapes, extra theorems) remain future work — see
[`decisions/0009`](../decisions/0009-ierc20-interface-honest-assumptions.md).
