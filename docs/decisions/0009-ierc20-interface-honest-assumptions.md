# 0009: `IERC20` interface + `HonestERC20` assumptions for cross-contract proofs

## Context

The escrow example calls `Token.transfer` via black-box `exec` ([`0003`](0003-exec-read-black-box.md)).
Tier-2 theorems (`release_debits_escrow`, etc.) fully characterize behavior against the concrete
LSC `Token` — not against every on-chain ERC20. Deployers need a clear trust boundary: Escrow-local
safety (auth, atomicity, reentrancy guard) vs token-balance effects (conservation), which require
explicit assumptions about the callee.

See also [`docs/todo/interfaces.md`](../todo/interfaces.md) for the broader opt-in interface sketch.

## Decision

Introduce two layers:

1. **Interface-typed storage + Solidity-style calls** — declare `token : IERC20` on storage; call
   `exec σ.token.transfer(recipient, amount);` (Lean lexes this as one dotted ident). Callee address
   comes from the `"token"` slot. For spec-faithful ERC20 `transfer` (returns `bool`, no auto-revert),
   use `let ok = exec token.transfer(..); require (ok) else revert ..` (`IR.externalCallBind`) or the
   inlined `SafeERC20.safeTransfer(..)` library (`derive_library`). Legacy `checkBoolReturn` on
   `IR.externalCall` remains for older paths. Black-box `exec Token.transfer(..)` remains for
   co-developed LSC callees. `ContractDef.interfaces` is populated from storage field types.

2. **`HonestERC20` typeclass** (`Lsc/Lib/Interfaces/IERC20.lean`) — bundles the conservation laws
   Escrow proofs need for a standard/honest token:
   - on successful `transfer(sender → recipient, amount)`: sender −amount, recipient +amount,
     all other balances unchanged (including self-transfer canceling);
   - failure is revert or `false` (codegen path; not re-proved per token);
   - no callback/reentrancy via token (structural for LSC callees; explicit assumption for
     arbitrary Solidity — documented, not enforced mechanically today).

**Trust model:** an `HonestERC20` instance is an assumption the contract author vouches for about
a callee whose source they do not control. When the callee is another LSC contract in the same repo
(e.g. `Token`), the instance is proved from characterization lemmas (`runTransferOk`), not assumed.

Escrow theorems split into:

| Tier | Depends on | Examples |
|------|------------|----------|
| A (Escrow-local) | framework only | `release_rejects_non_owner`, `release_atomic_on_transfer_failure` |
| B (token effects) | `[HonestERC20 T]` | balance debit/credit/preservation corollaries |

The LSC reference `Token` remains: reference callee, codegen smoke test, and **witness** that
`HonestERC20` is satisfiable — not a universal quantifier over all ERC20s.

## Rejected alternatives

**Prove against literal ERC20 ABI only (no HonestERC20).** Black-box `exec` cannot derive balance
conservation; only success/failure is observable.

**Replace Token with an opaque axiom.** Loses compositional proofs, codegen tests, and the
reference-instance pattern that makes assumptions checkable in-repo.

**Full `HonestWorld` / N-contract registry now.** Escrow needs one external token; defer general
dispatch to [`docs/todo/interfaces.md`](../todo/interfaces.md).

## Consequences

- [`Lsc/Lib/Interfaces/IERC20.lean`](../../Lsc/Lib/Interfaces/IERC20.lean) defines `IERC20Spec` /
  `HonestERC20` and compositional `PairM` lemmas.
- [`examples/escrow/test/EscrowProofs.lean`](../../examples/escrow/test/EscrowProofs.lean) uses
  `[HonestERC20 T]` for generic release characterization; Token instance in
  [`examples/escrow/test/TokenHonest.lean`](../../examples/escrow/test/TokenHonest.lean).
- `EscrowStorage` uses `token : IERC20` (codegen: one `Address` word in the `"token"` slot).
- **Multi-interface (v1):** one interface type per field; secondary interfaces on the same address
  (e.g. `IERC2612`) deferred to call-site cast syntax — see [`docs/todo/interfaces.md`](../todo/interfaces.md).
- Fee-on-transfer, rebasing, and hook tokens are **out of scope** for `HonestERC20`; document
  explicitly in [`docs/reference/TOKEN.md`](../reference/TOKEN.md).
