# Linear Types in LSC

Authoritative reference for the linear type system: motivation, enforcement, proof ergonomics, and the type library.

Read [DESIGN.md §7](../../DESIGN.md) and [IMPLEMENTATION.md](../../IMPLEMENTATION.md) first.

## Type library

Each type has its own file so it can be revised independently:

| Type | File | Status |
|------|------|--------|
| `TokenAmount` | [TokenAmount.md](TokenAmount.md) | v1 |
| `Allowance` | [Allowance.md](Allowance.md) | v1 |
| `FlashLoanReceipt` | [FlashLoanReceipt.md](FlashLoanReceipt.md) | v1 |
| `ReentrancyLock` | [ReentrancyLock.md](ReentrancyLock.md) | v1 |
| `Capability` | [Capability.md](Capability.md) | v1 — API under review |
| `OracleReading` | [OracleReading.md](OracleReading.md) | v1 |
| `WithdrawalRequest` | [WithdrawalRequest.md](WithdrawalRequest.md) | v1 |
| `PositionTicket` | [PositionTicket.md](PositionTicket.md) | v1 |
| `TwoPartyAgreement` | [TwoPartyAgreement.md](TwoPartyAgreement.md) | v2 / extension |

---

## What problem linear types solve

In a plain `UInt256`-based contract model, value is just a number. Nothing in the type system connects "the number in Alice's balance slot" to "the total supply of tokens in existence." You can write:

```lean
-- This is valid Lean. Nothing stops it.
s.storage.balances.set alice (s.storage.balances.get alice - 1)
-- Where did that 1 go? Nowhere. It was destroyed silently.
```

You could write a conservation theorem and prove it. But you have to remember to write it, state it correctly, and prove it for every function that touches balances. If you add a new function later and forget the theorem, the guarantee silently disappears.

Linear types make certain **mistakes inexpressible**, not just disprovable. A value of a linear type must be used exactly once on every execution path. The compiler rejects programs where a linear value is:

- **Dropped** — a code path reaches a return or revert without consuming it
- **Duplicated** — the value is used more than once (copied)

This is not a runtime check. It is a static analysis pass over your AST before any code is generated.

### What linear types do NOT solve

Linear types prevent **structural** bugs — wrong shape of code. They do not prevent **logical** bugs — wrong numbers in the right shape. Conservation theorems are still needed for arithmetic. Linear types reduce how many you need, but do not eliminate them entirely.

The rule of thumb: **linear types make theorems unnecessary. They do not make theorems easier.**

---

## How linearity is enforced

### Not by Lean's type system

Lean 4 does not have native linear types. Defining a `structure TokenAmount where raw : UInt256` does not prevent copying — Lean structs are value types and can be freely duplicated.

Linearity in LSC is enforced by a **static analysis pass** over the `Stmt` AST, run during elaboration before IR generation. By the time code is emitted, the check has already passed and all linear types are erased.

### The linearity check pass

The pass walks every `FunctionDef.body : Stmt` and tracks a `LinearCtx`:

```lean
structure LinearCtx where
  outstanding : Finset Ident  -- linear vars bound but not yet consumed
  consumed    : Finset Ident  -- linear vars already consumed
```

| Construct | Rule |
|-----------|------|
| `letBind x (linearExpr)` | Add `x` to `outstanding` |
| `var x` where `x` is linear | Remove from `outstanding`, add to `consumed`. Error if already in `consumed`. |
| `ifThenElse cond thn els` | Check both branches independently. Error if `outstanding` differs at join. |
| `revert _` | `outstanding` must be empty. |
| `seq s1 s2` | Thread `LinearCtx` from `s1` into `s2`. |
| Function return | `outstanding` must be empty. |

The branch rule prevents the common bug where the error path drops a `FlashLoanReceipt` while the success path repays it.

### Permission restrictions (redesign pending)

> **v2 status:** AST-level `LinearPermission` and function `permits` fields were removed. The sketch below describes the intended v1 design; the replacement will live under `Lib/Linear/` as a capability model when linearity work resumes.

Some linear type constructors are restricted to functions that declare the corresponding `LinearPermission`:

```lean
inductive LinearPermission
  | canMint (tokenType : Ident)
  | canBurn  (tokenType : Ident)
  | canFlashBorrow
```

A `Stmt.tokenMint` node in a function body that does not list `canMint` in its `permits` field is a linearity error.

### Erasure at IR

After the linearity pass, all linear type information is discarded. Each linear type compiles to its runtime representation (documented per type). From the EVM's perspective, none of this exists.

### Design pattern for each type

Every linear type follows the same structure:

1. An opaque Lean type
2. A constructor (may require a permission)
3. A destructor
4. Zero or more transformers
5. A compilation target (IR representation)
6. Theorems eliminated (what the user no longer proves)

---

## Proof ergonomics

After using the appropriate linear types, remaining theorems are about **numbers and logic**, not structural safety:

```lean
-- Still needed: the constant product formula is correct
theorem swap_preserves_k (w w' : AMMWorld) ... :
    w'.reserve0 * w'.reserve1 ≥ w.reserve0 * w.reserve1

-- NOT needed (structural via TokenAmount):
-- transfer_conserves_total_supply
-- no_double_spend
```

Framework theorems about linear type primitives (e.g. `TokenAmount.split_conserves`) are proved once and reused everywhere.

---

## How to add a new linear type

1. Name the invariant it enforces in one sentence.
2. List the theorems it would eliminate if it existed.
3. If the invariant is structural (not arithmetic), proceed.
4. Define the `opaque` type and its operations.
5. Prove conservation theorems once in the framework.
6. Add a `LinearPermission` variant if the constructor should be restricted.
7. Add an erasure case in `Compile/Lower.lean`.
8. Add a new file in this directory.

If the theorems it would eliminate are mostly arithmetic, consider `@math` specs or field constraints instead. Linear types are best for **permission, obligation, and custody** patterns.

---

## Quick reference

| Type | Represents | Constructor | Destructor | Eliminates |
|------|------------|-------------|------------|------------|
| `TokenAmount` | Value custody | `mint` (restricted) | `burn` (restricted) | Conservation theorems |
| `Allowance` | Spending permission | `grant` | `revoke` | `transferFrom_exceeds_allowance` |
| `FlashLoanReceipt` | Repayment obligation | `borrow` (restricted) | `repay` | `flashloan_always_repaid` |
| `ReentrancyLock` | Execution exclusivity | `acquire` | `release` | `external_calls_always_locked` |
| `Capability` | Access permission | `require` | `consume` | All `only_X_can_Y` theorems |
| `OracleReading` | Price freshness | `fetch` | `consume` | `price_is_fresh` |
| `WithdrawalRequest` | CEI order | `stage` | `execute` or `cancel` | `state_before_transfer` |
| `PositionTicket` | Debt obligation | `open` | `close` or `liquidate` | `positions_always_resolved` |
| `TwoPartyAgreement` | Mutual commitment | `offer` → `accept` | `settle` or `cancel` | `settlement_requires_both` |
