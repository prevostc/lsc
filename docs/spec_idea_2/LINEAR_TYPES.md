# Linear Types in LSC

> This document is the authoritative reference for the linear type system in LSC.
> It covers motivation, the full type library, implementation mechanics, proof ergonomics,
> and the compilation story. Read DESIGN.md and IMPLEMENTATION.md first.

---

## What Problem Linear Types Solve

In a plain `UInt256`-based contract model, value is just a number. Nothing in the
type system connects "the number in Alice's balance slot" to "the total supply of
tokens in existence." You can write:

```lean
-- This is valid Lean. Nothing stops it.
s.storage.balances.set alice (s.storage.balances.get alice - 1)
-- Where did that 1 go? Nowhere. It was destroyed silently.
```

You could write a conservation theorem and prove it. But you have to remember to
write it, state it correctly, and prove it for every function that touches balances.
If you add a new function later and forget the theorem, the guarantee silently disappears.

Linear types solve a different problem: they make certain **mistakes inexpressible**,
not just disprovable. A value of a linear type must be used exactly once on every
execution path. The compiler rejects programs where a linear value is:

- **Dropped** — a code path reaches a return or revert without consuming it
- **Duplicated** — the value is used more than once (copied)

This is not a runtime check. It is a static analysis pass over your AST before
any code is generated. The enforcement is at the language level, not the EVM level.

### What Linear Types Do NOT Solve

Linear types prevent **structural** bugs — wrong shape of code. They do not prevent
**logical** bugs — wrong numbers in the right shape. If your split function
computes `(amount, total - amount - 1)` and drops one unit, the linearity check
passes. Conservation theorems are still needed for the arithmetic. Linear types
reduce how many you need, but do not eliminate them entirely.

The rule of thumb: **linear types make theorems unnecessary. They do not make
theorems easier.**

---

## How Linearity Is Enforced

### Not by Lean's Type System

Lean 4 does not have native linear types. Defining a `structure TokenAmount where raw : UInt256`
does not prevent copying — Lean structs are value types and can be freely duplicated.

Linearity in LSC is enforced by a **static analysis pass** over the `Stmt` AST,
run during elaboration before IR generation. By the time code is emitted, the
check has already passed and all linear types are erased.

### The Linearity Check Pass

The pass walks every `FunctionDef.body : Stmt` and tracks a `LinearCtx`:

```lean
structure LinearCtx where
  -- linear variables bound but not yet consumed on this path
  outstanding : Finset Ident
  -- linear variables already consumed on this path
  consumed    : Finset Ident
```

Rules:

| Construct | Rule |
|-----------|------|
| `letBind x (linearExpr)` | Add `x` to `outstanding` |
| `var x` where `x` is linear | Remove from `outstanding`, add to `consumed`. Error if already in `consumed` (duplicate use). |
| `ifThenElse cond thn els` | Check both branches independently. Error if `outstanding` differs between branches at join point. |
| `revert _` | `outstanding` must be empty. Error if any linear var is outstanding. |
| `seq s1 s2` | Thread `LinearCtx` from `s1` into `s2`. |
| Function return | `outstanding` must be empty. |

The branch rule is the critical one. Both branches of an `if` must consume exactly
the same set of linear variables. This prevents the common bug where the error
path drops a `FlashLoanReceipt` while the success path repays it.

### Permission Restrictions

Some linear type constructors are restricted to functions that declare the
corresponding `LinearPermission`. The linearity pass checks this:

```lean
inductive LinearPermission
  | canMint (tokenType : Ident)
  | canBurn  (tokenType : Ident)
  | canFlashBorrow
```

A `Stmt.tokenMint` node in a function body that does not list `canMint` in its
`permits` field is a linearity error, reported with the position of the `emit`
call in the source.

### Erasure at IR

After the linearity pass, all linear type information is discarded. The IR has
no concept of linearity. Each linear type compiles to its runtime representation
(see §Compilation below). From the EVM's perspective, none of this exists.

---

## The Linear Type Library

### Design Pattern for Each Type

Every linear type in the library follows the same structure:

1. **An opaque Lean type** — users cannot pattern match or construct it directly
2. **A constructor** — the only way to create a value; may require a permission
3. **A destructor** — the only way to consume a value; produces something useful
4. **Zero or more transformers** — consume one value, produce another of the same type
5. **A compilation target** — what the type erases to at the IR level
6. **Theorems eliminated** — what the user no longer needs to prove

---

### `TokenAmount` — Value Custody

**Represents**: custody of a quantity of fungible tokens.

**The invariant enforced**: token value cannot be created from a raw number.
The only sources of `TokenAmount` are `mint` (restricted) and external calls
that return one. The only sinks are `burn` (restricted) and external calls that
consume one.

```lean
opaque TokenAmount : Type

namespace TokenAmount

/-- Create token value from nothing.
    Only callable in functions with `canMint tokenType` permission.
    Linearity: produces one outstanding TokenAmount. -/
def mint (amount : UInt256) : ContractM S E Err TokenAmount

/-- Destroy token value, returning its raw amount.
    Only callable in functions with `canBurn tokenType` permission.
    Linearity: consumes one outstanding TokenAmount. -/
def burn (t : TokenAmount) : ContractM S E Err UInt256

/-- Split into two parts. Conservation is proved once here, not per-contract.
    h proves no value is created: amount ≤ t.value.
    Linearity: consumes one, produces two. Both must be consumed downstream. -/
def split (t : TokenAmount) (amount : UInt256)
    (h : amount ≤ t.value) : TokenAmount × TokenAmount

/-- Merge two amounts of the same denomination.
    Linearity: consumes two, produces one. -/
def merge (t1 t2 : TokenAmount) : TokenAmount

/-- Read the value without consuming. Not linear — just a projection.
    Cannot be used to reconstruct a TokenAmount. -/
def value (t : TokenAmount) : UInt256

/-- Conservation theorems — proved once here, inherited everywhere. -/

theorem split_conserves (t : TokenAmount) (amount : UInt256) (h : amount ≤ t.value) :
    let (t1, t2) := split t amount h
    t1.value + t2.value = t.value

theorem merge_conserves (t1 t2 : TokenAmount) :
    (merge t1 t2).value = t1.value + t2.value

end TokenAmount
```

**Theorems eliminated per contract**:
- `transfer_conserves_total_value`
- `no_phantom_minting`
- `transfer_does_not_increase_sender_balance` (structural: sender's token is consumed)

**Compilation target**: `UInt256` in the IR. The linear wrapper is erased.

**What remains to prove**: arithmetic correctness within your contract logic.
Conservation of the token object itself is structural. Conservation of a
protocol-level invariant (e.g., LP shares = reserve ratio) still needs a theorem.

**Example — AMM swap using TokenAmount**:

```lean
-- In source syntax:
def swap : Tx := do
  -- inputToken is received from caller (external call returns TokenAmount)
  let inputToken ← ERC20.receiveFrom(msg.sender, amountIn);
  -- compute output using constant product formula
  let outputAmount := computeOutput(inputToken.value, storage.reserve0, storage.reserve1);
  -- split output from our reserve — reserve0's TokenAmount is consumed
  let (output, newReserve0) := storage.reserve0.split(outputAmount);
  -- merge input into our other reserve
  let newReserve1 := storage.reserve1.merge(inputToken);
  -- update storage
  storage.reserve0 := newReserve0;
  storage.reserve1 := newReserve1;
  -- return output to caller
  ERC20.sendTo(msg.sender, output);
```

In this function, `inputToken`, `output`, `newReserve0`, and `newReserve1` are
all linear. The linearity pass verifies every one is consumed exactly once.
There is no code path where a `TokenAmount` could silently disappear.

---

### `Allowance` — Spending Permission

**Represents**: a granted permission to spend tokens on behalf of another address,
up to a specified amount.

**The invariant enforced**: `transferFrom` cannot spend more than the approved
amount. This is guaranteed by the type of `consume`, not by a runtime check
that could be bypassed.

```lean
opaque Allowance : Type

namespace Allowance

/-- Grant a spending permission. The caller is granting permission to spend
    `amount` tokens from their balance to `spender`.
    Linearity: produces one outstanding Allowance. -/
def grant (owner : Address) (spender : Address) (amount : UInt256)
    : ContractM S E Err Allowance

/-- Consume part of an allowance.
    h : amount ≤ a.remaining proves at the type level that this cannot exceed the grant.
    Returns the remaining allowance (must be stored or revoked).
    Linearity: consumes one, produces one (the remainder). -/
def consume (a : Allowance) (amount : UInt256) (h : amount ≤ a.remaining)
    : ContractM S E Err Allowance

/-- Revoke the remaining allowance. Consumes it without using the value.
    Linearity: consumes one, produces nothing. -/
def revoke (a : Allowance) : ContractM S E Err Unit

/-- Read remaining amount. Not linear. -/
def remaining (a : Allowance) : UInt256

end Allowance
```

**Theorems eliminated per contract**:
- `transferFrom_cannot_exceed_allowance` — structural: `h : amount ≤ a.remaining` is in the type of `consume`
- `allowance_not_negative` — structural: `UInt256` cannot be negative

**Compilation target**: A storage slot `(owner, spender) → UInt256` (the remaining
amount). `grant` writes the initial value. `consume` reads, subtracts, writes back.
`revoke` writes zero.

---

### `FlashLoanReceipt` — Repayment Obligation

**Represents**: an outstanding flash loan that has not yet been repaid.

**The invariant enforced**: any function that borrows must repay before returning,
on all code paths including error paths.

This is particularly powerful because flash loan repayment is a **temporal**
property — the repayment must happen *after* the borrow, within the same
transaction. This kind of ordering property is very hard to state as a theorem
but trivial to enforce with a linear type.

```lean
opaque FlashLoanReceipt : Type

namespace FlashLoanReceipt

/-- Borrow tokens. Returns the tokens and a receipt.
    The receipt MUST be consumed before the function returns.
    Permission: function must declare `canFlashBorrow`.
    Linearity: produces one outstanding FlashLoanReceipt.
               Also produces a TokenAmount representing the borrowed funds. -/
def borrow (amount : UInt256)
    : ContractM S E Err (TokenAmount × FlashLoanReceipt)

/-- Repay the loan. Consumes both the receipt and the repayment funds.
    h : repayment.value ≥ receipt.amount — cannot underpay.
    Linearity: consumes one FlashLoanReceipt and one TokenAmount. -/
def repay (receipt : FlashLoanReceipt) (repayment : TokenAmount)
    (h : repayment.value ≥ receipt.amount)
    : ContractM S E Err Unit

/-- The borrowed amount (read-only). -/
def amount (r : FlashLoanReceipt) : UInt256

end FlashLoanReceipt
```

**What the linearity pass catches**:

```lean
-- REJECTED: receipt dropped on error path
def badFlashLoan : Tx := do
  let (funds, receipt) ← FlashLoanReceipt.borrow(1000);
  if (someCondition) {
    -- success path: repays correctly
    FlashLoanReceipt.repay(receipt, funds, ...);
  } else {
    -- error path: receipt not consumed!
    revert BadCondition;  -- linearity error: receipt is outstanding
  }

-- ACCEPTED: both paths consume the receipt
def goodFlashLoan : Tx := do
  let (funds, receipt) ← FlashLoanReceipt.borrow(1000);
  if (someCondition) {
    FlashLoanReceipt.repay(receipt, funds, ...);
  } else {
    -- must return funds and consume receipt even on error path
    FlashLoanReceipt.repay(receipt, funds, ...);
    revert BadCondition;
  }
```

**Theorems eliminated**:
- `flashloan_always_repaid`
- `flashloan_repayment_covers_principal`

**Compilation target**: A boolean storage slot `loan_outstanding`. `borrow` checks
the slot is `false`, sets it to `true`, transfers funds. `repay` verifies repayment,
sets slot back to `false`. The runtime check on `borrow` is belt-and-suspenders —
the linearity pass already guarantees no two borrows can be outstanding
simultaneously from your contract's perspective.

---

### `ReentrancyLock` — Exclusive Execution

**Represents**: proof that this contract's reentrancy guard is held.

**The invariant enforced**: external calls can only be made while holding the lock.
The lock can only be acquired once (acquiring checks `locked = false`). Any
reentrant call hits the lock check and reverts before touching state.

```lean
opaque ReentrancyLock : Type

namespace ReentrancyLock

/-- Acquire the lock. Fails if already locked (reentrancy detected).
    Sets `ContractState.locked = true`.
    Linearity: produces one outstanding ReentrancyLock. -/
def acquire : ContractM S E Err ReentrancyLock

/-- Release the lock. Sets `ContractState.locked = false`.
    Linearity: consumes one ReentrancyLock. -/
def release (lock : ReentrancyLock) : ContractM S E Err Unit

end ReentrancyLock

/-- Framework primitive: make an external call. Requires a lock.
    The lock is consumed and a new one is issued after the call returns.
    This models that the lock was held continuously throughout the call. -/
def externalCall
    (lock   : ReentrancyLock)
    (target : Address)
    (selector : UInt32)
    (args   : List UInt256)
    : ContractM S E Err (UInt256 × ReentrancyLock)
```

**Usage pattern** — this is the **only** way to make an external call:

```lean
def withdrawAll : Tx := do
  -- update state BEFORE calling out (checks-effects-interactions)
  let amount := storage.balance;
  storage.balance := 0;
  -- acquire lock
  let lock ← ReentrancyLock.acquire;
  -- make external call (lock consumed, new lock returned)
  let (result, lock) ← externalCall(lock, storage.recipient, TRANSFER_SELECTOR, [amount]);
  -- release lock
  ReentrancyLock.release(lock);
```

Note that `externalCall` takes the lock and returns a new one. This means the
lock variable must be rebound. If you try to use the old lock after the call,
the linearity pass rejects it as a duplicate use.

**Theorems eliminated**:
- `external_calls_require_lock` — structural: `externalCall` takes a `ReentrancyLock` argument
- `no_reentrant_state_modification` — if `locked = true`, `acquire` fails, so any reentrant function call reverts before touching state

**Compilation target**: the `locked : Bool` field in `ContractState`. `acquire` compiles to
`if sload(LOCK_SLOT) { revert(0,0) } sstore(LOCK_SLOT, 1)`. `release` compiles to
`sstore(LOCK_SLOT, 0)`. The `LOCK_SLOT` is a fixed slot reserved by the framework,
never assigned to a user storage field.

---

### `Capability` — Access Permission

**Represents**: proof that the current caller has a specific privilege.

**The invariant enforced**: privileged functions cannot be called without first
obtaining a `Capability`. The only way to obtain a `Capability` is to pass an
identity check. So the check is always performed — it cannot be forgotten.

```lean
/-- Capability tags — one per access role. User-defined. -/
inductive Cap
  | Owner
  | Pauser
  | Guardian
  -- user adds more as needed

opaque Capability (c : Cap) : Type

namespace Capability

/-- Obtain a capability by proving identity.
    Returns none if caller does not have this role.
    Linearity: produces one Capability if the check passes.
               If the check fails, nothing is produced (caller handles the none). -/
def obtain (c : Cap) : ContractM S E Err (Option (Capability c))

/-- Assert capability and fail with Unauthorized if caller doesn't have it.
    Convenience wrapper over obtain. -/
def require (c : Cap) : ContractM S E Err (Capability c)

/-- Consume a capability. After use, it's gone. -/
def consume (cap : Capability c) : ContractM S E Err Unit

end Capability
```

**Usage pattern**:

```lean
-- Only functions that take a Capability can be called by the holder.
-- A regular caller cannot call setFee — they have no Capability to pass.
def setFee (newFee : UInt256) : Tx := do
  -- require fails and reverts if caller is not Owner
  let cap ← Capability.require(.Owner);
  storage.fee := newFee;
  -- cap must be consumed — use it to "prove" we used the privilege
  Capability.consume(cap);
```

**Theorems eliminated**:
- `setFee_only_owner`
- `pause_only_pauser`
- Every `only_X_can_do_Y` theorem where Y requires a Capability

**Compilation target**: `Capability` erases to **nothing**. The identity check
already happened inside `Capability.require`. There is no runtime representation
of the capability itself. What compiles is only the identity check:
`if caller() != sload(OWNER_SLOT) { revert(0,0) }`.

This means `Capability` is the linear type that most dramatically reduces compiled
code size — it adds zero bytes to the runtime bytecode while eliminating an entire
class of theorems.

---

### `OracleReading` — Price Freshness

**Represents**: a price reading that was fetched this transaction and is guaranteed
fresh relative to a declared maximum age.

**The invariant enforced**: stale prices cannot be used. The only way to get a
price into your contract is through `OracleReading.fetch`, which checks the
reading's timestamp. The price cannot be cached across transactions because the
`OracleReading` type has no representation in storage — it only exists in memory
during a single transaction.

```lean
opaque OracleReading : Type

namespace OracleReading

/-- Fetch a fresh price.
    maxAge: maximum acceptable age in seconds.
    Reverts with StalePrice if the oracle's last update is older than maxAge.
    Linearity: produces one outstanding OracleReading. -/
def fetch (oracle : Address) (maxAge : UInt256)
    : ContractM S E Err OracleReading

/-- Extract the price. Consumes the reading.
    Linearity: consumes one OracleReading, produces a plain UInt256. -/
def consume (r : OracleReading) : ContractM S E Err UInt256

/-- Read price without consuming. Use with care — if you need to read it twice,
    use consume and store the result in a local let binding. -/
def price (r : OracleReading) : UInt256

end OracleReading
```

**Theorems eliminated**:
- `price_not_stale` — structural: `fetch` checks staleness, `price` can only come from a fresh reading

**Compilation target**: `(UInt256, UInt256)` — price and timestamp at fetch time.
`fetch` makes an external call to the oracle contract, reads the answer and
timestamp, checks `block.timestamp - timestamp ≤ maxAge`. `consume` returns
the price value.

---

### `WithdrawalRequest` — CEI Order Enforcement

**Represents**: a staged withdrawal — state has been updated (effects), funds
have not yet moved (interaction pending).

**The invariant enforced**: `Withdrawal.execute` (the actual fund transfer) can
only happen after `Withdrawal.stage` (the state update). Checks-effects-interactions
order is structural, not a convention that can be forgotten.

```lean
opaque WithdrawalRequest : Type

namespace WithdrawalRequest

/-- Stage a withdrawal: update internal accounting, record the pending withdrawal.
    Amount is debited from the user's internal balance here.
    Linearity: produces one outstanding WithdrawalRequest. -/
def stage (recipient : Address) (amount : UInt256)
    : ContractM S E Err WithdrawalRequest

/-- Execute: perform the actual fund transfer.
    Only possible if staging already happened (requires the receipt).
    Linearity: consumes one WithdrawalRequest. -/
def execute (req : WithdrawalRequest)
    : ContractM S E Err Unit

/-- Cancel: abort a staged withdrawal, reverse the accounting.
    Linearity: consumes one WithdrawalRequest. -/
def cancel (req : WithdrawalRequest)
    : ContractM S E Err Unit

end WithdrawalRequest
```

**Theorems eliminated**:
- `state_updated_before_transfer` — structural: `execute` requires a `WithdrawalRequest`, which requires `stage` first
- `no_double_withdraw` — structural: the `WithdrawalRequest` is consumed by `execute`, cannot be used twice

**Compilation target**: A storage record `(recipient, amount, pending: Bool)`.
`stage` writes the record and sets `pending = true`. `execute` reads the record,
sets `pending = false`, then performs the transfer. `cancel` sets `pending = false`
without transferring.

---

### `PositionTicket` — Open Debt Obligation

**Represents**: an open position in a lending or perpetuals protocol. Carries
an obligation: the position must eventually be closed (by repayment) or liquidated
(by proving undercollateralization). It cannot be abandoned.

**The invariant enforced**: bad debt cannot accumulate silently. Every open
position is tracked as a linear value. If the function that opened the position
returns without closing it, the linearity check fails.

```lean
opaque PositionTicket : Type

namespace PositionTicket

/-- Open a position. Collateral is deposited, debt is recorded.
    Linearity: produces one outstanding PositionTicket. -/
def open (collateral : TokenAmount) (debt : UInt256)
    : ContractM S E Err PositionTicket

/-- Close a position by repaying debt.
    h : repayment.value ≥ ticket.debt — must repay in full.
    Returns the collateral.
    Linearity: consumes one PositionTicket and one TokenAmount (repayment).
               Produces one TokenAmount (collateral returned). -/
def close (ticket : PositionTicket) (repayment : TokenAmount)
    (h : repayment.value ≥ ticket.debt)
    : ContractM S E Err TokenAmount

/-- Liquidate an undercollateralized position.
    h : isUndercollateralized ticket — must prove the position is unhealthy.
    Returns collateral to liquidator.
    Linearity: consumes one PositionTicket. -/
def liquidate (ticket : PositionTicket)
    (h : isUndercollateralized ticket)
    : ContractM S E Err TokenAmount

/-- Read collateral value. Not linear. -/
def collateralValue (t : PositionTicket) : UInt256

/-- Read debt value. Not linear. -/
def debt (t : PositionTicket) : UInt256

end PositionTicket
```

**Theorems eliminated**:
- `positions_always_resolved` — structural: ticket cannot be dropped
- `liquidation_requires_undercollateralization` — structural: `h` in `liquidate` type
- `close_requires_full_repayment` — structural: `h` in `close` type

**Compilation target**: A storage record per position: `(owner, collateral, debt, open: Bool)`.

---

### `TwoPartyAgreement` — Atomic Settlement

**Represents**: a commitment by two parties to exchange assets. Used for atomic
swaps, OTC trades, and settlement protocols.

**The invariant enforced**: settlement can only occur if both parties have
committed funds. Party A's funds cannot be settled without Party B's commitment.
If Party B never commits, Party A can always cancel and recover their funds.

```lean
opaque Offer     : Type  -- Party A committed, awaiting Party B
opaque Agreement : Type  -- Both parties committed

namespace TwoPartyAgreement

/-- Party A makes an offer. Commits funds.
    Linearity: produces one outstanding Offer. -/
def offer (funds : TokenAmount) (requestedAmount : UInt256) (counterparty : Address)
    : ContractM S E Err Offer

/-- Party B accepts. Commits funds. Produces an Agreement.
    Linearity: consumes one Offer, one TokenAmount. Produces one Agreement. -/
def accept (o : Offer) (funds : TokenAmount)
    (h : funds.value ≥ o.requestedAmount)
    : ContractM S E Err Agreement

/-- Settle: distribute funds to both parties.
    Linearity: consumes one Agreement. -/
def settle (a : Agreement)
    : ContractM S E Err (TokenAmount × TokenAmount)

/-- Cancel offer: recover Party A's funds.
    Linearity: consumes one Offer. -/
def cancel (o : Offer)
    : ContractM S E Err TokenAmount

end TwoPartyAgreement
```

**Theorems eliminated**:
- `settlement_requires_both_parties` — structural: `settle` requires `Agreement`, `Agreement` requires `accept`, `accept` requires `Offer`
- `party_a_funds_recoverable` — structural: `cancel` always returns the `TokenAmount` committed in `offer`

**Compilation target**: Storage records tracking offer state and committed amounts.

---

## Proof Ergonomics with Linear Types

### What theorems remain after using linear types

After using the appropriate linear types, the theorems you still need to write are
about **numbers and logic**, not about **structural safety**. Examples:

```lean
-- Still needed: the constant product formula is correct
theorem swap_preserves_k (w w' : AMMWorld) ... :
    w'.reserve0 * w'.reserve1 ≥ w.reserve0 * w.reserve1

-- Still needed: fee calculation is correct
theorem fee_does_not_exceed_input (amountIn fee : UInt256) ... :
    fee ≤ amountIn

-- Still needed: health factor threshold is correct
theorem liquidation_threshold_is_safe (ticket : PositionTicket) ... :
    isUndercollateralized ticket → ticket.collateralValue * 100 < ticket.debt * 150

-- NOT needed (structural via TokenAmount):
-- transfer_conserves_total_supply
-- no_double_spend
-- split_does_not_create_value
```

### Theorem shape for linear type operations

Theorems about functions that use linear types follow the same `simp` + `omega`
pattern as other theorems, because linear types erase by the time you are writing
proofs against the `ContractM` semantics.

```lean
-- The TokenAmount that split produces sums to the original
-- This is a framework theorem, not a per-contract theorem.
-- You never prove this yourself — you import it.
theorem TokenAmount.split_conserves
    (t : TokenAmount) (amount : UInt256) (h : amount ≤ t.value) :
    let (t1, t2) := TokenAmount.split t amount h
    t1.value + t2.value = t.value := by
  simp [TokenAmount.split]
  omega
```

When you use `split` in your AMM swap function, the AMM's conservation theorem
calls `TokenAmount.split_conserves` as a lemma — it does not re-prove conservation.
This is the compounding benefit: framework theorems about linear type primitives
are proved once and reused everywhere.

---

## How to Add a New Linear Type

When you identify a new pattern that requires a linear type not in the library:

1. **Name the invariant** it enforces in one sentence.
2. **List the theorems** it would eliminate if it existed.
3. If the invariant is structural (not arithmetic), proceed.
4. Define the `opaque` type.
5. Write constructor, destructor, and transformer operations.
6. Write the conservation theorem(s) for the framework — prove them once.
7. Add a `LinearPermission` variant if the constructor should be restricted.
8. Add an erasure case to `Compile/Lower.lean` mapping the type to its IR representation.
9. Document it here.

If the theorems it would eliminate are mostly arithmetic, you probably want a
**proof-required typeclass** (Option A from DESIGN.md) rather than a linear type.
Linear types are best suited for **permission, obligation, and custody** patterns.

---

## Quick Reference

| Type | Represents | Constructor | Destructor | Eliminates |
|---|---|---|---|---|
| `TokenAmount` | Value custody | `mint` (restricted) | `burn` (restricted) | Conservation theorems |
| `Allowance` | Spending permission | `grant` | `revoke` | `transferFrom_exceeds_allowance` |
| `FlashLoanReceipt` | Repayment obligation | `borrow` (restricted) | `repay` | `flashloan_always_repaid` |
| `ReentrancyLock` | Execution exclusivity | `acquire` | `release` | `external_calls_always_locked` |
| `Capability` | Access permission | `require` | `consume` | All `only_X_can_Y` theorems |
| `OracleReading` | Price freshness | `fetch` | `consume` | `price_is_fresh` |
| `WithdrawalRequest` | CEI order | `stage` | `execute` or `cancel` | `state_before_transfer` |
| `PositionTicket` | Debt obligation | `open` | `close` or `liquidate` | `positions_always_resolved` |
| `TwoPartyAgreement` | Mutual commitment | `offer` → `accept` | `settle` or `cancel` | `settlement_requires_both` |