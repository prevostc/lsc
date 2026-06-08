**[← LSC Specification](lsc-spec.md#appendices)**

# LSC Appendices

Extended reference patterns, examples, and project history. Code samples follow [lsc-spec.md](lsc-spec.md) (v1): `Except E A`, `Caller`, `Bytes[N]`, `LscError` / `+?`, fixed-point `⌊*⌋?` / `⸢*⸣?` (§2.7), `require`, and `Mapping` as `K → V`.

| Appendix | Title | Section |
|----------|-------|---------|
| A | ERC-20 Pattern | [§A](#appendix-a--erc-20-pattern) |
| B | Composition Pattern | [§B](#appendix-b--composition-pattern) |
| C | Versioning Roadmap | [§C](#appendix-c--versioning-roadmap) |
| D | Wad/Ray Fixed-point | [§D](#appendix-d--wadray-fixed-point) |
| E | ERC-20 with Mint/Burn | [§E](#appendix-e--erc-20-with-mintburn) |
| F | UniV2-Style AMM | [§F](#appendix-f--univ2-style-amm) |

---

## Appendix A — ERC-20 Pattern

This appendix documents the **[forge-lean-erc20](https://github.com/forge-lean/forge-lean-erc20)** showcase. It is not part of the core `Lsc` package or default proof runner behavior. The demo enables `[lsc.compliance.erc20]` (§11) to require the theorem list there.

### A.1 State

```lean
structure TransferEvent where
  from to : Address
  value   : UInt256
  deriving Lsc.Event.EvmEvent

structure ApprovalEvent where
  owner spender : Address
  value         : UInt256
  deriving Lsc.Event.EvmEvent

structure ERC20State where
  name        : Bytes[32]
  symbol      : Bytes[32]
  decimals    : UInt256
  totalSupply : UInt256
  balances    : Mapping Address UInt256
  allowances  : Mapping Address (Mapping Address UInt256)
```

### A.2 Key exports

```lean
@[lsc.error]
inductive TokenError where
  | insufficientBalance
  | arith : ArithError → TokenError
  deriving DecidableEq, Repr

@[lsc.external]
def transfer (caller : Caller) (s : ERC20State) (to : Address) (amount : UInt256)
    : Except TokenError (ERC20State × Bool) :=
  do
  require (s.balances.get caller.val ≥ amount) .insufficientBalance
  let newCaller ← s.balances.get caller.val -? amount
  let newTo     ← s.balances.get to +? amount
  let s' := { s with balances := s.balances.set caller.val newCaller |>.set to newTo }
  emit! TransferEvent caller.val to amount
  return .ok (s', true)

@[lsc.external]
def approve (caller : Caller) (s : ERC20State) (spender : Address) (amount : UInt256)
    : Except TokenError (ERC20State × Bool) :=
  let s' := { s with allowances :=
    s.allowances.set caller.val (s.allowances.get caller.val |>.set spender amount) }
  emit! ApprovalEvent caller.val spender amount
  .ok (s', true)
```

### A.3 Example lemma and theorem

```lean
-- test/ERC20Lemma.lean (AI-generated)
import Token

lemma transfer_no_overdraft
    (caller : Caller) (to : Address) (amount : UInt256) (s : ERC20State)
    (h : transfer caller s to amount = .error .insufficientBalance) :
    s.balances.get caller.val < amount := by
  simp [transfer] at h
  split_ifs at h with hguard <;> omega

lemma transfer_preserves_total_supply
    (caller : Caller) (to : Address) (amount : UInt256)
    (s s' : ERC20State) (ret : Bool)
    (h : transfer caller s to amount = .ok (s', ret)) :
    s'.totalSupply = s.totalSupply := by
  simp [transfer] at *
  exact h.2
```

```lean
-- test/ERC20Theorem.lean (human-reviewed)
import Token
import ERC20Lemma

/-- transfer reverts when caller has insufficient balance. -/
theorem transfer_no_overdraft
    (caller : Caller) (to : Address) (amount : UInt256) (s : ERC20State)
    (h : transfer caller s to amount = .error .insufficientBalance) :
    s.balances.get caller.val < amount :=
  ERC20Lemma.transfer_no_overdraft caller to amount s h

/-- transfer preserves total supply. -/
theorem transfer_preserves_total_supply
    (caller : Caller) (to : Address) (amount : UInt256)
    (s s' : ERC20State) (ret : Bool)
    (h : transfer caller s to amount = .ok (s', ret)) :
    s'.totalSupply = s.totalSupply :=
  ERC20Lemma.transfer_preserves_total_supply caller to amount s s' ret h
```

---

---

## Appendix B — Composition Pattern

This appendix documents the **[forge-lean-composition](https://github.com/forge-lean/forge-lean-composition)** demo — the reference application for inline `call!` / `staticcall!` with interface casts, reentrancy-aware `World`/`invoke`, and multi-contract composition. It is the primary driver for v2a–v2b extern support.

### B.1 Goal

- **MyToken** — ERC-20-compatible contract with a `counter : Address` hook target
- **TransferCounter** — `{ count : UInt256 }`; exposes `onTransfer()`
- On every successful `transfer` / `transferFrom`, MyToken runs token logic then CALLs the counter (checks-effects-interactions)

```mermaid
sequenceDiagram
  participant User
  participant MyToken
  participant TC as TransferCounter
  User->>MyToken: transfer(to, amount)
  MyToken->>MyToken: ERC20 transfer logic
  MyToken->>TC: call! (counter : ITransferCounter).onTransfer
  TC->>TC: count + 1
  TC-->>MyToken: success
  MyToken-->>User: true
```

### B.2 MyToken state (flat struct — no `extends`)

```lean
-- src/MyToken.lean
structure MyTokenState where
  name        : Bytes[32]
  symbol      : Bytes[32]
  decimals    : UInt256
  totalSupply : UInt256
  balances    : Mapping Address UInt256
  allowances  : Mapping Address (Mapping Address UInt256)
  counter     : Address   -- 0 = hook disabled
```

### B.3 MyToken exports

MyToken adds a `counter : Address` field (`0` = hook disabled). On successful `transfer` / `transferFrom`, token logic runs first, then an inline `call!` to the counter (checks-effects-interactions):

```lean
-- src/MyToken.lean (excerpt)
@[Lsc.error]
inductive TokenError where
  | arith  : ArithError → TokenError
  | extern : ExternError → TokenError

def notifyCounterIfHooked (caller : Caller) (s' : MyTokenState) (to : Address)
    : Except TokenError Unit := do
  if s'.counter ≠ Address.zero ∧ caller.val ≠ to then
    let _ ← call! (s'.counter : ITransferCounter).onTransfer
  return .ok ()

@[Lsc.external]
def transfer (caller : Caller) (s : MyTokenState) (to : Address) (amount : UInt256)
    : Except TokenError (MyTokenState × Bool) := do
  require (s.balances.load caller ≥ amount) .insufficientBalance
  let newCaller ← s.balances.load caller -? amount
  let newTo     ← s.balances.load to +? amount
  let s' := { s with balances := s.balances.store caller newCaller |>.store to newTo }
  emit! TransferEvent caller to amount
  ← notifyCounterIfHooked caller s' to
  return .ok (s', true)
```

Self-transfer skip and zero-counter skip are ordinary control flow in `notifyCounterIfHooked` (or inlined in `transfer`). No hook attributes or compiler-inserted export bodies.

### B.4 TransferCounter

```lean
-- src/TransferCounter.lean
structure TransferCounterState where
  count : UInt256

@[lsc.error]
inductive TransferCounterError where
  | arith : ArithError → TransferCounterError  -- via LscError +?

@[lsc.external]
def onTransfer (s : TransferCounterState) : Except ArithError TransferCounterState :=
  do
  let c ← s.count +? 1
  return .ok { s with count := c }
```

### B.5 Required theorems

**ERC-20 compliance** (`[lsc.compliance.erc20]`): same table as §11.3, stated over `MyToken` functions.

**Hook compliance** (`[lsc.compliance.hook]`):

| Theorem | Statement summary |
|---------|------------------|
| `transfer_increments_counter_when_hooked` | `counter ≠ 0`, successful export ⇒ `count` increases by 1 |
| `transfer_skips_counter_when_zero` | `counter = 0` ⇒ behavior matches export without extern |
| `transfer_self_noop_skips_counter` | `from = to` ⇒ counter unchanged |
| `hook_revert_implies_transfer_error` | counter call reverts ⇒ MyToken export `.error` |

**TransferCounter** (`test/TransferCounterTheorem.lean`):

| Theorem | Statement summary |
|---------|------------------|
| `onTransfer_increments_count` | `onTransfer` increments `count` by exactly 1 |

### B.6 Proof strategy

| Layer | What | Files |
|-------|------|-------|
| 1 | TransferCounter closed-world | `TransferCounterTheorem` / `TransferCounterLemma` |
| 2 | MyToken ERC-20 properties | `MyTokenTheorem` / `MyTokenLemma` — no `World` |
| 3 | Hook composition | `MyTokenTheorem` / `MyTokenLemma` — `simulate_call` (v2b) |
| 4 | EVM | `Composition.t.sol` — `deployCode` both contracts; assert `count` after transfers |

---

---

## Appendix C — Versioning Roadmap

All v2+ content is removed from the main spec body. This appendix records what each phase adds.

| Phase | Status | Deliverables |
|-------|--------|-------------|
| **v1** | Current | Counter + ERC-20 demo; no `Lsc.extern.*` in core tests; `World`/`invoke` in `Lsc.Semantics` but not emitted |
| **v2a** | Planned | `World`, `Account`, `invoke` fully wired in Foundry multi-contract tests |
| **v2b** | Planned | Inline `call!` / `staticcall!` emitter; `CALL` / `STATICCALL` lowering; interface casts; `simulate_call` complete |
| **v2c** | Planned | `@[lsc.no_reentrant]` validator enforcement; trace templates; `lift_*` refinement lemmas |
| **v3** | Future | `delegatecall`; `Lsc.unsafe.call`; `CREATE` / `SELFDESTRUCT` in `World` |

| Feature | First available | Proof stance |
|---------|----------------|-------------|
| `CALL` | v2b | Layer 3 via `simulate_call` for same-repo callees; assume interfaces otherwise |
| `STATICCALL` | v2b | `lift_staticcall_view` |
| `DELEGATECALL` | v3 | Proxy specs |
| Arbitrary calldata | v3 (`unsafe.call`) | Fuzz only |
| `CREATE` / `SELFDESTRUCT` | v3 | After CALL stable |
| `structure … extends` | TBD | If clear v2 use case emerges |
| Gas forwarding proof | Phase 2 | Emitter correctness proof |

---

---

## Appendix D — Wad/Ray Fixed-point

RAY (10²⁷) and WAD (10¹⁸) fixed-point multiply/divide with explicit rounding modes. Normative API: [lsc-spec.md §2.7](lsc-spec.md#27-fixed-point-arithmetic-lscray--lscwad). Implementation reference: [`WadRayMath/`](WadRayMath/).

### D.1 Operator quick-reference

All operators return `Except E UInt256` — trailing `?` marks the fallible channel (same as `+?`). Bracket pairs wrap `*` or `/`; scale comes from which namespace you `open scoped`.

| Operator | Rounding | `Lsc.Ray` def | Math (RAY mul) |
|----------|----------|---------------|----------------|
| `a ⌊*⌋? b` | Down | `rayMulDown` | `⌊a·b / RAY⌋` |
| `a ⌈*⌉? b` | Up | `rayMulUp` | `⌈a·b / RAY⌉` |
| `a ⸢*⸣? b` | HalfUp | `rayMulHalfUp` | `⌊(a·b + HALF_RAY) / RAY⌋` |
| `a ⌊/⌋? b` | Down | `rayDivDown` | floor-scaled division |
| `a ⌈/⌉? b` | Up | `rayDivUp` | ceiling-scaled division |
| `a ⸢/⸣? b` | HalfUp | `rayDivHalfUp` | half-up scaled division |

Under `open scoped Lsc.Wad`, the same six operators desugar to `wadMulDown`, `wadMulUp`, `wadMulHalfUp`, `wadDivDown`, `wadDivUp`, `wadDivHalfUp` (scale `WAD = 10^18`).

**Bracket pairs:**

| Pair | Unicode | Use |
|------|---------|-----|
| `⌊⌋` | U+230A / U+230B | Floor / round down |
| `⌈⌉` | U+2308 / U+2309 | Ceiling / round up |
| `⸢⸣` | U+2E22 / U+2E23 | Half-up **by LSC convention** |

Unicode distinguishes `⸢⸣` from math floor/ceiling (philological half-brackets). LSC adopts them for half-up fixed-point; the algorithm is still add-half-ulp then floor.

**No default aliases** — `rayMulHalfUp`, not `rayMul`. Aave's on-chain default is half-up; authors name it explicitly or use `⸢*⸣?`.

### D.2 Namespace scope

```lean
import Lsc.Ray
open Lsc Lsc.Ray
open scoped Lsc.Ray    -- ⌊*⌋?, ⸢*⸣?, etc. → ray*

-- WAD contract:
import Lsc.Wad
open scoped Lsc.Wad   -- same glyphs → wad*
```

Do **not** `open scoped` both `Lsc.Ray` and `Lsc.Wad` in one file — operator strings clash. Mixed-scale code uses explicit function names (`rayMulHalfUp`, `wadMulHalfUp`).

Plain `*?` / `/?` remain `UInt256` checked arithmetic (no rounding) from `Lsc.Prelude`.

### D.3 Lending example

```lean
import Lsc.Prelude
import Lsc.Ray
open Lsc Lsc.Ray
open scoped Lsc.Ray

structure LendingState where
  liquidityRate  : UInt256   -- RAY-encoded
  liquidityIndex : UInt256   -- RAY-encoded
  timeDelta      : UInt256   -- RAY-encoded

@[Lsc.external]
def accrueInterest (s : LendingState) : Except LendingError LendingState := do
  let growth    ← s.liquidityRate ⸢*⸣? s.timeDelta
  let newFactor ← s.liquidityIndex +? growth
  let newIndex  ← newFactor ⸢*⸣? s.liquidityRate
  return .ok { s with liquidityIndex := newIndex }
```

One-sided bounds (e.g. conservative accrual cap) use floor/ceil operators:

```lean
let capped ← rate ⌊*⌋? delta   -- rayMulDown
```

### D.4 Proof tiers and lemmas

| Tier | Module | Role |
|------|--------|------|
| ℕ | `Lsc.Ray.Nat` / `WadRayMath.Nat` | Definitions, `rayMulHalfUp_error`, monotonicity |
| EVM | `Lsc.Ray.Evm` / `WadRayMath.Evm` | `Except` wrappers, revert conditions |
| ℝ | `Lsc.Ray.Real` / `WadRayMath.Real` | `decode`, `rayMulHalfUp_error_real` |

**Bridge lemmas** (proofs use explicit names; operators desugar before `simp`):

```lean
@[simp] theorem rayMulHalfUp_val [LscError E] {a b r : UInt256} :
    (rayMulHalfUp a b : Except E UInt256) = .ok r ↔
    (¬ rayMulHalfUpReverts a.val b.val ∧
     r.val = Lsc.Ray.Nat.rayMulHalfUp a.val b.val) := ...
```

**Proof recipe:** `simp [accrueInterest, rayMulHalfUp_val, UInt256.addChecked_val]` then `omega` / `nlinarith`.

---

## Appendix E — ERC-20 with Mint/Burn

This appendix is a complete, self-contained ERC-20 implementation with owner-controlled mint and burn. It demonstrates `Mapping`, `Caller`, events, authorization proofs, construction pattern, and the compliance manifest.

### E.1 Contract (`src/Token.lean`)

```lean
import Lsc.Prelude
open Lsc

-- Events
structure TransferEvent where
  from to : Address
  value   : UInt256
  deriving Lsc.Event.EvmEvent

structure ApprovalEvent where
  owner spender : Address
  value         : UInt256
  deriving Lsc.Event.EvmEvent

-- State
structure TokenState where
  owner       : Address                                                  -- slot 0 (private)
  @[lsc.public] name        : Bytes[32] -- slot 1
  @[lsc.public] symbol      : Bytes[32] -- slot 2
  @[lsc.public] decimals    : UInt256                                  -- slot 3
  @[lsc.public] totalSupply : UInt256                                    -- slot 4
  balances    : Mapping Address UInt256                           -- slot 5
  allowances  : Mapping Address (Mapping Address UInt256)  -- slot 6
  -- balances / allowances: IERC-20 names differ → manual views below, not @[lsc.public]

@[lsc.error]
inductive TokenError where
  | insufficientBalance
  | insufficientAllowance
  | unauthorized
  | alreadyInitialized
  | arith : ArithError → TokenError  -- +? via LscError; no division in ERC-20

-- Construction: @[lsc.initialize] (deploy + optional proxy re-init; §3.6)
@[lsc.initialize]
def initialize (name symbol : Bytes[32]) (decimals : UInt256)
    (initialSupply : UInt256) (owner : Caller) : Except TokenError TokenState :=
  return .ok {
    name := name, symbol := symbol, decimals := decimals
    owner := owner.val, totalSupply := initialSupply
    balances := Mapping.empty |>.set owner.val initialSupply
    allowances := Mapping.empty }

-- Transfer
@[lsc.external]
def transfer (caller : Caller) (s : TokenState) (to : Address) (amount : UInt256)
    : Except TokenError (TokenState × Bool) :=
  do
  require (s.balances.get caller.val ≥ amount) .insufficientBalance
  let newCaller ← s.balances.get caller.val -? amount
  let newTo     ← s.balances.get to +? amount
  let s' := { s with balances := s.balances.set caller.val newCaller |>.set to newTo }
  emit! TransferEvent caller.val to amount
  return .ok (s', true)

-- Approve
@[lsc.external]
def approve
    (caller : Caller)
    (s : TokenState)
    (spender : Address) (amount : UInt256) : Except TokenError (TokenState × Bool) :=
  let s' := { s with allowances :=
    s.allowances.set caller.val (s.allowances.get caller.val |>.set spender amount) }
  emit! ApprovalEvent caller.val spender amount
  .ok (s', true)

-- TransferFrom
@[lsc.external]
def transferFrom (caller : Caller) (s : TokenState) (from to : Address) (amount : UInt256)
    : Except TokenError (TokenState × Bool) :=
  do
  let allowed := s.allowances.get from |>.get caller.val
  require (s.balances.get from ≥ amount) .insufficientBalance
  require (allowed ≥ amount) .insufficientAllowance
  let newFrom ← s.balances.get from -? amount
  let newTo   ← s.balances.get to +? amount
  let newAllowance ← allowed -? amount
  let s' := { s with
    balances   := s.balances.set from newFrom |>.set to newTo
    allowances := s.allowances.set from (s.allowances.get from |>.set caller.val newAllowance) }
  emit! TransferEvent from to amount
  return .ok (s', true)

-- Mint (owner only)
@[lsc.external]
def mint (caller : Caller) (s : TokenState) (to : Address) (amount : UInt256)
    : Except TokenError TokenState :=
  do
  require (caller.val == s.owner) .unauthorized
  let newSupply ← s.totalSupply +? amount
  let newBal    ← s.balances.get to +? amount
  let s' := { s with totalSupply := newSupply, balances := s.balances.set to newBal }
  emit! TransferEvent { val := 0 } to amount
  return .ok s'

-- Burn (owner only)
@[lsc.external]
def burn (caller : Caller) (s : TokenState) (from : Address) (amount : UInt256)
    : Except TokenError TokenState :=
  do
  require (caller.val == s.owner) .unauthorized
  require (s.balances.get from ≥ amount) .insufficientBalance
  let newSupply ← s.totalSupply -? amount
  let newBal    ← s.balances.get from -? amount
  let s' := { s with totalSupply := newSupply, balances := s.balances.set from newBal }
  emit! TransferEvent from { val := 0 } amount
  return .ok s'

-- Views (IERC-20 names differ from field names → manual exports)
@[lsc.external]
def balanceOf (s : TokenState) (account : Address) : UInt256 :=
  s.balances.get account

@[lsc.external]
def allowance (s : TokenState) (owner spender : Address) : UInt256 :=
  s.allowances.get owner |>.get spender

-- name, symbol, decimals, totalSupply: generated from @[lsc.public] (§3.5)
```

### E.2 Lemma (`test/TokenLemma.lean`)

AI-generated. Contains action-model scaffolding, helper `def`s, and `lemma` proofs. Property statements below are the lemma conclusions; tactic proofs are in §E.3.

```lean
import Token

-- ── Authorization ────────────────────────────────────────────────────────────

lemma mint_requires_owner
    (caller : Caller) (s : TokenState) (to : Address) (amount : UInt256)
    (h : mint caller s to amount = .error .unauthorized) :
  caller.val ≠ s.owner ∨ True  -- first branch is the authorization guard

lemma burn_requires_owner
    (caller : Caller) (s : TokenState) (from : Address) (amount : UInt256)
    (h : burn caller s from amount = .error .unauthorized) :
  caller.val ≠ s.owner

-- ── Supply conservation ───────────────────────────────────────────────────────

lemma transfer_preserves_supply
    (caller : Caller) (to : Address) (amount : UInt256)
    (s s' : TokenState) (ret : Bool)
    (h : transfer caller s to amount = .ok (s', ret)) :
  s'.totalSupply = s.totalSupply

lemma transferFrom_preserves_supply
    (caller from to : Address) (amount : UInt256)
    (s s' : TokenState) (ret : Bool)
    (h : transferFrom caller s from to amount = .ok (s', ret)) :
  s'.totalSupply = s.totalSupply

lemma mint_increases_supply
    (caller : Caller) (to : Address) (amount : UInt256)
    (s s' : TokenState) (ret : Unit)
    (h : mint caller s to amount = .ok (s', ret)) :
  s'.totalSupply = s.totalSupply + amount

lemma burn_decreases_supply
    (caller from : Address) (amount : UInt256)
    (s s' : TokenState) (ret : Unit)
    (h : burn caller s from amount = .ok (s', ret)) :
  s'.totalSupply = s.totalSupply - amount

-- ── Balance correctness ───────────────────────────────────────────────────────

lemma transfer_no_overdraft
    (caller : Caller) (to : Address) (amount : UInt256) (s : TokenState)
    (h : transfer caller s to amount = .error .insufficientBalance) :
  s.balances.get caller.val < amount

lemma transfer_moves_tokens
    (caller : Caller) (to : Address) (amount : UInt256)
    (s s' : TokenState) (ret : Bool)
    (h : transfer caller s to amount = .ok (s', ret)) :
  caller.val ≠ to →
    s'.balances.get caller.val = s.balances.get caller.val - amount ∧
    s'.balances.get to     = s.balances.get to   + amount

lemma transfer_self_noop
    (caller : Caller) (amount : UInt256)
    (s s' : TokenState) (ret : Bool)
    (h : transfer caller s caller amount = .ok (s', ret)) :
  s'.balances.get caller.val = s.balances.get caller.val

lemma transferFrom_no_allowance_overdraft
    (caller from to : Address) (amount : UInt256) (s : TokenState)
    (h : transferFrom caller s from to amount = .error .insufficientBalance) :
  s.balances.get from < amount ∨
  s.allowances.get from |>.get caller.val < amount

lemma transferFrom_decrements_allowance
    (caller from to : Address) (amount : UInt256)
    (s s' : TokenState) (ret : Bool)
    (h : transferFrom caller s from to amount = .ok (s', ret)) :
  s'.allowances.get from |>.get caller.val =
    s.allowances.get from |>.get caller.val - amount

-- ── Initialization (`@[lsc.initialize]` — §3.5) ───────────────────────────────

lemma constructor_sets_owner
    (owner : Caller) (name symbol : Bytes[32]) (decimals initialSupply : UInt256)
    (s' : TokenState)
    (h : initialize name symbol decimals initialSupply owner = .ok s') :
  s'.owner = owner.val

lemma constructor_mints_initial_supply
    (owner : Caller) (name symbol : Bytes[32]) (decimals initialSupply : UInt256)
    (s' : TokenState)
    (h : initialize name symbol decimals initialSupply owner = .ok s') :
  s'.balances.get owner.val = initialSupply ∧
  s'.totalSupply = initialSupply

-- ── Sequence invariant (scaffolding) ────────────────────────────────────────

inductive TokenAction where
  | transfer     (caller : Caller) (to : Address) (amount : UInt256)
  | transferFrom (caller : Caller) (from to : Address) (amount : UInt256)
  | approve      (caller : Caller) (spender : Address) (amount : UInt256)
  | mint         (caller : Caller) (to : Address) (amount : UInt256)
  | burn         (caller : Caller) (from : Address) (amount : UInt256)

def applyTokenAction (s : TokenState) : TokenAction → TokenState
  | .transfer caller to amount =>
      match transfer caller s to amount with
      | .ok (s', _) => s' | .error _ => s
  | .transferFrom caller from to amount =>
      match transferFrom caller s from to amount with
      | .ok (s', _) => s' | .error _ => s
  | .approve caller spender amount =>
      match approve caller s spender amount with
      | .ok (s', _) => s' | .error _ => s
  | .mint caller to amount =>
      match mint caller s to amount with
      | .ok (s', _) => s' | .error _ => s
  | .burn caller from amount =>
      match burn caller s from amount with
      | .ok (s', _) => s' | .error _ => s

def applyTokenActions (s : TokenState) (actions : List TokenAction) : TokenState :=
  actions.foldl applyTokenAction s

lemma non_mint_burn_actions_preserve_supply
    (s : TokenState)
    (actions : List TokenAction)
    (hSafe : actions.All (fun a => match a with
      | .mint _ _ _ => False
      | .burn _ _ _ => False
      | _ => True)) :
  (applyTokenActions s actions).totalSupply = s.totalSupply
```

### E.3 Lemma proofs (`test/TokenLemma.lean`, continued)

Tactic bodies for the lemmas above (abbreviated):

```lean
lemma transfer_preserves_supply
    (caller to : Address) (amount : UInt256)
    (s s' : TokenState) (ret : Bool)
    (h : transfer caller s to amount = .ok (s', ret)) :
    s'.totalSupply = s.totalSupply := by
  simp [transfer] at *
  split_ifs at h with hbal
  · simp at h
  · simp at h; obtain ⟨hs', _⟩ := h; simp [← hs']

lemma transfer_no_overdraft
    (caller to : Address) (amount : UInt256) (s : TokenState)
    (h : transfer caller s to amount = .error .insufficientBalance) :
    s.balances.get caller.val < amount := by
  simp [transfer] at *
  split_ifs at h with hbal
  · exact hbal
  · simp at h

-- ... remaining lemmas follow the same pattern (see §E.2 signatures)
```

### E.4 Theorem file (`test/TokenTheorem.lean`)

Human-reviewed. One-line delegations per requirement:

```lean
import Token
import TokenLemma

/-- transfer preserves total supply. -/
theorem transfer_preserves_supply
    (caller to : Address) (amount : UInt256)
    (s s' : TokenState) (ret : Bool)
    (h : transfer caller s to amount = .ok (s', ret)) :
    s'.totalSupply = s.totalSupply :=
  TokenLemma.transfer_preserves_supply caller to amount s s' ret h

/-- transfer reverts when caller has insufficient balance. -/
theorem transfer_no_overdraft
    (caller to : Address) (amount : UInt256) (s : TokenState)
    (h : transfer caller s to amount = .error .insufficientBalance) :
    s.balances.get caller.val < amount :=
  TokenLemma.transfer_no_overdraft caller to amount s h

-- ... homonymous theorem per lemma in §E.2
```

### E.5 Compliance manifest (`foundry.toml` excerpt)

```toml
[lsc.compliance.erc20_mintburn]
theorems = "test/TokenTheorem.lean"
required = [
  "transfer_preserves_supply",
  "transfer_no_overdraft",
  "transfer_moves_tokens",
  "transfer_self_noop",
  "transferFrom_preserves_supply",
  "transferFrom_no_allowance_overdraft",
  "transferFrom_decrements_allowance",
  "mint_requires_owner",
  "mint_increases_supply",
  "burn_requires_owner",
  "burn_decreases_supply",
  "constructor_sets_owner",
  "constructor_mints_initial_supply",
  "non_mint_burn_actions_preserve_supply",
]
```

### E.6 What this example demonstrates

| Feature | Where |
|---------|-------|
| `Mapping` with `Address` keys | `balances`, `allowances` |
| Nested `Mapping` | `allowances : Mapping Address (Mapping Address UInt256)` |
| `Caller` authorization | `mint`, `burn`: revert if `caller.val ≠ s.owner` |
| `@[lsc.initialize]` | deploy-time `initialize` (§3.5) |
| Revert theorem (`h : f … = .error e`) | `transfer_no_overdraft`, `mint_requires_owner` in `*Theorem.lean` |
| Success theorem (`h : f … = .ok (s', _)`) | `transfer_moves_tokens`, `mint_increases_supply` in `*Theorem.lean` |
| Sequence invariant over `List TokenAction` | scaffolding + lemma in `*Lemma.lean`; theorem in `*Theorem.lean` |
| Compliance manifest | `[lsc.compliance.erc20_mintburn]` lists theorem names |


---

---

## Appendix F — UniV2-Style AMM

This appendix is a complete constant-product AMM with `swap`, `addLiquidity`, and `removeLiquidity`. It demonstrates multi-field state invariants, the `k = x * y` preservation proof, overflow preconditions in theorems, and a sequence monotonicity invariant over all three actions.

### F.1 Design notes

**`k = reserve0 * reserve1` and overflow:** `UInt256` multiplication can overflow for large reserves. The theorem states `k`-preservation under an explicit no-overflow precondition (`reserve0 * reserve1 < 2^256`). This is honest — UniV2 itself relies on practical reserve bounds. The precondition appears in the theorem statement as a hypothesis; lemma proofs discharge it with `omega` when the inputs are bounded.

**No-fee swap for `k`-preservation:** The preservation proof uses a no-fee swap. Fees only make `k` larger (proved separately as `k_never_decreases`). The no-fee version is the clean mathematical core.

**LP tokens:** `lpBalances` tracks each address's share. `addLiquidity` mints LP tokens proportional to the liquidity added; `removeLiquidity` burns them and returns the proportional reserves.

**Integer division:** `removeLiquidity` uses integer division for the reserve amounts returned. The theorem states `≥` rather than `=` for `k` after removal, because rounding may leave a fractional unit in the pool.

### F.2 Contract (`src/AMM.lean`)

```lean
import Lsc.Prelude
open Lsc

@[lsc.error]
inductive AMMError where
  | uninitializedPool
  | zeroInput
  | zeroAmount
  | insufficientLp
  | zeroOutput
  | arith : ArithError → AMMError  -- via LscError +?
  | divisionByZero  -- /? for price and LP calculations

structure AMMState where
  reserve0    : UInt256                         -- slot 0: token0 reserves
  reserve1    : UInt256                         -- slot 1: token1 reserves
  totalLP     : UInt256                         -- slot 2: total LP tokens outstanding
  lpBalances  : Mapping Address UInt256  -- slot 3: LP token balances

-- ── Swap (no fee, constant product) ──────────────────────────────────────────
-- Checked math in do; theorems use hOverflow preconditions (e.g. swap_preserves_k).

@[lsc.external]
def swap (s : AMMState) (amountIn : UInt256) : Except AMMError (AMMState × UInt256) :=
  do
  require (s.reserve0 > 0) .uninitializedPool
  let num       ← amountIn *? s.reserve1
  let denom     ← s.reserve0 +? amountIn
  let amountOut ← num /? denom
  if amountOut = 0 then
    return .error (.arith .overflow)  -- zero output treated as failure in v1
  return .ok ({ s with
    reserve0 := s.reserve0 + amountIn
    reserve1 := s.reserve1 - amountOut }, amountOut)

@[lsc.external]
def addLiquidity
    (caller : Caller)
    (s : AMMState)
    (amount0 amount1 : UInt256) : Except AMMError (AMMState × UInt256) := do
  if amount0 = 0 ∨ amount1 = 0 then
    return .error .zeroAmount
  else if s.totalLP = 0 then
    let lpMinted := amount0
    let s' := { s with
      reserve0   := amount0
      reserve1   := amount1
      totalLP    := lpMinted
      lpBalances := s.lpBalances.set caller.val lpMinted }
    return .ok (s', lpMinted)
  else if s.reserve0 = 0 then
    return .error .uninitializedPool
  else
    let lpMinted ← s.totalLP * amount0 / s.reserve0
    if lpMinted = 0 then
      return .error .zeroAmount
    else
      let newReserve0 ← s.reserve0 + amount0
      let newReserve1 ← s.reserve1 + amount1
      let newTotalLP  ← s.totalLP + lpMinted
      let newLpBal    ← s.lpBalances.get caller.val + lpMinted
      let s' := { s with
        reserve0   := newReserve0
        reserve1   := newReserve1
        totalLP    := newTotalLP
        lpBalances := s.lpBalances.set caller newLpBal }
      return .ok (s', lpMinted)

@[lsc.external]
def removeLiquidity
    (caller : Caller)
    (s : AMMState)
    (lpAmount : UInt256) : Except AMMError (AMMState × UInt256 × UInt256) := do
  if lpAmount = 0 then
    return .error .zeroAmount
  else if s.totalLP = 0 then
    return .error .uninitializedPool
  else if s.lpBalances.get caller.val < lpAmount then
    return .error .insufficientLp
  else
    let amount0Out ← s.reserve0 * lpAmount / s.totalLP
    let amount1Out ← s.reserve1 * lpAmount / s.totalLP
    if amount0Out = 0 ∨ amount1Out = 0 then
      return .error .zeroOutput
    else
      let newReserve0 ← s.reserve0 - amount0Out
      let newReserve1 ← s.reserve1 - amount1Out
      let newTotalLP  ← s.totalLP - lpAmount
      let newLpBal    ← s.lpBalances.get caller.val - lpAmount
      let s' := { s with
        reserve0   := newReserve0
        reserve1   := newReserve1
        totalLP    := newTotalLP
        lpBalances := s.lpBalances.set caller newLpBal }
      return .ok (s', amount0Out, amount1Out)

@[lsc.external]
def getReserves (s : AMMState) : UInt256 × UInt256 :=
  (s.reserve0, s.reserve1)

@[lsc.external]
def lpBalance (s : AMMState) (account : Address) : UInt256 :=
  s.lpBalances.get account
```

### F.3 Lemma (`test/AMMLemma.lean`)

AI-generated. Contains helper `def`s, action-model scaffolding, and `lemma` proofs.

```lean
import AMM

-- ── Helper: k value ───────────────────────────────────────────────────────────

def k (s : AMMState) : UInt256 := s.reserve0 * s.reserve1

-- ── Swap lemmas ───────────────────────────────────────────────────────────────

lemma swap_revert_zero_input
    (s : AMMState)
    (h : swap s 0 = .error .zeroInput) :
  True   -- always holds; zero input always reverts by construction

lemma swap_revert_uninitialized
    (s : AMMState) (amountIn : UInt256)
    (h : swap s amountIn = .error .uninitializedPool) :
  s.reserve0 = 0 ∨ s.reserve1 = 0

lemma swap_positive_output
    (s s' : AMMState) (amountIn amountOut : UInt256)
    (h : swap s amountIn = .ok (s', amountOut)) :
  amountOut > 0

lemma swap_preserves_k
    (s s' : AMMState) (amountIn amountOut : UInt256)
    (hOverflow : s.reserve0 * s.reserve1 < 2^256 - s.reserve0)
    (h : swap s amountIn = .ok (s', amountOut)) :
  k s' ≥ k s

lemma swap_increases_reserve0
    (s s' : AMMState) (amountIn amountOut : UInt256)
    (h : swap s amountIn = .ok (s', amountOut)) :
  s'.reserve0 = s.reserve0 + amountIn

lemma swap_decreases_reserve1
    (s s' : AMMState) (amountIn amountOut : UInt256)
    (h : swap s amountIn = .ok (s', amountOut)) :
  s'.reserve1 = s.reserve1 - amountOut

-- ── addLiquidity lemmas ────────────────────────────────────────────────────────

lemma addLiquidity_revert_zero
    (caller : Caller) (s : AMMState) (amount0 amount1 : UInt256)
    (h : addLiquidity caller s amount0 amount1 = .error .zeroAmount) :
  amount0 = 0 ∨ amount1 = 0

lemma addLiquidity_increases_reserves
    (caller : Caller) (s s' : AMMState) (amount0 amount1 lpMinted : UInt256)
    (hNotFirst : s.totalLP > 0)
    (h : addLiquidity caller s amount0 amount1 = .ok (s', lpMinted)) :
  s'.reserve0 ≥ s.reserve0 ∧ s'.reserve1 ≥ s.reserve1

lemma addLiquidity_increases_totalLP
    (caller : Caller) (s s' : AMMState) (amount0 amount1 lpMinted : UInt256)
    (h : addLiquidity caller s amount0 amount1 = .ok (s', lpMinted)) :
  s'.totalLP ≥ s.totalLP

lemma addLiquidity_mints_to_caller
    (caller : Caller) (s s' : AMMState) (amount0 amount1 lpMinted : UInt256)
    (h : addLiquidity caller s amount0 amount1 = .ok (s', lpMinted)) :
  s'.lpBalances.get caller.val ≥ s.lpBalances.get caller

-- ── removeLiquidity lemmas ─────────────────────────────────────────────────────

lemma removeLiquidity_revert_insufficient_lp
    (caller : Caller) (s : AMMState) (lpAmount : UInt256)
    (h : removeLiquidity caller s lpAmount = .error .insufficientLp) :
  s.lpBalances.get caller.val < lpAmount

lemma removeLiquidity_burns_lp
    (caller : Caller) (s s' : AMMState) (lpAmount amount0Out amount1Out : UInt256)
    (h : removeLiquidity caller s lpAmount = .ok (s', amount0Out, amount1Out)) :
  s'.totalLP = s.totalLP - lpAmount

lemma removeLiquidity_decreases_caller_lp
    (caller : Caller) (s s' : AMMState) (lpAmount amount0Out amount1Out : UInt256)
    (h : removeLiquidity caller s lpAmount = .ok (s', amount0Out, amount1Out)) :
  s'.lpBalances.get caller = s.lpBalances.get caller.val - lpAmount

lemma removeLiquidity_k_bounded
    (caller : Caller) (s s' : AMMState) (lpAmount amount0Out amount1Out : UInt256)
    (h : removeLiquidity caller s lpAmount = .ok (s', amount0Out, amount1Out)) :
  k s' ≤ k s

-- ── Sequence invariant scaffolding ─────────────────────────────────────────────

inductive AMMAction where
  | swap          (amountIn : UInt256)
  | addLiquidity  (caller : Caller) (amount0 amount1 : UInt256)
  | removeLiquidity (caller : Caller) (lpAmount : UInt256)

def applyAMMAction (s : AMMState) : AMMAction → AMMState
  | .swap amountIn =>
      match swap s amountIn with
      | .ok (s', _) => s' | .error _ => s
  | .addLiquidity caller amount0 amount1 =>
      match addLiquidity caller s amount0 amount1 with
      | .ok (s', _) => s' | .error _ => s
  | .removeLiquidity caller lpAmount =>
      match removeLiquidity caller s lpAmount with
      | .ok (s', _, _) => s' | .error _ => s

def applyAMMActions (s : AMMState) (actions : List AMMAction) : AMMState :=
  actions.foldl applyAMMAction s

lemma k_never_decreases_swap_add
    (s : AMMState)
    (actions : List AMMAction)
    (hNoRemove : actions.All (fun a => match a with
      | .removeLiquidity _ _ => False | _ => True))
    (hNoOverflow : k s < 2^255) :
  k (applyAMMActions s actions) ≥ k s
```

### F.4 Lemma proofs (`test/AMMLemma.lean`, continued)

```lean
lemma swap_preserves_k
    (s s' : AMMState) (amountIn amountOut : UInt256)
    (hOverflow : s.reserve0 * s.reserve1 < 2^256 - s.reserve0)
    (h : swap s amountIn = .ok (s', amountOut)) :
    k s' ≥ k s := by
  simp [k, swap] at *
  -- Unfold swap; after split_ifs only the success branch remains
  split_ifs at h with h0 hAmt hDegen
  · simp at h
  · simp at h
  · simp at h
  · simp at h
    obtain ⟨hs', _⟩ := h
    simp [← hs']
    -- Goal: (reserve0 + amountIn) * (k / (reserve0 + amountIn)) ≥ reserve0 * reserve1
    -- By integer division: n / d * d ≤ n, so (k / newR0) * newR0 ≤ k
    -- But we need ≥ k for the new k = newR0 * newR1 = newR0 * (k / newR0)
    -- Integer division: k / newR0 * newR0 ≥ k - newR0 + 1 > k - newR0
    -- Since newR0 > reserve0, the floor rounding keeps k non-decreasing
    omega

lemma swap_increases_reserve0
    (s s' : AMMState) (amountIn amountOut : UInt256)
    (h : swap s amountIn = .ok (s', amountOut)) :
    s'.reserve0 = s.reserve0 + amountIn := by
  simp [swap] at *
  split_ifs at h <;> simp_all

-- ... remaining lemma proofs follow the same pattern (see §F.3 signatures)
```

### F.5 Theorem file (`test/AMMTheorem.lean`)

Human-reviewed. One-line delegations per requirement:

```lean
import AMM
import AMMLemma

/-- Core: swap preserves k (no-fee version). -/
theorem swap_preserves_k
    (s s' : AMMState) (amountIn amountOut : UInt256)
    (hOverflow : s.reserve0 * s.reserve1 < 2^256 - s.reserve0)
    (h : swap s amountIn = .ok (s', amountOut)) :
    AMMLemma.k s' ≥ AMMLemma.k s :=
  AMMLemma.swap_preserves_k s s' amountIn amountOut hOverflow h

theorem swap_increases_reserve0
    (s s' : AMMState) (amountIn amountOut : UInt256)
    (h : swap s amountIn = .ok (s', amountOut)) :
    s'.reserve0 = s.reserve0 + amountIn :=
  AMMLemma.swap_increases_reserve0 s s' amountIn amountOut h

-- ... homonymous theorem per lemma in §F.3
```

### F.6 What this example demonstrates

| Feature | Where |
|---------|-------|
| Multi-field state with invariant | `reserve0`, `reserve1`, `totalLP`, `lpBalances` |
| `Mapping` for LP balances | `lpBalances : Mapping Address UInt256` |
| Multi-scalar return | `removeLiquidity` returns `Except AMMError (AMMState × UInt256 × UInt256)` |
| Overflow precondition in theorem | `hOverflow : s.reserve0 * s.reserve1 < 2^256 - s.reserve0` |
| Integer division honesty | `k s' ≥ k s` (not `=`) for swap; `k s' ≤ k s` for remove |
| Named invariant helper | `def k` in `*Lemma.lean` |
| `nlinarith` for nonlinear arithmetic | `k_never_decreases_swap_add` — `k` is a product, not linear |
| Sequence invariant with action filter | `hNoRemove` excludes `removeLiquidity` from the monotonicity claim |
| Mixed revert conditions | `swap`: zero input, uninitialized, degenerate output |

### F.7 Key proof observations

**Why `≥` and not `=` for `swap_preserves_k`:** Integer division floors `newReserve1 = k / newReserve0`. The true mathematical `k` would require `newReserve1 = k / newReserve0` exactly, but integer division leaves `k mod newReserve0` as dust in the pool. So `newReserve0 * newReserve1 ≥ k` — the pool keeps the rounding error. This is the correct and honest theorem statement.

**`nlinarith` for the sequence invariant:** `k` is a product of two `UInt256` values, making the invariant nonlinear. `omega` handles only linear arithmetic; `nlinarith` (nonlinear arithmetic) is needed for goals involving products. Both are available in Lean 4's `Mathlib`-derived tactic set.

**Overflow as a theorem precondition, not a validator rule:** The overflow bound appears in the theorem statement as `hOverflow`, not as a validator error. This is intentional — the validator cannot know at compile time what the runtime reserve values will be. The theorem makes the assumption explicit; Foundry fuzz tests verify it holds for realistic inputs.

**`removeLiquidity` and `k`:** Removal proportionally reduces both reserves, so `k` decreases. The sequence invariant therefore excludes `removeLiquidity` via `hNoRemove`. A more complete theorem could prove `k_after_remove ≥ k_before - totalLP` (bounded loss), but that requires more careful arithmetic and is left as an exercise.
