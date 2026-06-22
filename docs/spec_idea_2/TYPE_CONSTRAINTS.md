# Type Constraints in LSC

> Field-level decorators that attach invariants to storage fields. Each decorator
> generates a named theorem and optionally inserts a runtime check. They are
> independent tools — use none, one, or several per field depending on what the
> field represents. They do not form a complete invariant system; they are
> conveniences for the most common field-level properties in DeFi.
>
> Read DESIGN.md §9 (Storage Model) and MATH.md before this document.

---

## Syntax

```lean
contract AMM where

  storage:
    @monotonic
    supplyIndex : Ray := RAY

    @min(0.0001)
    fee : Wad := 0.003

    @bounded(1, 10^24)
    reserve0 : Wad := 0

    @bounded(1, 10^24)
    reserve1 : Wad := 0

    @immutable
    token0 : Address

    @immutable
    token1 : Address

    paused : Bool  := false
    owner  : Address
```

Decorators sit on the line immediately above the field declaration. Multiple
decorators stack on one field. Undecorated fields have no generated theorems
and no runtime checks.

---

## `@monotonic`

### What it means

The field value can only increase over time. Every successful transaction either
leaves the field unchanged or increases it. It never decreases.

```lean
@monotonic
supplyIndex : Ray := RAY
```

### Generated theorem

```lean
theorem AMM.supplyIndex_monotonic
    (s s' : ContractState AMMStorage)
    (tx : AMM.AnyTx) (h : runS tx s = .ok ((), s', _)) :
    s.storage.supplyIndex ≤ s'.storage.supplyIndex
```

Available in all proof files that import the contract. No hypothesis needed.

### Runtime behavior

On every write to `supplyIndex`, the compiler inserts:

```lean
require (newValue ≥ storage.supplyIndex) else revert .ConstraintViolated
```

**Exception — static elimination**: if the write expression is structurally
monotone, the elaborator proves the check statically and emits no runtime code.
The canonical pattern that eliminates the runtime check:

```lean
-- write: multiply by a factor ≥ 1
storage.supplyIndex := storage.supplyIndex.rayMul growthFactor
-- if the elaborator can prove growthFactor ≥ RAY, no require is inserted
-- the check becomes a compile-time proof obligation instead
```

If the static proof fails, the runtime check is inserted and the elaborator
emits a warning: `note: could not eliminate @monotonic check on supplyIndex
statically; runtime check inserted.` This warning is informational — the
contract is still correct, just slightly more expensive.

### Proof ergonomics

The primary value is in `@math` theorems. Formulas that involve index values
typically require a monotonicity hypothesis to prove meaningful bounds. With
`@monotonic`, that hypothesis is free:

```lean
-- WITHOUT @monotonic: must thread hypothesis manually
theorem interestAccrued_nonneg
    (s s' : ContractState LendingStorage)
    (hmono : s.storage.supplyIndex ≤ s'.storage.supplyIndex) :  -- explicit
    interestAccrued s s' ≥ 0 := ...

-- WITH @monotonic: hypothesis is available from the theorem
theorem interestAccrued_nonneg
    (s s' : ContractState LendingStorage)
    (htx : runS accrueInterest s = .ok ((), s', _)) :
    interestAccrued s s' ≥ 0 := by
  -- LendingStorage.supplyIndex_monotonic htx gives the monotonicity fact
  have hmono := LendingStorage.supplyIndex_monotonic htx
  ...
```

### Gas cost

One `≤` comparison and a conditional revert per write, unless statically
eliminated. For `Ray` fields: approximately 3 opcodes.

---

## `@min(v)`

### What it means

The field value is always greater than or equal to `v`. Every write is checked.
The default value must satisfy the bound or the contract does not compile.

```lean
@min(0.0001)
fee : Wad := 0.003    -- 0.003 ≥ 0.0001 ✓
```

The bound `v` is written in **decoded units** matching the field type. For a
`Wad` field, `@min(0.0001)` means `raw ≥ 0.0001 * WAD`. For a `Ray` field,
`@min(1)` means `raw ≥ 1 * RAY`. The user never thinks about encoding.

### Generated theorem

```lean
theorem AMM.fee_min_bound
    (s : ContractState AMMStorage) :
    s.storage.fee ≥ wadLit 0.0001
```

This holds for **any** reachable state — not just after a specific transaction.
The theorem has no transaction hypothesis. It is an unconditional fact about
the storage type.

### Runtime behavior

```lean
require (newValue ≥ wadLit 0.0001) else revert .ConstraintViolated
```

Inserted on every write to `fee`. The bound is a compile-time constant, so
the comparison is against a literal — one `LT` opcode and a `JUMPI`.

### Compile-time enforcement on defaults

```lean
@min(0.005)
fee : Wad := 0.003    -- COMPILE ERROR: default 0.003 < min 0.005
```

The elaborator checks default values against all decorators at contract
definition time. This is a hard error, not a warning.

### Proof ergonomics

The primary use is providing lower bounds for `@math` faithfulness proofs.
Without `@min`, every faithfulness theorem needs an explicit `(h : 0 < fee)`
hypothesis. With `@min(0.0001)`, the theorem `fee_min_bound` is in scope and
`linarith` can close positivity goals automatically.

### Gas cost

One comparison and conditional revert per write. Approximately 3 opcodes.

---

## `@bounded(lo, hi)`

### What it means

The field value is always between `lo` and `hi` inclusive. Sugar for `@min(lo)`
plus `@max(hi)` but generates slightly cleaner theorems.

```lean
@bounded(1, 10^24)
reserve0 : Wad := 1
```

Both `lo` and `hi` are decoded literals in the field's unit. The default value
must satisfy both bounds.

### Generated theorems

```lean
-- individual bounds
theorem AMM.reserve0_lower : ∀ s, s.storage.reserve0 ≥ wadLit 1
theorem AMM.reserve0_upper : ∀ s, s.storage.reserve0 ≤ wadLit (10^24)

-- combined (most useful for @math proofs)
theorem AMM.reserve0_bounded :
    ∀ s, wadLit 1 ≤ s.storage.reserve0 ∧ s.storage.reserve0 ≤ wadLit (10^24)
```

### Runtime behavior

```lean
require (newValue ≥ wadLit 1)      else revert .ConstraintViolated
require (newValue ≤ wadLit (10^24)) else revert .ConstraintViolated
```

Both checks inserted on every write. Two comparisons total.

### The key use case: concrete ε in `@math` proofs

Without bounds, a faithfulness theorem for `computeOutput` can only say:

```lean
|decode out_impl - out_spec| ≤ (1 + MAX_UINT256) * WAD_ERROR
-- useless: this is a number larger than the observable universe
```

With `@bounded(1, 10^24)` on both reserves:

```lean
|decode out_impl - out_spec| ≤ (1 + wadLit (10^24)) * WAD_ERROR
-- = (10^24 + 1) * 10^-18 = 10^6 + 10^-18 ≈ 10^6
-- concrete, meaningful, derivable by norm_num
```

The elaborator automatically threads `reserve0_bounded` and `reserve1_bounded`
into `@math` faithfulness proof obligations when those fields appear in the
function body. The user does not pass these as explicit hypotheses.

### Choosing bounds

Bounds should reflect protocol design constraints, not type limits. Do not
write `@bounded(0, MAX_UINT256)` — that is the same as no bound and produces
a useless ε.

Good bounds come from protocol documentation:
- What is the minimum meaningful reserve size? (`@bounded(10^6, ...)` for a
  pool that requires $1 minimum liquidity)
- What is the maximum position size the protocol accepts? (`@bounded(..., 10^15)`
  from a MAX_DEBT constant)
- What fee range is governance allowed to set? (`@bounded(0.0001, 0.01)` for
  1bp to 100bp)

### Gas cost

Two comparisons and two conditional reverts per write. Approximately 6 opcodes.

---

## `@immutable`

### What it means

The field is set once (at deployment via the constructor or default value) and
never changes. Writes outside the constructor are a **compile error**.

```lean
@immutable
token0 : Address

@immutable
token1 : Address

@immutable
factory : Address
```

### Generated theorem

```lean
theorem AMM.token0_immutable
    (s s' : ContractState AMMStorage)
    (tx : AMM.AnyTx) (h : runS tx s = .ok ((), s', _)) :
    s'.storage.token0 = s.storage.token0
```

### Compile-time enforcement

```lean
def setToken (newToken : Address) : Tx := do
  storage.token0 := newToken   -- COMPILE ERROR: token0 is @immutable
```

This is a hard compile error at the write site, reported with source position.
Not a runtime revert — the program does not compile.

### No runtime cost

`@immutable` generates **zero bytecode**. The invariant is enforced entirely
at compile time. This is the only decorator with zero gas cost.

### Proof ergonomics

`token0_immutable` eliminates an entire class of hypotheses from multi-step
theorems. Any theorem that reasons about two states `s` and `s'` can use
`token0_immutable` to rewrite `s'.storage.token0` as `s.storage.token0`:

```lean
-- without @immutable: must carry equality hypothesis
theorem AMM.swap_uses_correct_token
    (s s' : ContractState AMMStorage)
    (htoken : s'.storage.token0 = s.storage.token0)  -- explicit
    ...

-- with @immutable: rewrite for free
theorem AMM.swap_uses_correct_token
    (s s' : ContractState AMMStorage)
    (htx : runS swap s = .ok ((), s', _)) :
    s'.storage.token0 = EXPECTED_TOKEN := by
  rw [AMM.token0_immutable htx]  -- one line
  ...
```

### `@immutable` with no default

If a field is `@immutable` and has no default, it must be set by the
constructor. The elaborator enforces this: an `@immutable` field with no
default and no constructor write is a compile error.

```lean
@immutable
token0 : Address        -- no default: must be set in constructor

constructor (t0 t1 : Address) : Tx := do
  storage.token0 := t0  -- valid: constructor is the one allowed write site
  storage.token1 := t1
```

---

## Stacking Decorators

Multiple decorators on one field are allowed and compose independently.

```lean
@monotonic @bounded(RAY, 10^9 * RAY)
supplyIndex : Ray := RAY
```

This generates:
- `supplyIndex_monotonic` theorem
- `supplyIndex_lower` theorem (`≥ RAY`)
- `supplyIndex_upper` theorem (`≤ 10^9 * RAY`)
- `supplyIndex_bounded` combined theorem
- Runtime: monotonicity check + two bound checks on every write

Useful combinations:

| Pattern | Combination | Meaning |
|---|---|---|
| Lending index | `@monotonic @bounded(RAY, MAX_INDEX)` | grows, stays sane |
| Protocol fee | `@bounded(MIN_FEE, MAX_FEE)` | governance range |
| Pool addresses | `@immutable` | set at deployment, never change |
| Collateral ratio | `@bounded(1.0, 2.0)` | always overcollateralized |
| Discount factor | `@bounded(0, RAY) @antitone` | decreases, stays in [0,1] |

---

## What Type Constraints Do Not Do

**No cross-field constraints.** `reserve0 * reserve1 ≥ K` is not expressible
as a field decorator. That is a contract-level theorem you write manually.

**No dynamic bounds.** `@min(storage.otherField)` is not allowed. Bounds are
literals only. If your min depends on another field, write a manual `require`.

**No mapping fields.** Decorators apply to scalar storage fields only.
`balances : Mapping Address Wad` cannot be decorated.

**No conditional constraints.** There is no `@monotonic_when(condition)`.
If monotonicity only holds under certain conditions, write the theorem manually.

**No proof of preservation.** Decorators do not prove their theorems for you.
The theorems follow directly from the runtime checks (or compile-time
restrictions for `@immutable`) — those proofs are generated by the framework.
What you still prove manually are theorems *about* the contract that *use*
these as lemmas.

---

## Implementation Notes for Developers

Each decorator is handled in the elaboration pass (`Lang/Contract.lean`), not
in `macro_rules`. The elaboration pass:

1. Reads the decorator list for each storage field
2. For `@monotonic`, `@min`, `@bounded`: injects `Stmt.require` nodes into
   the body of every `Tx` that writes the decorated field, immediately after
   the write statement
3. For `@immutable`: scans all non-constructor `Tx` bodies for writes to the
   field and reports a compile error with `Lean.logErrorAt` if found
4. For all decorators: generates the named theorem statements and registers
   them as `sorry`-free theorems proved directly from the inserted `require`
   structure

The generated theorems are proved by the framework, not by the user. They
follow mechanically from the structure of the inserted checks. A user should
never see a `sorry` in a decorator-generated theorem.

Decorator values (the `v` in `@min(v)`, `lo`/`hi` in `@bounded(lo, hi)`) are
parsed as source-level numeric literals in the field's decoded unit and
converted to raw `UInt256` values (`v * WAD` for `Wad` fields, `v * RAY` for
`Ray` fields) during elaboration.