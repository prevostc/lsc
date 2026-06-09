# LSC — Lean Smart Contracts Specification

**Language version:** LSC 0.1 (in-progress)
**Lean baseline:** `leanprover/lean4:stable` (pinned per project)
**Companion document:** [lsc-toolchain.md](lsc-toolchain.md) — compiler, Foundry integration, project layout

---

## §1 Overview

**LSC** is a Lean 4 dialect for writing smart contracts whose correctness properties are machine-checked by the Lean kernel before deployment.

Authors write **stateful monadic functions** (`ContractM E S α`) over a simulated `World`. The macro layer (`state!`, `contract!`, `error!`) generates the boilerplate. Proof files use `runS` to reduce contract functions to pure state transitions and prove properties with `simp` + `omega`.

### §1.1 The three modules

| File | Role | Kernel-checked |
|---|---|---|
| `src/Counter.lean` | Contract — `state!` + `contract!` + `@[lsc.external]` functions | Yes (types) |
| `test/CounterLemma.lean` | Lemmas — tactic proofs | Yes (full proof check) |
| `test/CounterTheorem.lean` | Theorems — requirements, one-line lemma delegations | Yes (full proof check) |

The **contract** deploys. The **theorem** file is the human-reviewed requirements document. Each `theorem` states a readable property and delegates to a homonymous proof in `*Lemma.lean`. The Lean kernel checks both.

### §1.2 End-to-end Counter example

`src/Counter.lean`:
```lean4
import Lsc.Prelude
open Lsc

error! CounterError where
  | IsPausedError
  | arith : ArithError → CounterError

state! Counter where
  number : UInt256 @public
  paused : Bool

contract! Counter CounterError

@[lsc.external]
def pause : Counter Unit := do
  set .paused true

@[lsc.external]
def unpause : Counter Unit := do
  set .paused false

@[lsc.external]
def increment : Counter Unit := do
  failWhen (← get .paused) .IsPausedError
  let n ← get .number
  let n' ← n +? 1
  set .number n'
```

`test/CounterTheorem.lean`:
```lean4
import Counter
import CounterLemma
import Lsc.Prelude

open Lsc

/-- When unpaused, increment increases `number` by exactly 1. -/
theorem increment_increases_number_when_unpaused (s s' : Counter.State) (hp : ¬s.paused)
    (h : runS increment s = .ok ((), s')) :
    s'.number.val = s.number.val + 1 ∧ s'.paused = s.paused :=
  CounterLemma.increment_increases_number_when_unpaused s s' hp h

/-- When paused, increment reverts with `.IsPausedError`. -/
theorem increment_reverts_when_paused (s : Counter.State) (hp : s.paused) :
    runS increment s = .error (.contract .IsPausedError) :=
  CounterLemma.increment_errors_when_paused s hp
```

`test/CounterLemma.lean`:
```lean4
import Counter
import Lsc.Prelude

open Lsc

namespace CounterLemma

theorem increment_increases_number_when_unpaused
    (s s' : Counter.State) (hp : ¬s.paused)
    (h : runS increment s = .ok ((), s')) :
    s'.number.val = s.number.val + 1 ∧ s'.paused = s.paused := by
  by_cases hlt : s.number.val + 1 < 2 ^ 256
  · simp [runS, increment, failWhen, hp, UInt256.addCheckedNat, dif_pos hlt] at h
    subst h
    exact ⟨rfl, (Bool.not_iff_eq_false).mp hp |>.symm⟩
  · exfalso
    simp [runS, increment, failWhen, hp, UInt256.addCheckedNat, dif_neg hlt,
          ContractM.arithFail] at h

theorem increment_errors_when_paused
    (s : Counter.State) (hp : s.paused) :
    runS increment s = .error (.contract .IsPausedError) := by
  have hpt : s.paused = true := hp
  simp [runS, increment, failWhen, hpt, ContractM.revert, ContractM.revertFail]

end CounterLemma
```

---

## PART I — THE CONTRACT LANGUAGE

---

## §2 Types

### §2.1 Primitive types

| LSC type | Lean definition | Notes |
|---|---|---|
| `UInt256` | `{ n : Nat // n < 2^256 }` | Bounded; no plain `+ - * /` — use `+?` |
| `Address` | `structure Address where val : UInt256` | Not coercible to `UInt256` without `.val` |
| `Bool` | Lean built-in | |

#### Arithmetic semantics

`UInt256` does **not** have `Add`/`Mul` instances. Plain `+ - * /` on `UInt256` are a **type error** in contract code.

| Mode | Syntax | Returns | Use when |
|---|---|---|---|
| Checked with `UInt256` | `a +? b` | `ContractM E S UInt256` | default — overflow reverts |
| Checked with `Nat` literal | `a +? 1` | `ContractM E S UInt256` | adding constants |

Only `+?` is implemented. `-?`, `*?`, `/?` are planned.

**Comparisons:** `=`, `≤`, `≥`, `<`, `>` on `UInt256` compare via `.val`.

**`UInt256` definitions:**

```lean4
-- Lsc.UInt256
abbrev UInt256 := { n : Nat // n < 2 ^ 256 }

namespace UInt256
def val   (a : UInt256) : Nat := a.1
def zero  : UInt256 := ⟨0, by decide⟩
def one   : UInt256 := ⟨1, by decide⟩
def max   : UInt256 := ⟨2^256 - 1, by omega⟩

@[simp] theorem eq_iff  {a b : UInt256} : a = b ↔ a.val = b.val
@[simp] theorem le_iff  {a b : UInt256} : a ≤ b ↔ a.val ≤ b.val
@[simp] theorem lt_iff  {a b : UInt256} : a < b ↔ a.val < b.val

/-- Proof-side literal add. Not for contract code. -/
def addNat (a : UInt256) (n : Nat) (h : a.val + n < 2^256) : UInt256
end UInt256
```

#### The `+?` operator family (checked, in `ContractM`)

```lean4
-- Lsc.CheckedArith
def UInt256.addChecked {E S} (a b : UInt256) : ContractM E S UInt256
def UInt256.addCheckedNat {E S} (a : UInt256) (n : Nat) : ContractM E S UInt256

macro a:term " +? " n:num  : term => `(UInt256.addCheckedNat $a $n)
macro a:term " +? " b:term : term => `(UInt256.addChecked $a $b)
```

Both revert with `.arith .overflow` on overflow.

**Proof recipe:** unfold with `simp [runS, f, UInt256.addCheckedNat, dif_pos hlt]` for the success case; use `dif_neg hlt` + `ContractM.arithFail` to discharge the error case. `omega` closes the linear goals.

### §2.2 `Address`

```lean4
-- Lsc.World
structure Address where
  val : UInt256
  deriving Repr, DecidableEq

def Address.zero : Address := ⟨UInt256.zero⟩
```

### §2.3 `World`

`World` is the simulated chain state. Contract functions thread `World` implicitly via `ContractM`.

```lean4
-- Lsc.World
structure World where
  storage : Address → Nat → UInt256
  balance : Address → UInt256
  code    : Address → ByteArray

namespace World
def empty : World
def getStorage (w : World) (addr : Address) (slot : Nat) : UInt256
def setStorage (w : World) (addr : Address) (slot : Nat) (v : UInt256) : World

@[simp] theorem getStorage_setStorage     -- same slot: reads back
@[simp] theorem getStorage_setStorage_ne  -- different slot: unchanged
end World
```

### §2.4 `ContractM`

`ContractM E S α` is the contract monad. It threads a `World` and can revert with a `ContractError E`.

```lean4
-- Lsc.ContractM
abbrev ContractM (E S α : Type) :=
  StateT World (Except (ContractError E)) α
```

`S` is a phantom type parameter that pins the `ContractState` instance, keeping `Counter` distinct from `Vault` etc.

**Running a contract function:**

```lean4
-- Lsc.Run
def runS {E S α : Type} [ContractState S] (f : ContractM E S α) (s : S) :
    Except (ContractError E) (α × S)
```

`runS` embeds `s` into `World.empty`, applies `f`, then projects back via `ContractState.view`.

**Key `@[simp]` lemmas:**

```lean4
-- ContractM.pure_apply
(pure a : ContractM E S α) w = .ok (a, w)

-- ContractM.bind_apply
(m >>= f) w = match m w with | .ok (a, w') => f a w' | .error e => .error e
```

### §2.5 Error types and `LscError`

```lean4
-- Lsc.Error
inductive ArithError where
  | overflow
  | divisionByZero
  deriving DecidableEq, Repr

inductive ContractError (E : Type) where
  | contract : E → ContractError E
  | arith    : ArithError → ContractError E
  deriving Repr

class LscError (E : Type) where
  arith : ArithError → E

instance : LscError ArithError where arith := id
```

The `LscError` typeclass lets `+?` inject arithmetic faults into any `ContractM E S` without an explicit lift at every call site.

---

## §3 State

### §3.1 The `state!` macro

Contract state is declared with **`state!`**. The macro name is `state! ModName where ...` — the module name is explicit.

```lean4
state! Counter where
  number : UInt256 @public
  paused : Bool
```

The `state!` macro generates:

1. **`Counter.State` struct** — one field per declaration:
   ```lean4
   structure Counter.State where
     number : UInt256
     paused : Bool
   ```

2. **Field witnesses** in the `fields` namespace — offset-tagged typed witnesses:
   ```lean4
   @[simp] def fields.number : Lsc.Field Counter.State UInt256 := ⟨0⟩
   @[simp] def fields.paused : Lsc.Field Counter.State Bool     := ⟨1⟩
   ```

3. **`ContractState Counter.State` instance** — registers `self`, `view`, and `embed`:
   - `self` — executing contract address (defaults to `Lsc.defaultSelf`)
   - `view : World → Counter.State` — projects storage slots back to the struct
   - `embed : Counter.State → World → World` — writes struct fields into `World`

4. **`@[simp]` unfolding theorems** — `Counter.State.view_unfold` and `Counter.State.embed_unfold` let `simp` fully reduce `ContractState.view` / `ContractState.embed`.

5. **`@[lsc.public]` tag** on `fields.number` — marks it for ABI getter synthesis.

**`@public` fields** get an ABI getter synthesized by the emitter. The `@public` annotation appears after the type: `field : Type @public`.

### §3.2 The `contract!` macro

```lean4
contract! Counter CounterError
```

Generates:
- `abbrev Counter (α : Type) := ContractM CounterError Counter.State α`
- `@[simp] def Counter.view : World → Counter.State := ContractState.view`

The `Counter.view` function is used in **world-shaped theorems** (§9.2).

### §3.3 The `error!` macro

```lean4
error! CounterError where
  | IsPausedError
  | arith : ArithError → CounterError
```

Generates:
- `inductive CounterError` with the given constructors, `deriving DecidableEq, Repr`
- `instance : LscError CounterError where arith := .arith`
- `attribute [lsc.error] CounterError`

The `| arith : ArithError → E` constructor **must** be present — the macro errors otherwise.

### §3.4 `ContractState` and `Field`

```lean4
-- Lsc.ContractState
structure Field (S σ : Type) where
  offset : Nat
  deriving Repr, DecidableEq, BEq

class ContractState (S : Type) where
  self  : Address
  view  : World → S
  embed : S → World → World
```

`state!` registers the `ContractState` instance. `view` and `embed` are inverse for fields that were stored via `ContractM.set`.

### §3.5 Storage access: `get` and `set`

Contract functions access state via `get .field` and `set .field val`.

```lean4
-- ContractM.get — reads one slot via FromWord
@[simp] def ContractM.get {E S σ} [ContractState S] [FromWord σ] (field : Field S σ) :
    ContractM E S σ

-- ContractM.set — writes one slot via ToWord
@[simp] def ContractM.set {E S σ} [ContractState S] [ToWord σ] (field : Field S σ) (val : σ) :
    ContractM E S Unit
```

**Macro sugar:**

```lean4
-- In a do-block:
let n ← get .number        -- resolves to ContractM.get fields.number
set .number n'             -- resolves to ContractM.set fields.number n'
```

The dot-accessor macros resolve names through the `fields` namespace at elaboration time.

---

## §4 Functions

### §4.1 `@[lsc.external]`

Public ABI functions are tagged `@[lsc.external]`. The `def` name is the ABI function name.

```lean4
@[lsc.external]
def increment : Counter Unit := do
  failWhen (← get .paused) .IsPausedError
  let n ← get .number
  let n' ← n +? 1
  set .number n'
```

### §4.2 Guards

**`require cond err`** — revert when condition is false:

```lean4
-- desugars to: unless cond do ContractM.revert err
require (n > 0) .ZeroAmount
```

**`failWhen b err`** — revert when `Bool` is true:

```lean4
-- defined in Lsc.ContractM
def failWhen {E S} (b : Bool) (err : E) : ContractM E S Unit :=
  if b then ContractM.revert err else pure ()

-- usage:
failWhen (← get .paused) .IsPausedError
```

**`ContractM.revert err`** — unconditional revert:

```lean4
ContractM.revert .SomeError   -- : ContractM E S α
```

### §4.3 Return shapes

| Return shape | Meaning |
|---|---|
| `Counter Unit` | Mutator, no return value |
| `Counter α` | Mutator or view returning `α` |

Whether a function is a view is inferred by the emitter from whether it contains `set` calls.

---

## §5 Revert

`ContractM.revert e` produces `.error (.contract e)`. `ContractM.arithFail e` produces `.error (.arith e)`. On error, the `World` is simply not returned — the `Except` short-circuit discards any prior `setStorage` calls because `StateT` threads the world as a value, not in-place.

---

## PART II — THE PROOF SYSTEM

---

## §6 Proof Files

### §6.1 Lemma files (`test/*Lemma.lean`)

Lemma files are **AI-generated**. They contain:

- `theorem` proofs (naming convention: `*Lemma.lean` uses `theorem` inside a `namespace CounterLemma`)
- No `sorry`. Kernel-checked.

**Proof recipe:**

1. `simp [runS, functionName, ...]` to unfold the monad layers.
2. Use `dif_pos hlt` / `dif_neg hlt` for the `if h : a.val + n < 2^256` branches in `+?`.
3. `omega` closes linear arithmetic goals over `.val`.
4. `subst h` when `simp` reduces to an equality of state tuples.

**Example:**

```lean4
namespace CounterLemma

theorem increment_increases_number_when_unpaused
    (s s' : Counter.State) (hp : ¬s.paused)
    (h : runS increment s = .ok ((), s')) :
    s'.number.val = s.number.val + 1 ∧ s'.paused = s.paused := by
  by_cases hlt : s.number.val + 1 < 2 ^ 256
  · simp [runS, increment, failWhen, hp, UInt256.addCheckedNat, dif_pos hlt] at h
    subst h
    exact ⟨rfl, (Bool.not_iff_eq_false).mp hp |>.symm⟩
  · exfalso
    simp [runS, increment, failWhen, hp, UInt256.addCheckedNat, dif_neg hlt,
          ContractM.arithFail] at h

end CounterLemma
```

**Simp set for most contract proofs:** `[runS, functionName, failWhen, get, set, UInt256.addCheckedNat, dif_pos/dif_neg, ContractM.arithFail, ContractM.revert, ContractM.revertFail]`

### §6.2 Theorem files (`test/*Theorem.lean`)

Theorem files are the **requirements document** — written and reviewed by humans. Each `theorem`:

- States a readable business property inline
- Carries a docstring
- Delegates to the homonymous `CounterLemma.*` in exactly one line

```lean4
import Counter
import CounterLemma
import Lsc.Prelude

open Lsc

/-- When unpaused, increment increases `number` by exactly 1. -/
theorem increment_increases_number_when_unpaused (s s' : Counter.State) (hp : ¬s.paused)
    (h : runS increment s = .ok ((), s')) :
    s'.number.val = s.number.val + 1 ∧ s'.paused = s.paused :=
  CounterLemma.increment_increases_number_when_unpaused s s' hp h
```

### §6.3 Proof modes

Two proof modes depending on what the theorem quantifies over:

| Mode | State type | When |
|---|---|---|
| **State-shaped** (default) | `Counter.State` | Property mentions only this contract's fields |
| **World-shaped** | `World` | Property involves the raw world (e.g. low-level storage theorems) |

**State-shaped** — use `runS`:

```lean4
theorem pause_sets_paused (s s' : Counter.State) (h : runS pause s = .ok ((), s')) :
    s'.paused = true ∧ s'.number = s.number
```

**World-shaped** — thread `World` directly and project via `Contract.view`:

```lean4
theorem increment_increases_number_world_when_unpaused (w w' : World)
    (hp : ¬(Counter.view w).paused)
    (h : increment w = .ok ((), w')) :
    (Counter.view w').number.val = (Counter.view w).number.val + 1 ∧
    (Counter.view w').paused = (Counter.view w).paused
```

`Counter.view` is generated by `contract!` as `@[simp] def Counter.view := ContractState.view`.

### §6.4 Proof authorship

AI writes `*Lemma.lean`. Humans craft `*Theorem.lean`. The Lean kernel is the arbiter for both.

### §6.5 Naming conventions

- `{function}_{property}` for single-call: `increment_increases_number_when_unpaused`
- `{function}_{reverts/errors}_when_{condition}`: `increment_errors_when_paused`
- `{subject}_{invariant}` for sequence: `number_never_decreases`

---

## §7 Proof Helpers

### §7.1 Layer 1 — Pure (default)

Lemmas proved directly over `@[lsc.external]` functions using `simp` + `omega`.

**Simp lemma: `Bool.not_iff_eq_false`**

```lean4
-- Lsc.ContractM
@[simp] theorem Bool.not_iff_eq_false {b : Bool} : (¬b) ↔ (b = false)
```

This is needed when a `hp : ¬s.paused` hypothesis must be turned into `s.paused = false` for `simp` to discharge the `failWhen` guard.

### §7.2 `runS` simp lemmas

```lean4
-- Generated by state!
@[simp] Counter.State.view_unfold (w : World) : ContractState.view (S := Counter.State) w = ...
@[simp] Counter.State.embed_unfold (s : Counter.State) (w : World) : ContractState.embed s w = ...
@[simp] Counter.State.self_eq : ContractState.self (S := Counter.State) = defaultSelf
```

These let `simp [runS, ...]` fully reduce without needing to manually unfold class projections.

---

## §8 Validator

Runs as a post-elaboration pass. Hard errors abort compilation.

### §8.1 Contract module errors (partial — v0.1)

| Construct | Severity | Error |
|---|---|---|
| `+?` / `-?` on `UInt256` missing error type | error | type error at elaboration |
| `error!` type without `arith` constructor | error | `error!: 'E' must include '| arith : ArithError → E'` |
| `state!` field with invalid type | error | Lean type error |
| `sorry` in proof file | error | Lean kernel rejects |

### §8.2 Proof module rules

| Condition | Severity |
|---|---|
| `sorry` | error (Lean kernel) |
| `theorem` in `*Lemma.lean` without `CounterLemma` namespace | style warning |

---

## §9 Emitter (planned)

The emitter pipeline (Lean IR → Yul → bytecode) and ERC-7201 storage layout are **planned** for v1. Current state:

- `@[lsc.external]` and `@[lsc.public]` attributes are registered and drive codegen.
- `World.getStorage` / `World.setStorage` use sequential slot offsets (field declaration order, 0-indexed).
- ERC-7201 namespaced storage roots are **not yet computed** — the proof harness uses `defaultSelf = Address.zero` as the contract address and flat slot numbers.

For the current toolchain integration, see [lsc-toolchain.md](lsc-toolchain.md).

---

## Appendix A — Design Decisions

### A.1 Why `StateT World (Except E)` instead of a free monad

The spec originally described a free monad (`World E`). The implementation uses `StateT World (Except (ContractError E))` because:

- **Simpler proofs.** `StateT` `simp`s cleanly with `bind_apply` and `pure_apply`. Free monads require bridge lemmas to reduce `Free.roll` terms.
- **Direct `simp` reduction.** `runS f s` unfolds to pattern-matching on `Except` results, which `simp` + `omega` handles without extra scaffolding.
- **Rollback on error is free.** `Except` short-circuits; the `World` value is simply not returned on error paths — no explicit rollback logic needed.

The trade-off: `StateT` ties the monad to a single interpreter (proofs) rather than supporting multiple interpreters (EVM codegen, testing). For v0.1, one interpreter is sufficient.

### A.2 Why `state! ModName where` (not `state! where`)

The module name is explicit in `state! Counter where` rather than inferred from the file. This lets the macro generate unambiguous names (`Counter.State`, `fields.*`, `ContractState Counter.State`) without relying on the Lean elaboration environment knowing the current module name.

### A.3 Why `get`/`set` instead of `load`/`store`

`get`/`set` are shorter, unambiguous in a `do`-block context, and directly parallel the underlying `ContractM.get` / `ContractM.set` calls. `load`/`store` notation (with `store [ .field := val ]`) is aspirational syntax for v1.

### A.4 Why `runS` instead of `.run`

`runS` is a plain function call that is visually distinct from the field accessor syntax. `.run` as a method (e.g., `increment.run s`) requires `ContractM` to be a structure or namespace with a `run` projection — `runS` as a standalone function is simpler. The name may change in v1.
