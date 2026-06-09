# LSC — Lean Smart Contracts Language Specification

**Language version:** LSC 1.0
**Lean baseline:** `leanprover/lean4:stable` (pinned per project)
**Execution target:** EVM (bytecode via formally-verified lowering; standard JSON ABI)
**Companion document:** [lsc-toolchain.md](lsc-toolchain.md) — reference compiler, Foundry integration, artifacts, demos

---

## §1 Overview

### §1.1 What LSC is

**LSC (Lean Smart Contracts)** is a strict subset of Lean 4 for writing smart contracts whose correctness properties are machine-checked by the Lean kernel before deployment.

Authors write **functions over a free monad** (`World E`) that describes storage access, external calls, and errors. The compiler generates everything the EVM needs — ABI wrappers, `SLOAD`/`SSTORE` opcodes, `LOG` opcodes, `CALL` lowering. Authors never touch raw EVM opcodes, ABI encoding, or storage slot numbers directly.

Contract state is declared with the **`state!` macro**. The resulting struct (`Counter.State`, `AMM.State`, …) is a **schema** — it declares what the contract owns and determines storage layout. Layout uses **[ERC-7201](https://eips.ethereum.org/EIPS/eip-7201) namespaced storage** by default (§3.3). The struct is never passed as a function argument in contract code. Functions access state via `load`/`store` using typed slot paths derived from the schema.

This separation is intentional. The free monad (`World E`) keeps contract functions pure enough for the Lean kernel to prove things about them. The `state!` schema gives authors named, typed fields without manual slot numbering or namespace root computation. The compiler bridges the two into EVM bytecode.

**What you can deploy:** persistent storage and mappings, events/logs, standard ABIs (ERC-20 `bool` returns, etc.), ETH transfers, cross-contract calls, revert semantics, full EVM bytecode.

**What is restricted in author code:** stateful monads (`StateM`, `IO`), higher-order functions, closures, unbounded collections in state, `Nat`/`Int`/`String`, `structure … extends`, unbounded recursion, manual storage IO (`sload`/`sstore`/`ssload`/`readSlots`/`writeSlots`). `do`-notation over `World E` is the standard authoring style.

### §1.2 The three modules

Every LSC project produces three module kinds per contract:

| File | Role | Kernel-checked |
|---|---|---|
| `src/Counter.lean` | Contract — `state!` + `@[lsc.external]` functions | Yes (types) |
| `test/CounterLemma.lean` | Lemma — action model scaffolding + `lemma` proofs | Yes (full proof check) |
| `test/CounterTheorem.lean` | Theorem — high-level requirements, one-line lemma delegations | Yes (full proof check) |

The **contract** is what deploys. The **theorem** file is the requirements document — written and reviewed by humans. Each `theorem` states a readable business property inline and delegates to a homonymous `lemma` in exactly one line. The **lemma** file is AI-generated and holds scaffolding (`CounterAction`, `applyAction`, `applyActions`) plus all tactic proofs; humans do not review it. The Lean kernel checks both files.

**End-to-end Counter example:**

`src/Counter.lean`:
```lean4
import Lsc.Prelude
open Lsc

state! where
  number : UInt256 @public   -- offset 0 in erc7201:"Counter"

@[lsc.error]
inductive CounterError where
  | arith : ArithError → CounterError

abbrev Counter := World CounterError

@[lsc.external]
def increment : Counter UInt256 := do
  let n ← load .number       -- explicit state load
  let n' ← n +? 1            -- explicit "might overflow" operation
  store [ .number := n' ]    -- explicit state store
  return n'
```

`test/CounterTheorem.lean`:
```lean4
import Counter
import CounterLemma

/-- On success, increment increases number by exactly 1. -/
theorem increment_increases_number (s s' : Counter.State)
    (h : increment.run s = .ok s') :
    s'.number = s.number + 1 :=
  CounterLemma.increment_increases_number s s' h

/-- increment errors iff number is at UInt256 max. -/
theorem increment_overflows_iff (s : Counter.State)
    (h : increment.run s = .error (.arith .overflow)) :
    s.number = UInt256.max :=
  CounterLemma.increment_overflows_iff s h

/-- No sequence of actions can decrease the number. -/
theorem number_never_decreases (s : Counter.State) (actions : List CounterLemma.CounterAction) :
    s.number ≤ (CounterLemma.applyActions s actions).number :=
  CounterLemma.number_never_decreases s actions
```

`test/CounterLemma.lean`:
```lean4
import Counter

inductive CounterAction where
  | increment

def applyAction (s : Counter.State) : CounterAction → Counter.State
  | .increment =>
      match increment.run s with
      | .ok s' => s'
      | .error _ => s

def applyActions (s : Counter.State) (actions : List CounterAction) : Counter.State :=
  actions.foldl applyAction s

lemma increment_increases_number (s s' : Counter.State)
    (h : increment.run s = .ok s') :
    s'.number = s.number + 1 := by
  simp [increment, Lsc.run, load, store, LscState,
        UInt256.addChecked_val] at h ⊢
  omega

lemma increment_overflows_iff (s : Counter.State)
    (h : increment.run s = .error (.arith .overflow)) :
    s.number = UInt256.max := by
  simp [increment, Lsc.run, load, UInt256.addChecked_error] at h ⊢
  omega

lemma number_never_decreases (s : Counter.State) (actions : List CounterAction) :
    s.number ≤ (applyActions s actions).number := by
  simp only [applyActions]
  apply Lsc.Invariant applyAction
      (fun s' => s'.number ≥ s.number)
  · intro s'' a hP
    cases a
    · simp [applyAction, increment, Lsc.run, load, store,
            LscState, UInt256.addChecked_val] at hP ⊢
      omega
  · rfl
```

---

## PART I — THE CONTRACT LANGUAGE

---

## §2 Types

### §2.1 Primitive types

| LSC type | Lean definition | EVM/ABI type | Notes |
|---|---|---|---|
| `UInt256` | `{ n : ℕ // n < 2^256 }` | `uint256` | Bounded; no default `+ - * /` — use `+?` or `+↻` |
| `Address` | `structure Address where val : UInt256` | `address` | Not coercible to `UInt256` without `.val` |
| `Bool` | Lean built-in | `bool` | |
| `Bytes32` | `structure Bytes32 where val : UInt256` | `bytes32` | Opaque 32-byte word; not coercible to `UInt256` |
| `Bytes[N]` | `{ b : ByteArray // b.size ≤ N }` | `bytes` / `string` | Bounded; see §2.2 |

#### Arithmetic semantics

`UInt256` is a bounded natural subtype. It does **not** inherit `Fin`'s modular `Add`/`Mul` instances — plain `+ - * /` on `UInt256` are a **type error** in author code. Two explicit operator families:

| Mode | Syntax | Returns | Use when |
|---|---|---|---|
| Checked | `a +? b` | `World E UInt256` | **default** — overflow reverts |
| Wrapping | `a +↻ b` | `UInt256` | Intentional mod-2²⁵⁶ |

Same pattern for `-?`/`-↻`, `*?`/`*↻`, `/?`. The wrap suffix ↻ is U+21BB.

Checked arithmetic returns `World E _` via the in-scope `LscError E` instance. Compose with `←` in a `do`-block over `World E`. See §2.5.

**Comparisons:** `=`, `≤`, `≥`, `<`, `>` on `UInt256` compare via `.val` (prelude instances).

### §2.2 Bytes[N]

`Bytes[N]` is a bounded byte array.

```lean4
-- Lsc.Prelude
abbrev Bytes (n : Nat) := { b : ByteArray // b.size ≤ n }
notation "Bytes[" n "]" => Bytes n
```

**Storage layout:**
- `b.size ≤ 31`: left-aligned in slot, `b.size * 2` in LSB.
- `b.size > 31`: slot `p` holds `b.size * 2 + 1`; payload at `keccak256(p)` in 32-byte chunks.

**Validator rules:** `N` must be a numeric literal. `N = 0` is a warning.

### §2.3 Mapping

`Mapping K V` is a plain Lean 4 function:

```lean4
-- Lsc.Prelude
abbrev Mapping (K V : Type) := K → V

namespace Mapping
def get (m : Mapping K V) (k : K) : V := m k
def set [DecidableEq K] (m : Mapping K V) (k : K) (v : V) : Mapping K V :=
  Function.update m k v
def empty [Inhabited V] : Mapping K V := fun _ => default
end Mapping

scoped notation m:65 "[" k:65 "]"         => Mapping.get m k
scoped notation m:65 "[" k:65 " := " v:65 "]" => Mapping.set m k v
```

**Storage layout (within an ERC-7201 namespace):** mapping root at `erc7201(ns) + offset`; entry at key `k` lives at `keccak256(abi.encode(k, root + offset))` — identical to Solidity rules within the namespace.

**Simp laws:**
```lean4
@[simp] theorem Mapping.get_set_same  [DecidableEq K] (m : Mapping K V) (k : K) (v : V) :
    (m.set k v).get k = v
@[simp] theorem Mapping.get_set_other [DecidableEq K] (m : Mapping K V) (k k' : K) (v : V)
    (h : k ≠ k') : (m.set k v).get k' = m.get k'
@[simp] theorem Mapping.get_empty     [Inhabited V] (k : K) :
    (Mapping.empty : Mapping K V).get k = default
@[simp] theorem Mapping.set_set_same  [DecidableEq K] (m : Mapping K V) (k : K) (v v' : V) :
    (m.set k v).set k v' = m.set k v'
```

### §2.4 The `World` free monad

`World E α` is the contract monad. It is a free monad over `WorldF E` — a pure Lean value that describes a sequence of storage accesses, external calls, and error conditions without executing them. The compiler interprets this description to generate EVM bytecode; the proof layer interprets it via `Lsc.run` (state snapshots) and `World.runWith` (full simulation) to reason about state transitions.

```lean4
-- Lsc.Prelude
structure ReadEntry where
  slot : UInt256
  -- decode : UInt256 → Option α — elaborator supplies FromWord.decode per entry (heterogeneous batch)

structure WriteEntry where
  slot : UInt256
  word : UInt256                -- ToWord.encode of the assigned value

inductive WorldF (E : Type) (α : Type) where
  | readSlots    : Address → Array ReadEntry → (Array UInt256 → α) → WorldF E α
  | writeSlots   : Address → Array WriteEntry → α                  → WorldF E α
  | call         : Address → FuncSel → ByteArray → (CallResult → α) → WorldF E α
  | delegatecall : Address → FuncSel → ByteArray → (CallResult → α) → WorldF E α  -- v3
  | emit         : EventLog → α                                    → WorldF E α
  | revert       : E → WorldF E α
  | arith        : ArithError → WorldF E α

abbrev World (E : Type) := Free WorldF E
```

**`LogPolicy`** — a typeclass for log-handling policy in the proof-layer interpreter:

```lean4
-- Lsc.Prelude
class LogPolicy (P : Type) where
  empty  : P
  append : EventLog → P → P

instance : LogPolicy Unit where
  empty  := ()
  append := fun _ _ => ()        -- discard

instance : LogPolicy (List EventLog) where
  empty  := []
  append := fun log logs => logs ++ [log]   -- source order (§6.2)
```

**`World.runWith`** — the generic proof-layer interpreter. Threads a `WorldState` and a log accumulator `P` through the free monad; reverts roll back state automatically because `Except` short-circuits before any `writeSlots` commits:

```lean4
-- Lsc.Prelude
def World.runWith {E α P : Type} [LogPolicy P]
    : World E α → WorldState → Except (ContractError E) (α × WorldState × P)
  | Free.pure a,  w => .ok (a, w, LogPolicy.empty)
  | Free.roll op, w => match op with
    | .readSlots addr entries k =>
        let words := entries.map fun e => w.storage addr e.slot
        World.runWith (k words) w
    | .writeSlots addr entries next =>
        let w' := entries.foldl (fun w e => { w with storage := w.storage.set addr e.slot e.word }) w
        World.runWith next w'
    | .call   addr sel args k =>
        match worldDispatch addr sel args w with
        | .ok (res, w') => World.runWith (k res) w'
        | .error e      => .error e
    | .delegatecall addr sel args k =>   -- v3: storage root stays at selfAddress
        match worldDispatchDelegatecall addr sel args w with
        | .ok (res, w') => World.runWith (k res) w'
        | .error e      => .error e
    | .emit   log next =>
        match World.runWith next w with
        | .ok (v, w', p) => .ok (v, w', LogPolicy.append log p)
        | .error e       => .error e
    | .revert e => .error (.contract e)
    | .arith  e => .error (.arith e)
```

Two public aliases — same underlying implementation, clean return types:

```lean4
-- default for state theorems (logs erased from return type)
def World.run {E α : Type}
    : World E α → WorldState → Except (ContractError E) (α × WorldState) :=
  fun f w => (World.runWith (P := Unit) f w).map fun (v, w', _) => (v, w')

-- explicit for event theorems
def World.runCollect {E α : Type}
    : World E α → WorldState
    → Except (ContractError E) (α × WorldState × List EventLog) :=
  World.runWith (P := List EventLog)

scoped notation f:65 ".runCollect" w:65 => World.runCollect f w
```

**`Lsc.run`** — the default proof interpreter for **state-snapshot theorems** (§3.4, §9). Threads a `state!` struct (`Counter.State`, `AMM.State`, …) rather than raw `WorldState`:

```lean4
-- Lsc.Prelude
class LscState (S : Type) where
  embed   : S → WorldState
  project : WorldState → S

structure RunResult (α S : Type) where
  value : α
  state : S

def Lsc.run {S E α : Type} [LscState S]
    (f : World E α) (s : S) : Except (ContractError E) (RunResult α S) :=
  match World.runWith (P := Unit) f (LscState.embed s) with
  | .ok (v, w', _) => .ok { value := v, state := LscState.project w' }
  | .error e       => .error e

-- State-snapshot theorems (default)
scoped notation f:65 ".run" s:65 => Lsc.run f s

-- Full WorldState simulation (composition / v2b — §8.6)
scoped notation f:65 ".runW" w:65 => World.run f w
```

`[LscState S]` is registered by **`state!`** at elaboration time. Slot encode/decode lives inside the instance — never in theorem statements.

**Success hypothesis shapes** for `Lsc.run`:

| Return type | Hypothesis form |
|---|---|
| `World E Unit` | `f.run s = .ok s'` |
| `World E α` (α ≠ Unit) | `f.run s = .ok ⟨v, s'⟩` |

Key properties:
- **Rollback on error** — `Except` short-circuits; any `writeSlots` ops before a `revert` or `arith` are discarded because the `WorldState` is threaded as a value, not mutated in place.
- **Extcall reentrancy is visible** — when `.call` fires, it receives the current `w` including all `writeSlots` so far. If the external contract reenters, it sees the already-updated storage. This matches EVM semantics and falls out of the handler naturally.
- **Dual log modes** — default `World.run` discards logs at the type level (`Unit` instance compiles away); `World.runCollect` accumulates them in source order for event correctness theorems (§6.3).

**`ContractError`** — wraps contract-specific errors alongside universal ones:

```lean4
inductive ContractError (E : Type) where
  | contract : E           → ContractError E
  | arith    : ArithError  → ContractError E
  | extern   : ExternError → ContractError E
```

### §2.5 Error types, arithmetic errors, and `LscError`

#### `@[lsc.error]` — declaring contract error types

Registers the inductive with the emitter for ABI `errors` generation and revert encoding. Every `@[lsc.error]` type **must** include an `arith` constructor and a `LscError` instance (auto-derived if omitted):

```lean4
@[lsc.error]
inductive AMMError where
  | uninitializedPool
  | zeroInput
  | zeroOutput
  | insufficientLp
  -- auto-injected by @[lsc.error] if omitted:
  | arith : ArithError → AMMError
  deriving DecidableEq, Repr

-- auto-injected:
instance : LscError AMMError where arith := .arith
```

#### `ArithError`

```lean4
inductive ArithError where
  | overflow
  | divisionByZero
  deriving DecidableEq, Repr
```

#### `LscError` typeclass

```lean4
class LscError (E : Type) where
  arith : ArithError → E

instance : LscError ArithError where arith := id
```

This typeclass is the mechanism by which `+?`, `-?`, `*?`, `/?` inject arithmetic faults into any `World E` without an explicit lift at every call site.

#### `UInt256` definition and projections

```lean4
abbrev UInt256 := { n : ℕ // n < 2^256 }

namespace UInt256
def val (a : UInt256) : ℕ := a.1
def max : UInt256 := ⟨2^256 - 1, by omega⟩

@[simp] theorem eq_iff {a b : UInt256} : a = b ↔ a.val = b.val := Subtype.ext_iff
@[simp] theorem le_iff {a b : UInt256} : a ≤ b ↔ a.val ≤ b.val := Iff.rfl
@[simp] theorem lt_iff {a b : UInt256} : a < b ↔ a.val < b.val := Iff.rfl

def addNat (a : UInt256) (n : ℕ) (h : a.val + n < 2^256 := by omega) : UInt256 :=
  ⟨a.val + n, h⟩
instance : HAdd UInt256 ℕ UInt256 where hAdd := UInt256.addNat
end UInt256
```

#### The `+?` operator family (checked, lifted into `World E`)

```lean4
def UInt256.addChecked [LscError E] (a b : UInt256) : World E UInt256 :=
  if h : a.val + b.val < 2^256 then return ⟨a.val + b.val, h⟩
  else Free.liftF (.arith .overflow)

def UInt256.subChecked [LscError E] (a b : UInt256) : World E UInt256 :=
  if h : b.val ≤ a.val then return ⟨a.val - b.val, by omega⟩
  else Free.liftF (.arith .overflow)

def UInt256.mulChecked [LscError E] (a b : UInt256) : World E UInt256 :=
  if h : a.val * b.val < 2^256 then return ⟨a.val * b.val, h⟩
  else Free.liftF (.arith .overflow)

def UInt256.divChecked [LscError E] (a b : UInt256) : World E UInt256 :=
  if h : b.val ≠ 0 then return ⟨a.val / b.val, by omega⟩
  else Free.liftF (.arith .divisionByZero)

scoped notation a " +? " b => UInt256.addChecked a b
scoped notation a " -? " b => UInt256.subChecked a b
scoped notation a " *? " b => UInt256.mulChecked a b
scoped notation a " /? " b => UInt256.divChecked a b
```

#### The `+↻` operator family (wrapping)

```lean4
def UInt256.addMod (a b : UInt256) : UInt256 := ⟨(a.val + b.val) % 2^256, by omega⟩
def UInt256.subMod (a b : UInt256) : UInt256 := ⟨(a.val + 2^256 - b.val) % 2^256, by omega⟩
def UInt256.mulMod (a b : UInt256) : UInt256 := ⟨(a.val * b.val) % 2^256, by omega⟩

scoped notation a " +↻ " b => UInt256.addMod a b
scoped notation a " -↻ " b => UInt256.subMod a b
scoped notation a " *↻ " b => UInt256.mulMod a b
```

#### Bridge lemmas (`@[simp]`)

```lean4
@[simp] theorem UInt256.addChecked_val [LscError E] {a b r : UInt256} :
    World.run (a +? b : World E UInt256) w = .ok (r, w) ↔
    (a.val + b.val < 2^256 ∧ r.val = a.val + b.val) := by
  simp [UInt256.addChecked, World.run]; constructor <;> intro h <;> split_ifs at h <;> simp_all <;> omega

@[simp] theorem UInt256.subChecked_val [LscError E] {a b r : UInt256} :
    World.run (a -? b : World E UInt256) w = .ok (r, w) ↔
    (b.val ≤ a.val ∧ r.val = a.val - b.val) := by
  simp [UInt256.subChecked, World.run]; constructor <;> intro h <;> split_ifs at h <;> simp_all <;> omega

@[simp] theorem UInt256.mulChecked_val [LscError E] {a b r : UInt256} :
    World.run (a *? b : World E UInt256) w = .ok (r, w) ↔
    (a.val * b.val < 2^256 ∧ r.val = a.val * b.val) := by
  simp [UInt256.mulChecked, World.run]; constructor <;> intro h <;> split_ifs at h <;> simp_all <;> omega

@[simp] theorem UInt256.divChecked_val [LscError E] {a b r : UInt256} :
    World.run (a /? b : World E UInt256) w = .ok (r, w) ↔
    (b.val ≠ 0 ∧ r.val = a.val / b.val) := by
  simp [UInt256.divChecked, World.run]; constructor <;> intro h <;> split_ifs at h <;> simp_all <;> omega

-- Error-direction lemmas
@[simp] theorem UInt256.addChecked_error [LscError E] {a b : UInt256} (h : a.val + b.val ≥ 2^256) :
    World.run (a +? b : World E UInt256) w = .error (.arith .overflow)
@[simp] theorem UInt256.subChecked_error [LscError E] {a b : UInt256} (h : a.val < b.val) :
    World.run (a -? b : World E UInt256) w = .error (.arith .overflow)
@[simp] theorem UInt256.divChecked_error [LscError E] {a : UInt256} :
    World.run (a /? 0 : World E UInt256) w = .error (.arith .divisionByZero)
```

**Proof recipe:** `simp [myFunction, World.run, load, store, UInt256.addChecked_val, ...]` unfolds the free monad and rewrites all checked arithmetic into pure `ℕ` propositions about `.val`. `omega` closes linear goals; `nlinarith` closes nonlinear ones.

### §2.6 Forbidden types

| Forbidden | Validator error | Use instead |
|---|---|---|
| `Nat`, `Int`, `Float` | `lsc: use UInt256` | `UInt256` |
| `String`, `Char` | `lsc: use Bytes[N]` | `Bytes[N]` |
| `List`, `Array` in state | `lsc: use Mapping` | `Mapping` |
| `IO`, `StateM`, `ST` | `lsc: stateful monads not allowed` | `World E` |
| Higher-order functions | `lsc: functions cannot be passed as arguments` | Top-level helpers |
| `structure … extends` | `lsc: storage inheritance not supported in v1` | Compose structs manually |
| `sload`/`sstore`/`ssload`/`readSlots`/`writeSlots` in author code | `lsc: storage IO is emitter-only` | `load` / `store [ … := … ]` |

### §2.7 Fixed-point arithmetic (`Lsc.Ray` / `Lsc.Wad`)

DeFi contracts routinely multiply and divide `UInt256` values that represent decimal fractions. `Lsc.Ray` and `Lsc.Wad` are the built-in fixed-point libraries (scale 10²⁷ and 10¹⁸).

#### Scale constants

```lean4
def WAD : ℕ := 10^18
def RAY : ℕ := 10^27
def HALF_WAD : ℕ := WAD / 2
def HALF_RAY : ℕ := RAY / 2
```

#### Ray/WAD operations (lifted into `World E`)

Three explicit rounding variants per operation — no default aliases. All return `World E UInt256`:

```lean4
-- Lsc.Ray
def rayMulDown   [LscError E] (a b : UInt256) : World E UInt256
def rayMulUp     [LscError E] (a b : UInt256) : World E UInt256
def rayMulHalfUp [LscError E] (a b : UInt256) : World E UInt256
def rayDivDown   [LscError E] (a b : UInt256) : World E UInt256
def rayDivUp     [LscError E] (a b : UInt256) : World E UInt256
def rayDivHalfUp [LscError E] (a b : UInt256) : World E UInt256

-- Lsc.Wad — same six defs with wad* prefix and WAD = 10^18 scale
```

#### Bracket-pair operators

| Pair | Rounding | Notation |
|---|---|---|
| `⌊·⌋` | Down | `a ⌊*⌋? b`, `a ⌊/⌋? b` |
| `⌈·⌉` | Up | `a ⌈*⌉? b`, `a ⌈/⌉? b` |
| `⸢·⸣` | HalfUp | `a ⸢*⸣? b`, `a ⸢/⸣? b` |

Scale from namespace — `open scoped Lsc.Ray` or `open scoped Lsc.Wad`. Do not open both in the same file.

**Usage:**
```lean4
import Lsc.Ray
open Lsc Lsc.Ray
open scoped Lsc.Ray

@[lsc.external]
def accrueInterest : LendingAMM Unit := do
  let (rate, index, delta) ← load [.liquidityRate, .liquidityIndex, .timeDelta]
  let growth   ← rate ⸢*⸣? delta
  let newFactor ← index +? growth
  let newIndex  ← newFactor ⸢*⸣? rate
  store [ .liquidityIndex := newIndex ]
```

Bridge lemmas follow the same biconditional pattern as `+?` — see §2.5.

---

## §3 State

### §3.1 Declaring contract state (`state!`)

Contract state is declared with the **`state!` macro**. The macro expands at Lean elaboration time (same category as `require`, `extcall!`) into the state struct, typed slot constants, and a `[LscState]` instance. The struct is a **schema** — it declares what the contract owns and determines slot layout. It is **never** passed as a function argument in contract code; functions access state via `load`/`store`.

**Default** (namespace defaults to module name — `AMM` from `src/AMM.lean`):

```lean4
-- src/AMM.lean  →  erc7201:"AMM"
state! where
  token0 token1 : IERC20              -- offset 0–1: external IERC20 refs (stored as address)
  reserve0   : UInt256                 -- offset 2
  reserve1   : UInt256                 -- offset 3
  totalLP    : UInt256                 -- offset 4
  lpBalances : Mapping Address UInt256 -- offset 5
-- expands to structure AMM.State where token0 token1 : ContractAt IERC20 …
```

**Interface-typed external references:** A field typed `IERC20` (or any type with a `[LscInterface]` instance that is not a layout struct) occupies one slot in the parent namespace, ABI-encoded as `address`. `load .token0` yields `ContractAt IERC20`; `store [ .token0 := addr ]` accepts `Address` or `ContractAt IERC20`. See §3.7.

**Explicit namespace:**

```lean4
state! @namespace "my.app.amm" where
  reserve0 : UInt256
```

**Named layout** (shared `lib/` layout types — see §3.7):

```lean4
-- lib/ERC20.lean  →  layout type ERC20; canonical instance id "ERC20"
state! @namespace "ERC20" where
  balances   : Mapping Address UInt256
  totalSupply : UInt256
-- expands to structure ERC20 where … (imported as ERC20, not ERC20.State)
```

**Proxy module** (EIP-1967 fixed slots — not ERC-7201; see §3.8):

```lean4
-- src/TransparentProxy.lean
state! @proxy where
  implementation : Address
  admin : Address
```

The `state!` macro does four things:

**1. Generates typed slot constants** — one per field, named in PascalCase, carrying namespace id and offset within that namespace (§3.3):

```lean4
-- generated; never written by authors
def Token0    : TypedSlot (ContractAt IERC20)         := ⟨"AMM", 0⟩
def Token1    : TypedSlot (ContractAt IERC20)         := ⟨"AMM", 1⟩
def Reserve0  : TypedSlot UInt256                     := ⟨"AMM", 2⟩
-- …
```

**2. Registers `[LscState AMM.State]`** — embeds a state snapshot into `WorldState` at `selfAddress` (all namespaces owned by the contract) and projects back after `World.runWith`. Used internally by `Lsc.run` (§2.4); not part of the theorem-facing API.

**3. Defines the contract monad alias** — the error type `E` is inferred from the `@[lsc.error]` declaration in the same module:

```lean4
-- generated
abbrev AMM := World AMMError
```

**4. Field visibility** — `@public` on a field (see §3.5) marks it for ABI getter synthesis.

At most one unnamed `state! where …` per contract module. Proxy modules use `state! @proxy where` (§3.8).

### §3.2 TypedSlot and load / store

`TypedSlot α` pairs an ERC-7201 namespace id and field offset with a type (§3.3). The emitter resolves each pair to an absolute storage slot at compile time. Authors access contract storage via **`load`** and **`store`** — typed wrappers over the internal `readSlots` / `writeSlots` IR nodes. Raw `sload`/`sstore`/`ssload`/`readSlots`/`writeSlots` are forbidden in author code (§12). Authors use **`load`** / **`store [ … := … ]`** only.

```lean4
-- Lsc.Prelude
structure TypedSlot (α : Type) where
  namespace : String
  offset    : UInt256

-- single slot (1-element readSlots); `LscSlot.resolve` is elaboration-time for each generated constant
def load {α E : Type} [FromWord α] [LscError E]
    (slot : TypedSlot α) : World E α :=
  Free.liftF (.readSlots selfAddress #[⟨LscSlot.resolve slot, FromWord.decode⟩]
    fun words => FromWord.decode words[0]!)

-- batch load — heterogeneous tuple inferred from slot list
def load {σ E : Type} [ReadBundle σ] [LscError E]
    (slots : ReadBundle.Slots σ) : World E σ :=
  ReadBundle.liftLoad slots

-- record-update store (1 or more fields; bracket form is canonical)
macro "store" "[" updates:term,* "]" : doElem =>
  `(doElem| $(StoreBundle.elabUpdates updates))

-- elaborates to writeSlots with one WriteEntry per `field := value` update
```

**Loads** — dot-access resolves slot constants from the in-scope `state!` declaration. Nested layout fields use path syntax (§3.7):

```lean4
let n ← load .number                                              -- single
let (rate, index, delta) ← load [.liquidityRate, .liquidityIndex, .timeDelta]  -- batch
let bal ← load (.balances ctx.caller)                             -- mapping entry
let (ta, tb) ← load [.vaultA.totalDeposits, (.vaultB.balances a)]  -- nested layout instances
```

**Stores** — record-update syntax only (mirrors `{ s with field := val }` from pure-state proofs):

```lean4
store [ .number := n' ]

store [
  .liquidityIndex := newIndex,
  .totalSupply    := newSupply,
]

store [ (.balances ctx.caller) := newBal ]
```

Source order is preserved in lowering (§13.1). The CEI linter (§8.5) warns on `store` after interactions unless `@[lsc.allow_store_after_call]` is set on the export. `store .field v` and tuple-pair forms are rejected (§12).

**Monadic bind on reads:** `←` sequences `World E` actions, not mutation. Only `store` and `call` mutate `WorldState`; `load` is still monadic because its result depends on the current storage snapshot and its position relative to prior stores and calls.

Attempting to `load`/`store` on a name not declared in the schema is a validator error.

**Bridge lemmas** (proof layer — `@[simp]`):

```lean4
@[simp] theorem load_val {α S E : Type} [LscState S] [FromWord α]
    (slot : TypedSlot α) (s : S) :
    (load slot).run s = .ok ⟨LscState.get s slot, LscState.get s slot⟩

@[simp] theorem store_val {S E : Type} [LscState S] (slot : TypedSlot α) [ToWord α]
    (val : α) (s : S) :
    (store [ slot := val ]).run s = .ok ⟨(), LscState.set s slot val⟩

@[simp] theorem readSlots_eq_seq ...   -- batch read = sequential single reads
@[simp] theorem writeSlots_eq_seq ...  -- batch write = sequential single writes
```

### §3.3 ERC-7201 namespaced storage (default layout)

Every `state!` block (except `@proxy` — §3.8) is rooted at an **ERC-7201 namespace**. Fields occupy sequential **offsets** `0, 1, 2, …` within that namespace. `Mapping` fields occupy one offset (the mapping root); individual entries live at `keccak256(abi.encode(key, root + offset))` — identical to Solidity layout rules, rooted at the namespace base instead of slot `0`.

**Namespace root formula** ([ERC-7201](https://eips.ethereum.org/EIPS/eip-7201)):

```
erc7201(id) = keccak256( keccak256(bytes(id)) − 1 ) & ~bytes32(0xff)
```

Solidity equivalent: `keccak256(abi.encode(uint256(keccak256(bytes(id))) - 1)) & ~bytes32(uint256(0xff))`

**Namespace id resolution:**

| Form | Namespace id |
|---|---|
| `state! where` in `src/Counter.lean` | module name (`"Counter"`) |
| `state! @namespace "foo" where` | `"foo"` |
| `state! ERC20 where` in `lib/` | type name (`"ERC20"`) unless block `@namespace` overrides |

The emitter computes `erc7201(id)` once per namespace and lowers `load`/`store` to `SLOAD`/`SSTORE` at `root + offset` (plus mapping hashing). Authors never write namespace roots or absolute slot numbers.

**Compiler-reserved namespaces** (not in author `state!`): `"lsc.reentrancy.lock"` (reentrancy guard, §13.1), `"lsc.initialized"` (proxy init flag, §3.8). These use the same ERC-7201 formula and are stable across implementation upgrades.

`structure … extends` is **not supported**. Shared storage shapes are composed via **nested layout fields** (§3.7).

> **Why ERC-7201 by default?** Namespaces isolate storage regions — lib layouts, nested instances, and proxy app state do not collide. Upgradeable implementations can freeze a lib namespace (e.g. `"ERC20"`) while appending fields in the contract namespace. The formula is collision-resistant against Solidity's sequential slot-0 layout and against other namespaces.

> **Why no `extends`?** Storage inheritance introduces slot-layout ambiguity in upgradeable patterns. Nested layout fields with explicit namespace ids are unambiguous. Vyper takes the same position on `extends`.

### §3.4 State in contract functions vs theorems

| Context | How state is accessed | Form |
|---|---|---|
| Contract function body | `load` / `store [ … := … ]` via typed slot constants | `let r ← load .reserve0` |
| Theorem statements (default) | `state!` struct fields directly | `s.reserve0`, `s'.number` |
| Theorem statements (composition) | Scene product or `WorldState` | `scene'.counter.count`, `w` (§8.6) |
| Lemma bodies (simp) | `Lsc.run` + `load`/`store` bridge lemmas | `simp [Lsc.run, load, store, LscState]` |

The state struct never appears as a **contract function** parameter. In **theorem files** (default mode), theorems quantify over `Module.State` snapshots — not `WorldState`.

#### Proof modes

| Mode | Theorem state type | When |
|---|---|---|
| **State snapshot** (default) | `Counter.State`, `AMM.State`, … | Property mentions only this contract's fields |
| **Scene snapshot** (composition) | Named product (`HookScene`, …) | Property mentions callee fields (§8.6) |
| **Full simulation** (v2b) | `WorldState` + `simulate_call` | Reentrancy, assumed interfaces |

### §3.5 The `@public` field annotation

Mark a state field `@public` in `state!` to expose it as a read-only ABI getter. The compiler synthesizes a lazy `@[lsc.external]` view that loads only the relevant slot(s).

```lean4
state! where
  number : UInt256 @public   -- offset 0 in erc7201:"Counter"
-- Compiler synthesizes:
-- @[lsc.external]
-- def number : Counter UInt256 := load .number
```

**Generation rules:**

| Field type | Generated signature |
|---|---|
| Scalar | `def fieldName : ContractM FieldType` |
| Interface ref (`IERC20`, …) | `def fieldName : ContractM Address` (ABI returns `address`) |
| `Mapping K V` | `def fieldName (k : K) : ContractM V` |
| Nested `Mapping` | one key parameter per mapping level |

When the ABI name differs from the field name (e.g. ERC-20 `balanceOf` vs field `balances`), omit `@public` and write a manual `@[lsc.external]`.

### §3.6 `@[lsc.initialize]`

At most one initialization function per contract, called at deployment:

```lean4
@[lsc.initialize]
def initialize (name symbol : Bytes[32]) (decimals initialSupply : UInt256)
    (ctx : MsgContext) : ERC20 Unit := do
  store [
    .name        := name,
    .symbol      := symbol,
    .decimals    := decimals,
    .totalSupply := initialSupply,
  ]
  store [ (.balances ctx.sender) := initialSupply ]
```

- Return type must be `ContractM Unit` or `ContractM α`.
- The emitter generates an ABI constructor (not a named function).
- `ctx.sender` is bound to `msg.sender` at deploy time.

### §3.7 Nested layout fields

Lib modules declare **layout types** with `state!` — reusable field shapes stored in their own ERC-7201 namespace when used standalone. Deployable contracts **nest** layout types as fields to compose owned sub-state. Each nested field is a **layout instance** with its own namespace root.

**Owned sub-state vs external references:**

| Storage | LSC shape | `load` type | Example |
|---|---|---|---|
| **Owned sub-state** (this contract's storage) | Nested layout type | layout struct | `token : ERC20` in MyToken; `vaultA : VaultLedger` in DualVault |
| **External interface reference** | Interface type in parent namespace | `ContractAt I` | `token0 token1 : IERC20` in AMM |
| **External contract reference** (untyped) | `Address` scalar | `Address` | `counter : Address` in MyToken |
| **External contract's storage** | Not nested — `call` / `staticcall!` | — | `IERC20.transferFrom` via assumed interface (§8.2) |

Do **not** nest a layout type for tokens the contract merely references (AMM pool config). Use `IERC20` (interface ref) for external token addresses; nest layouts only for storage **this contract owns**. Validator error if a layout type (`ERC20` from `lib/`) is used where balances live externally: *use IERC20 for external token references, not nested ERC20 layout*.

**AMM example:**

```lean4
state! @namespace "AMM" where
  token0 token1 : IERC20
  reserve0 reserve1 totalLP : UInt256
  lpBalances : Mapping Address UInt256
```

**Lib layout type:**

```lean4
-- lib/VaultLedger.lean
state! @namespace "VaultLedger" where
  balances      : Mapping Address UInt256
  totalDeposits : UInt256
```

**Multiple instances** (duplicate layout types — auto namespace per field):

```lean4
-- src/DualVault.lean
import VaultLedger

state! @namespace "DualVault" where
  vaultA : VaultLedger    -- erc7201:"DualVault.vaultA" (auto)
  vaultB : VaultLedger    -- erc7201:"DualVault.vaultB" (auto)
```

**Singleton nested layout** with optional canonical namespace override:

```lean4
-- src/MyToken.lean
import ERC20

state! @namespace "MyToken" where
  token   : ERC20                    -- auto erc7201:"MyToken.token"
  counter : Address                  -- erc7201:"MyToken" offset 0

-- or pin token ledger to lib canonical namespace:
state! @namespace "MyToken" where
  token   : ERC20 @namespace "ERC20"
  counter : Address
```

**Instance namespace rules:**

| Situation | Resolved instance id |
|---|---|
| Nested layout field, no field `@namespace` | `"<parentNs>.<fieldName>"` (auto) |
| Nested layout field with `@namespace "id"` | `"id"` (override) |
| Scalar / non-layout field in parent block | Parent block namespace |
| Two fields resolving to the same instance id | **error** — duplicate namespace |

Field `@namespace` is written only when overriding the auto id. Validator: all instance ids unique per deployable contract.

**Contract access:**

```lean4
let (ta, tb) ← load [.vaultA.totalDeposits, (.vaultB.balances a)]
store [ (.vaultA.balances a) := v, .counter := hook ]
```

**Proof snapshot:** `DualVault.State` has `vaultA vaultB : VaultLedger` — theorems use `s.vaultA.balances`, `s.vaultB.balances`. ERC20 lemmas apply to any `ERC20` sub-struct regardless of instance id. `[LscState Parent.State]` composes embed/project over all instance namespaces plus parent scalars via `[LscStateFragment]` (one fragment per namespace).

### §3.8 Proxy storage (`@proxy`)

Proxy modules declare state with **`state! @proxy where`**. This is **not** ERC-7201. The compiler assigns **EIP-1967** standard slots by field name — authors never supply hex literals.

```lean4
state! @proxy where
  implementation : Address
  admin : Address
```

| Field | Slot |
|---|---|
| `implementation` | `0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc` |
| `admin` | `0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103` |

Rules:

- `@proxy` and `@namespace` are **mutually exclusive** on the same `state!` block.
- At most one `state! @proxy where` per proxy module.
- Implementation modules use ERC-7201 (`@namespace`); under `delegatecall` (§8.7, v3) they read/write the **proxy account's** ERC-7201 namespaces.
- `@[lsc.initialize]` on the implementation may be invoked via delegatecall after proxy deploy; `"lsc.initialized"` guards one-time init.

Artifact metadata: `"layout": "proxy"`, `"standard": "eip-1967"`. See [Appendix H](lsc-appendices.md#appendix-h--proxy-and-upgradeable-storage).

### §3.9 Schema versioning and migration

Deployable contracts may carry **`@[lsc.schema "Module/N"]`** on `state!` (optional but recommended for upgradeable implementations). The validator enforces **per-namespace** migration rules against the prior artifact (or checked-in schema snapshot):

**Allowed within a namespace:**

- Append new fields at the end (new offsets only)
- Optional reserved `__gapN : UInt256` fields in v1 for future offsets

**Forbidden (hard error):**

- Reorder fields within a namespace
- Remove or change the type of an existing field
- Rename a namespace id or instance id (including auto `"Parent.field"` ids)
- Change a nested layout's field order or types when that layout is frozen

**Frozen namespaces:** lib layout types (e.g. `"ERC20"`) and explicit field overrides (e.g. `@namespace "ERC20"`) are shared across implementation versions — layout must not change once deployed.

**Append-only parent namespace:** contract scalars in `"MyToken"` may gain new trailing fields in v2; nested instance namespaces (`"MyToken.token"`, `"DualVault.vaultA"`) are unchanged unless the field is renamed (breaking).

Artifact records each namespace:

```json
"storageLayout": {
  "layout": "erc7201",
  "schemaId": "MyToken/2",
  "namespaces": [
    {
      "id": "ERC20",
      "root": "0xcb9fa12623879b77…",
      "fields": [{ "name": "balances", "offset": 0, "type": "mapping(address => uint256)" }]
    },
    {
      "id": "MyToken",
      "root": "0x…",
      "fields": [{ "name": "counter", "offset": 0, "type": "address" }]
    }
  ]
}
```

Compatible with Solidity `@custom:storage-location erc7201:<id>` (0.8.20+) for cross-language audit. See §13.2.

---

## §4 Functions (Exports)

### §4.1 The `@[lsc.external]` annotation

Public ABI functions are declared with `@[lsc.external]`. The Lean `def` name **is** the ABI function name.

**Reentrancy lock (default):** All `@[lsc.external]` functions are **non-reentrant by default**. The emitter wraps each export with a **contract-wide** reentrancy lock (ERC-7201 namespace `"lsc.reentrancy.lock"`, not in author `state!` — OpenZeppelin `ReentrancyGuard` semantics). While the lock is held, any other guarded export reverts. Use `@[lsc.allow_reentrant]` to opt out of the lock (validator warning issued).

**CEI guidance:** With the default lock, authors may write `store` before or after `call` / `staticcall` / `native_transfer!` in the `do` block. The validator warns when `store` appears after an interaction anywhere in the export's transitive call graph (§8.5, §12.1). Use `@[lsc.allow_store_after_call]` on an export to suppress that warning when non-CEI ordering is intentional (requires a `-- cei: <reason>` doc comment).

```lean4
@[lsc.external]
def increment : Counter Unit := do
  let n ← load .number
  let n' ← n +? 1
  store [ .number := n' ]
```

**Guarded withdraw with intentional store-after-call (suppress CEI warning):**

```lean4
/-- cei: guarded withdraw; contract-wide lock prevents reentry during transfer -/
@[lsc.external]
@[lsc.allow_store_after_call]
def withdraw (ctx : MsgContext) (amount : UInt256) : Vault UInt256 := do
  let bal ← load (.balances ctx.caller)
  require (bal ≥ amount) .insufficient
  call (token : IERC20).transfer ctx.caller amount
  store [ (.balances ctx.caller) := bal - amount ]
  return amount
```

### §4.2 Mutators and views

| Return shape | Meaning |
|---|---|
| `ContractM Unit` | Mutator, no ABI return value |
| `ContractM V` | Mutator or view with return value |

Whether a function is a **mutator** or **view** is inferred from its `World` operations:
- Functions that contain only `load` (no `store`, no `call`) → view; emitter generates `STATICCALL`-safe wrapper.
- Functions with any `store` or `call` → mutator; nonpayable by default.

**`require` — inline precondition guard:**

```lean4
require (condition) .ErrorVariant
-- desugars to:
if ¬condition then Free.liftF (.revert .ErrorVariant) else return ()
```

**Mutator with return value:**
```lean4
@[lsc.external]
def swap (ctx : MsgContext) (zeroForOne : Bool) (amountIn : UInt256) : AMM UInt256 := do
  require (amountIn > 0) .zeroInput
  let (r0, r1) ← load [.reserve0, .reserve1]
  require (r0 > 0 ∧ r1 > 0) .uninitializedPool
  let (tokenIn, tokenOut, rIn, rOut) :=
    if zeroForOne then (← load .token0, ← load .token1, r0, r1)
    else               (← load .token1, ← load .token0, r1, r0)
  let amountOut ← computeAmountOut rIn rOut amountIn
  -- CEI: writes before calls
  store [
    .reserve0 := (r0 + if zeroForOne then amountIn  else 0),
    .reserve1 := (r1 - if zeroForOne then 0         else amountOut)
  ]
  call tokenIn.transferFrom ctx.caller self amountIn
  call tokenOut.transfer    ctx.caller      amountOut
  return amountOut
```

**View:**
```lean4
@[lsc.external]
def price : AMM UInt256 := do
  let (r0, r1) ← load [.reserve0, .reserve1]
  require (r1 > 0) .uninitializedPool
  r0 /? r1
```

### §4.3 ABI inference rules

| Return shape | Mutability | ABI return | ABI errors |
|---|---|---|---|
| `ContractM Unit` (stores only) | nonpayable | none | `E` variants |
| `ContractM UInt256` (stores) | nonpayable | `uint256` | `E` variants |
| `ContractM Bool` (stores) | nonpayable | `bool` | `E` variants |
| `ContractM Address` (stores) | nonpayable | `address` | `E` variants |
| `ContractM UInt256` (reads only) | view | `uint256` | `E` variants |
| `ContractM Bool` (reads only) | view | `bool` | `E` variants |

When an export is marked `@[lsc.payable]` or `@[lsc.receive]` (§5.2), the ABI function is marked `payable`.

**EVM behavior summary:**

| `World.run` result | EVM behavior |
|---|---|
| `.error (.contract e)` | `REVERT` with `abi.encode(e)`; no storage commit; no events |
| `.error (.arith e)` | `REVERT` with `abi.encode(e)`; no storage commit; no events |
| `.ok (v, w')` (mutator) | Inline `SSTORE`/`LOG` per source order; ABI-encode `v` |
| `.ok (v, w)` (view, `w` unchanged) | No `SSTORE`; ABI-encode `v` |

### §4.4 Parameter filtering

| Parameter kind | ABI | Rule |
|---|---|---|
| `ctx : MsgContext` | excluded | Bound to message/block context (§5.1) |
| All primitive types | included | In declaration order |

Unlike the old model, there is no `s : State` parameter to filter — state lives in the world.

---

## §5 Message Context and ETH Handling

### §5.1 The `MsgContext` type

```lean4
-- Lsc.Prelude
structure MsgContext where
  caller    : Address
  value     : UInt256   -- msg.value
  timestamp : UInt256   -- block.timestamp
  number    : UInt256   -- block.number
```

Any parameter of type `MsgContext` is excluded from ABI calldata. The emitter binds all fields from EVM opcodes at each export boundary. Parameter name convention: `ctx`.

**Field bindings:**

| Field | Bound to |
|---|---|
| `ctx.caller` | `msg.sender` |
| `ctx.value` | `msg.value` |
| `ctx.timestamp` | `block.timestamp` |
| `ctx.number` | `block.number` |

#### Implicit contract address (`self`)

`self : Address` is an **ambient identifier** in contract modules — the executing contract's own address (Solidity `address(this)`). It is **not** a `state!` field and must not appear in `initialize` parameters.

| Binding | Source | In state? |
|---|---|---|
| `ctx.caller` | `CALLER` | no |
| `self` | `ADDRESS` / `selfAddress` | no |

- **Emitted bytecode:** `ADDRESS` at each use site (or bound once per export entry — equivalent for non-delegatecall exports).
- **`Lsc.run` / proofs:** desugars to the same `selfAddress` used by `readSlots`/`writeSlots` (§3.2, `LscState.embed`).
- **Delegatecall:** `self` is the proxy address; storage root remains `selfAddress` (§8.7) — same as Solidity.

**Validator rules:**
- At most one `MsgContext` parameter per function.
- `Address` parameter named `caller`, `sender`, `from`, or `owner` used for authorization → warning: use `ctx.caller` instead.
- `self` as a `state!` field or author `def` → error: `lsc: self is reserved for the implicit contract address`.

### §5.2 ETH handling

#### Payable functions

```lean4
@[lsc.payable]
@[lsc.external]
def deposit (ctx : MsgContext) : VaultAMM Unit := do
  require (ctx.value > 0) .zeroDeposit
  let bal ← load (.balances ctx.caller)
  let newBal ← bal +? ctx.value
  store [ (.balances ctx.caller) := newBal ]
```

#### Non-payable protection (default)

Non-`@[lsc.payable]` exports revert if `msg.value > 0`.

#### ETH transfers out

```lean4
-- Lsc.Prelude
-- native_transfer! desugars to Free.liftF (.transfer to amount ())
native_transfer! to amount   -- World E Unit; reverts on failure
```

Requires `eth : EthError → E` constructor on the error type.

#### Receive and fallback

```lean4
@[lsc.receive]
def receive (ctx : MsgContext) : VaultAMM Unit := do
  require (ctx.value > 0) .zeroDeposit
  let bal ← load .totalDeposited
  let newBal ← bal +? ctx.value
  store [ .totalDeposited := newBal ]

@[lsc.fallback]
def fallback : VaultAMM Unit :=
  Free.liftF (.revert .unknownSelector)
```

---

## §6 Events

### §6.1 Declaring events

```lean4
structure TransferEvent where
  from to : Address
  value   : UInt256
  deriving Lsc.Event.EvmEvent
```

### §6.2 Emitting events

Authors emit via `WorldF.emit` in `do`-blocks over `World E`. `EvmEvent` supplies `toLog` for each event struct:

```lean4
Free.liftF (.emit (TransferEvent.toLog ctx.caller to amount) ())
```

Each call on a path that reaches `.ok` is collected by the emitter and by `World.runCollect`. No logs fire on error paths — `Except` short-circuits before any `.emit` after the failing op is reached.

**Emit ordering:** `LOG` opcodes run on the success path in source order, after all preceding `SSTORE`/`CALL` nodes at their respective program points (§13.1).

### §6.3 Dual proof modes

State-snapshot and event theorems share `World.runWith` under the hood. **`Lsc.run`** (default) threads `Module.State`; **`World.runCollect`** threads full `WorldState` for log accumulation.

| Mode | API | Return type | Use |
|---|---|---|---|
| State theorems (default) | `Lsc.run` / `.run` | `RunResult α S` | Balance, supply, reserve invariants |
| Event theorems | `World.runCollect` / `.runCollect` | `α × WorldState × List EventLog` | Log correctness at Layer 1 |
| Composition (v2b) | `World.run` / `.runW` | `α × WorldState` | Cross-contract, reentrancy (§8.6) |

**State theorems** — logs discarded at the type level:

```lean4
(swap ctx z amountIn).run s = .ok ⟨out, s'⟩
```

**Event theorems** — logs accumulated in source order (embed `s` via `LscState` or use `WorldState` directly):

```lean4
theorem transfer_emits_transfer_event
    (ctx : MsgContext) (to : Address) (amount : UInt256) (s s' : Token.State)
    (hOk : (transfer ctx to amount).runCollect s =
      .ok (s', [TransferEvent.toLog ctx.caller to amount])) :
    True := by trivial   -- delegate to lemma in practice
```

Full observational equivalence of LOG lowering is in the verified pipeline (§13.3).

---

## §7 Revert

`.error e` paths in `World.run` produce `REVERT` with `abi.encode(e)`; no storage is committed; no events fire. This falls out of the free monad handler structure — the `WorldState` value is simply not returned on error paths.

`require (cond) e` desugars to:
```lean4
if ¬cond then Free.liftF (.revert e) else return ()
```

---

## §8 External Calls

> **v1 status:** `call`, `staticcall`, and `Lsc.extern.*` are specified here and support the composition demo (Appendix B), but full emitter support lands in v2b.

### §8.1 World and accounts

The `WorldState` models all accounts:

```lean4
structure WorldState where
  storage : Address → UInt256 → UInt256
  balance : Address → UInt256
  code    : Address → ByteArray
```

Contract functions do not take `WorldState` as a parameter. `call` and `staticcall` may appear in any `src/*.lean` `def`. `World.run` threads `WorldState` through call sites, making reentrancy visible as discussed in §2.4.

### §8.2 Interface cast, `staticcall`, `call`

#### Interface cast

```lean4
-- Cast notation (macro in Lsc.Prelude)
(e : IERC20)   -- desugars to (e : ContractAt IERC20)
```

Interface-typed `state!` fields (§3.1, §3.7) already yield `ContractAt I` from `load` — no cast needed at `call`/`staticcall` sites. The `(e : I)` cast remains for raw `Address` locals and helper parameters.

#### `staticcall` (read-only)

```lean4
let bal ← staticcall (tokenAddr : IERC20).balanceOf who
```

#### `call` (mutating)

```lean4
let ok ← call (tokenAddr : IERC20).transferFrom from to amount
```

Authors bind only the return type. `WorldState` threading is implicit — supplied by the export wrapper, like `LOG` opcodes for `WorldF.emit`.

**Example:**
```lean4
@[lsc.external]
def swap (ctx : MsgContext) (zeroForOne : Bool) (amountIn : UInt256) : AMM UInt256 := do
  require (amountIn > 0) .zeroInput
  let (r0, r1) ← load [.reserve0, .reserve1]
  require (r0 > 0 ∧ r1 > 0) .uninitializedPool
  let (tokenIn, tokenOut, rIn, rOut) :=
    if zeroForOne then (← load .token0, ← load .token1, r0, r1)
    else               (← load .token1, ← load .token0, r1, r0)
  let amountOut ← computeAmountOut rIn rOut amountIn
  -- CEI: all stores before all calls
  store [
    .reserve0 := (r0 + if zeroForOne then amountIn  else 0),
    .reserve1 := (r1 - if zeroForOne then 0         else amountOut)
  ]
  call tokenIn.transferFrom ctx.caller self amountIn
  call tokenOut.transfer    ctx.caller      amountOut
  return amountOut
```

#### Typing and errors

`call` composes with `←` in `do`-blocks over `World E`. Callee revert maps to `.error` via a required constructor:

```lean4
@[lsc.error]
inductive AMMError where
  | uninitializedPool
  | zeroInput
  | zeroOutput
  | insufficientLp
  | arith  : ArithError  → AMMError   -- auto-injected
  | extern : ExternError → AMMError   -- required when module uses call
```

### §8.3 Proof erasure

`call` desugars to `Free.liftF (.call ...)`. In `World.runWith`, `.call` dispatches through `worldDispatch` — a function that can be axiomatized for assumed callees or defined concretely for same-repo callees. **Tier 1** proofs over own-state fields work without reasoning about callee storage: `Lsc.run` embeds the state snapshot, runs through call sites, and projects back. Lemma proofs `simp` on contract definitions + CEI ordering; call sites are opaque when they do not affect the fields in the theorem.

### §8.4 Registered vs assumed callees

| Callee kind | Resolution | Proof strength |
|---|---|---|
| **Same-repo** | `src/*.lean` contract + matching interface | Layer 3 via `simulate_call` + callee theorems |
| **Assumed** | `@[extern_assume "IERC20"]` + axioms in `*Lemma.lean` | Trust interface axioms (human-reviewed) |

### §8.5 Reentrancy and CEI

**Primary defense — contract-wide reentrancy lock:** Default `@[lsc.external]` exports are wrapped with a single per-contract lock in `"lsc.reentrancy.lock"` (§4.1, §13.1). The wrapper sets the lock before the author body and clears it on both `.ok` and `.error` paths. While held, any other guarded export reverts. This makes the familiar Solidity pattern (checks → external call → store) safe against classic same-contract reentrancy drains when the lock is active.

**Secondary guidance — CEI linter:** The validator warns when `store` (or `writeSlots`) appears after any **interaction** — `call`, `staticcall`, or `native_transfer!` — anywhere in the transitive call graph from an `@[lsc.external]` or `@[lsc.initialize]` entry (including helpers). Severity: **warning**. Message: `lsc: store after call violates CEI; move stores before calls or add @[lsc.allow_store_after_call]`.

**Suppress CEI warning:** `@[lsc.allow_store_after_call]` on an export silences the warning for that export's closure. Requires an adjacent doc comment containing `cei: <reason>`. The compiler records `"allowStoreAfterCall": true` on the export in artifact metadata (§13.1). Typical use: guarded exports that intentionally store after an external transfer.

**`@[lsc.allow_reentrant]`:** No lock is generated. The CEI warning still applies — authors should write effects before interactions, or add `@[lsc.allow_store_after_call]` with justification when non-CEI ordering is deliberate.

**Free monad semantics:** When `World.runWith` processes a `.call` node, it passes the current `WorldState` (including all `writeSlots` committed so far in source order) to `worldDispatch`. If the callee reenters a guarded export, the lock reverts; if it reenters an `allow_reentrant` export, it sees storage as updated up to that point in the monad — matching EVM semantics when lowering preserves source order (§13.1).

**Not linted (v1):** `emit` after interaction (events commit only on `.ok` anyway); checks-before-effects ordering (convention only).

See [Appendix G](lsc-appendices.md#appendix-g--reentrancy-and-cei) for withdraw, hook, and comparison examples.

### §8.6 Proof tiers for functions with external calls

External calls do **not** force `WorldState` in theorem statements. They force `WorldState` **inside** `Lsc.run` (via `LscState.embed` → `World.runWith` → `LscState.project`). What theorems quantify over depends on **what the property mentions**, not whether the function body contains `call`.

| Tier | Theorem state type | When |
|---|---|---|
| **State snapshot** (default) | `AMM.State`, `Counter.State`, … | Property mentions only this contract's fields — **even if** the function issues `call`/`staticcall` |
| **Scene snapshot** (composition) | Named product (`HookScene`, …) | Property mentions callee fields (Appendix B) |
| **Full simulation** (v2b) | `WorldState` + `simulate_call` | Reentrancy, assumed interfaces, arbitrary account state |

**Tier 1 example** — AMM `swap` calls `IERC20.transferFrom`, but `swap_preserves_k` only mentions reserves. CEI stores reserves before calls; token transfers do not touch AMM slots:

```lean4
-- AMMTheorem.lean
def k (s : AMM.State) : ℕ := s.reserve0.val * s.reserve1.val

theorem swap_preserves_k (ctx : MsgContext) (zeroForOne : Bool) (amountIn : UInt256)
    (s s' : AMM.State) (out : UInt256)
    (h : (swap ctx zeroForOne amountIn).run s = .ok ⟨out, s'⟩) :
    k s ≤ k s' :=
  AMMlemma.swap_preserves_k ctx zeroForOne amountIn s s' out h
```

**Tier 2 example** — MyToken hook → TransferCounter (Appendix B):

```lean4
structure HookScene where
  token   : MyToken.State
  counter : TransferCounter.State

theorem transfer_increments_counter_when_hooked
    (scene scene' : HookScene) (ctx : MsgContext) (to : Address) (amount : UInt256)
    (h : (transfer ctx to amount).run scene = .ok scene') :
    scene'.counter.count = scene.counter.count + 1 := ...
```

Optional: **`scene!`** macro for address layout (same elaboration-time pattern as `state!`).

**Decision rule:** own fields → `Module.State`; named callees → scene product; reentrancy / arbitrary accounts → `WorldState`.

### §8.7 `delegatecall` and upgradeable proxies (v3)

> **v3 status:** `delegatecall` is specified here for proxy semantics and proof architecture; emitter lowering lands in v3 (see [Appendix C](lsc-appendices.md#appendix-c--versioning-roadmap)). `@proxy` state (§3.8) and ERC-7201 implementation layouts (§3.3) are normative in v1.

`WorldF.delegatecall` runs implementation bytecode in the **caller's storage context** — `readSlots`/`writeSlots` during the delegatecall target the **proxy account's** ERC-7201 namespaces, not the implementation contract's address.

```lean4
-- Lsc.Prelude (v3)
-- WorldF.delegatecall : Address → FuncSel → ByteArray → (CallResult → α) → WorldF E α
```

**`World.runWith` semantics:** `.delegatecall impl sel args k` dispatches through `worldDispatch` with `CallKind.delegatecall`. Storage root remains `selfAddress` (the proxy when invoked from proxy exports). Reentrancy lock (§8.5) applies across delegatecall boundaries the same as `call`.

**Proxy deploy flow:**

1. Deploy implementation module (logic bytecode; ERC-7201 layout in artifact).
2. Deploy proxy module (`state! @proxy`); `@[lsc.initialize]` sets `implementation` and `admin`.
3. First-time app init: admin triggers implementation `@[lsc.initialize]` via **delegatecall**; `"lsc.initialized"` namespace prevents replay.
4. Upgrade: admin sets new `implementation` address; frozen namespaces (`"ERC20"`, `"DualVault.vaultA"`, …) unchanged on chain; append-only parent namespaces per §3.9.

Walkthrough: [Appendix H](lsc-appendices.md#appendix-h--proxy-and-upgradeable-storage).

---

## PART II — THE PROOF SYSTEM

---

## §9 Proof Files

### §9.1 Lemma files (`test/*Lemma.lean`)

Lemma files are **AI-generated**. They import the contract module and contain:

- **Action model scaffolding** (`inductive Action`, `applyAction`, `applyActions`) operating over `Module.State`
- **Helper `def`s** used only by proofs (not read by humans)
- **`lemma` proofs** with full tactic bodies

No `sorry`. Kernel-checked.

```lean4
import AMM

inductive AMMAction where
  | swap (ctx : MsgContext) (zeroForOne : Bool) (amountIn : UInt256)
  | addLiquidity (ctx : MsgContext) (amount0 amount1 : UInt256)
  | removeLiquidity (ctx : MsgContext) (lpAmount : UInt256)

def applyAction (s : AMM.State) : AMMAction → AMM.State
  | .swap ctx z a =>
      match (swap ctx z a).run s with
      | .ok ⟨_, s'⟩ => s' | .error _ => s
  | .addLiquidity ctx a0 a1 =>
      match (addLiquidity ctx a0 a1).run s with
      | .ok ⟨_, s'⟩ => s' | .error _ => s
  | .removeLiquidity ctx lp =>
      match (removeLiquidity ctx lp).run s with
      | .ok ⟨_, s'⟩ => s' | .error _ => s

def applyActions (s : AMM.State) (actions : List AMMAction) : AMM.State :=
  actions.foldl applyAction s

lemma swap_preserves_k (ctx : MsgContext) (zeroForOne : Bool) (amountIn : UInt256)
    (s s' : AMM.State) (out : UInt256)
    (hOk : (swap ctx zeroForOne amountIn).run s = .ok ⟨out, s'⟩) :
    s.reserve0.val * s.reserve1.val ≤ s'.reserve0.val * s'.reserve1.val := by
  simp [swap, Lsc.run, load, store, computeAmountOut, LscState,
        UInt256.mulChecked_val, UInt256.addChecked_val,
        UInt256.subChecked_val, UInt256.divChecked_val] at hOk ⊢
  nlinarith [hOk.1, hOk.2]
```

#### Sequence invariants and `Lsc.Invariant`

```lean4
-- Lsc.Prelude
theorem Lsc.Invariant
    {W A : Type} (step : W → A → W) (P : W → Prop)
    (hstep : ∀ (w : W) (a : A), P w → P (step w a))
    (w : W) (actions : List A) (h0 : P w)
    : P (List.foldl step w actions)
```

### §9.2 Theorem files (`test/*Theorem.lean`)

Theorem files are the **requirements document** — written and reviewed by humans. Each `theorem`:
- States a readable business property inline
- Carries a docstring describing the requirement
- Delegates to a homonymous `lemma` in **exactly one line**

```lean4
import AMM
import AMMlemma

def k (s : AMM.State) : ℕ := s.reserve0.val * s.reserve1.val

/-- Constant product never decreases on a successful swap. -/
theorem swap_preserves_k
    (ctx : MsgContext) (zeroForOne : Bool) (amountIn : UInt256)
    (s s' : AMM.State) (out : UInt256)
    (hOk : (swap ctx zeroForOne amountIn).run s = .ok ⟨out, s'⟩) :
    k s ≤ k s' :=
  AMMlemma.swap_preserves_k ctx zeroForOne amountIn s s' out hOk

/-- Constant product is non-decreasing across any sequence of actions. -/
theorem k_nondecreasing (s : AMM.State) (actions : List AMMlemma.AMMAction) :
    k s ≤ k (AMMlemma.applyActions s actions) :=
  AMMlemma.k_nondecreasing s actions
```

### §9.3 Naming convention

- `{function}_{property}` for single-call properties: `swap_preserves_k`, `transfer_no_overdraft`
- `{subject}_{invariant}` for sequence invariants: `k_nondecreasing`, `totalSupply_constant`

### §9.4 Requirements checklist

Every mutating export should have at minimum:

1. A **success theorem** — `(hOk : (f ...).run s = .ok s')` or `(hOk : (f ...).run s = .ok ⟨v, s'⟩)` — what holds after the call
2. A **revert theorem** — `(hErr : (f ...).run s = .error e)` — what inputs cause each revert

Composition theorems use scene snapshots or `WorldState` per §8.6.

Contracts with global invariants additionally need an action model plus an invariant theorem.

### §9.5 Proof authorship

AI writes `*Lemma.lean`. Humans craft `*Theorem.lean`. The Lean kernel is the arbiter for both.

### §9.6 Enforcement rules

| Condition | Result |
|---|---|
| `sorry` in any proof file | FAIL |
| Lean type error | FAIL |
| Required theorem missing | FAIL |
| Theorem body not a single lemma delegation | error |
| `theorem` with no homonymous `lemma` | FAIL (typecheck) |
| `lemma` with no matching `theorem` | warning (helper lemma) |

### §9.7 Writing `.val`-free theorem statements

Theorem files are the requirements document — they should read like a protocol specification. Vocabulary comes from `src/*.lean` (`Module.State`, field names, export names). **Named invariant helpers belong in `*Theorem.lean`**, not `*Lemma.lean`.

#### Named invariant functions (economic properties)

```lean4
-- AMMTheorem.lean (human-reviewed)
def k (s : AMM.State) : ℕ := s.reserve0.val * s.reserve1.val

theorem swap_preserves_k ... (s s' : AMM.State) (h : (swap ...).run s = .ok ⟨out, s'⟩) :
    k s ≤ k s' :=
  AMMlemma.swap_preserves_k ...
```

The homonymous `lemma` in `*Lemma.lean` proves the expanded form (`s.reserve0.val * s.reserve1.val ≤ …`); the theorem goal unfolds `k` definitionally, so one-line delegation typechecks.

#### Multi-field relationships

Prefer direct field access on `Module.State`:

```lean4
theorem addLiquidity_increases_reserves ... (s s' : AMM.State) :
    s'.reserve0 ≥ s.reserve0 ∧ s'.reserve1 ≥ s.reserve1 := ...
```

**Guideline:** `.val` belongs inside theorem helper defs (like `k`), not scattered in every theorem statement type.

---

## §10 Proof Helpers

### §10.1 Layer 1 — Pure (default)

Lemmas proved directly over `@[lsc.external]` functions using `simp [Lsc.run, load, store, LscState, ...]`, `omega`, and `Mapping` lemmas.

**Proof recipe for multi-step functions:**

```lean4
lemma transfer_decrements_balance (ctx : MsgContext) (to : Address) (amount : UInt256)
    (s s' : Token.State) (hOk : (transfer ctx to amount).run s = .ok s') :
    s'.balances[ctx.caller] = s.balances[ctx.caller] - amount := by
  simp [transfer, Lsc.run, load, store, LscState,
        UInt256.subChecked_val, Mapping.get_set_same] at hOk ⊢
  omega
```

**Proof recipe for revert conditions:**

```lean4
lemma transfer_no_overdraft (ctx : MsgContext) (to : Address) (amount : UInt256)
    (s : Token.State)
    (hErr : (transfer ctx to amount).run s = .error (.contract .insufficientBalance)) :
    s.balances[ctx.caller] < amount := by
  simp [transfer, Lsc.run, load, LscState] at hErr
  split_ifs at hErr with hguard
  · omega
  · simp at hErr
```

#### `Except` discriminators

```lean4
@[simp] theorem Except.ok_ne_error {E A : Type} (a : A) (e : E) :
    (Except.ok a : Except E A) ≠ Except.error e := by simp
```

### §10.2 Layer 2 — Wrapped (export bridge)

Used when a lemma must reason about compiler-generated export wrappers. Most contracts do not need this layer.

Layer 1 event proofs can call `World.runCollect` directly on `@[lsc.external]` functions — no export wrapper needed. `Lsc.lift_logs` bridges the export-wrapper return type `Ret × List LogEntry` to `World.runCollect` when reasoning about the compiled artifact.

```lean4
-- Export-wrapper logs match World.runCollect on the internal function
theorem Lsc.lift_logs {α E : Type} (f : World E α) (w : WorldState) :
    exportExecute f w = (World.runCollect f w).map fun (v, w', logs) =>
      (v, logs.map LogEntry.ofEventLog) ...

-- Export with no extern sites equals internal fn then load/store
theorem Lsc.lift_no_extern ...
```

### §10.3 Layer 3 — Composed (cross-contract, v2b)

> **TODO v2b:** `simulate_call` threads `WorldState` through callees and composes callee theorems with caller theorems.

### §10.4 Tactics

**`export_cases`** — destructs `Except E (Ret × List LogEntry)` for Layer 2 goals. For Layer 1 event goals, use `World.runCollect` directly and `simp [World.runCollect, ...]` instead.

---

## §11 Compliance Manifests

### §11.1 Opt-in theorem requirements

```toml
[lsc.compliance.erc20]
theorems = "test/ERC20Theorem.lean"
required = [
  "transfer_preserves_total_supply",
  "transfer_no_overdraft",
  "transfer_no_creation",
  "transfer_self_noop",
  "approve_sets_allowance",
  "transferFrom_respects_allowance",
  "transferFrom_decrements_allowance",
  "transferFrom_respects_balance",
  "constructor_mints_initial_supply",
  "constructor_sets_metadata",
]
```

### §11.2 Proof runner verification

For each listed name the runner checks:
1. A `theorem <name>` exists in the corresponding `*Theorem.lean`.
2. The theorem body is a one-line `*Lemma.<name>` delegation.
3. A homonymous `lemma <name>` typechecks in `*Lemma.lean`.

### §11.3 ERC-20 required theorems

| Group | Theorem | Statement summary |
|---|---|---|
| Transfer | `transfer_preserves_total_supply` | `totalSupply` unchanged on success |
| Transfer | `transfer_no_overdraft` | insufficient balance → error |
| Transfer | `transfer_no_creation` | tokens conserved between distinct parties |
| Transfer | `transfer_self_noop` | `from = to` → world unchanged |
| Approve | `approve_sets_allowance` | allowance equals requested amount |
| Approve | `increaseAllowance_additive` | allowance increases by delta |
| Approve | `decreaseAllowance_subtractive` | allowance decreases by delta |
| TransferFrom | `transferFrom_respects_allowance` | insufficient allowance → error |
| TransferFrom | `transferFrom_decrements_allowance` | allowance reduced by amount |
| TransferFrom | `transferFrom_respects_balance` | insufficient balance → error |
| Constructor | `constructor_mints_initial_supply` | deployer balance = `initialSupply` |
| Constructor | `constructor_sets_metadata` | `name`, `symbol`, `decimals` stored correctly |

---

## PART III — TOOLCHAIN BOUNDARY

---

## §12 Validator

Runs as a post-elaboration pass. All messages use prefix `lsc:` with file, line, and column. **Hard errors** abort compilation. **Warnings** are reported but do not abort.

### §12.1 Contract module errors

| Construct | Severity | Error message |
|---|---|---|
| `Nat`, `Int`, `Float` | error | `lsc: use UInt256` |
| `String`, `Char` | error | `lsc: use Bytes[N]` |
| Closures / lambda capturing outer variable | error | `lsc: use a top-level function` |
| Partial application | error | `lsc: partial application not supported` |
| `IO`, `StateM`, `ST` | error | `lsc: stateful monads not allowed; use World E` |
| Higher-order functions | error | `lsc: functions cannot be passed as arguments` |
| Unbounded recursion | error | `lsc: recursive function must be structurally terminating` |
| `List` or `Array` in author code | error | `lsc: use Mapping` |
| `structure … extends` | error | `lsc: storage inheritance not supported in v1` |
| Hand-written export wrapper | error | `lsc: use @[lsc.external]` |
| `sload`/`sstore`/`ssload`/`readSlots`/`writeSlots` in author code | error | `lsc: storage IO is emitter-only; use load/store` |
| `store .field v` or tuple pairs in `store [ … ]` | error | `lsc: store requires record-update syntax [ .field := v ]` |
| Dynamic key in batch `load [ … ]` list | error | `lsc: batch load requires static schema fields` |
| `WorldState` as function parameter | error | `lsc: WorldState not allowed as function parameter; use load/store` |
| Error type without `@[lsc.error]` | error | `lsc: error type must be declared with @[lsc.error]` |
| `@[lsc.error]` type missing `arith` constructor | error | `lsc: error type must include arith : ArithError → E` |
| `@[lsc.error]` type missing `extern` constructor when `call` used | error | `lsc: error type must include extern : ExternError → E` |
| `@[lsc.error]` type missing `eth` constructor when `native_transfer!` used | error | `lsc: error type must include eth : EthError → E` |
| `@[lsc.error]` type missing `LscError` instance | error | `lsc: error type must have a LscError instance` |
| Invalid `@[lsc.external]` return shape | error | `lsc: must return World E α` |
| Unresolved polymorphism | error | `lsc: polymorphic function cannot be compiled` |
| `Bytes[N]` literal longer than `N` | error | `lsc: Bytes literal exceeds declared bound` |
| More than one `@[lsc.initialize]` | error | `lsc: at most one @[lsc.initialize] per contract module` |
| `call`/`staticcall` in `test/*Lemma.lean` or `test/*Theorem.lean` | error | `lsc: extern calls not allowed in proof files` |
| `store` after interaction in export transitive closure | warning | `lsc: store after call violates CEI; move stores before calls or add @[lsc.allow_store_after_call]` |
| `@[lsc.allow_store_after_call]` on export | — | suppresses CEI warning for that export's closure |
| `@[lsc.allow_store_after_call]` without `cei:` doc comment | error | `lsc: allow_store_after_call requires cei: justification comment` |
| `@[lsc.allow_reentrant]` | warning | `lsc: reentrant export; ensure CEI is manually verified` |
| `Address` parameter named `caller`/`sender`/`from` used for auth | warning | `lsc: prefer ctx.caller from MsgContext` |
| `state!` with zero fields | warning | `lsc: empty state struct` |
| `load`/`store` on name not in `state!` schema | error | `lsc: unknown storage slot` |
| More than one unnamed `state!` per module | error | `lsc: at most one state! where per contract module` |
| `state!` with both `@proxy` and `@namespace` | error | `lsc: @proxy and @namespace are mutually exclusive` |
| More than one `state! @proxy` per module | error | `lsc: at most one state! @proxy per contract module` |
| Duplicate ERC-7201 namespace id in one contract | error | `lsc: duplicate storage namespace` |
| Nested layout field: type not from imported `state!` | error | `lsc: unknown layout type` |
| Layout type used for external token reference | error | `lsc: use IERC20 for external token references, not nested ERC20 layout` |
| `state!` field type: not storable and not layout/interface ref | error | `lsc: invalid state field type` |
| `self` as `state!` field or author `def` | error | `lsc: self is reserved for the implicit contract address` |
| `@[lsc.schema]` migration: reorder/retype/remove field in namespace | error | `lsc: breaking storage migration` |
| `@[lsc.schema]` migration: rename namespace or instance id | error | `lsc: breaking namespace id change` |

### §12.2 Proof module rules

| Condition | Severity |
|---|---|
| `sorry` | error |
| `+?` / `-?` / `*?` / `/?` in proof goal (not hypothesis) | warning: use `UInt256.addChecked_val` bridge lemma |
| `axiom` without `@[extern_assume]` | warning |
| `theorem` with no homonymous `lemma` | error (typecheck) |
| `lemma` with no matching `theorem` | warning (helper lemma) |

---

## §13 Emitter and Lowering

### §13.1 Export wrapper generation

For each `@[lsc.external] def f (ctx : MsgContext) (p₁ : T₁) ... : ContractM α`, the emitter generates:

1. **ABI dispatcher** — 4-byte selector from `keccak256(canonicalSignature(f))`; ABI-decode calldata into `(p₁, ...)`.
2. **`MsgContext` binding** — `ctx.caller := CALLER`, `ctx.value := CALLVALUE`, etc.
3. **Reentrancy lock** (unless `@[lsc.allow_reentrant]`) — one **contract-wide** slot in compiler namespace `"lsc.reentrancy.lock"` (not in author `state!` — §3.3):
   - `require lock == 0` (else revert)
   - `lock := 1`
   - on both success and revert paths after the author body: `lock := 0`
4. **Execute** — lower `f`'s `World` term to Yul in **source order** (inlined; no Lean runtime):
   - each `readSlots` / `load` → `SLOAD` at the corresponding program point
   - each `writeSlots` / `store` → inline `SSTORE` at the corresponding program point (**before** any subsequent `call` / `staticcall` / `native_transfer!` in the tree)
   - each `call` / `staticcall` / `native_transfer!` → `CALL` / `STATICCALL` at the corresponding program point
   - each `emit` → collected; `LOG` opcodes emitted on the success path in source order before `RETURN`
5. **On `.ok (v, w')`** — ABI-encode `v`; `RETURN`.
6. **On `.error e`** — `REVERT` with `abi.encode(e)`; no `LOG`; lock cleared; no storage from the failing path persists (monadic rollback semantics).

**Lowering invariant:** Observable self-storage at each external-call boundary in generated bytecode matches `World.runWith` at that point in the free-monad tree. Pre-call `writeSlots` must not be deferred past the next `call` node (§13.3).

**Artifact metadata:** Per export entry in `out/<Contract>.lean/<Contract>.json`:

```json
{
  "name": "withdraw",
  "allowReentrant": false,
  "allowStoreAfterCall": true
}
```

`allowStoreAfterCall` is `true` when `@[lsc.allow_store_after_call]` is present.

### §13.2 Storage layout derivation

**ERC-7201 namespaces** (default): each namespace id maps to root `erc7201(id)` (§3.3). Fields map to `root + offset` in declaration order within that namespace. Nested layout instances each own a namespace (auto `"Parent.field"` or field `@namespace` override — §3.7). The mapping from `(namespace, offset)` to absolute slot is stable for a given schema version. Reordering or retyping fields within a namespace is a breaking change (validator error under `@[lsc.schema]` — §3.9).

**Proxy modules** (`@proxy`): fields map to EIP-1967 fixed slots (§3.8). Artifact: `"layout": "proxy"`.

**Compiler-reserved namespaces:** `"lsc.reentrancy.lock"`, `"lsc.initialized"` — roots computed at emit time; omitted from author `state!`.

`Mapping` entries: mapping root at `root + offset` for the field; entry at key `k` at `keccak256(abi.encode(k, root + offset))` with ABI-padded key — identical to Solidity layout within the namespace.

**Artifact `storageLayout`** (§3.9): lists all namespaces (`id`, computed `root`, `fields` with `offset` and `type`), `schemaId`, and `layout` (`erc7201` | `proxy`). Emitted in `out/<Contract>.lean/<Contract>.json` metadata.

### §13.3 Formal verification of lowering

The lowering pipeline is verified in Lean. Key theorems:

```lean4
-- State: compiled export matches World.run
theorem lowering_correct {E α : Type} (f : World E α) (w : WorldState) :
    evmExecute (compile f) w = World.run f w

-- Batch IR nodes equal sequential single-entry interpretation
theorem readSlots_eq_seq {E α : Type} (addr : Address) (es : Array ReadEntry) (k : Array UInt256 → World E α) (w : WorldState) :
    World.run (Free.liftF (.readSlots addr es k)) w =
    World.run (es.foldlM (fun _ e => Free.liftF (.readSlots addr #[e] (·))) k) w

theorem writeSlots_eq_seq {E α : Type} (addr : Address) (es : Array WriteEntry) (next : World E α) (w : WorldState) :
    World.run (Free.liftF (.writeSlots addr es next)) w =
    World.run (es.foldlM (fun acc e => Free.liftF (.writeSlots addr #[e] acc)) next) w

-- Logs: compiled LOG opcodes match World.runCollect (source order)
theorem lowering_logs_correct {E α : Type} (f : World E α) (w : WorldState) :
    evmExecuteLogs (compile f) w =
      (World.runCollect f w).map fun (v, w', logs) => (v, w', logs)

-- Storage layout matches Solidity for all field types
theorem slot_layout_matches_solidity (schema : StorageSchema) :
    compileSlots schema = soliditySlots schema

-- Observable storage at each call boundary matches World.runWith
theorem lowering_reentrancy_refines {E α : Type} (f : World E α) (w : WorldState) :
    ∀ (w_at_call : WorldState) (call_site : CallSite),
      call_site ∈ callSites (compile f) →
      evmStorageAt call_site (evmExecuteUpTo (compile f) w call_site) =
        w_at_call.storage self :=
      w_at_call = World.runUpTo f w call_site
```

---

## §14 Full AMM Example

The complete AMM contract under the updated model:

```lean4
import Lsc.Prelude
import IERC20
open Lsc

-- ── Errors ───────────────────────────────────────────────────────────────────

@[lsc.error]
inductive AMMError where
  | uninitializedPool
  | zeroInput
  | zeroOutput
  | insufficientLp
  -- auto-injected: | arith : ArithError → AMMError
  -- required when using call:
  | extern : ExternError → AMMError

-- ── State schema ──────────────────────────────────────────────────────────────

state! where                              -- erc7201:"AMM"
  token0 token1 : IERC20              -- offset 0–1: external IERC20 refs (stored as address)
  reserve0   : UInt256                 -- offset 2
  reserve1   : UInt256                 -- offset 3
  totalLP    : UInt256                 -- offset 4
  lpBalances : Mapping Address UInt256 -- offset 5

-- abbrev AMM := World AMMError  (auto-generated)

-- ── Private helpers ───────────────────────────────────────────────────────────

private def computeAmountOut (reserveIn reserveOut amountIn : UInt256) : AMM UInt256 := do
  let num   ← reserveOut *? amountIn
  let denom ← reserveIn  +? amountIn
  let out   ← num /? denom
  require (out > 0) .zeroOutput
  return out

-- ── Initialize ────────────────────────────────────────────────────────────────

@[lsc.initialize]
def initialize (token0 token1 : Address) : AMM Unit := do
  store [
    .token0 := token0,
    .token1 := token1,
    .reserve0 := 0,
    .reserve1 := 0,
    .totalLP := 0
  ]

-- ── Swap ──────────────────────────────────────────────────────────────────────

@[lsc.external]
def swap (ctx : MsgContext) (zeroForOne : Bool) (amountIn : UInt256) : AMM UInt256 := do
  require (amountIn > 0) .zeroInput
  let (r0, r1) ← load [.reserve0, .reserve1]
  require (r0 > 0 ∧ r1 > 0) .uninitializedPool
  let (tokenIn, tokenOut, rIn, rOut) :=
    if zeroForOne then (← load .token0, ← load .token1, r0, r1)
    else               (← load .token1, ← load .token0, r1, r0)
  let amountOut ← computeAmountOut rIn rOut amountIn
  -- CEI: all stores before all calls
  store [
    .reserve0 := (r0 + if zeroForOne then amountIn  else 0),
    .reserve1 := (r1 - if zeroForOne then 0         else amountOut)
  ]
  call tokenIn.transferFrom ctx.caller self amountIn
  call tokenOut.transfer    ctx.caller      amountOut
  return amountOut

-- ── Add liquidity ─────────────────────────────────────────────────────────────

@[lsc.external]
def addLiquidity (ctx : MsgContext) (amount0 amount1 : UInt256) : AMM UInt256 := do
  require (amount0 > 0 ∧ amount1 > 0) .zeroInput
  let (r0, r1, total) ← load [.reserve0, .reserve1, .totalLP]
  let lp ← if total = 0 then
    -- first deposit: geometric mean
    do let prod ← amount0 *? amount1; sqrt? prod
  else do
    let share0 ← do let n ← amount0 *? total; n /? r0
    let share1 ← do let n ← amount1 *? total; n /? r1
    return (min share0 share1)
  require (lp > 0) .zeroOutput
  -- CEI: all stores before all calls
  store [
    .reserve0 := (r0    + amount0),
    .reserve1 := (r1    + amount1),
    .totalLP := (total + lp)
  ]
  let prevBal ← load (.lpBalances ctx.caller)
  store [ (.lpBalances ctx.caller) := (prevBal + lp) ]
  let (t0, t1) ← load [.token0, .token1]
  call t0.transferFrom ctx.caller self amount0
  call t1.transferFrom ctx.caller self amount1
  return lp

-- ── Remove liquidity ──────────────────────────────────────────────────────────

@[lsc.external]
def removeLiquidity (ctx : MsgContext) (lpAmount : UInt256) : AMM (UInt256 × UInt256) := do
  require (lpAmount > 0) .zeroInput
  let bal ← load (.lpBalances ctx.caller)
  require (bal ≥ lpAmount) .insufficientLp
  let (r0, r1, total) ← load [.reserve0, .reserve1, .totalLP]
  let amount0 ← do let n ← r0 *? lpAmount; n /? total
  let amount1 ← do let n ← r1 *? lpAmount; n /? total
  require (amount0 > 0 ∧ amount1 > 0) .zeroOutput
  -- CEI: all stores before all calls
  store [
    .reserve0 := (r0    - amount0),
    .reserve1 := (r1    - amount1),
    .totalLP := (total - lpAmount),
    (.lpBalances ctx.caller) := (bal  - lpAmount)
  ]
  let (t0, t1) ← load [.token0, .token1]
  call t0.transfer ctx.caller amount0
  call t1.transfer ctx.caller amount1
  return (amount0, amount1)
```

And the corresponding theorem file:

```lean4
import AMM
import AMMlemma

def k (s : AMM.State) : ℕ := s.reserve0.val * s.reserve1.val

/-- Constant product never decreases on a successful swap. -/
theorem swap_preserves_k
    (ctx : MsgContext) (zeroForOne : Bool) (amountIn : UInt256)
    (s s' : AMM.State) (out : UInt256)
    (hOk : (swap ctx zeroForOne amountIn).run s = .ok ⟨out, s'⟩) :
    k s ≤ k s' :=
  AMMlemma.swap_preserves_k ctx zeroForOne amountIn s s' out hOk

/-- Adding liquidity strictly increases reserves. -/
theorem addLiquidity_increases_reserves
    (ctx : MsgContext) (amount0 amount1 : UInt256)
    (s s' : AMM.State) (lp : UInt256)
    (hOk : (addLiquidity ctx amount0 amount1).run s = .ok ⟨lp, s'⟩) :
    s'.reserve0 ≥ s.reserve0 ∧ s'.reserve1 ≥ s.reserve1 :=
  AMMlemma.addLiquidity_increases_reserves ctx amount0 amount1 s s' lp hOk

/-- Removing liquidity strictly decreases reserves. -/
theorem removeLiquidity_decreases_reserves
    (ctx : MsgContext) (lpAmount : UInt256)
    (s s' : AMM.State) (amounts : UInt256 × UInt256)
    (hOk : (removeLiquidity ctx lpAmount).run s = .ok ⟨amounts, s'⟩) :
    s'.reserve0 ≤ s.reserve0 ∧ s'.reserve1 ≤ s.reserve1 :=
  AMMlemma.removeLiquidity_decreases_reserves ctx lpAmount s s' amounts hOk

/-- Total LP supply is non-decreasing across any sequence of actions. -/
theorem totalLP_nondecreasing
    (s : AMM.State) (actions : List AMMlemma.AMMAction) :
    s.totalLP ≤ (AMMlemma.applyActions s actions).totalLP :=
  AMMlemma.totalLP_nondecreasing s actions
```

---

## Appendix A — Design Decisions

### A.1 Why `World E` free monad instead of `StateT WorldState (Except E)`

Both model state access and rollback-on-error. The key differences:

| | `StateT WorldState (Except E)` | `World E` free monad |
|---|---|---|
| Rollback on error | ✓ | ✓ |
| Multiple interpreters | ✗ | ✓ |
| EVM codegen handler | ✗ | ✓ |
| Test/trace handler | ✗ | ✓ |
| `simp` reduces cleanly | ✓ | ✓ (via bridge lemmas) |
| Reentrancy visible | ✓ | ✓ |

The free monad allows the same function term to be interpreted by `World.run` for proofs, by `evmHandler` for codegen, and by `traceHandler` for testing — without changing the function. `StateT` would require different function implementations per interpretation.

### A.2 Why `state!` struct as schema, not passed state in contract functions

Passing `s : AMM.State` as a **contract function parameter** was clean for proofs but created a mismatch with EVM semantics: the EVM does not pass state as a value, it loads it from storage. The `state!` model aligns authoring with EVM reality:

- Authors think in named fields (`load .reserve0`, `store [ .reserve0 := v ]`) not slot numbers
- The compiler owns the slot assignment; authors cannot accidentally collide slots
- The same struct is the **proof snapshot** in theorem files (`s s' : AMM.State`, `s'.reserve0`)
- The schema is the single source of truth for both codegen and proofs

The struct declared by **`state!`** is the schema at authoring time (`load`, `store [ … := … ]`) and the proof snapshot at verification time (`s.field` in theorems). It is never an on-chain function parameter.

### A.3 Why no inheritance

`structure … extends` creates slot-layout ambiguity in upgradeable proxy patterns, fragile base class issues, and C3 linearization surprises. Auditors cannot read a contract top-to-bottom without tracing an inheritance tree. LSC composes storage via **nested layout fields** (§3.7) with per-instance ERC-7201 namespaces — explicit, collision-free, and proof-friendly (`s.token.balances` on nested snapshots). Vyper takes the same position on `extends`.

### A.5 Why ERC-7201 namespaced storage

Sequential slot-0 layout makes multi-layout composition and upgrades fragile (prefix slots must stay stable; proxy and app state can collide). ERC-7201 gives each namespace an isolated root derived from a string id — lib layouts (`"ERC20"`), nested instances (`"DualVault.vaultA"`), and contract scalars (`"MyToken"`) coexist without collision. EIP-1967 proxy metadata (`@proxy`) stays orthogonal. Authors keep `load`/`store` syntax; the compiler owns root computation and artifact export.

### A.4 Why contract-wide lock + CEI linter (not type-level CEI)

Type-level enforcement of checks-effects-interactions (e.g. indexing `World` by phase so `store` after `call` is ill-typed) was considered and rejected for v1. It adds elaborator complexity, hurts `do`-notation ergonomics, and fights the common guarded pattern (external call then store) that the reentrancy lock already makes safe.

The chosen model:

| Layer | Mechanism | Role |
|---|---|---|
| **Primary** | Contract-wide reentrancy lock on default exports | Blocks reentry during external calls; makes store-after-call safe for classic drain attacks |
| **Guidance** | CEI linter (warning, interprocedural) | Nudges toward effects-before-interactions; especially important on `@[lsc.allow_reentrant]` exports |
| **Opt-out** | `@[lsc.allow_store_after_call]` + `cei:` comment | Suppresses the warning when non-CEI ordering is intentional; recorded in artifact metadata |

Flat `World E` is unchanged. Lowering preserves source order so `World.runWith` and on-chain observability agree at call boundaries (§13.1, §13.3).