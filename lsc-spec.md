# LSC — Lean Smart Contracts Language Specification

**Language version:** LSC 1.0
**Lean baseline:** `leanprover/lean4:stable` (pinned per project)
**Execution target:** EVM (bytecode via formally-verified lowering; standard JSON ABI)
**Companion document:** [lsc-toolchain.md](lsc-toolchain.md) — reference compiler, Foundry integration, artifacts, demos

---

## §1 Overview

### §1.1 What LSC is

**LSC (Lean Smart Contracts)** is a strict subset of Lean 4 for writing smart contracts whose correctness properties are machine-checked by the Lean kernel before deployment.

Authors write **pure state-transition functions** in Lean. The compiler generates everything the EVM needs — ABI wrappers, storage load/store, LOG opcodes, CALL lowering. Authors never touch `sload`, `sstore`, ABI encoding, or log assembly directly.

This restriction is intentional. Lean's kernel checks proofs about pure functions automatically. The moment authors write storage IO or ABI ceremony, proofs become hard. LSC restricts the *language* rather than what you can deploy — the same tradeoff Vyper makes for security, applied here for provability.

**What you can deploy:** persistent storage and mappings, events/logs, standard ABIs (ERC-20 `bool` returns, etc.), ETH transfers, cross-contract calls, revert semantics, full EVM bytecode.

**What is restricted in author code:** stateful monads (`StateM`, `IO`), higher-order functions, closures, unbounded collections in state, `Nat`/`Int`/`String`, `structure … extends`, unbounded recursion, manual storage IO. `do`-notation over `Except E` is allowed for fallible exports. See §12 for the full validator error table.

### §1.2 What the compiler generates vs what authors write

Authors write pure functions. The compiler generates everything else at `@[Lsc.external]` boundaries:

| Author writes | Compiler generates |
|---------------|--------------------|
| `@[Lsc.external] def increment (s : CounterState) : Except ArithError CounterState` | ABI dispatcher, `sload` all fields, call `increment`, on `.ok s'` → `sstore`, on `.error e` → `revert(abi.encode(e))` |
| `@[Lsc.public]` on a State field (e.g. `number`) | `@[Lsc.external]` view + lazy slot read (§3.5) |
| `emit! TransferEvent from to amount` in function body | `LOG2` opcode after store, with correct topic0 and ABI-encoded data |
| `ctx : MsgContext` parameter | bound to `msg.sender`, `msg.value`, `block.timestamp`, `block.number` (§5.1); `@[Lsc.payable]` marks function payable (§5.2) |

Proofs target the author-written functions directly — the same signatures that get deployed. The lowering pipeline is formally verified in Lean (§13.3).

### §1.3 The three modules

Every LSC project produces three module kinds per contract. There is no `spec/` directory.

| File | Role | Kernel-checked |
|------|------|---------------|
| `src/Counter.lean` | Contract — `State` struct + `@[Lsc.external]` functions | Yes (types) |
| `test/CounterLemma.lean` | Lemma — action model scaffolding + `lemma` proofs | Yes (full proof check) |
| `test/CounterTheorem.lean` | Theorem — high-level requirements, one-line lemma delegations | Yes (full proof check) |

The **contract** is what deploys. The **theorem** file is the requirements document — written and reviewed by humans. Each `theorem` states a readable business property inline and delegates to a homonymous `lemma` in exactly one line. The **lemma** file is AI-generated and holds scaffolding (`CounterAction`, `applyAction`, `applyActions`) plus all tactic proofs; humans do not review it. The Lean kernel checks both files.

**End-to-end Counter example:**

`src/Counter.lean`:
```lean
import Lsc.Prelude
open Lsc

structure CounterState where
  @[Lsc.public]
  number : UInt256

@[Lsc.external]
def increment (s : CounterState) : Except ArithError CounterState := do
  let n ← s.number +? 1
  return .ok { s with number := n }
```

`test/CounterTheorem.lean`:
```lean
import Counter
import CounterLemma

/-- On success, increment increases number by exactly 1. -/
theorem increment_increases_number (s s' : CounterState) (h : increment s = .ok s') :
    s'.number = s.number + 1 :=
  CounterLemma.increment_increases_number s s' h

/-- increment errors iff number is at UInt256 max. -/
theorem increment_overflows_iff (s : CounterState) (h : increment s = .error .overflow) :
    s.number = UInt256.max :=
  CounterLemma.increment_overflows_iff s h

/-- No sequence of actions can decrease the number. -/
theorem number_never_decreases (s : CounterState) (actions : List CounterLemma.CounterAction) :
    (CounterLemma.applyActions s actions).number ≥ s.number :=
  CounterLemma.number_never_decreases s actions
```

```mermaid
flowchart LR
  Contract[Counter.lean] --> Lemma[CounterLemma.lean]
  Lemma --> Theorem[CounterTheorem.lean]
  Theorem --> Kernel[Lean kernel ✓]
```

`test/CounterLemma.lean`:
```lean
import Counter

inductive CounterAction where
  | increment

def applyAction (s : CounterState) : CounterAction → CounterState
  | .increment =>
      match increment s with
      | .ok s'   => s'
      | .error _ => s

def applyActions (s : CounterState) (actions : List CounterAction) : CounterState :=
  actions.foldl applyAction s

lemma increment_increases_number (s s' : CounterState) (h : increment s = .ok s') :
    s'.number = s.number + 1 := by
  rw [UInt256.eq_iff]
  simp [increment, UInt256.addChecked_val] at h ⊢; omega

lemma increment_overflows_iff (s : CounterState) (h : increment s = .error .overflow) :
    s.number = UInt256.max := by
  simp [increment, UInt256.addChecked_error (by omega)] at h; omega

lemma number_never_decreases (s : CounterState) (actions : List CounterAction) :
    (applyActions s actions).number ≥ s.number := by
  simp only [applyActions]
  apply Lsc.Invariant applyAction (fun s' => s'.number ≥ s.number)
  · intro s' a hP; cases a <;> simp [applyAction, increment, UInt256.addChecked_val, UInt256.le_iff] at hP ⊢ <;> omega
  · simp
```

### §1.4 Non-goals (v1)

- Upgradeability / proxies
- `structure … extends` storage inheritance (see §3.3)
- Gas optimization in the proof model
- Mandatory application compliance packs in the language definition

For `lakefile.lean` layout, see [lsc-toolchain.md §2](lsc-toolchain.md#2-project-layout-and-lake).

---

## PART I — THE CONTRACT LANGUAGE

---

## §2 Types

### §2.1 Primitive types

| LSC type | Lean definition | EVM/ABI type | Notes |
|----------|----------------|--------------|-------|
| `UInt256` | `{ n : ℕ // n < 2^256 }` | `uint256` | Bounded; no default `+ - * /` — use `+?` or `+↻` |
| `Address` | `structure Address where val : UInt256` | `address` | Not coercible to `UInt256` without `.val` |
| `Bool` | Lean built-in | `bool` | |
| `Bytes32` | `structure Bytes32 where val : UInt256` | `bytes32` | Opaque 32-byte word; not coercible to `UInt256` |
| `Bytes[N]` | `{ b : ByteArray // b.size ≤ N }` | `bytes` / `string` | Bounded; see §2.2 |

#### Arithmetic semantics

`UInt256` is a bounded natural subtype at the ABI/storage boundary. It does **not** inherit `Fin`'s modular `Add`/`Mul` instances — plain `+ - * /` on `UInt256` are a **type error** in author code. Two explicit operator families:

| Mode | Syntax | Returns | Use when |
|------|--------|---------|----------|
| Checked | `a +? b` | `Except E UInt256` | **default** — overflow reverts (Solidity default) |
| Wrapping | `a +↻ b` | `UInt256` | Intentional mod-2²⁵⁶ — Solidity `unchecked { }` |

Same pattern for `-?`/`-↻`, `*?`/`*↻`, `/?` (checked; divide-by-zero reverts). Modular add/sub/mul use `+↻ -↻ *↻`; division has no modular wrap on EVM — use `/?` or `UInt256.divMod a b hb` when `b ≠ 0`.

The wrap suffix ↻ is U+21BB (clockwise open circle arrow), paired with the checked suffix `?`.

Checked arithmetic returns `Except E _` via the in-scope `LscError E` instance. Compose with `←` in a `do`-block over `Except E`. See §2.5.

**Comparisons:** `=`, `≤`, `≥`, `<`, `>` on `UInt256` compare via `.val` (prelude instances). Theorem statements use `s'.field = s.field + 1` and `s'.field ≥ s.field` — not `.val`.

**Lemma files:** `+?` is contract-only (§12.2). `UInt256 + ℕ` literal add (`addNat` / `HAdd`) is for proof goals only — validator forbids it in contract modules. Use `+↻` for modular `UInt256` algebra; use named `ℕ` helpers (§9.7) for nonlinear invariants like `k s`.

### §2.2 Bytes[N]

`Bytes[N]` is a Vyper-style bounded byte array. Both spellings are valid; `Bytes[N]` is the canonical form in LSC.

```lean
-- Lsc.Prelude
abbrev Bytes (n : Nat) := { b : ByteArray // b.size ≤ n }
notation "Bytes[" n "]" => Bytes n
-- Both Bytes[64] and Bytes 64 are accepted; Bytes[N] is preferred.
```

**Storage layout** (identical to Vyper/Solidity):
- `b.size ≤ 31`: left-aligned in slot, `b.size * 2` in LSB.
- `b.size > 31`: slot `p` holds `b.size * 2 + 1`; payload at `keccak256(p)` in 32-byte chunks.

**Validator rules:** `N` must be a numeric literal. `N = 0` is a warning.

### §2.3 Mapping

`Mapping K V` is a plain Lean 4 function, matching Vyper's `HashMap` model:

```lean
-- Lsc.Prelude
abbrev Mapping (K V : Type) := K → V

namespace Mapping
def get (m : Mapping K V) (k : K) : V := m k
def set [DecidableEq K] (m : Mapping K V) (k : K) (v : V) : Mapping K V :=
  Function.update m k v
def empty [Inhabited V] : Mapping K V := fun _ => default
end Mapping

scoped notation m:65 "[" k:65 "]" => Mapping.get m k
scoped notation m:65 "[" k:65 " := " v:65 "]" => Mapping.set m k v
```

**Storage layout:** slot `p` for a `Mapping` field; entry at key `k` lives at `keccak256(abi.encode(k, p))` using ABI-encoded (padded) key encoding — identical to Solidity. Test vector:

```
slot p = 4, key k = address(0xABCD...):
entry slot = keccak256(
  0x000000000000000000000000ABCD...   -- address, padded to 32 bytes
  0x0000000000000000000000000000000000000000000000000000000000000004  -- slot index
)
```

Nested mappings (e.g. ERC-20 allowances) are `Mapping K (Mapping K' V)`. Reads chain: `s.allowances[owner][spender]`. Writes nest: `s.allowances[owner := s.allowances[owner][spender := amount]]`.

**Simp laws** (derived from `Function.update`; no custom axioms):

```lean
@[simp] theorem Mapping.get_set_same [DecidableEq K] (m : Mapping K V) (k : K) (v : V) :
    (m.set k v).get k = v := Function.update_same k v m

@[simp] theorem Mapping.get_set_other [DecidableEq K] (m : Mapping K V)
    (k k' : K) (v : V) (h : k ≠ k') :
    (m.set k v).get k' = m.get k' := Function.update_noteq h v m

@[simp] theorem Mapping.get_empty [Inhabited V] (k : K) :
    (Mapping.empty : Mapping K V).get k = default := rfl

@[simp] theorem Mapping.set_set_same [DecidableEq K] (m : Mapping K V) (k : K) (v v' : V) :
    (m.set k v).set k v' = m.set k v' := Function.update_idem k v v' m
```

> **Why `K → V` instead of `Finsupp`?** Contracts never enumerate or sum over keys. A plain function is the minimal model that makes `simp [Mapping.get_set_same]` work with no extra instances.

Bracket notation (`m[k]`, `m[k := v]`) is preferred in author examples; it desugars to `Mapping.get` / `Mapping.set`.

### §2.4 Except

LSC uses Lean 4's standard `Except E A` for fallible functions. No custom `Result` type is defined.

The four return shapes:

| Shape | Meaning |
|-------|---------|
| `S` | Infallible mutator |
| `V` | Infallible view |
| `Except E S` | Fallible mutator, no ABI return value |
| `Except E (S × V)` | Fallible mutator with return value |

`.ok val` — success; emitter persists state and ABI-encodes the non-state component.
`.error e` — EVM revert; emitter ABI-encodes `e` as a Solidity custom error.

### §2.5 Error types, arithmetic errors, and `LscError`

#### `@[Lsc.error]` — declaring contract error types

Registers the inductive with the emitter for ABI `errors` generation and revert encoding.

Every `@[Lsc.error]` type **must** include an `arith` constructor and a `LscError` instance. This is enforced by the validator (§12.1). It makes the arithmetic fault channel part of the error type's contract — LSC does not allow error types that silently discard arithmetic faults.

```lean
@[Lsc.error]
inductive TokenError where
  | insufficientBalance
  | insufficientAllowance
  | unauthorized
  | arith : ArithError → TokenError
  deriving DecidableEq, Repr

instance : LscError TokenError where
  arith := .arith
```

The `arith` constructor and `LscError` instance can be auto-derived by the `@[Lsc.error]` attribute — authors may omit them and the attribute will inject both:

```lean
-- Equivalent shorthand: @[Lsc.error] derives arith constructor + LscError instance automatically
@[Lsc.error]
inductive TokenError where
  | insufficientBalance
  | insufficientAllowance
  | unauthorized
  deriving DecidableEq, Repr
-- arith : ArithError → TokenError and instance LscError TokenError injected by @[Lsc.error]
```

#### `ArithError` — prelude arithmetic error type

```lean
-- Lsc.Prelude
inductive ArithError where
  | overflow
  | divisionByZero
  deriving DecidableEq, Repr
```

#### `LscError` — the arithmetic fault typeclass

```lean
-- Lsc.Prelude
class LscError (E : Type) where
  arith : ArithError → E

-- ArithError is its own LscError (identity instance, for simple contracts)
instance : LscError ArithError where
  arith := id
```

This typeclass is the mechanism by which `+?`, `-?`, `*?`, `/?` inject arithmetic faults into any error type `E` without an explicit lift at every call site. The instance is resolved at elaboration time.

#### Type definition and projections

```lean
-- Lsc.Prelude
abbrev UInt256 := { n : ℕ // n < 2^256 }

namespace UInt256
def val (a : UInt256) : ℕ := a.1
def mk (n : ℕ) (h : n < 2^256) : UInt256 := ⟨n, h⟩
def max : UInt256 := ⟨(2^256 - 1), by omega⟩

instance : DecidableEq UInt256 :=
  ⟨fun a b => decide (a.val = b.val), by intros; simp [UInt256.val]; exact Subtype.ext_iff.mpr⟩

instance : LE UInt256 where le a b := a.val ≤ b.val
instance : LT UInt256 where lt a b := a.val < b.val
instance : DecidableLE UInt256 := ⟨fun a b => decide (a.val ≤ b.val), by intros; simp [UInt256.le_iff]⟩
instance : DecidableLT UInt256 := ⟨fun a b => decide (a.val < b.val), by intros; simp [UInt256.lt_iff]⟩

@[simp] theorem eq_iff {a b : UInt256} : a = b ↔ a.val = b.val :=
  ⟨fun h => by simp [h], Subtype.ext⟩

@[simp] theorem le_iff {a b : UInt256} : a ≤ b ↔ a.val ≤ b.val := ⟨fun _ => id, fun _ => id⟩
@[simp] theorem lt_iff {a b : UInt256} : a < b ↔ a.val < b.val := ⟨fun _ => id, fun _ => id⟩

/-- Add a natural literal; bound proof synthesized by `omega` at each use site. -/
def addNat (a : UInt256) (n : ℕ) (h : a.val + n < 2^256 := by omega) : UInt256 := ⟨a.val + n, h⟩

instance : HAdd UInt256 ℕ UInt256 where hAdd := UInt256.addNat

-- OfNat instance for literals n with n < 2^256 (compile-time check)
end UInt256

structure Bytes32 where
  val : UInt256
  deriving DecidableEq, Repr
```

> **Why subtype not `Fin`?** `Fin (2^256)` is definitionally the same carrier but ships modular arithmetic instances. LSC forbids silent wrap: checked ops revert (`+?`), modular ops are opt-in (`+↻`). A standalone subtype without `Fin` instances makes the wrong thing a type error.

#### The `+?` operator family (checked)

`+?`, `-?`, `*?`, `/?` return `Except E A` directly (not `Option`), using the `LscError E` instance in scope.

```lean
-- Lsc.Prelude
def UInt256.addChecked [LscError E] (a b : UInt256) : Except E UInt256 :=
  if h : a.val + b.val < 2^256 then .ok ⟨a.val + b.val, h⟩
  else .error (LscError.arith .overflow)
def UInt256.subChecked [LscError E] (a b : UInt256) : Except E UInt256 :=
  if h : b.val ≤ a.val then .ok ⟨a.val - b.val, by omega⟩
  else .error (LscError.arith .overflow)
def UInt256.mulChecked [LscError E] (a b : UInt256) : Except E UInt256 :=
  if h : a.val * b.val < 2^256 then .ok ⟨a.val * b.val, h⟩
  else .error (LscError.arith .overflow)
def UInt256.divChecked [LscError E] (a b : UInt256) : Except E UInt256 :=
  if h : b.val ≠ 0 then .ok ⟨a.val / b.val, by omega⟩
  else .error (LscError.arith .divisionByZero)

scoped notation a " +? " b => UInt256.addChecked a b
scoped notation a " -? " b => UInt256.subChecked a b
scoped notation a " *? " b => UInt256.mulChecked a b
scoped notation a " /? " b => UInt256.divChecked a b
```

#### The `+↻` operator family (wrapping)

Modular arithmetic mod 2²⁵⁶. Rare — bit packing, `unchecked`-style algorithms. ↻ is U+21BB.

```lean
-- Lsc.Prelude
def UInt256.addMod (a b : UInt256) : UInt256 :=
  ⟨(a.val + b.val) % 2^256, by omega⟩
def UInt256.subMod (a b : UInt256) : UInt256 :=
  ⟨(a.val + 2^256 - b.val) % 2^256, by omega⟩
def UInt256.mulMod (a b : UInt256) : UInt256 :=
  ⟨(a.val * b.val) % 2^256, by omega⟩
scoped notation a " +↻ " b => UInt256.addMod a b
scoped notation a " -↻ " b => UInt256.subMod a b
scoped notation a " *↻ " b => UInt256.mulMod a b

/-- Truncating division when `b ≠ 0`; EVM `unchecked` still reverts on divide-by-zero. -/
def UInt256.divMod (a b : UInt256) (hb : b.val ≠ 0) : UInt256 :=
  ⟨a.val / b.val, by omega⟩
```

No `/↻` notation — nonzero divisor proof is required at each call site. In contracts use `/?`; in lemmas use `a.val / b.val` or `divMod` with an explicit `hb`.

Because `+?` etc. return `Except E _` directly, they compose naturally with `←` in a `do`-block over `Except E` — no macro, no wrapper, no lift annotation needed.

**AMM swap example:**

```lean
@[Lsc.external]
def swap (s : AMMState) (amountIn : UInt256) : Except AMMError AMMState := do
  require (s.reserve0 > 0 ∧ s.reserve1 > 0) .uninitializedPool
  let num       ← amountIn   *? s.reserve1
  let denom     ← s.reserve0 +? amountIn
  let amountOut ← num        /? denom
  require (amountOut > 0) .insufficientLiquidity
  let r0' ← s.reserve0 +? amountIn
  let r1' ← s.reserve1 -? amountOut
  return .ok { s with reserve0 := r0', reserve1 := r1' }
```

**Simple contracts** use `ArithError` directly as `E`; the identity `LscError ArithError` instance is in the prelude:

```lean
@[Lsc.external]
def increment (s : CounterState) : Except ArithError CounterState := do
  let n ← s.number +? 1
  return .ok { s with number := n }
```

**Solidity comparison:**

| | Solidity | LSC |
|---|---|---|
| Default | `a + b` reverts | `let x ← a +? b` in `do`-block |
| Opt-out | `unchecked { a + b }` | `a +↻ b` |
| Plain `+` on `UInt256` | N/A | Type error |

#### Bridge lemmas (`@[simp]`)

The bridge lemmas are **biconditional** — they rewrite `(a +? b = .ok r)` into a pure `ℕ` proposition about `.val`. This means a single `simp [myFunction, UInt256.addChecked_val, ...]` call in a tactic proof immediately reduces any goal to plain natural number arithmetic, with no subtype coercions leaking through.

```lean
-- Lsc.Prelude
@[simp] theorem UInt256.addChecked_val [LscError E] {a b r : UInt256} :
    (a +? b : Except E UInt256) = .ok r ↔
    (a.val + b.val < 2^256 ∧ r.val = a.val + b.val) := by
  simp [UInt256.addChecked]; constructor <;> intro h <;> split_ifs at h <;> simp_all <;> omega

@[simp] theorem UInt256.subChecked_val [LscError E] {a b r : UInt256} :
    (a -? b : Except E UInt256) = .ok r ↔
    (b.val ≤ a.val ∧ r.val = a.val - b.val) := by
  simp [UInt256.subChecked]; constructor <;> intro h <;> split_ifs at h <;> simp_all <;> omega

@[simp] theorem UInt256.mulChecked_val [LscError E] {a b r : UInt256} :
    (a *? b : Except E UInt256) = .ok r ↔
    (a.val * b.val < 2^256 ∧ r.val = a.val * b.val) := by
  simp [UInt256.mulChecked]; constructor <;> intro h <;> split_ifs at h <;> simp_all <;> omega

@[simp] theorem UInt256.divChecked_val [LscError E] {a b r : UInt256} :
    (a /? b : Except E UInt256) = .ok r ↔
    (b.val ≠ 0 ∧ r.val = a.val / b.val) := by
  simp [UInt256.divChecked]; constructor <;> intro h <;> split_ifs at h <;> simp_all <;> omega

-- Error-direction lemmas (unchanged, still useful)
@[simp] theorem UInt256.addChecked_error [LscError E] {a b : UInt256} (h : a.val + b.val ≥ 2^256) :
    (a +? b : Except E UInt256) = .error (LscError.arith .overflow) := by
  simp [UInt256.addChecked]; omega
@[simp] theorem UInt256.subChecked_error [LscError E] {a b : UInt256} (h : a.val < b.val) :
    (a -? b : Except E UInt256) = .error (LscError.arith .overflow) := by
  simp [UInt256.subChecked]; omega
@[simp] theorem UInt256.divChecked_error [LscError E] {a : UInt256} :
    (a /? 0 : Except E UInt256) = .error (LscError.arith .divisionByZero) := by
  simp [UInt256.divChecked]
```

**Proof recipe:** `simp [myFunction, UInt256.addChecked_val, UInt256.subChecked_val, UInt256.mulChecked_val, UInt256.divChecked_val]` unfolds `+?`, `-?`, `*?`, `/?` and rewrites all checked arithmetic results into pure `ℕ` hypotheses about `.val` in one step. `omega` closes linear goals; `nlinarith` closes nonlinear ones (e.g. constant-product inequalities). Arithmetic revert theorems use `.error (LscError.arith .overflow)` or `.error (.arith .overflow)` interchangeably when the instance is in scope.

> **Why biconditional?** A one-directional lemma (`h → simp result`) forces proofs to supply the bound hypothesis first, producing `.val`-laden intermediate goals. The biconditional form lets `simp` rewrite `(a +? b = .ok r)` → `(a.val + b.val < 2^256 ∧ r.val = a.val + b.val)` in one shot, with no manual `.val` unwrapping. All subtype machinery is absorbed by the bridge lemmas; downstream proofs only see `ℕ`.

#### `Option.orError` — single-operation option lift (rare)

```lean
-- Lsc.Prelude — for non-arithmetic Option sites
def Option.orError (e : E) : Option A → Except E A
  | some a => .ok a
  | none   => .error e
```

### §2.6 Forbidden types

| Forbidden | Validator error | Use instead |
|-----------|----------------|-------------|
| `Nat`, `Int`, `Float` | `lsc: use UInt256` | `UInt256` |
| `String`, `Char` | `lsc: use Bytes[N]` | `Bytes[N]` |
| `List`, `Array` in state | `lsc: use Mapping` | `Mapping` |
| `IO`, `StateM`, `ST` | `lsc: stateful monads not allowed; use explicit state passing` | Explicit state |
| Higher-order functions | `lsc: functions cannot be passed as arguments` | Top-level helpers |
| Recursive inductives with >2 constructors | `lsc: use Struct + Mapping` | Struct + `Mapping` |
| `Option (S × Ret)` on mutator | `lsc: use Except E (S × Ret)` | `Except E (S × Ret)` |

`do`-notation over `Except E` is allowed — it only threads the error channel; `s` remains explicit.

> **Why not richer types?** `simp` + `omega` + `decide` work best on flat finite structures. Every restriction here trades expressiveness for proofs that close in one step.

### §2.7 Fixed-point arithmetic (`Lsc.Ray` / `Lsc.Wad`)

DeFi contracts routinely multiply and divide `uint256` values that represent decimal fractions — interest rates, exchange rates, price indices. Without a library, authors write their own fixed-point mul/div and lose all verified bounds. `Lsc.Ray` and `Lsc.Wad` are the built-in fixed-point libraries (scale 10²⁷ and 10¹⁸), wrapping the three-tier [`WadRayMath`](WadRayMath/) design. Extended operator reference: [Appendix D](lsc-appendices.md#appendix-d--wadray-fixed-point).

#### Scale constants

```lean
-- Lsc.Ray / Lsc.Wad
def WAD : ℕ := 10^18   -- 1.0 in WAD encoding
def RAY : ℕ := 10^27   -- 1.0 in RAY encoding
def HALF_WAD : ℕ := WAD / 2
def HALF_RAY : ℕ := RAY / 2
```

Values stored on-chain are plain `UInt256`; their `.val` represents a RAY- or WAD-scaled integer. `1.0` is `RAY` (10²⁷); `0.5` is `HALF_RAY`; `1.05` is `RAY + RAY / 20`.

#### Ray/WAD fixed-point operations

Operations live in `Lsc.Ray` (RAY scale) and `Lsc.Wad` (WAD scale) and follow the same `Except E` pattern as `+?`. **Three explicit rounding variants** are provided for each operation — there are no default aliases. Aave's on-chain convention is half-up (`rayMulHalfUp` / `wadMulHalfUp`); authors must name the rounding mode at every call site.

```lean
-- Lsc.Ray  (all return Except E UInt256; E resolved via LscError instance)

-- RAY multiply
def rayMulDown   [LscError E] (a b : UInt256) : Except E UInt256
def rayMulUp     [LscError E] (a b : UInt256) : Except E UInt256
def rayMulHalfUp [LscError E] (a b : UInt256) : Except E UInt256

-- RAY divide
def rayDivDown   [LscError E] (a b : UInt256) : Except E UInt256
def rayDivUp     [LscError E] (a b : UInt256) : Except E UInt256
def rayDivHalfUp [LscError E] (a b : UInt256) : Except E UInt256

-- Lsc.Wad — same six defs with wad* prefix and WAD = 10^18 scale
def wadMulDown   [LscError E] (a b : UInt256) : Except E UInt256
def wadMulUp     [LscError E] (a b : UInt256) : Except E UInt256
def wadMulHalfUp [LscError E] (a b : UInt256) : Except E UInt256
def wadDivDown   [LscError E] (a b : UInt256) : Except E UInt256
def wadDivUp     [LscError E] (a b : UInt256) : Except E UInt256
def wadDivHalfUp [LscError E] (a b : UInt256) : Except E UInt256
```

Revert conditions mirror Aave's `WadRayMath`:

| Operation | Reverts when |
|-----------|-------------|
| `rayMulHalfUp a b` | `b ≠ 0 ∧ a > (UINT256_MAX - HALF_RAY) / b` |
| `rayDivHalfUp a b` | `b = 0 ∨ a > (UINT256_MAX - b/2) / RAY` |
| `rayMulDown a b` | `b ≠ 0 ∧ a > UINT256_MAX / b` |
| `rayDivDown a b` | `b = 0 ∨ a > UINT256_MAX / RAY` |

(`wadMulHalfUp` / `wadDivHalfUp` / `wadMulDown` / `wadDivDown` use the same predicates with `HALF_WAD` / `WAD`.)

#### Bracket-pair operators

Fixed-point ops may revert (overflow / division-by-zero), so operators use a **trailing `?`** like `+?`. The rounding mode is a **bracket pair wrapping `*` or `/`**:

| Pair | Rounding | Math (RAY mul) |
|------|----------|----------------|
| `⌊·⌋` | Down | `⌊a·b / RAY⌋` |
| `⌈·⌉` | Up | `⌈a·b / RAY⌉` |
| `⸢·⸣` | HalfUp | `⌊(a·b + HALF_RAY) / RAY⌋` |

`⸢⸣` (U+2E22 / U+2E23, Supplemental Punctuation half-bracket pair) is adopted **by LSC convention** for half-up — distinct from philological use in Unicode. Algorithm unchanged: add half-ulp then floor.

```
a ⌊*⌋? b    rayMulDown      may revert
a ⌈*⌉? b    rayMulUp        may revert
a ⸢*⸣? b    rayMulHalfUp    may revert   (Aave default)
a ⌊/⌋? b    rayDivDown      may revert
a ⌈/⌉? b    rayDivUp        may revert
a ⸢/⸣? b    rayDivHalfUp    may revert
```

**Scale from namespace** — Lean cannot infer RAY vs WAD from `UInt256` alone. Import one module and `open scoped` it; the same glyph strings desugar to `ray*` or `wad*` defs:

```lean
-- Lsc/Ray.lean
namespace Lsc.Ray
  scoped notation a:65 " ⌊*⌋? " b:65 => rayMulDown a b
  scoped notation a:65 " ⌈*⌉? " b:65 => rayMulUp a b
  scoped notation a:65 " ⸢*⸣? " b:65 => rayMulHalfUp a b
  scoped notation a:65 " ⌊/⌋? " b:65 => rayDivDown a b
  scoped notation a:65 " ⌈/⌉? " b:65 => rayDivUp a b
  scoped notation a:65 " ⸢/⸣? " b:65 => rayDivHalfUp a b
end Lsc.Ray

-- Lsc/Wad.lean — identical operators, wad* defs
```

Do **not** `open scoped` both `Lsc.Ray` and `Lsc.Wad` in the same file — operators clash. Mixed-scale files use explicit function names.

**Usage in contract code:**

```lean
import Lsc.Prelude
import Lsc.Ray
open Lsc Lsc.Ray
open scoped Lsc.Ray

@[Lsc.external]
def accrueInterest (s : LendingState) : Except LendingError LendingState := do
  -- index *= (1 + rate);  all values RAY-encoded
  let growth    ← s.liquidityRate ⸢*⸣? s.timeDelta
  let newFactor ← s.liquidityIndex +? growth
  let newIndex  ← newFactor ⸢*⸣? s.liquidityRate
  return .ok { s with liquidityIndex := newIndex }
```

#### Three tiers of verified behaviour

`Lsc.Ray` is backed by three layers ( `Lsc.Wad` mirrors the same structure at WAD scale):

| Tier | Module | What it gives you |
|------|--------|-------------------|
| **ℕ code** | `Lsc.Ray.Nat` | Definitions + helper lemmas + rounding bounds over `ℕ` |
| **EVM code** | `Lsc.Ray.Evm` | `Except`-wrapped contract ops + simulation theorems (overflow conditions match) |
| **Real bounds** | `Lsc.Ray.Real` | `decode`, `toReal`, bridge lemmas bounding error in `ℝ` |

For most contracts only the ℕ tier is needed. Import `Lsc.Ray.Real` when you need to prove precision statements like "the accrued interest is within 10⁻²⁷ of the true value."

#### Bridge lemmas

Each operation gets the same biconditional bridge lemma pattern as `+?` (§2.5). Names match the explicit def (example for half-up mul; down/up/half-up div follow the same shape):

```lean
-- Lsc.Ray
@[simp] theorem rayMulHalfUp_val [LscError E] {a b r : UInt256} :
    (rayMulHalfUp a b : Except E UInt256) = .ok r ↔
    (¬ rayMulHalfUpReverts a.val b.val ∧
     r.val = Lsc.Ray.Nat.rayMulHalfUp a.val b.val) := ...

@[simp] theorem rayDivHalfUp_val [LscError E] {a b r : UInt256} :
    (rayDivHalfUp a b : Except E UInt256) = .ok r ↔
    (¬ rayDivHalfUpReverts a.val b.val ∧
     r.val = Lsc.Ray.Nat.rayDivHalfUp a.val b.val) := ...
```

After `simp [accrueInterest, rayMulHalfUp_val, UInt256.addChecked_val]` all goals reduce to `ℕ` arithmetic. Bracket operators desugar to these defs before `simp`. The rounding-bound theorems (`rayMulHalfUp_error`, `double_rayMulHalfUp_decode_error`) are available in `Lsc.Ray.Nat` and `Lsc.Ray.Real` respectively.

#### Rounding-bound theorems (available in `Lsc.Ray.Nat`)

```lean
-- Single multiply: result is within HALF_RAY of the exact product
theorem rayMulHalfUp_error (a b : ℕ) :
    rayDist (a * b) (rayMulHalfUp a b * RAY) ≤ HALF_RAY

-- Single multiply: one-sided bounds
theorem rayMulHalfUp_exact_le (a b : ℕ) : a * b ≤ rayMulHalfUp a b * RAY + HALF_RAY
theorem rayMulHalfUp_exact_ge (a b : ℕ) : rayMulHalfUp a b * RAY ≤ a * b + HALF_RAY

-- Composition: double rayMulHalfUp slack at scale 2
theorem double_rayMulHalfUp_scaled_error (sd a b : ℕ) :
    rayDist (rayMulHalfUp sd (rayMulHalfUp a b) * RAY * RAY) (sd * (a * b)) ≤
      sd * RAY + RAY * RAY
```

#### Real-valued precision bounds (available in `Lsc.Ray.Real`)

```lean
-- decode n = (n : ℝ) / RAY  (the mathematical value of a RAY-encoded integer)

-- Single multiply is within 10^-27 of the true product
theorem rayMulHalfUp_error_real (a b : ℕ) :
    |decode a * decode b - decode (rayMulHalfUp a b)| ≤ (1 : ℝ) / (2 * RAY)

-- Double multiply error in decoded space
theorem double_rayMulHalfUp_decode_error (sd a b : ℕ) :
    |decode (rayMulHalfUp sd (rayMulHalfUp a b)) - decode sd * decode a * decode b| ≤
      (1 + decode sd) * (1 / (2 * RAY))
```

#### Named invariant pattern for ray-valued quantities

Following §9.7, define economic quantities using `decode` so theorem statements stay clean:

```lean
-- *Lemma.lean
open Lsc.Ray.Real in
def interestRate (s : LendingState) : ℝ := decode s.liquidityRate.val
def liquidityIndex (s : LendingState) : ℝ := decode s.liquidityIndex.val

-- *Theorem.lean
/-- The liquidity index is non-decreasing on every accrual. -/
theorem accrueInterest_index_nondecreasing (s s' : LendingState)
    (h : accrueInterest s = .ok s') :
    liquidityIndex s ≤ liquidityIndex s' :=
  LendingLemma.accrueInterest_index_nondecreasing s s' h
```

#### What is *not* in `Lsc.Ray` / `Lsc.Wad`

- **No `rayPow` / `wadPow`** — exponentiation requires unbounded loops; use a caller-supplied pre-computed factor or iterate with bounded recursion.
- **No fixed-point square root** — same reason.
- **No WAD↔RAY conversion helpers** — multiply/divide by `RAY / WAD = 10^9` using the plain `*?` / `/?` operators; no special case needed.

---

## §3 State

### §3.1 Defining a State struct

Contract storage is a plain Lean 4 struct. Each field is a primitive type or `Mapping`. Fields receive sequential storage slots in declaration order from slot 0.

```lean
structure ERC20State where
  name        : Bytes[32]                              -- slot 0
  symbol      : Bytes[32]                              -- slot 1
  decimals    : UInt256                                -- slot 2
  totalSupply : UInt256                                -- slot 3
  balances    : Mapping Address UInt256                -- slot 4
  allowances  : Mapping Address (Mapping Address UInt256) -- slot 5
```

The **contract name** is the file stem (`Counter` from `src/Counter.lean`). The validator requires PascalCase file stems.

### §3.2 Slot layout

Fields occupy slots 0, 1, 2, … in declaration order. `Mapping` fields occupy one slot (the mapping root); individual entries live at `keccak256(abi.encode(key, slot))` with ABI-padded key encoding (see §2.3 for test vector).

`structure … extends` is **not supported in v1**. Shared field patterns are expressed by composing structs manually.

> **Why no `extends`?** Storage inheritance introduces slot-layout ambiguity with no clean answer absent significant validator complexity. Vyper takes the same position.

### §3.3 State vocabulary

| Term | Meaning | Who uses it |
|------|---------|-------------|
| `get` / `set` | Functional mapping access: `m[k]`, `m[k := v]` (desugar to `Mapping.get` / `Mapping.set`) | Contract authors |
| `store` (record) | Scalar field update: `{ s with field := v }` | Contract authors |
| `State` | Full contract snapshot threaded through `@[Lsc.external]` functions | Authors and theorem files |
| `sstore` | Persist snapshot to chain via EVM `SSTORE` | **Emitter only** |

Authors never call `sstore`. Theorems quantify over complete `s` and `s'`. Bracket notation is preferred in author examples; `Mapping.get` / `Mapping.set` remain the underlying names for proofs and macro expansion.

> **Why whole-state load/store?** Theorems on complete snapshots make `s'.field = s.field` trivially provable by `simp` when `field` doesn't appear in the function body.

### §3.4 The `@[Lsc.public]` annotation

Mark a State field `@[Lsc.public]` to expose it as a read-only ABI getter. The compiler synthesizes a lazy `@[Lsc.external]` view that loads only the relevant slot(s) — identical performance to Solidity/Vyper public variables.

```lean
structure CounterState where
  @[Lsc.public]
  number : UInt256
-- Compiler synthesizes (lazy slot read, not full sload):
-- @[Lsc.external]
-- def number (s : CounterState) : UInt256 := s.number
```

Fields without `@[Lsc.public]` are storage-only. Only `@[Lsc.external]` functions and `@[Lsc.public]`-generated getters appear in the deployed ABI.

**Generation rules:**

| Field type | Generated signature |
|------------|---------------------|
| Scalar | `def fieldName (s : State) : T` |
| `Mapping K V` | `def fieldName (s : State) (k : K) : V` |
| Nested `Mapping` | one key parameter per mapping level |

When the standard ABI name differs from the field name (e.g. IERC-20 `balanceOf` vs field `balances`), omit `@[Lsc.public]` and write a manual `@[Lsc.external]` export instead.

### §3.5 `@[Lsc.initialize]`

At most one initialization function per contract, called at deployment (constructor).

```lean
@[Lsc.initialize]
def initialize (name symbol : Bytes[32]) (decimals : UInt256)
    (initialSupply : UInt256) (ctx : MsgContext)
    : Except TokenError TokenState :=
  return .ok {
    name        := name
    symbol      := symbol
    decimals    := decimals
    totalSupply := initialSupply
    balances    := Mapping.empty[ctx.sender := initialSupply]
    allowances  := Mapping.empty }
```

- Return type must be `Except E S` or bare `S`.
- The emitter generates an ABI constructor (not a named function).
- `ctx.sender` is bound to `msg.sender` at deploy time (§5.1).

---

## §4 Functions (Exports)

### §4.1 The `@[Lsc.external]` annotation

Public ABI functions are declared with `@[Lsc.external]`. The Lean `def` name **is** the ABI function name. The compiler computes the 4-byte selector via `keccak256(canonicalSignature)`.

All `@[Lsc.external]` functions are **non-reentrant by default** — the emitter generates a reentrancy guard. Use `@[Lsc.allow_reentrant]` to opt out (validator warning issued).

```lean
@[Lsc.external]
def increment (s : CounterState) : Except ArithError CounterState := do
  let n ← s.number +? 1
  return .ok { s with number := n }
```

### §4.2 Mutators

| Return shape | Meaning |
|---|---|
| `S` | Infallible mutator |
| `Except E S` | Fallible mutator, no ABI return value |
| `Except E (S × V)` | Fallible mutator with return value |

**`require` — inline precondition guard:**

```lean
require (condition) .ErrorVariant
-- desugars to:
if ¬condition then return .error .ErrorVariant
```

`require` on an infallible function (return type `S` or `V`) is a validator error.

```lean
-- Fallible mutator with return value
@[Lsc.external]
def transfer (ctx : MsgContext) (s : ERC20State)
    (to : Address) (amount : UInt256) : Except TokenError (ERC20State × Bool) := do
  require (s.balances[ctx.sender] ≥ amount) .insufficientBalance
  let newSender ← s.balances[ctx.sender] -? amount
  let newTo     ← s.balances[to] +? amount
  let s' := { s with balances := s.balances[ctx.sender := newSender][to := newTo] }
  emit! TransferEvent ctx.sender to amount
  return .ok (s', true)

-- Infallible mutator
@[Lsc.external]
def activate (s : FlagState) : FlagState := { s with active := true }
```

### §4.3 Views

```lean
-- Fallible view (rare)
@[Lsc.external]
def price (s : AMMState) : Except AMMError UInt256 := do
  require (s.reserve1 > 0) .uninitializedPool
  let p ← s.reserve0 /? s.reserve1
  return .ok p
```

The emitter generates a read-only wrapper; no `sstore` is emitted. For `@[Lsc.public]`-generated views, only the relevant slot is read (lazy load).

### §4.4 ABI inference rules

| Author return shape | Mutability | ABI return | ABI errors |
|--------------------|-----------|------------|------------|
| `S` | nonpayable | none | none |
| `V` (not State) | view | ABI type of `V` | none |
| `Except E S` | nonpayable | none | `E` variants |
| `Except E (S × Bool)` | nonpayable | `bool` | `E` variants |
| `Except E (S × UInt256)` | nonpayable | `uint256` | `E` variants |
| `Except E (S × Address)` | nonpayable | `address` | `E` variants |
| `Except E (S × Bytes32)` | nonpayable | `bytes32` | `E` variants |
| `Except E V` (V not State) | view | ABI type of `V` | `E` variants |
| `Option _` on mutator | **validator error** | — | use `Except` |

When an export is marked `@[Lsc.payable]` or `@[Lsc.receive]` (§5.2), the function is marked `payable` in the ABI.

**EVM behavior summary:**

| Lean return | EVM behavior |
|-------------|-------------|
| `.error e` | `REVERT` with `abi.encode(e)`; no storage commit; no events |
| `.ok s'` (mutator) | persist `s'`; emit events; ABI-encode non-state component |
| `val` (infallible view) | read-only; ABI-encode `val`; no store |
| `.ok v` (fallible view) | read-only; ABI-encode `v`; no store |

### §4.5 Parameter filtering

| Parameter kind | ABI | Rule |
|---------------|-----|------|
| `s : SomeState` | excluded | Loaded from storage by compiler |
| `ctx : MsgContext` | excluded | Bound to message/block context (§5.1) |
| All other primitive types | included | In declaration order after excluded params |

---

## §5 Message Context and ETH Handling

### §5.1 The `MsgContext` type

```lean
-- Lsc.Prelude
structure MsgContext where
  sender    : Address
  value     : UInt256   -- msg.value
  timestamp : UInt256   -- block.timestamp
  number    : UInt256   -- block.number
```

Any parameter of type `MsgContext` is excluded from ABI calldata. The emitter binds all fields from EVM opcodes at each export boundary. The type itself is the signal — no annotation required. Parameter name convention: `ctx`.

```lean
@[Lsc.external]
def transfer (ctx : MsgContext) (s : ERC20State)
    (to : Address) (amount : UInt256)
    : Except TokenError (ERC20State × Bool) := ...
```

**Field bindings:**

| Field | Bound to |
|-------|----------|
| `ctx.sender` | `msg.sender` |
| `ctx.value` | `msg.value` |
| `ctx.timestamp` | `block.timestamp` |
| `ctx.number` | `block.number` |

**Validator rules:**
- At most one `MsgContext` parameter per function.
- `Address` parameter named `caller`, `sender`, `from`, or `owner` used for authorization → warning: use `ctx.sender` from `MsgContext` instead.

**Optional on exports:** functions that need no message or block context (e.g. `increment (s : CounterState)`) omit `ctx`. Exports that need only `ctx.sender` still take the full `MsgContext` — unused fields are available for time-locked logic without adding types later.

**In proofs:** theorems quantify over `ctx : MsgContext` directly. No `EvmContext`.

> **Why a `structure`?** Bundling sender, value, and block fields in one excluded parameter beats four parallel type-as-signal parameters. Proofs use field projections (`ctx.sender`, `ctx.value`); `simp` and `cases ctx` work uniformly.

### §5.2 ETH handling

LSC has explicit, cohesive ETH handling. There is no implicit `msg.value` — authors read `ctx.value` when a function accepts ETH.

#### Payable functions

A function that accepts ETH **must** be marked `@[Lsc.payable]`. The emitter marks the function `payable` in the ABI and skips the `msg.value` guard. The author reads `ctx.value`:

```lean
@[Lsc.payable]
@[Lsc.external]
def deposit (ctx : MsgContext) (s : VaultState)
    : Except VaultError VaultState := do
  require (ctx.value > 0) .zeroDeposit
  let newBal ← s.balances[ctx.sender] +? ctx.value
  return .ok { s with balances := s.balances[ctx.sender := newBal] }
```

#### Non-payable protection (default)

If an export is **not** marked `@[Lsc.payable]` or `@[Lsc.receive]`, the emitter generates a guard that reverts if `msg.value > 0`. This applies even when `ctx : MsgContext` is present (e.g. ERC-20 `transfer`). It prevents ETH from being locked in a contract that has no way to withdraw it.

#### ETH transfers out

To send ETH from the contract, use `native_transfer!`:

```lean
-- Lsc.Prelude
-- macro; desugars to Lsc.Eth.transfer (emitter lowers to CALL with value)
native_transfer! to amount
-- desugars to:
Lsc.Eth.transfer to amount   -- Except EthError Unit; .error .transferFailed on failure
```

Composes with `←` in `do`-blocks over the contract's `Except E`. Failure maps via a required constructor on `@[Lsc.error]` types:

```lean
@[Lsc.error]
inductive VaultError where
  | arith : ArithError → VaultError
  | eth   : EthError → VaultError   -- required when module uses native_transfer!
```

```lean
@[Lsc.external]
def withdraw (ctx : MsgContext) (s : VaultState) (amount : UInt256)
    : Except VaultError VaultState := do
  require (s.balances[ctx.sender] ≥ amount) .insufficientBalance
  let newBal ← s.balances[ctx.sender] -? amount
  let s' := { s with balances := s.balances[ctx.sender := newBal] }
  let _ ← native_transfer! ctx.sender amount
  return .ok s'
```

#### Receive and fallback

```lean
-- Optional: accept plain ETH transfers (no calldata)
@[Lsc.receive]
def receive (ctx : MsgContext) (s : VaultState) : Except VaultError VaultState := do
  require (ctx.value > 0) .zeroDeposit
  let newBal ← s.totalDeposited +? ctx.value
  return .ok { s with totalDeposited := newBal }

-- Optional: called when no selector matches
@[Lsc.fallback]
def fallback (s : VaultState) : Except VaultError VaultState :=
  return .error .unknownSelector
```

- `@[Lsc.receive]` must take `ctx : MsgContext` (validator error otherwise); implies `payable`.
- `@[Lsc.fallback]` is nonpayable by default; use `@[Lsc.allow_value]` to accept `msg.value`.
- If neither is defined and plain ETH is sent, the transaction reverts (safe default).

#### In proofs

Theorems quantify over `ctx : MsgContext` directly:

```lean
theorem deposit_increases_balance
    (ctx : MsgContext) (s s' : VaultState)
    (h : deposit ctx s = .ok s') :
    s'.balances[ctx.sender] = s.balances[ctx.sender] + ctx.value :=
  VaultLemma.deposit_increases_balance ctx s s' h
```

---

## §6 Events

### §6.1 Declaring events

```lean
structure TransferEvent where
  from to : Address
  value   : UInt256
  deriving Lsc.Event.EvmEvent
```

The `EvmEvent` instance supplies the canonical ABI signature and which fields are indexed (topics) vs non-indexed (data).

### §6.2 Emitting: `emit!`

```lean
emit! TransferEvent ctx.sender to amount
-- desugars to:
Lsc.Event.log (TransferEvent.mk ctx.sender to amount)
```

The first argument is the event structure (must have `deriving Lsc.Event.EvmEvent`). Positional arguments match the structure fields in declaration order.

**Multiple events on one path:**
```lean
emit! TransferEvent ctx.sender to amount
if fee > 0 then emit! FeeEvent ctx.sender fee
return .ok (s', true)
```

Each call on a path to `.ok _` is collected independently. No logs fire on `.error _` paths.

Emit ordering: **load → call author function → on `.ok` → sstore → LOG(s) in source order → ABI return.**

### §6.3 Proof erasure

`emit!` desugars to `Lsc.Event.log`, which is proof-erased: it is definitionally equal to the identity in the Lean kernel. Theorems quantify only over `Except` returns — log calls do not appear in proofs.

Log correctness (correct `topic0`, encoding, ordering) is covered by the formally-verified lowering pipeline (§13.3).

> **Why proof erasure?** Returning log lists from functions would pollute every theorem with list destructions the spec doesn't care about. Log *correctness* belongs in the verified emitter, not in Lean proofs.


---

## §7 Revert

Covered by §4.4 (EVM behavior table) and §9.4 (requirements checklist). In brief:

- `.error e` → `REVERT` with `abi.encode(e)`; no storage commit; no events.
- Error specs use `(h : f ... = .error .Variant)` as the hypothesis and prove the condition under which that error fires.

---

## §8 External Calls

> **v1 status:** `World`, `invoke`, and `Lsc.extern.*` are specified for completeness and to support the composition demo ([Appendix B](lsc-appendices.md#appendix-b--composition-pattern)), but full emitter support lands in v2b. See [Appendix C](lsc-appendices.md#appendix-c--versioning-roadmap).

### §8.1 World and accounts

Single-contract `State → Except E S` is insufficient when bytecode calls other contracts. Multi-contract storage lives in `World`:

```lean
structure World where
  accounts : Mapping Address Account
```

Author functions never take `World` as a parameter. `extcall!` and `staticcall!` may appear in any contract-module `def` (`src/*.lean`). The compiler threads `World` through those sites when lowering exports and their callees (see §8.2).

### §8.2 External calls: interface cast, `staticcall!`, `extcall!`

Authors invoke other contracts inline in ordinary `do`-blocks — same as `emit!` and `require`. No separate export body, hook attribute, or `World` argument.

#### Interface cast

Mirror Solidity's `IERC20(addr).balanceOf(who)` — one expression carries the runtime **address** and compile-time **interface**:

```lean
-- Lsc.Interfaces
class LscInterface (I : Type) where
  -- method signatures for validator + selector lookup

abbrev ContractAt (I : Type) [LscInterface I] := Address
```

**Cast notation** (macro in `Lsc.Prelude`):

```lean
(e : I)   -- when I is an interface with [LscInterface I]
-- desugars to:
(e : ContractAt I)
```

`ContractAt I` is proof-transparent (`ContractAt I` = `Address`). Interface typeclasses live in `Lsc.Interfaces` or project `interfaces/*.lean`.

#### `staticcall!` and `extcall!`

**Read-only — `staticcall!` (callee must not modify storage):**

```lean
let bal ← staticcall! (tokenAddr : IERC20).balanceOf who
-- emitter desugars each site to:
Lsc.extern.staticcall IERC20.balanceOf tokenAddr w ctx args : Ret
```

**Mutating — `extcall!` (callee may update `World`; revert rolls back):**

```lean
let ok ← extcall! (tokenAddr : IERC20).transferFrom from to amount
-- emitter desugars each site to:
Lsc.extern.extcall IERC20.transferFrom tokenAddr w ctx args : Except ExternError Ret
```

Authors bind only the interface method's return type (`Ret`), not `World × Ret`. `w` and `ctx` (`msg.sender`, etc.) are implicit — supplied by the export wrapper at each site, like `LOG` opcodes for `emit!`.

**Example — composition hook inline (Appendix B):**

```lean
@[Lsc.external]
def transfer (ctx : MsgContext) (s : MyTokenState) (to : Address) (amount : UInt256)
    : Except TokenError (MyTokenState × Bool) := do
  require (s.balances[ctx.sender] ≥ amount) .insufficientBalance
  let newSender ← s.balances[ctx.sender] -? amount
  let newTo     ← s.balances[to] +? amount
  let s' := { s with balances := s.balances[ctx.sender := newSender][to := newTo] }
  emit! TransferEvent ctx.sender to amount
  if s'.counter ≠ Address.zero ∧ ctx.sender ≠ to then
    let _ ← extcall! (s'.counter : ITransferCounter).onTransfer
  return .ok (s', true)
```

**Example — view with `staticcall!`:**

```lean
@[Lsc.external]
def check (s : PoolState) (tokenAddr : Address) (who : Address) : Except PoolError UInt256 := do
  let bal ← staticcall! (tokenAddr : IERC20).balanceOf who
  return .ok bal
```

#### Typing and errors

`extcall!` and `staticcall!` compose with `←` in `do`-blocks over the contract's `Except E`. Callee revert maps to `.error` via a required constructor on `@[Lsc.error]` types:

```lean
@[Lsc.error]
inductive TokenError where
  | arith  : ArithError → TokenError
  | extern : ExternError → TokenError   -- required when module uses extcall!
```

Same propagation model as `+?` / `require`. Contract modules using `staticcall!` only (no `extcall!`) do not require `extern`.

#### Helpers

The guard + `extcall!` block may live in a top-level helper in the same contract module:

```lean
def notifyCounterIfHooked (ctx : MsgContext) (s' : MyTokenState) (to : Address)
    : Except TokenError Unit := do
  if s'.counter ≠ Address.zero ∧ ctx.sender.val ≠ to then
    let _ ← extcall! (s'.counter : ITransferCounter).onTransfer
  return .ok ()

@[Lsc.external]
def transfer ... := do
  ...
  ← notifyCounterIfHooked ctx s' to
  return .ok (s', true)
```

`extcall!` / `staticcall!` are allowed in **any `def` in `src/*.lean`**, not only on `@[Lsc.external]` entry points. Forbidden in `test/*Lemma.lean` and `test/*Theorem.lean`. Helpers that only perform extern side effects return `Except E Unit`. The emitter lowers sites in the **transitive closure** of each export (internal function or inline). CEI order follows dynamic call order in the author `do` block.

#### Export lowering

The compiler-generated export wrapper still performs load/store, reentrancy guard, and `MsgContext` binding (§13.1). It runs the author function (including callees), lowering each `extcall!` / `staticcall!` site to `CALL` / `STATICCALL` with ambient `w` / `ctx`. On `.error` — revert; no self `sstore`; no `emit!` logs; extern `World` changes rolled back.

Macros live in `Lsc.Prelude` alongside `emit!`, `native_transfer!`, `require`, `extcall!`, and `staticcall!`.

### §8.3 Proof erasure

`extcall!` desugars to `Lsc.extern.invoke`, which is **proof-erased for `World` effects** in the Lean kernel — definitionally a no-op on author `State` (parallel to `Lsc.Event.log` for logs in §6.3).

**Layer 1:** theorems over `transfer`, `increment`, etc. unfold author `do` without `World`. Inline `extcall!` sites do not appear in state-transition proofs. ERC-20 lemmas unchanged.

**Layer 3:** hook / composition theorems (`transfer_increments_counter_when_hooked`, etc.) use `simulate_call` + callee theorems ([Appendix B](lsc-appendices.md#appendix-b--composition-pattern)).

**Assumed interfaces** (`IERC20` on an unknown token): `staticcall!` results used in author logic may need axioms in `*Lemma.lean` (§8.4) — trusted external behavior.

> **Why proof-erasure for `extcall!` but not for `staticcall!` results?** World threading pollutes every theorem; erased. A `UInt256` balance used in a `require` is part of author logic — proved via axioms (assumed callee) or Layer 3 (same-repo callee). Only the multi-contract store aspect is erased at Layer 1.

Extern-call correctness (selector, encoding, CEI ordering, revert rollback) is covered by the formally-verified lowering pipeline (§13.3).

### §8.4 Registered vs assumed callees

| Callee kind | Resolution | Proof strength |
|-------------|-----------|----------------|
| **Same-repo** | `src/*.lean` contract + matching interface in `interfaces/*.lean` | Layer 3 via `simulate_call` (§10.3) + callee theorems |
| **Assumed** | `@[extern_assume "IERC20"]` + axioms in `test/*Lemma.lean` | Trust interface axioms (human-reviewed) |

`[lsc.contracts]` in `foundry.toml` is a **deploy/test tooling** address table for Foundry multi-contract tests — not part of author call syntax.

### §8.5 Reentrancy

`@[Lsc.external]` functions are non-reentrant by default (§4.1). `@[Lsc.allow_reentrant]` opts out. Proofs of re-entrant exports must use Layer 2 helpers (§10).

---

## PART II — THE PROOF SYSTEM

---

## §9 Proof Files

Each contract has two proof modules in `test/`: `*Lemma.lean` (AI-generated) and `*Theorem.lean` (human-reviewed requirements).

### §9.1 Lemma files (`test/*Lemma.lean`)

Lemma files are **AI-generated**. Humans do not review them. They import the contract module and contain:

- **Action model scaffolding** for sequence invariants (`inductive Action`, `applyAction`, `applyActions`)
- **Helper `def`s** used by proofs
- **`lemma` proofs** with full tactic bodies

No `sorry`. Kernel-checked.

```lean
import Counter

inductive CounterAction where | increment

def applyAction (s : CounterState) : CounterAction → CounterState
  | .increment => match increment s with | .ok s' => s' | .error _ => s

def applyActions (s : CounterState) (actions : List CounterAction) : CounterState :=
  actions.foldl applyAction s

lemma increment_increases_number (s s' : CounterState) (h : increment s = .ok s') :
    s'.number = s.number + 1 := by
  rw [UInt256.eq_iff]
  simp [increment, UInt256.addChecked_val] at h ⊢; omega

lemma number_never_decreases (s : CounterState) (actions : List CounterAction) :
    (applyActions s actions).number ≥ s.number := by
  simp only [applyActions]
  apply Lsc.Invariant applyAction (fun s' => s'.number ≥ s.number)
  · intro s' a hP; cases a <;> simp [applyAction, increment, UInt256.addChecked_val, UInt256.le_iff] at hP ⊢ <;> omega
  · simp
```

#### Sequence invariants and `Lsc.Invariant`

For properties that must hold across any sequence of actions, define in `*Lemma.lean`:
1. `inductive Action` — one variant per exported mutator.
2. `def applyAction (s : S) : Action → S` — run one action; on `.error`, return `s` unchanged.
3. `def applyActions := actions.foldl applyAction`.

Then prove the corresponding `lemma` using `Lsc.Invariant`:

```lean
-- Lsc.Prelude
theorem Lsc.Invariant
    {S A : Type} (step : S → A → S) (P : S → Prop)
    (hstep : ∀ (s : S) (a : A), P s → P (step s a))
    (s : S) (actions : List A) (h0 : P s)
    : P (List.foldl step s actions)
```

`Lsc.Invariant` eliminates manual list induction. The proof obligation reduces to one case per action type.

**When to use direct `induction` instead:** when the property relates initial to final state in a way that depends on the full history (e.g. "total tokens transferred equals sum of individual transfers").

`axiom` is allowed in `*Lemma.lean` for `@[extern_assume]` interface assumptions (§8.4).

### §9.2 Theorem files (`test/*Theorem.lean`)

Theorem files are the **requirements document** — written and reviewed by humans. Each `theorem`:

- States a readable business property **inline** in its type (not via a separate spec module)
- Carries a docstring describing the requirement
- Delegates to a homonymous `lemma` in **exactly one line**

No `sorry`. This is the CI `PASS`/`FAIL` enumeration surface.

```lean
import Counter
import CounterLemma

/-- On success, increment increases number by exactly 1. -/
theorem increment_increases_number (s s' : CounterState) (h : increment s = .ok s') :
    s'.number = s.number + 1 :=
  CounterLemma.increment_increases_number s s' h

/-- No sequence of actions can decrease the number. -/
theorem number_never_decreases (s : CounterState) (actions : List CounterLemma.CounterAction) :
    (CounterLemma.applyActions s actions).number ≥ s.number :=
  CounterLemma.number_never_decreases s actions
```

### §9.3 Naming convention

- `{function}_{property}` for single-call properties: `increment_increases_number`, `transfer_no_overdraft`
- `{subject}_{invariant}` for sequence invariants: `number_never_decreases`, `constant_product_nondecreasing`

Each name appears as a homonymous `lemma` / `theorem` pair.

### §9.4 Requirements checklist

Every mutating export should have at minimum in `*Theorem.lean`:
1. A **success theorem** — `(h : f … s = .ok s')` — what holds after the call
2. A **revert theorem** — `(h : f … = .error e)` — what inputs cause each revert

Contracts with global invariants additionally need an action model in `*Lemma.lean` (`Action`, `applyAction`, `applyActions`) plus an invariant theorem in `*Theorem.lean`.

### §9.5 Proof authorship

AI writes `*Lemma.lean` (scaffolding + tactic proofs). Humans craft `*Theorem.lean` (theorem statements + one-line delegations). The Lean kernel is the arbiter for both.

### §9.6 Enforcement rules

| Condition | Result |
|-----------|--------|
| `sorry` in lemma or theorem file | FAIL |
| Lean type error in lemma or theorem file | FAIL |
| Required theorem missing from `*Theorem.lean` | FAIL |
| Theorem body is not a single lemma delegation | error |
| `theorem` with no homonymous `lemma` | FAIL (typecheck) |
| `lemma` with no matching `theorem` | warning (helper lemma) |

### §9.7 Writing `.val`-free theorem statements

Theorem files are the **requirements document** — they should read like a protocol specification, not implementation plumbing. Use `UInt256` equality and ordering (`=`, `≤`) directly — prelude instances handle the comparison. Raw `.val` projections on **multi-field** expressions are a readability smell: `s'.reserve0.val * s'.reserve1.val ≥ s.reserve0.val * s.reserve1.val` is harder to read than `k s ≤ k s'`.

Two patterns to eliminate `.val` noise:

#### Named invariant functions (preferred for economic properties)

Define the economic quantities once in `*Lemma.lean` as plain `ℕ`-valued functions, then state theorems purely over those:

```lean
-- AMMlemma.lean
def k (s : AMMState) : ℕ := s.reserve0.val * s.reserve1.val
def price (s : AMMState) : ℚ := s.reserve1.val / s.reserve0.val  -- for real-valued bounds
```

```lean
-- AMMTheorem.lean
/-- Constant product never decreases on a successful swap. -/
theorem swap_k_nondecreasing (s s' : AMMState) (amountIn : UInt256)
    (h : swap s amountIn = .ok s') : k s ≤ k s' :=
  AMMlemma.swap_k_nondecreasing s s' amountIn h

/-- reserve0 strictly increases on every successful swap. -/
theorem swap_reserve0_increases (s s' : AMMState) (amountIn : UInt256)
    (hPos : amountIn.val > 0) (h : swap s amountIn = .ok s') :
    k s ≤ k s' :=
  AMMlemma.swap_reserve0_increases s s' amountIn hPos h
```

The `.val` is hidden once inside `k`; every downstream theorem is clean.

#### View projection (for multi-field state structs)

When a theorem needs to mention several fields of a state struct, a `view` projection keeps the statement readable without per-field `.val`:

```lean
-- AMMlemma.lean
structure AMMView where
  reserve0 reserve1 totalLp : ℕ

def AMMState.view (s : AMMState) : AMMView :=
  { reserve0 := s.reserve0.val, reserve1 := s.reserve1.val, totalLp := s.totalLp.val }

-- Conventional notation; import into *Theorem.lean via `open AMMlemma`
scoped notation s "↓" => AMMState.view s
```

```lean
-- AMMTheorem.lean
/-- Swap preserves total liquidity. -/
theorem swap_lp_unchanged (s s' : AMMState) (amountIn : UInt256)
    (h : swap s amountIn = .ok s') : (s↓).totalLp = (s'↓).totalLp :=
  AMMlemma.swap_lp_unchanged s s' amountIn h

/-- Adding liquidity never decreases LP supply. -/
theorem addLiquidity_lp_nondecreasing
    (ctx : MsgContext) (s s' : AMMState) (a0 a1 lpMint : UInt256)
    (h : addLiquidity ctx s a0 a1 = .ok (s', lpMint)) :
    (s↓).totalLp ≤ (s'↓).totalLp :=
  AMMlemma.addLiquidity_lp_nondecreasing ctx s s' a0 a1 lpMint h
```

**Guideline:** use named invariant functions when the quantity has an economic name (`k`, `price`, `totalSupply`, `solvency`). Use the view projection `↓` when the theorem is about structural state relationships (field X vs field Y). Either way, `.val` belongs in `*Lemma.lean` definitions, not in `*Theorem.lean` statement types.

---

## §10 Proof Helpers

### §10.1 Layer 1 — Pure (default)

Lemmas proved directly over `@[Lsc.external]` functions using `simp`, `omega`, and `Mapping` lemmas. This is the default layer. Most contracts never leave Layer 1.

#### `Except` discriminators

```lean
@[simp] theorem Except.ok_ne_error {E A : Type} (a : A) (e : E) :
    (Except.ok a : Except E A) ≠ Except.error e := by simp
@[simp] theorem Except.error_ne_ok {E A : Type} (a : A) (e : E) :
    (Except.error e : Except E A) ≠ Except.ok a := by simp
```

#### `bind_ok` — intermediate state extraction

```lean
@[simp] theorem Except.bind_ok {E A B : Type} {ma : Except E A} {f : A → Except E B}
    {b : B} (h : ma >>= f = .ok b) : ∃ a, ma = .ok a ∧ f a = .ok b := by
  cases ma with | error e => simp at h | ok a => exact ⟨a, rfl, h⟩
```

**Proof recipe for multi-step functions:**

```lean
-- simp [f] to unfold; obtain ⟨mid, hmid, hrest⟩ := Except.bind_ok h to extract intermediate
-- state; simp [Mapping.get_set_same] + omega to close
lemma transferFrom_decrements_allowance ... := by
  simp [transferFrom] at h ⊢
  obtain ⟨bal, hbal, hrest⟩ := Except.bind_ok h
  obtain ⟨alw, halw, hfinal⟩ := Except.bind_ok hrest
  simp [Mapping.get_set_same, Mapping.get_set_other,
        UInt256.subChecked_ok (by omega)] at *
  omega
```

**Proof recipe for revert conditions with `split_ifs`:**

```lean
lemma transfer_no_overdraft ... := by
  simp [transfer] at h
  -- require desugars to if; split_ifs names the branches
  split_ifs at h with hguard
  · omega   -- hguard : ¬(balance ≥ amount) gives balance < amount directly
  · simp [UInt256.subChecked_ok (by omega)] at h  -- contradiction: this branch can't error here
```

### §10.2 Layer 2 — Wrapped (export bridge)

Used when a lemma must reason about compiler-generated export wrappers or ABI `Bool` returns. Most contracts do not need this layer.

```lean
-- Strip event log lists from compiler-generated export
theorem Lsc.lift_logs {S α E : Type} ...

-- Export with no extern sites equals internal fn then load/store
theorem Lsc.lift_no_extern ...
```

### §10.3 Layer 3 — Composed (cross-contract, v2b)

> **TODO v2b:** `simulate_call` threads `World` through callees and composes callee theorems with caller theorems.

### §10.4 Tactics

**`export_cases`** — destructs `Except E (Ret × List LogEntry)` for Layer 2 goals.
**`erc_cases`** — destructs `Except E (S × Bool)`.

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

Compliance is always opt-in. The default proof runner imposes no application requirements.

### §11.2 Proof runner verification

For each listed name the runner checks:
1. A `theorem <name>` exists in the corresponding `*Theorem.lean`.
2. The theorem body is a one-line `*Lemma.<name>` delegation.
3. A homonymous `lemma <name>` typechecks in `*Lemma.lean` (implicit).

CI reports `PASS`/`FAIL` per **theorem** name only.

### §11.3 ERC-20 required theorems

| Group | Theorem | Statement summary |
|-------|---------|------------------|
| Transfer | `transfer_preserves_total_supply` | `totalSupply` unchanged on success |
| Transfer | `transfer_no_overdraft` | insufficient balance → error |
| Transfer | `transfer_no_creation` | tokens conserved between distinct parties |
| Transfer | `transfer_self_noop` | `from = to` → state unchanged |
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

Runs as a post-elaboration pass over contract, lemma, and theorem modules. All messages use prefix `lsc:` with file, line, and column. **Hard errors** abort compilation. **Warnings** are reported but do not abort.

### §12.1 Contract module errors

| Construct | Severity | Error message |
|-----------|----------|--------------|
| `Nat`, `Int`, `Float` | error | `lsc: use UInt256` |
| `String`, `Char` | error | `lsc: use Bytes[N]` |
| Closures / lambda capturing outer variable | error | `lsc: use a top-level function` |
| Partial application | error | `lsc: partial application not supported` |
| `IO`, `StateM`, `ST` | error | `lsc: stateful monads not allowed; do-notation over Except E is permitted` |
| Higher-order functions | error | `lsc: functions cannot be passed as arguments` |
| Unbounded recursion | error | `lsc: recursive function must be structurally terminating` |
| `List` or `Array` in author code | error | `lsc: use Mapping` |
| `structure … extends` | error | `lsc: storage inheritance not supported in v1` |
| Hand-written export wrapper | error | `lsc: use @[Lsc.external] on contract functions` |
| `EvmContext` in author code | error | `lsc: use MsgContext for message/block context` |
| Error type without `@[Lsc.error]` | error | `lsc: error type must be declared with @[Lsc.error]` |
| `@[Lsc.error]` on non-inductive | error | `lsc: @[Lsc.error] may only annotate inductive types` |
| `@[Lsc.error]` type missing `arith` constructor | error | `lsc: error type must include arith : ArithError → E` |
| `@[Lsc.error]` type missing `extern` constructor when `extcall!` used | error | `lsc: error type must include extern : ExternError → E` |
| `@[Lsc.error]` type missing `eth` constructor when `native_transfer!` used | error | `lsc: error type must include eth : EthError → E` |
| `@[Lsc.error]` type missing `LscError` instance | error | `lsc: error type must have a LscError instance` |
| Bare `Option State` on mutator | error | `lsc: use Except E S` |
| Invalid `@[Lsc.external]` return shape | error | `lsc: must return Except E S, Except E (S × V), S, or V` |
| Unresolved polymorphism | error | `lsc: polymorphic function cannot be compiled` |
| `Bytes[N]` literal longer than `N` | error | `lsc: Bytes literal exceeds declared bound` |
| More than one `@[Lsc.initialize]` | error | `lsc: at most one @[Lsc.initialize] per contract module` |
| `sload` / `sstore` in author code | error | `lsc: storage IO is emitter-only` |
| `World` in contract functions | error | `lsc: World not allowed in contract functions` |
| `extcall!` / `staticcall!` in `test/*Lemma.lean` or `test/*Theorem.lean` | error | `lsc: external calls are contract-module only` |
| Invalid interface cast `(e : I)` | error | `lsc: I must be an interface with LscInterface instance` |
| Unknown interface method in `extcall!` / `staticcall!` | error | `lsc: method not found on interface I` |
| Malformed event signature | error | `lsc: invalid event signature; expected "Name(type,type)"` |
| Event arg count / type mismatch | error | `lsc: event argument mismatch` |
| Multiple `MsgContext` parameters | error | `lsc: at most one MsgContext parameter per export` |
| `require` on infallible function | error | `lsc: require requires Except return type` |
| `assert` in contract function | error | `lsc: use require; assert! is a runtime panic` |
| Plain `+ - * /` on `UInt256` | error | `lsc: use +? or +↻ on UInt256` |
| `UInt256 + ℕ` in contract module | error | `lsc: use +? for arithmetic in contract functions` |
| `@[Lsc.public]` not on State field | error | `lsc: @[Lsc.public] may only annotate State struct fields` |
| `@[Lsc.public]` field name collides with existing `@[Lsc.external]` | error | `lsc: field is @[Lsc.public] but @[Lsc.external] def already exists` |
| `@[Lsc.receive]` without `MsgContext` parameter | error | `lsc: @[Lsc.receive] must take MsgContext` |
| `@[Lsc.allow_reentrant]` on export | warning | `lsc: REENTRANT function; ensure reentrancy safety manually` |
| `Address` named caller/sender/from/owner for authorization | warning | `lsc: use ctx.sender from MsgContext instead of an Address parameter` |
| `Bytes[0]` field | warning | `lsc: field can never hold data` |

### §12.2 Lemma module errors (`test/*Lemma.lean`)

| Construct | Severity | Error message |
|-----------|----------|--------------|
| `theorem` (non-helper) | error | `lsc: use lemma in *Lemma.lean; put requirements in *Theorem.lean` |
| `sorry` | error | `lsc: sorry not allowed in lemma modules` |
| `+?`, `-?`, `*?`, `/?` | error | `lsc: checked arithmetic (+?) is contract-only; lemmas use .val or +↻` |
| `UInt256 + UInt256` (or `- * /` between two `UInt256`) | error | `lsc: use .val arithmetic on ℕ, +↻, or UInt256 + ℕ literal add` |
| `extcall!` / `staticcall!` | error | `lsc: external calls are contract-module only` |

### §12.3 Theorem module errors (`test/*Theorem.lean`)

| Construct | Severity | Error message |
|-----------|----------|--------------|
| `sorry` | error | `lsc: sorry not allowed in theorem modules` |
| Theorem body is not a single lemma delegation | error | `lsc: theorem body must be a one-line *Lemma delegation` |
| Missing required theorem | error | `lsc: compliance requires "f" but no theorem in *Theorem.lean` |
| `lemma` | error | `lsc: put proofs in *Lemma.lean` |
| `extcall!` / `staticcall!` | error | `lsc: external calls are contract-module only` |

---

## §13 Compiler-Generated Code

### §13.1 What the emitter produces

At each `@[Lsc.external]` boundary, the emitter generates:

1. **ABI dispatcher** — 4-byte selector from `keccak256(canonicalSignature)`; Yul dispatch
2. **Calldata decode** — ABI-decode included parameters (§4.5) from calldata
3. **`msg.value` guard** — revert if `CALLVALUE > 0` on non-payable exports (§5.2)
4. **Reentrancy guard** — unless `@[Lsc.allow_reentrant]`; standard mutex pattern
5. **`MsgContext` binding** — when `ctx : MsgContext` is present: `sender := msg.sender`, `value := msg.value`, `timestamp := block.timestamp`, `number := block.number`
6. **State load** — `sload` all struct fields (full load for mutators; lazy slot read for views and `@[Lsc.public]` getters)
7. **Author function call** — invoke the `@[Lsc.external]` function (and its callees); lower each `extcall!` / `staticcall!` site to `CALL` / `STATICCALL` with ambient `World` and `MsgContext`
8. **On `.error e`** — `revert(abi.encode(e))`; no storage writes; no events; extern `World` changes rolled back
9. **On `.ok val`** — `sstore` all modified fields; collect and emit `emit!` / `Lsc.Event.log` sites in source order via `LOG` opcodes; ABI-encode non-state component as returndata

For `@[Lsc.public]`-generated getters and all view exports: step 6 performs a lazy load of only the accessed slot(s); step 9 is skipped.

### §13.2 Auto load/store invariant

Any emitter optimization (lazy view loads, diff stores) must produce observable behavior identical to:

```
load all fields → call author function → store all fields (on `.ok`)
```

This invariant bridges Lean proofs (pure functions on `State` snapshots) and EVM bytecode (individual slot reads/writes).

### §13.3 Formal verification of the lowering pipeline

The Lean IR → Yul emitter is implemented in Lean 4 and **formally verified**: the emitter is proved correct with respect to the auto load/store invariant (§13.2). This includes:

| Component | Verification status |
|-----------|-------------------|
| Lean IR → Yul emitter | Formally verified in Lean |
| ABI encoding/decoding fidelity | Formally verified in Lean |
| `LOG` opcode encoding from `emit!` / `Lsc.Event.log` | Formally verified in Lean |
| `keccak256` selector computation | Formally verified in Lean |
| `Mapping` slot layout match (Lean model ↔ Yul output) | Formally verified in Lean |

Foundry fuzz tests (`deployCode` + property assertions) serve as an additional independent check. The emitter correctness proof and test suite are part of the LSC distribution.

### §13.4 Gas (non-goal in v1)

Gas estimation, optimization, and EIP-150 gas forwarding rules for `CALL` are outside the v1 proof scope. Gas is fully delegated to the emitter and testable via Foundry.