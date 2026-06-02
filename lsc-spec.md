# LSC — Lean Smart Contracts Language Specification

**Language version:** LSC 1.0
**Lean baseline:** `leanprover/lean4:stable` (pinned per project)
**Execution target:** EVM (bytecode via lowering; standard JSON ABI)
**Companion document:** [lsc-toolchain.md](lsc-toolchain.md) — reference compiler, Foundry integration, artifacts, demos

---

## §1 Overview

### §1.1 What LSC is

**LSC (Lean Smart Contracts)** is a strict subset of Lean 4 for writing smart contracts whose correctness properties are machine-checked by the Lean kernel before deployment.

The core idea is simple: authors write **pure state-transition functions** in Lean. The compiler generates everything the EVM needs — ABI wrappers, storage load/store, LOG opcodes, CALL lowering. Authors never touch `sload`, `sstore`, ABI encoding, or log assembly directly.

This restriction is intentional. Lean's kernel can check proofs about pure functions automatically. The moment authors write storage IO or ABI ceremony, proofs become hard. LSC chooses to restrict the *language* rather than restrict *what you can deploy* — the same tradeoff Vyper makes for security, applied here for provability.

**What you can deploy:** persistent storage and mappings, events/logs, standard ABIs (ERC-20 `bool` returns, etc.), cross-contract calls, revert semantics, full EVM bytecode.

**What is restricted in author code:** stateful monads (`StateM`, `IO`), higher-order functions, closures, unbounded collections in state, `Nat`/`Int`/`String`, `structure … extends`, unbounded recursion, manual storage IO. `do`-notation over `Except E` is allowed for fallible exports. See §13 for the full validator error table.

### §1.2 The three files

Every LSC project produces three kinds of module for each contract:

| File | Role | Kernel-checked |
|------|------|---------------|
| `src/Counter.lean` | Contract — `State` struct + `@[lsc.external]` functions | Yes (types) |
| `spec/CounterSpec.lean` | Spec — `def` declarations of type `Prop` | Yes (well-formedness) |
| `test/CounterProof.lean` | Proof — `theorem` proofs of each spec `def` | Yes (full proof check) |

The **contract** is what deploys. The **spec** is the requirements document — written and reviewed by humans, containing only `Prop` definitions, no proof terms. The **proof** is generated (typically by an LLM) and checked by the Lean kernel; it never needs human review because the kernel guarantees correctness when it compiles without `sorry`.

**End-to-end Counter example:**

`src/Counter.lean`:
```lean
import Lsc.Prelude
open Lsc

structure CounterState where
  @[lsc.public]
  number : UInt256

-- Fallible mutator: overflow at UInt256 max routes to ArithError
@[lsc.external]
def increment (s : CounterState) : Except ArithError CounterState :=
  checked id do
  let n ← s.number +? 1
  return .ok { s with number := n }
```

`spec/CounterSpec.lean`:
```lean
import Counter

inductive CounterAction where
  | increment

/-- Single-step semantics: apply one action; on `.error`, leave state unchanged. -/
def applyAction (s : CounterState) : CounterAction → CounterState
  | .increment =>
      match increment s with
      | .ok s'    => s'
      | .error _ => s

/-- Sequence semantics: fold `applyAction` (same as recursive error-skipping). -/
def applyActions (s : CounterState) (actions : List CounterAction) : CounterState :=
  actions.foldl applyAction s

/-- On success, increment increases number by exactly 1. -/
def increment_increases_number
    (s s' : CounterState)
    (h : increment s = .ok s') : Prop :=
  s'.number = s.number + 1

/-- increment errors iff number is at UInt256 max (overflow). -/
def increment_overflows_iff
    (s : CounterState)
    (h : increment s = .error .overflow) : Prop :=
  s.number = UInt256.max

/-- No sequence of actions can decrease the number. -/
def number_never_decreases
    (s : CounterState) (actions : List CounterAction) : Prop :=
  (applyActions s actions).number ≥ s.number
  -- equivalently: (actions.foldl applyAction s).number ≥ s.number
```

`test/CounterProof.lean`:
```lean
import CounterSpec

theorem increment_increases_number
    (s s' : CounterState)
    (h : increment s = .ok s') :
    CounterSpec.increment_increases_number s s' h := by
  simp [CounterSpec.increment_increases_number, increment] at h
  simp [UInt256.addChecked_some (by omega), Option.orWrap_some] at h; omega

theorem increment_overflows_iff
    (s : CounterState)
    (h : increment s = .error .overflow) :
    CounterSpec.increment_overflows_iff s h := by
  simp [CounterSpec.increment_overflows_iff, increment] at h
  simp [UInt256.addChecked_none_of_ge (by omega), Option.orWrap_none] at h; omega

theorem number_never_decreases
    (s : CounterState) (actions : List CounterAction) :
    CounterSpec.number_never_decreases s actions := by
  simp only [CounterSpec.number_never_decreases, CounterSpec.applyActions]
  apply Lsc.Invariant CounterSpec.applyAction (fun s' => s'.number ≥ s.number)
  · intro s' a hP
    cases a <;> simp [CounterSpec.applyAction, increment] at hP ⊢ <;> omega
  · simp
```

Three theorems matching three spec `def`s: the success property, the overflow condition, and the global monotonicity invariant via `Lsc.Invariant` on `applyAction` (§9.1).

```mermaid
flowchart LR
  Contract[Counter.lean]
  Spec[CounterSpec.lean]
  Proof[CounterProof.lean]
  Contract --> Spec
  Spec --> Proof
  Proof --> Kernel[Lean kernel ✓]
```

### §1.3 What the compiler generates vs what authors write

Authors write pure functions. The compiler generates everything else at `@[lsc.external]` boundaries:

| Author writes | Compiler generates |
|---------------|--------------------|
| `@[lsc.external] def increment (s : CounterState) : Except ArithError CounterState` | ABI dispatcher, `sload` all fields, call `increment`, on `.ok s'` → `sstore`, on `.error e` → `revert(abi.encode(e))` |
| `@[lsc.public]` on a State field (e.g. `number`) | `@[lsc.external]` view `def` + read-only dispatcher (§3.5) |
| `Lsc.Event.log (TransferEvent.mk from to amount)` in function body | `LOG2` opcode after store, with correct topic0 and ABI-encoded data |
| `Lsc.extern.call IERC20.transferFrom ...` in export body (v2b) | `call(gas, addr, 0, ...)` + ABI encode/decode |

Proofs target the author-written functions directly — the same signatures that get deployed. The compiler-generated wrappers are trusted in v1 (tested via Foundry fuzz tests; see §14.3).

### §1.4 Non-goals (v1)

- Payable functions (`msg.value > 0`)
- Upgradeability / proxies
- `structure … extends` storage inheritance (removed for simplicity; see §3.3)
- Formal proof of the lowering pipeline (Phase 2)
- Gas optimization in the proof model
- Mandatory application compliance packs in the language definition
- LLM prompt guidance (proof generation is external; the kernel is the arbiter)

For `lakefile.lean` layout, see [lsc-toolchain.md §2](lsc-toolchain.md#2-project-layout-and-lake).

---

## PART I — THE CONTRACT LANGUAGE

---

## §2 Types

### §2.1 Primitive types

The validator permits exactly these primitive types in contract code.

| LSC type | Lean definition | EVM/ABI type | Notes |
|----------|----------------|--------------|-------|
| `UInt256` | `Fin (2^256)` | `uint256` | Arithmetic is modular (`Fin`), identical in contract and spec code |
| `Address` | `structure Address where val : UInt256` | `address` | Distinct newtype; not coercible to `UInt256` without `.val` |
| `Bool` | Lean built-in | `bool` | ABI boundary and guards |
| `Bytes32` | `Fin (2^256)` newtype | `bytes32` | Raw 32-byte value |
| `Bytes[N]` | `{ b : ByteArray // b.size ≤ N }` | `bytes` / `string` | Explicit max length; see §2.2 |

#### Arithmetic semantics — one rule everywhere

`UInt256 = Fin (2^256)` throughout. `+ - * /` mean modular (`Fin`) arithmetic in
**all contexts** — contract code, spec files, and proof files. There is no implicit
operator rewriting.

Two arithmetic modes are available in contract functions:

| Mode | Syntax | Returns | Use when |
|------|--------|---------|----------|
| Wrapping | `a + b` | `UInt256` (Fin) | overflow is impossible or irrelevant |
| Checked | `a +? b` | `Option UInt256` | overflow must revert |

Checked arithmetic is routed to the error type via `checked <variant> do` — a
block macro that auto-wraps every `← +?` result without repeating the variant
name on each line. See §2.5 for the full design.

`do`-notation in `@[lsc.external]` functions is standard `Except E` do-notation.
There is no operator rewriting — `+` is always `Fin` add everywhere.

> **Why not rewrite `+` to checked arithmetic inside `do`?**
> Implicit operator rewriting creates a semantic gap between contract code and spec
> code: the same expression would mean different things in different files. LSC
> eliminates this gap — `a + b` is always `Fin` addition. The `+?` operator and
> `checked` block make fallible arithmetic visible and explicit without being
> verbose. The specification and the implementation share exactly one arithmetic
> model.

`Address` is defined in `Lsc.Prelude`:
```lean
structure Address where
  val : UInt256
  deriving DecidableEq, Repr
```

It is not coercible to `UInt256` without an explicit `.val` projection, preventing accidental arithmetic on addresses.

### §2.2 Bytes[N]

`Bytes[N]` is a Vyper-style bounded byte array. The length bound is part of the type.

```lean
-- Lean 4 definition (Lsc.Prelude)
abbrev Bytes (n : Nat) := { b : ByteArray // b.size ≤ n }

notation "Bytes[" n "]" => Bytes n
```

**Examples:**
```lean
tokenUri   : Bytes[512]
ipfsCid    : Bytes[64]
shortLabel : Bytes[32]
```

**Validator rules:**
- `N` must be a numeric literal (not a variable). Runtime-variable bounds are not
  supported in v1.
- `N = 0` is a validator warning (field can never hold data).
- No global maximum in the type system; the emitter may impose a practical limit
  (e.g. 4096 bytes) to avoid pathological storage layouts. This limit is
  configurable in `foundry.toml` under `[lsc.limits]`.

**Storage layout** mirrors Vyper/Solidity:
- If `b.size ≤ 31`: data is left-aligned in the slot with `b.size * 2` in the LSB.
- If `b.size > 31`: slot `p` holds `b.size * 2 + 1`; payload lives at
  `keccak256(p)` in 32-byte chunks.

ABI mapping: `Bytes[N]` ↔ `bytes` (or `string` for text metadata).

### §2.3 Mapping

`Mapping K V` is defined as a plain Lean 4 function:

```lean
-- Lsc.Prelude
abbrev Mapping (K V : Type) := K → V

namespace Mapping

def get (m : Mapping K V) (k : K) : V := m k

def set [DecidableEq K] (m : Mapping K V) (k : K) (v : V) : Mapping K V :=
  Function.update m k v

def empty [Inhabited V] : Mapping K V := fun _ => default

end Mapping
```

#### Simp laws (all free from `Function.update`)

```lean
-- These follow from Function.update_same and Function.update_noteq in Lean core.
-- No custom axioms needed.

@[simp] theorem Mapping.get_set_same [DecidableEq K] (m : Mapping K V) (k : K) (v : V) :
    (m.set k v).get k = v :=
  Function.update_same k v m

@[simp] theorem Mapping.get_set_other [DecidableEq K] (m : Mapping K V)
    (k k' : K) (v : V) (h : k ≠ k') :
    (m.set k v).get k' = m.get k' :=
  Function.update_noteq h v m

@[simp] theorem Mapping.get_empty [Inhabited V] (k : K) :
    (Mapping.empty : Mapping K V).get k = default := rfl

@[simp] theorem Mapping.set_set_same [DecidableEq K] (m : Mapping K V)
    (k : K) (v v' : V) :
    (m.set k v).set k v' = m.set k v' :=
  Function.update_idem k v v' m   -- or: funext + Function.update_same/noteq
```

There is **no storage axiom**. Key injectivity follows from `DecidableEq K` and
`Function.update_noteq`. Struct field slot disjointness is proved by `decide`.

Nested mappings (e.g. ERC-20 allowances) are `Mapping K (Mapping K' V)`.

> **Why `K → V` instead of `Finsupp K V`?**
> Contracts never enumerate keys, iterate mappings, or sum over them. `Finsupp`
> would require `AddZeroClass V` on every value type and adds proof obligations
> that don't correspond to any on-chain behavior. A plain function is the
> minimal model that makes `simp [Mapping.get_set_same]` work and keeps proof
> obligations finite.

### §2.4 Except

LSC uses Lean 4's standard `Except E A` as the return type for fallible functions.
No custom `Result` type is defined.

```lean
-- From Lean 4 core (Lsc.Prelude re-exports these for convenience)
-- inductive Except (E A : Type) where
--   | ok    : A → Except E A
--   | error : E → Except E A
--
-- instance : Monad (Except E) -- already in core
```

The four return shapes:

| Shape | Meaning | Example |
|-------|---------|---------|
| `S` | Infallible mutator | `def setFlag (s : S) : S` |
| `V` | Infallible view | `def number (s : S) : UInt256` |
| `Except E S` | Fallible mutator, no ABI return value | `def increment (s : S) : Except E S` |
| `Except E (S × V)` | Fallible mutator with return value | `def swap (s : S) ... : Except E (S × UInt256)` |

`S` must be the contract's `State` type for the emitter to treat it as a mutator. `V` is any primitive or product of primitives. The validator distinguishes shapes by whether the success type contains `State`.

- `.ok val` — success; emitter persists state, ABI-encodes the non-state component
- `.error e` — EVM revert; emitter ABI-encodes `e` as a Solidity custom error

**Infallible shapes** are wrapped in an unconditional success path by the emitter.

**Views that can fail** (rare): `Except E V` where `V` is not `State`.

Because `Monad (Except E)` is in Lean core, all standard do-notation and bind
combinators work without any LSC-specific plumbing.

The full ABI inference rules are in §4.4.

### §2.5 Error types, `@[lsc.error]`, arithmetic errors, and `checked`

#### `@[lsc.error]` — declaring contract error types

`@[lsc.error]` does exactly one thing: **registers the inductive with the emitter**
for ABI `errors` generation and revert encoding. No instances are generated, no
conventions on variant names are imposed.

```lean
@[lsc.error]
inductive TokenError where
  | insufficientBalance
  | insufficientAllowance
  | unauthorized
  | arith (e : ArithError)   -- recommended: one variant wraps all arithmetic failures
  deriving DecidableEq, Repr
```

Everything else — `DecidableEq`, `Repr`, doc comments, additional instances — is
plain Lean 4 `deriving` or `instance` as normal.

#### `ArithError` — the prelude arithmetic error type

`Lsc.Prelude` provides a single arithmetic error type for use across all contracts:

```lean
-- Lsc.Prelude
inductive ArithError where
  | overflow
  | divisionByZero
  deriving DecidableEq, Repr
```

Contracts embed it as a single variant. No typeclass, no instance, no codegen.

#### The `+?` operator family

`+?`, `-?`, `*?`, `/?` return `Option UInt256`. They are the only way to express
fallible arithmetic in LSC. Plain `+ - * /` always wrap (Fin semantics):

```lean
-- Lsc.Prelude
def UInt256.addChecked (a b : UInt256) : Option UInt256 :=
  if a.val + b.val < 2^256 then some ⟨a.val + b.val⟩ else none

def UInt256.subChecked (a b : UInt256) : Option UInt256 :=
  if a.val ≥ b.val then some ⟨a.val - b.val⟩ else none

def UInt256.mulChecked (a b : UInt256) : Option UInt256 :=
  if a.val = 0 ∨ b.val ≤ (2^256 - 1) / a.val then some ⟨a.val * b.val⟩ else none

def UInt256.divChecked (a b : UInt256) : Option UInt256 :=
  if b.val ≠ 0 then some ⟨a.val / b.val⟩ else none

scoped notation a " +? " b => UInt256.addChecked a b
scoped notation a " -? " b => UInt256.subChecked a b
scoped notation a " *? " b => UInt256.mulChecked a b
scoped notation a " /? " b => UInt256.divChecked a b
```

#### `checked <f> do` — the recommended arithmetic block

`checked <f> do` is the primary way to write fallible arithmetic in LSC.
It is a `do`-block macro that declares the error-routing constructor **once**
at the block header; every `← expr` where `expr : Option A` is automatically
wrapped via `orWrap f`. Lines with `← expr` where `expr : Except E A` (e.g.
`require`) are left untouched.

```lean
-- Lsc.Prelude
macro "checked" f:term " do" body:doSeq : term =>
  `((do $body : Option _) |>.orWrap $f)
-- Each `← e` where e : Option A  desugars to `← e |>.orWrap $f`
-- Each `← e` where e : Except E A is left unchanged
```

**Full example — AMM swap:**

```lean
@[lsc.external]
def swap (s : AMMState) (amountIn : UInt256)
    : Except AMMError AMMState := checked .arith do
  require (s.reserve0 > 0) .uninitializedPool
  let num       ← amountIn  *? s.reserve1    -- Option; auto-wrapped via .arith
  let denom     ← s.reserve0 +? amountIn     -- Option; auto-wrapped via .arith
  let amountOut ← num /? denom               -- Option; auto-wrapped via .arith
  return .ok { s with
    reserve0 := s.reserve0 + amountIn        -- plain Fin +, no check
    reserve1 := s.reserve1 - amountOut       -- plain Fin -, no check
  }
```

`.arith` is the constructor `ArithError → AMMError`. Any `none` from `+? -? *?`
produces `.error (.arith .overflow)`; `/?` producing `none` becomes
`.error (.arith .overflow)` in v1 (see note on division below).

**Naming:** `checked` is the exact dual of Solidity's `unchecked`. In Solidity,
arithmetic reverts by default and `unchecked { }` opts out. In LSC, `+` wraps
by default and `checked .arith do` opts in to overflow checking:

| | Solidity | LSC |
|---|---|---|
| Default `+` | reverts on overflow | wraps (Fin) |
| Opt-out/in block | `unchecked { a + b }` | `a + b` (plain) |
| Checked | `a + b` (default) | `checked .arith do; let x ← a +? b` |

**ERC-20 transfer — full pattern:**

```lean
@[lsc.error]
inductive TokenError where
  | insufficientBalance
  | unauthorized
  | arith (e : ArithError)
  deriving DecidableEq, Repr

@[lsc.external]
def transfer (caller : Caller) (s : ERC20State)
    (to : Address) (amount : UInt256)
    : Except TokenError (ERC20State × Bool) := checked .arith do
  require (s.balances.get caller.val ≥ amount) .insufficientBalance
  let newCaller ← s.balances.get caller.val -? amount
  let newTo     ← s.balances.get to         +? amount
  let s' := { s with balances :=
    s.balances.set caller.val newCaller |>.set to newTo }
  Lsc.Event.log (TransferEvent.mk caller.val to amount)
  return .ok (s', true)
```

#### `orWrap` and `orError` — single-operation fallback

For a single checked operation outside a `checked` block, or when `ArithError`
is used as the top-level error type directly:

```lean
-- Lsc.Prelude

/-- Map None to a wrapped ArithError. f is a constructor ArithError → E.
    Use with +? -? *? for single operations outside a checked block. -/
def Option.orWrap (f : ArithError → E) : Option A → Except E A
  | some a => .ok a
  | none   => .error (f .overflow)

/-- Like orWrap but uses .divisionByZero. Use with /? -/
def Option.orWrapDiv (f : ArithError → E) : Option A → Except E A
  | some a => .ok a
  | none   => .error (f .divisionByZero)

/-- Map None to a concrete error value.
    Use when ArithError is your top-level E (no wrapping needed). -/
def Option.orError (e : E) : Option A → Except E A
  | some a => .ok a
  | none   => .error e
```

**Simple contracts** (no domain errors) may use `ArithError` directly as `E`:

```lean
@[lsc.external]
def increment (s : CounterState) : Except ArithError CounterState :=
  checked id do
  let n ← s.number +? 1
  return .ok { s with number := n }
```

#### Summary

| Pattern | When to use | Example |
|---------|------------|---------|
| `checked .arith do` | Multiple arithmetic ops (recommended) | AMM, ERC-20 |
| `\|>.orWrap .arith` | Single operation outside `checked` | One-off update |
| `\|>.orWrapDiv .arith` | Division outside `checked` | Price calc |
| `\|>.orError .overflow` | `ArithError` is top-level `E` | Simple counter |

> **Why does `/?` inside `checked` map to `.overflow` and not `.divisionByZero`?**
> `checked .arith do` uses a single constructor `f : ArithError → E`. `orWrap`
> always passes `f .overflow`. Division-by-zero semantics require `f .divisionByZero`,
> which `orWrapDiv` provides. For `/?` inside a `checked` block, use
> `let x ← a /? b |>.orWrapDiv .arith` explicitly. v2 may detect `/?` and
> route to `.divisionByZero` automatically.

#### Bridge lemmas (Mathlib naming, all `@[simp]`)

```lean
@[simp] theorem UInt256.addChecked_some {a b : UInt256} (h : a.val + b.val < 2^256) :
    a +? b = some ⟨a.val + b.val⟩ := by simp [UInt256.addChecked, h]

@[simp] theorem UInt256.addChecked_none_of_ge {a b : UInt256} (h : a.val + b.val ≥ 2^256) :
    a +? b = none := by simp [UInt256.addChecked]; omega

@[simp] theorem UInt256.subChecked_some {a b : UInt256} (h : a.val ≥ b.val) :
    a -? b = some ⟨a.val - b.val⟩ := by simp [UInt256.subChecked, h]

@[simp] theorem UInt256.subChecked_none_of_lt {a b : UInt256} (h : a.val < b.val) :
    a -? b = none := by simp [UInt256.subChecked]; omega

@[simp] theorem Option.orWrap_some {f : ArithError → E} {a : A} :
    (some a).orWrap f = .ok a := rfl

@[simp] theorem Option.orWrap_none {f : ArithError → E} :
    (none : Option A).orWrap f = .error (f .overflow) := rfl

@[simp] theorem Option.orWrapDiv_none {f : ArithError → E} :
    (none : Option A).orWrapDiv f = .error (f .divisionByZero) := rfl

-- *? analogous to +?; /? analogous to -?
```

**Proof recipe:** `simp [myFunction]` unfolds `checked`, `+?`, and `orWrap`
in one step. Bridge lemmas fire automatically; `omega` closes arithmetic goals.

### §2.6 Forbidden types

The validator permits exactly these primitive types in contract code. Any other type is a hard error (§13.1).

| Forbidden | Validator error | Use instead |
|-----------|----------------|-------------|
| `Nat`, `Int`, `Float` | `lsc: type Nat is not allowed; use UInt256` | `UInt256` |
| `String`, `Char` | `lsc: String is not allowed; use Bytes[N]` | `Bytes[N]` |
| `List`, `Array` in state | `lsc: List is not allowed in contract code` | `Mapping` |
| `IO`, `StateM`, `ST`, or any monad that threads implicit state | `lsc: stateful monads are not allowed in contracts; use explicit state passing` | Explicit state passing |
| Higher-order functions | `lsc: functions cannot be passed as arguments` | Top-level helpers |
| Recursive types / inductives with >2 constructors | `lsc: inductive type X is not allowed` | Struct + `Mapping` (except `@[lsc.error]` error enums) |
| `Option (S × Ret)` on mutator | `lsc: use Except E (S × Ret) for mutators` | `Except E (S × Ret)` |

**`do`-notation over `Except E` is allowed and recommended** for functions that can fail. This is the only monad permitted in contract code. It does not thread implicit state — `s` remains an explicit parameter, `s'` is an explicit return value — so theorems are unaffected.

```lean
-- Allowed: do-notation over Except E (error-only monad)
@[lsc.external]
def increment (s : CounterState) : Except ArithError CounterState :=
  checked id do
  let n ← s.number +? 1
  return .ok { s with number := n }

-- Banned: StateM or any monad that hides s
def increment : StateM CounterState Unit := ...
-- lsc: stateful monads are not allowed in contracts
```

> **Why not richer types?**
> Lean's proof automation (`simp`, `omega`, `decide`) works best on flat, finite structures. `Nat` requires `omega` extensions that interact poorly with `Fin`; `List` in state makes proof obligations unbounded; stateful monads hide the state threading that theorems need to quantify over (`s` and `s'` must stay explicit). `do` over `Except E` only threads errors. Every restriction here trades expressiveness for a proof that `simp` can close in one step.

> **Why `Except` instead of a custom `Result` or bare `Option`?**
> `Option` cannot express *which* error fired. Lean's core `Except E A` is the standard fallible monad; specs prove "this specific error fires under these conditions" via `.error e`. `Except.ok.injEq` / `Except.error.injEq` and the bridge lemmas in §11.1 keep proof bodies short. See §11.1.

---

## §3 State

### §3.1 Defining a State struct

Contract storage is a plain Lean 4 struct. Each field is a primitive type or `Mapping`.

```lean
structure CounterState where
  @[lsc.public]
  number : UInt256   -- slot 0; ABI getter generated (§3.5)
```

```lean
structure ERC20State where
  name        : Bytes[32]                                      -- slot 0
  symbol      : Bytes[32]                                      -- slot 1
  decimals    : UInt256                                        -- slot 2
  totalSupply : UInt256                                        -- slot 3
  balances    : Mapping Address UInt256                 -- slot 4
  allowances  : Mapping Address (Mapping Address UInt256)  -- slot 5
```

Fields receive sequential storage slots in declaration order from slot 0. Mappings use `keccak256(abi.encode(key, slot))` per Solidity layout rules.

The **contract name** is the file stem (`Counter` from `src/Counter.lean`). No contract-name attribute exists; the validator requires PascalCase file stems.

### §3.2 Mapping laws

`Mapping` is `K → V` with `get` / `set` / `empty` and four `@[simp]` lemmas derived from `Function.update` (§2.3). There is **no storage axiom**. Struct field slot disjointness is provable by `decide` from sequential slot assignment.

### §3.3 Slot layout

Fields occupy slots 0, 1, 2, … in declaration order. `Mapping` fields occupy one slot (the mapping root); individual entries live at `keccak256(abi.encode(key, slot))`.

`structure … extends` is **not supported in v1**. Each contract defines its own complete `State` struct. Shared field patterns (e.g. ERC-20 base) are expressed by composing structs manually or by using a library `def` over the full state type.

> **Why no `extends`?**
> Storage inheritance introduces slot-layout questions (what happens with deep chains? diamond patterns?) that have no clean answer without significant validator complexity. Vyper takes the same position. The proof benefit of `extends` is marginal — authors can always include the parent fields directly. Deferred to v2 if a clear use case emerges.

### §3.4 State vocabulary

Three terms are used precisely and consistently:

| Term | Meaning | Who uses it |
|------|---------|-------------|
| `set` | Functional update: `Mapping.set`, record `{ s with field := v }` | Contract authors |
| `State` | Full contract snapshot struct threaded through `@[lsc.external]` functions | Authors and spec theorems |
| `store` | Persist snapshot to chain storage via `sstore` | **Emitter only** at `@[lsc.external]` boundary |

Authors never call `store`. Theorems quantify over complete `s` and `s'`. The emitter's whole-state load → apply → store semantics are the trust boundary (§14.3).

> **Why whole-state load/store instead of diff-store?**
> Theorems quantify over `s` and `s'` as complete snapshots. Partial loads or diff-stores would require invariant lemmas in every proof to show unwritten fields are unchanged. Whole-state load/store makes this trivial — `s'.field = s.field` when `field` doesn't appear in the function body is closed by `simp`.

### §3.5 The `@[lsc.public]` annotation

Mark a State field with `@[lsc.public]` to expose it on-chain as a read-only ABI getter. The compiler synthesizes an `@[lsc.external]` view named after the field — authors do not write the boilerplate `def fieldName (s : State) : T := s.fieldName`.

```lean
structure CounterState where
  @[lsc.public]
  number : UInt256
-- Generated (not written by author):
-- @[lsc.external]
-- def number (s : CounterState) : UInt256 := s.number
```

**Default visibility:** fields without `@[lsc.public]` are storage-only (no ABI entry). Only `@[lsc.external]` functions and `@[lsc.public]`-generated getters appear in the deployed ABI.

**Generation rules:**

| Field type | Generated signature | Body |
|------------|---------------------|------|
| Scalar (`UInt256`, `Address`, `Bool`, `Bytes32`, `Bytes[N]`) | `def fieldName (s : State) : T` | `s.fieldName` |
| `Mapping K V` | `def fieldName (s : State) (k : K) : V` | `s.fieldName.get k` |
| Nested `Mapping` | one key parameter per mapping level, left-to-right | nested `.get` |

Generated exports are infallible views (§4.3): return type `T` directly, not `Except` or `Option`. The emitter treats them like author-written views — no `sstore`, `s : State` excluded from ABI calldata (§4.5).

**Naming:** the ABI function name equals the Lean field name. v1 has no alias attribute. When the standard ABI name differs from the field name (e.g. IERC-20 `balanceOf` vs field `balances`), omit `@[lsc.public]` on that field and write a manual `@[lsc.external]` export instead.

**Proofs:** theorems continue to use `s.field` directly. Generated getters exist for deploy/ABI parity; spec modules need not reference them.

**Validator rules:** see §13.1.

> **Why an annotation instead of exposing all fields?**
> Most storage is internal. Opt-in `@[lsc.public]` mirrors Solidity `public` without generating getters for every field (mappings, internal counters, etc.). Proofs stay on record fields; the compiler only adds ABI surface where requested.

### §3.6 `@[lsc.initialize]`

Every contract may declare exactly one initialization function with `@[lsc.initialize]`.
This is called once at deployment (constructor) and also serves as the designated
re-initialization entry point for proxy upgrade patterns.

```lean
@[lsc.initialize]
def initialize (name symbol : Bytes[32]) (decimals : UInt256)
    (initialSupply : UInt256) (owner : Caller)
    : Except TokenError TokenState :=
  return .ok {
    name        := name
    symbol      := symbol
    decimals    := decimals
    totalSupply := initialSupply
    balances    := Mapping.empty |>.set owner.val initialSupply
    allowances  := Mapping.empty
  }
```

**Rules:**
- At most one `@[lsc.initialize]` per contract module (validator error if more).
- The return type must be `Except E S` or the bare state type `S` (infallible
  constructor). No ABI return value.
- `Caller` parameters are bound to `msg.sender` at deploy time, same as
  `@[lsc.external]`.
- The emitter generates an ABI constructor (not a named function) from
  `@[lsc.initialize]`.
- For proxy patterns, the emitter additionally generates an `initialize(...)` named
  ABI function callable post-deployment. The validator enforces that if
  `@[lsc.initialize]` is present and the contract is marked `@[lsc.proxy_compatible]`,
  a reentrancy guard on `initialize` is generated automatically.

**Spec / proof:** `@[lsc.initialize]` functions are treated identically to
`@[lsc.external]` in spec and proof files. The compliance manifest (§12) includes
constructor theorems (e.g. `constructor_mints_initial_supply`).

---

## §4 Functions (Exports)

### §4.1 The `@[lsc.external]` annotation

Public ABI functions are declared by annotating contract functions with `@[lsc.external]` (parameterless). Fields marked `@[lsc.public]` also produce `@[lsc.external]` view exports at elaboration time (§3.5). Only these exports appear in the deployed ABI.

```lean
@[lsc.external]
def increment (s : CounterState) : Except ArithError CounterState :=
  checked id do
  let n ← s.number +? 1
  return .ok { s with number := n }
```

The Lean `def` name **is** the ABI function name. The compiler computes the 4-byte selector via `keccak256(canonicalSignature)` from the name and inferred parameter types.

The compiler **generates** the Yul dispatcher entry and export wrapper (§14.2). Authors do not write separate export functions or ABI signature strings.

### §4.2 Mutators

Mutators read and modify state. The return shape depends on fallibility and whether the ABI returns a value:

| Return shape | Meaning |
|---|---|
| `S` | Infallible mutator — always succeeds |
| `Except E S` | Fallible mutator, no ABI return value |
| `Except E (S × V)` | Fallible mutator, ABI returns `V` |

**`require` — inline precondition checks:**

`require` is the LSC guard macro. It reads as a precondition, matches Vyper/Solidity
ergonomics, and does not collide with any Lean 4 builtin:

```lean
require (condition) .ErrorVariant
-- desugars to:
if ¬condition then return .error .ErrorVariant
```

`assert!` (Lean 4 builtin) is a runtime panic and cannot be used in contract
functions. `require` is the LSC equivalent.

```lean
-- Fallible mutator, no return value (increment can overflow)
@[lsc.external]
def increment (s : CounterState) : Except ArithError CounterState :=
  checked id do
  let n ← s.number +? 1
  return .ok { s with number := n }

-- Fallible mutator with return value (transfer returns bool)
@[lsc.external]
def transfer (caller : Caller) (s : TokenState)
    (to : Address) (amount : UInt256) : Except TokenError (TokenState × Bool) :=
  checked .arith do
  require (s.balances.get caller.val ≥ amount) .insufficientBalance
  let newCaller ← s.balances.get caller.val -? amount
  let newTo     ← s.balances.get to +? amount
  let s' := { s with balances := s.balances.set caller.val newCaller |>.set to newTo }
  Lsc.Event.log (TransferEvent.mk caller.val to amount)
  return .ok (s', true)

-- Infallible mutator (sets a flag, no arithmetic, cannot fail)
@[lsc.external]
def activate (s : FlagState) : FlagState :=
  { s with active := true }
```

```lean
@[lsc.external]
def deposit (caller : Caller) (s : VaultState) (amount : UInt256)
    : Except VaultError VaultState := checked .arith do
  require (amount > 0) .insufficientBalance
  let newBalance ← s.balances.get caller.val +? amount
  return .ok { s with balances := s.balances.set caller.val newBalance }
```

### §4.3 Views

Views read state without modifying it:

```lean
-- Infallible view from @[lsc.public] on CounterState.number (§3.5); compiler-generated:
-- def number (s : CounterState) : UInt256 := s.number

-- Fallible view (rare): author-written
@[lsc.external]
def price (s : AMMState) : Except AMMError UInt256 := do
  require (s.reserve1 > 0) .uninitializedPool
  let p ← s.reserve0 /? s.reserve1 |>.orWrapDiv .arith
  return .ok p
```

The emitter generates a read-only wrapper for all view forms; no `sstore` is emitted.

### §4.4 ABI inference rules

The compiler infers the full ABI from the `@[lsc.external]` function signature.

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

Each `@[lsc.error]` variant becomes one Solidity `error` entry in the ABI JSON.

### §4.5 Parameter filtering

The compiler excludes certain parameters from ABI calldata automatically:

| Parameter kind | ABI | Rule |
|---------------|-----|------|
| `s : SomeState` (contract State struct) | excluded | Loaded by compiler from storage |
| `caller : Caller` | excluded | Bound to `msg.sender` by wrapper |
| `UInt256`, `Address`, `Bool`, `Bytes32`, `Bytes[N]` (no annotation) | included | In declaration order |

Parameters are included in the ABI in the order they appear after the excluded ones are removed.

### §4.6 State threading

State is threaded **explicitly** through every function. Stateful monads are disallowed (§2.6); `do` over `Except E` is allowed.

```lean
-- Correct: explicit state threading with do-notation over Except
@[lsc.external]
def increment (s : CounterState) : Except ArithError CounterState :=
  checked id do
  let n ← s.number +? 1
  return .ok { s with number := n }

-- Infallible: no do needed
@[lsc.external]
def activate (s : FlagState) : FlagState :=
  { s with active := true }

-- Rejected: monadic state
def increment : StateM CounterState Unit := ...  -- lsc: stateful monads are not allowed
```

All proofs are written against the same `@[lsc.external]` signatures that get deployed.

> **Why allow `do`-notation but ban `StateM`?**
> `do` over `Except E` only threads the error channel — `s` stays an explicit parameter, `s'` stays an explicit return value. Theorems quantify over both as before: `(h : f s = .ok s')`. `StateM` hides `s` inside the monad, making it impossible to state theorems of that form. The ban is on implicit state, not on `do`-notation itself.

> **Why infer the ABI instead of requiring an explicit signature string?**
> Explicit ABI strings duplicate information already in the type. They drift, have typos, and create a second proof surface. Inferring from types keeps the contract module as the single source of truth — including error types, which map to Solidity `error` declarations automatically.

---

## §5 Caller Identity

### §5.1 The `Caller` type

When a function needs to know who called it, the caller's address is passed as a
`Caller` parameter:

```lean
-- Lsc.Prelude
structure Caller where
  val : Address
  deriving DecidableEq, Repr
```

Any parameter of type `Caller` is **excluded from ABI calldata** and bound to
`msg.sender` by the emitter. No annotation is required — the type itself is the
signal.

```lean
@[lsc.external]
def transfer (caller : Caller) (s : ERC20State)
    (to : Address) (amount : UInt256)
    : Except TokenError (ERC20State × Bool) := do
  require (s.balances.get caller.val ≥ amount) .insufficientBalance
  ...
```

### §5.2 Validator rules

- **At most one `Caller` parameter per function** — validator error if more than one.
- **`Caller` may appear in any position** — the validator identifies it by type,
  not position.
- **`Address` as first non-state parameter with name `caller`, `sender`, `from`,
  or `owner`** — validator warning suggesting `Caller` type to avoid accidental
  ABI exposure.

```lean
-- Correct
def withdraw (caller : Caller) (s : VaultState) (amount : UInt256) : ...

-- Validator warning: Address named 'caller' without Caller type
def withdraw (caller : Address) (s : VaultState) (amount : UInt256) : ...
-- lsc: parameter 'caller : Address' looks like a caller address; use type Caller
--      to exclude from ABI and bind to msg.sender

-- Validator error: two Caller parameters
def foo (a : Caller) (b : Caller) (s : S) : ...
-- lsc: at most one Caller parameter per export
```

### §5.3 In proofs

Theorems quantify over `caller : Caller` directly:

```lean
theorem transfer_no_overdraft
    (caller : Caller) (to : Address) (amount : UInt256) (s : ERC20State)
    (h : transfer caller s to amount = .error .insufficientBalance) :
    ERC20Spec.transfer_no_overdraft caller to amount s h := by ...
```

No `EvmContext` appears in author-facing proofs. The caller is always a
first-class proof variable.

> **Why a newtype instead of `@[lsc.caller]` annotation?**
> A type-level distinction means the proof system tracks caller parameters
> without any attribute magic. `funext` and `simp` work uniformly.
> When `block.timestamp` or other context values are needed in future versions,
> they become separate newtypes (`BlockTimestamp`, `BlockNumber`) following the
> same pattern — each excluded from ABI by type, each a clean proof variable.
> No `EvmContext` struct is needed and no annotation proliferation occurs.

---

## §6 Events

### §6.1 Declaring events

Authors declare each on-chain event as a Lean struct with a `Lsc.Event.EvmEvent` instance:

```lean
structure TransferEvent where
  from to : Address
  value   : UInt256
  deriving Lsc.Event.EvmEvent
```

The `EvmEvent` instance (provided by `Lsc.Prelude` for standard events, or by the project) supplies:
- The canonical ABI signature string (e.g. `"Transfer(address,address,uint256)"`)
- Which fields are indexed (become `topic1`–`topic3`) vs non-indexed (ABI-encoded in `data`)

Alternatively, v1 accepts a string signature directly on each log call (§6.2) when no typed descriptor exists.

### §6.2 Emitting: `Lsc.Event.log`

Events are emitted inline in the function body with `Lsc.Event.log`. This is analogous to Solidity `emit Transfer(...)` or Vyper `log Transfer(...)`.

```lean
@[lsc.external]
def transfer (caller : Caller) (s : ERC20State)
    (to : Address) (amount : UInt256) : Except TokenError (ERC20State × Bool) :=
  checked .arith do
  require (s.balances.get caller.val ≥ amount) .insufficientBalance
  let newCaller ← s.balances.get caller.val -? amount
  let newTo     ← s.balances.get to +? amount
  let s' := { s with balances := s.balances.set caller.val newCaller |>.set to newTo }
  Lsc.Event.log (TransferEvent.mk caller.val to amount)
  return .ok (s', true)
```

**String signature form (v1 fallback):**
```lean
Lsc.Event.log "Transfer(address,address,uint256)" caller to amount
```

The validator checks argument count and types against the signature.

**Multiple events on one path:**
```lean
Lsc.Event.log (TransferEvent.mk caller to amount)
if fee > 0 then Lsc.Event.log (FeeEvent.mk caller fee)
.ok (s', true)
```

Each `Lsc.Event.log` on a path to `.ok _` is collected independently. No logs fire on paths that return `.error _`.

### §6.3 Proof erasure

`Lsc.Event.log` is **proof-erased**: it desugars to the identity in the Lean kernel. The expression:

```lean
Lsc.Event.log (TransferEvent.mk caller to amount)
.ok (s', true)
```

is definitionally equal to:

```lean
.ok (s', true)
```

As a result, `simp [transfer]` in a proof unfolds `transfer` as if `Lsc.Event.log` were absent. Spec theorems quantify only over `Except` returns; `transfer … = .ok (s', _)` has the same meaning whether or not the body contains log calls.

Log correctness (correct `topic0`, correct indexed/non-indexed encoding, correct emit ordering) is a compiler obligation tested via `deployCode` + log assertions in Foundry `.t.sol` tests (§14.3).

### §6.4 Compiler lowering

The emitter represents each log entry internally as:

```lean
-- Compiler-internal; not available in src/*.lean
structure LogEntry where
  topic0  : Bytes32
  topics  : List Bytes32   -- indexed args; max 3 (validator-enforced)
  data    : Bytes          -- non-indexed ABI-encoded payload
```

Emit ordering: **load → call author function → on `some _` → store → LOG(s) in source order → ABI return.**

Logs never fire on `none` paths (revert before store).

### §6.5 Optional `@[lsc.event]` lint

`@[lsc.event "canonicalSignature"]` on a function is optional lint — it declares which events may fire from that export. It does not supply payload data and does not replace `Lsc.Event.log`. The validator warns if a function annotated with `@[lsc.event]` never calls `Lsc.Event.log` for that signature, or vice versa.

> **Why not return `List LogEntry` from the function?**
> Returning log lists pollutes the proof surface. Every theorem would need to destruct a log list it doesn't care about. Proof erasure keeps theorems clean while the compiler handles log assembly. Log *correctness* belongs in Foundry tests, not Lean proofs.

> **Why not auto-emit from function arguments or names?**
> Auto-emission requires the compiler to guess which arguments map to which event fields. Explicit `Lsc.Event.log` at the call site is unambiguous, matches Solidity/Vyper's ergonomics, and makes multi-event paths straightforward.

---

## §7 Revert

### §7.1 `.error e` = EVM REVERT

Fallible `@[lsc.external]` functions return `Except E A`. `.error e` models EVM revert with a typed custom error; `.ok val` models success.

```lean
@[lsc.external]
def transfer (caller : Caller) (s : TokenState)
    (to : Address) (amount : UInt256) : Except TokenError (TokenState × Bool) :=
  checked .arith do
  require (s.balances.get caller.val ≥ amount) .insufficientBalance
  let newCaller ← s.balances.get caller.val -? amount
  let newTo     ← s.balances.get to +? amount
  Lsc.Event.log (TransferEvent.mk caller.val to amount)
  return .ok ({ s with balances := s.balances.set caller.val newCaller |>.set to newTo }, true)
```

Infallible functions (`S` or `V` return shapes) never revert.

### §7.2 Lean to EVM mapping

| Lean return | EVM behavior |
|-------------|-------------|
| `.error e` | `REVERT` with `abi.encode(e)` — no storage commit, no events |
| `.ok s'` (infallible mutator `S`) | persist `s'`; no ABI returndata |
| `.ok (s', v)` (fallible `Except E (S × V)`) | persist `s'`, emit events, ABI-encode `v` |
| `val` (infallible view `V`) | read-only; ABI-encode `val`; no store |
| `.ok v` (fallible view `Except E V`) | read-only; ABI-encode `v`; no store |

### §7.3 Error specs

Error specs use `(h : f ... = .error .Variant)` as the hypothesis:

```lean
/-- transfer reverts with insufficientBalance when caller has too little. -/
def transfer_no_overdraft
    (caller : Caller) (to : Address) (amount : UInt256) (s : TokenState)
    (h : transfer caller s to amount = .error .insufficientBalance) : Prop :=
  s.balances.get caller.val < amount

/-- transfer reverts with arithmetic error when checked ops fail. -/
def transfer_arith_overflow
    (caller : Caller) (to : Address) (amount : UInt256) (s : TokenState)
    (h : transfer caller s to amount = .error (.arith .overflow)) : Prop :=
  s.balances.get caller.val ≥ amount /\
  s.balances.get to + amount ≥ 2^256
```

Specs can now distinguish *which* error fired. The matching theorem proves each condition with `simp [transfer] + omega`.

> **Why `Except` with typed errors instead of `Option`?**
> `Option` cannot express which error fired. `Except E A` lets specs prove exact error conditions — essential for user-facing contracts. Core `Except` discriminators, `require` desugaring, and bridge lemmas in §11.1 keep proof bodies short.

> **Why not partial functions?**
> Lean requires totality for kernel checking. Partial functions break `simp` and LLM proof generation.
---

## §8 External Calls

> **v1 status:** `World`, `invoke`, and `Lsc.extern.*` are specified here for completeness and to support the composition demo ([Appendix B](lsc-appendices.md#appendix-b--composition-pattern)), but are **not** part of the v1 Counter smoke tests. Full emitter support lands in v2b. See [Appendix C](lsc-appendices.md#appendix-c--versioning-roadmap) for the versioning roadmap.

### §8.1 World and accounts

Single-contract `State → Except E S` is insufficient when bytecode calls other contracts. Multi-contract storage lives in `World` in `Lsc.Semantics`:

```lean
inductive TypedAccount where
  | counter (s : CounterState)
  | custom (tag : String) (payload : Bytes)

structure Account where
  typed   : Option TypedAccount
  raw     : Mapping UInt256 UInt256
  balance : UInt256

structure World where
  accounts : Mapping Address Account
```

Author contract functions remain `State → Except E S` (or infallible `S`) — they never take `World`. `World` threading happens only in compiler-generated export bodies.

### §8.2 `invoke` semantics

```lean
inductive CallKind where | call | staticcall | delegatecall

def invoke (w : World) (self : Address) (selector : UInt32) (args : Bytes)
    : StepResult
```

`invoke` loads `self` from `w`, runs the matching `@[lsc.external]` function on that contract's model, and returns `StepResult.done` or `StepResult.reverted`. Reentrancy is handled by threading the current `World` at each extern site.

### §8.3 `Lsc.extern.call` / `staticcall`

External calls use typed, validator-checked primitives. They appear only in **compiler-generated export bodies**, not in author contract functions.

```lean
-- Read-only (staticcall): callee must not modify storage
Lsc.extern.staticcall IERC20.balanceOf tokenAddr ctx w who : UInt256

-- Mutating (call): may update World and reenter; returns new world
Lsc.extern.call IERC20.transferFrom tokenAddr ctx w from to amount
  : Except ExternError (World × Bool)
```

Interface typeclasses (`IERC20`, etc.) live in `Lsc.Interfaces` or project `interfaces/*.lean`.

### §8.4 Registered vs assumed callees

| Callee kind | Resolution | Proof strength |
|-------------|-----------|----------------|
| **Registered** | Same repo `src/*.lean` + `[lsc.contracts]` address table | Compose callee spec theorems via `simulate_call` (§11.5) |
| **Assumed** | `@[extern_assume "IERC20"]` + axioms in `spec/` | Trust interface axioms (human-reviewed) |

### §8.5 Reentrancy

`@[lsc.no_reentrant]` on an export is a validator-checked annotation: no `Lsc.extern.call` (mutating) may appear in the dynamic call graph of this export while a frame for `self` is on the stack. Proofs may use `lift_no_reentrant` (§11.6) to reduce to `State → Except E S` without trace quantification.

### §8.6 Unsafe escape hatch (v3)

```lean
Lsc.unsafe.call (addr : Address) (value : UInt256) (calldata : Bytes)
  : Except ExternError (World × Bytes)
```

No spec support in default templates. Requires `@[lsc.allow_unsafe_calls]` on the contract module. Foundry fuzz tests only.

> **Why not `ContractM World α` in author code?**
> Monadic state in author code hides the revert/reentrancy order that proofs need to reason about. Explicit `Lsc.extern.*` at export boundaries keeps the call graph visible to the validator and the proof helpers. Authors write closed-world pure functions; the compiler composes them with `World`.

---

## PART II — THE PROOF SYSTEM

---

## §9 Spec Files

### §9.1 Format

`spec/<Contract>Spec.lean` contains **only** `def` declarations with return type `Prop`. This is the contract's requirements document — written and reviewed by humans.

```lean
import Counter

inductive CounterAction where
  | increment

/-- Single-step model for sequence proofs (`Lsc.Invariant`). -/
def applyAction (s : CounterState) : CounterAction → CounterState
  | .increment =>
      match increment s with
      | .ok s'    => s'
      | .error _ => s

def applyActions (s : CounterState) (actions : List CounterAction) : CounterState :=
  actions.foldl applyAction s

/-- increment increases the stored number by exactly 1. -/
def increment_increases_number
    (s s' : CounterState)
    (h : increment s = .ok s') : Prop :=
  s'.number = s.number + 1

/-- Global invariant: no sequence of user actions can decrease the number. -/
def number_never_decreases
    (s : CounterState) (actions : List CounterAction) : Prop :=
  (applyActions s actions).number ≥ s.number
```

The RHS is the proposition body — what must hold given the hypothesis. Single-call specs use `(h : f … s = .ok s')` or `(h : f … = .ok (s', ret))` for success and `(h : f … = .error e)` for revert.

**Sequence specs** (like `number_never_decreases`) define three pieces in the spec file:

1. `inductive Action` — one variant per exported mutator (with the parameters the spec needs).
2. `def applyAction (s : S) : Action → S` — run one export; on `.error`, return `s` unchanged.
3. `def applyActions := actions.foldl applyAction` — fold into a list (or an equivalent recursive `def`).

Proofs of sequence invariants use `Lsc.Invariant applyAction P` (§9.1) so authors prove one case per action instead of hand-written list induction. `Nat` and `List` are allowed in spec files; they are banned only in contract code (§2.6). Specs use plain `Fin` `+` on `UInt256` — the same semantics as contract code (§2.1).

#### Sequence invariants and `Lsc.Invariant`

For properties that must hold across any sequence of actions (e.g. AMM constant
product, token supply conservation), LSC provides a canonical combinator in
`Lsc.Prelude`:

```lean
-- Lsc.Prelude
/-- `Lsc.Invariant step P` states that predicate `P` is preserved by every
    single step, and therefore holds after any sequence of steps.
    Use for global contract invariants. -/
theorem Lsc.Invariant
    {S A : Type}
    (step  : S → A → S)
    (P     : S → Prop)
    (hstep : ∀ (s : S) (a : A), P s → P (step s a))
    (s     : S)
    (actions : List A)
    (h0    : P s)
    : P (List.foldl step s actions) := by
  induction actions generalizing s with
  | nil  => exact h0
  | cons a rest ih =>
      simp [List.foldl]
      exact ih (step s a) (hstep s a h0)
```

**AMM example — constant product invariant:**

```lean
-- spec/AMMSpec.lean

inductive AMMAction where
  | swap (amountIn : UInt256)
  | addLiquidity (caller : Caller) (amount0 amount1 : UInt256)

def applyAction (s : AMMState) : AMMAction → AMMState
  | .swap amountIn =>
      match swap s amountIn with
      | .ok (s', _) => s'
      | .error _   => s
  | .addLiquidity caller a0 a1 =>
      match addLiquidity caller s a0 a1 with
      | .ok (s', _) => s'
      | .error _    => s

def applyAMMActions (s : AMMState) (actions : List AMMAction) : AMMState :=
  actions.foldl applyAction s

/-- The constant product k = reserve0 * reserve1 never decreases (after any sequence). -/
def constant_product_nondecreasing
    (s : AMMState) (actions : List AMMAction)
    (h0 : s.reserve0 * s.reserve1 = s.k) : Prop :=
  let s' := applyAMMActions s actions
  s'.reserve0 * s'.reserve1 ≥ s.k
```

**Proof sketch:**

```lean
-- test/AMMProof.lean

theorem constant_product_nondecreasing ... := by
  simp only [AMMSpec.constant_product_nondecreasing, AMMSpec.applyAMMActions]
  apply Lsc.Invariant AMMSpec.applyAction (fun s => s.reserve0 * s.reserve1 ≥ s.k)
  · intro s a hP
    cases a with
    | swap amountIn =>
        simp [AMMSpec.applyAction, swap] at hP ⊢; omega
    | addLiquidity caller a0 a1 =>
        simp [AMMSpec.applyAction, addLiquidity] at hP ⊢; omega
  · simpa using h0
```

`Lsc.Invariant` eliminates the need for authors to write induction boilerplate.
The proof obligation reduces to one case per action type.

**When to use `Lsc.Invariant` vs direct induction:**
- Use `Lsc.Invariant` when the property is a simple predicate on state that
  each action independently preserves.
- Use direct `induction` when the property relates the *initial* state to the
  *final* state in a way that depends on the full history (e.g. "total tokens
  transferred equals sum of individual transfers").

### §9.2 Naming convention

Spec `def` names follow `{function}_{property}` for single-call specs, and `{subject}_{invariant}` for sequence specs, e.g.:
- `increment_increases_number` (single-call)
- `transfer_no_overdraft` (single-call revert)
- `transfer_preserves_total_supply` (single-call)
- `number_never_decreases` (sequence invariant)

The proof file uses the **same name** for the proving `theorem`. The compliance manifest and proof runner key off these shared names (§12).

### §9.3 Checklist

Every mutating export should have at least:
1. One **success property** using `(h : f … s = .ok s')` or `(h : f … = .ok (s', _))` — what holds after the call
2. One **revert property** using `(h : f … = .error e)` — what inputs cause revert

Views typically need one success property.

Contracts with global invariants (properties that must hold across any sequence of calls) should additionally have at least one **sequence spec**: `Action`, `applyAction`, `applyActions` (fold), and a `def` over `applyActions` or `List.foldl applyAction`. See the Counter example in §1.2 and §9.1.

### §9.4 Validator rules for spec files

| Construct | Error |
|-----------|-------|
| `theorem` or `lemma` | `lsc: spec modules use def … : Prop, not theorem; put proofs in *Proof.lean` |
| `sorry` | `lsc: sorry is not allowed in spec modules` |
| `by` tactic proof | `lsc: spec modules must not contain proof terms` |
| `def` not returning `Prop` | `lsc: spec definition "f" must return Prop` |

`axiom` is allowed in spec files for `@[extern_assume]` interface assumptions (§8.4). These are human-reviewed alongside the `def` propositions.

### §9.5 Accessibility

Since spec files contain only `Prop` definitions — no proof terms, no tactics — human review focuses entirely on *what* must hold, not *how* to prove it. The proof generation (§10.3) is fully automated; authors only need to write and review the `def` bodies.

`Lsc.SpecTemplates` provides skeletons for common patterns:

```lean
-- success_preserves_field skeleton
def transfer_preserves_totalSupply
    (caller to : Address) (amount : UInt256)
    (s s' : ERC20State) (ret : Bool)
    (h : transfer caller s to amount = .ok (s', ret)) : Prop :=
  s'.totalSupply = s.totalSupply
```

> **Why `def … : Prop` instead of `theorem … := by sorry`?**
> `theorem … := by sorry` mixes requirements with proof obligations. A reviewer can't tell whether a `sorry` is a placeholder spec or an unfinished proof. `def … : Prop` is unambiguous — it's a declaration, not a proof attempt. The separate proof file (§10) holds all proof terms. This separation is the core design of LSC's review model.

---

## §10 Proof Files

### §10.1 Format

`test/<Contract>Proof.lean` contains `theorem` proofs of each spec `Prop`. No `sorry` is allowed.

```lean
import CounterSpec

-- Single-call theorem: same arguments as the spec def, conclusion is that def applied to them.
theorem increment_increases_number
    (s s' : CounterState)
    (h : increment s = .ok s') :
    CounterSpec.increment_increases_number s s' h := by
  simp [CounterSpec.increment_increases_number, increment] at h
  exact h

-- Sequence theorem: `Lsc.Invariant` on `applyAction` (§9.1).
theorem number_never_decreases
    (s : CounterState) (actions : List CounterAction) :
    CounterSpec.number_never_decreases s actions := by
  simp only [CounterSpec.number_never_decreases, CounterSpec.applyActions]
  apply Lsc.Invariant CounterSpec.applyAction (fun s' => s'.number ≥ s.number)
  · intro s' a hP; cases a <;> simp [CounterSpec.applyAction, increment] at hP ⊢ <;> omega
  · simp

theorem increment_overflows_iff
    (s : CounterState)
    (h : increment s = .error .overflow) :
    CounterSpec.increment_overflows_iff s h := by
  simp [CounterSpec.increment_overflows_iff, increment] at h
  simp [UInt256.addChecked_none_of_ge (by omega), Option.orWrap_none] at h; omega
```

Each `theorem`:
- Has the **same name** as the spec `def`
- Takes the **same arguments** as the spec `def`
- Concludes that the spec `def` applied to those arguments holds (`CounterSpec.<name> …`)

Sequence theorems typically use `Lsc.Invariant` on the spec's `applyAction`. Direct `induction` over the action list remains valid when the property is not a simple per-step predicate (§9.1).

### §10.2 Conclusion shape rule

The Lean kernel enforces this automatically — the conclusion `CounterSpec.increment_increases_number s s' ret h` is the spec `def` applied to the arguments, which unfolds to `s'.number = s.number + 1`. A theorem that proves `True` instead cannot satisfy this conclusion type.

The compliance manifest runner (§12) additionally verifies that each listed theorem's conclusion **is** the corresponding spec `def` applied to matching arguments — not just that a theorem with the right name exists.

### §10.3 Proof authorship

Proofs are generated externally (typically by an LLM) and checked by the Lean kernel. **The kernel is the arbiter — a proof file that compiles without `sorry` is correct by definition.** Authors do not need to read or understand proof bodies.

The workflow:
1. Author completes `spec/CounterSpec.lean` with `def … : Prop := …`
2. Proof file `test/CounterProof.lean` is generated with matching `theorem` declarations
3. Proof runner checks each theorem — PASS if it compiles, FAIL if `sorry` or type error

There is no `lsc prove` command in v1.

### §10.4 Enforcement rules

| Condition | Result |
|-----------|--------|
| `sorry` in proof file | FAIL |
| `theorem` or `sorry` in spec file | FAIL |
| Lean type error in proof | FAIL |
| Spec `def` present but no matching proof `theorem` | FAIL |
| Proof `theorem` not naming any spec `def` | warning (allowed for helper lemmas) |
| `theorem` conclusion does not match spec `def` applied to arguments | FAIL |

> **Why separate spec and proof files instead of one file?**
> Human review focuses on spec files (pure `Prop` declarations). Proof files never need human review — the kernel checks them. Mixing proof terms into spec files would force reviewers to read and understand tactic proofs, which defeats the accessibility goal.

---

## §11 Proof Helpers (`Lsc.ProofHelpers`)

### §11.1 Layer 1 — direct proofs (default)

The default proof layer. Theorems are stated and proved directly over `@[lsc.external]` functions using `simp`, `omega`, and `Mapping` lemmas. No `World`, no export wrappers, no lifting.

#### `Except` discriminators

```lean
-- Lean 4 core already provides Except.ok.injEq and Except.error.injEq.
-- LSC adds the ne directions which fire in error proofs:

@[simp] theorem Except.ok_ne_error {E A : Type} (a : A) (e : E) :
    (Except.ok a : Except E A) ≠ Except.error e := by simp

@[simp] theorem Except.error_ne_ok {E A : Type} (a : A) (e : E) :
    (Except.error e : Except E A) ≠ Except.ok a := by simp
```

#### Arithmetic in proofs

`+?` returns `Option`; `orWrap` / `orError` convert to `Except`. Both are
`@[simp]`-transparent. The proof recipe for a function body containing
`s.number +? 1 |>.orWrap .arith`:

```lean
-- Success branch (h : ... = .ok ...):
simp [UInt256.addChecked_some (by omega), Option.orWrap_some] at h

-- Failure branch (h : ... = .error (.arith .overflow)):
simp [UInt256.addChecked_none_of_ge (by omega), Option.orWrap_none] at h
```

In practice `simp [myFunction]` unfolds everything and `omega` closes the
arithmetic goals — the bridge lemmas fire automatically.

#### `bind_ok` — intermediate state extraction

Replaces the underspecified `compose` helper. Useful when reasoning about two
sequential fallible operations where the intermediate state is not yet named:

```lean
/-- If binding two fallible operations succeeds, extract the intermediate state. -/
@[simp] theorem Except.bind_ok {E A B : Type} {ma : Except E A} {f : A → Except E B}
    {b : B} (h : ma >>= f = .ok b) :
    ∃ a, ma = .ok a ∧ f a = .ok b := by
  cases ma with
  | error e => simp at h
  | ok a    => exact ⟨a, rfl, h⟩
```

This is the key lemma for multi-step proofs. Instead of `compose` (which required
knowing `s'` upfront), `bind_ok` destructures the intermediate state from the
success hypothesis.

#### Worked example: two-step transfer

```lean
-- Spec:
def transferFrom_decrements_allowance
    (spender owner to : Address) (amount : UInt256) (s s' : ERC20State) (ret : Bool)
    (h : transferFrom spender s owner to amount = .ok (s', ret)) : Prop :=
  s'.allowances.get owner |>.get spender = s.allowances.get owner |>.get spender - amount

-- Proof:
theorem transferFrom_decrements_allowance ... := by
  simp [ERC20Spec.transferFrom_decrements_allowance, transferFrom] at h ⊢
  -- transferFrom body: require check then two checkedSub calls
  -- simp unfolds require; remaining h is about the arithmetic path
  obtain ⟨bal, hbal, hrest⟩ := Except.bind_ok h     -- extract after first ←
  obtain ⟨alw, halw, hfinal⟩ := Except.bind_ok hrest -- extract after second ←
  simp [Mapping.get_set_same, Mapping.get_set_other,
        UInt256.subChecked_some (by omega)] at *
  omega
```

#### Worked example: revert condition with `split_ifs`

When the function body has conditional branches, `simp` alone may not reduce
to a single goal. Use `split_ifs` to case-split, then close each branch:

```lean
-- Spec:
def transfer_no_overdraft
    (caller : Caller) (to : Address) (amount : UInt256) (s : ERC20State)
    (h : transfer caller s to amount = .error .insufficientBalance) : Prop :=
  s.balances.get caller.val < amount

-- Proof:
theorem transfer_no_overdraft
    (caller : Caller) (to : Address) (amount : UInt256) (s : ERC20State)
    (h : transfer caller s to amount = .error .insufficientBalance) :
    ERC20Spec.transfer_no_overdraft caller to amount s h := by
  simp [ERC20Spec.transfer_no_overdraft, transfer] at h
  -- After simp [transfer], h contains the unfolded body.
  -- require desugars to an if; split_ifs names the two branches:
  split_ifs at h with hguard
  · -- hguard : ¬(s.balances.get caller.val ≥ amount)
    -- h      : Except.error .insufficientBalance = Except.error .insufficientBalance
    omega   -- hguard gives s.balances.get caller.val < amount directly
  · -- hguard : s.balances.get caller.val ≥ amount
    -- h      : the continuation returned .error .insufficientBalance
    -- This branch contradicts: continuation only errors on checked arithmetic
    simp [UInt256.subChecked_some (by omega)] at h
```

**Pattern:** `simp [f]` to unfold; `split_ifs` to name branches; `omega` or
`simp [UInt256.addChecked_some]` to close each case.

`Lsc.Invariant` (§9.1) reduces sequence proofs to per-step obligations. `applyActions_monotone` remains available for monotonicity specs that do not fit the invariant combinator.

### §11.2 Worked example: `transfer_no_overdraft`

See the full `split_ifs` proof pattern in §11.1. The spec and proof use `caller : Caller` and `.error .insufficientBalance` (not `Option`/`none`). After `simp [transfer] at h`, `split_ifs` names the `require` guard branch; `omega` closes the balance inequality.

### §11.3 `Mapping` simp lemmas in proofs

The four laws from §3.2 fire automatically via `simp`. A typical proof involving a mapping update:

```lean
-- After simp [transfer], h contains a goal about balances after set
-- get_set_same fires: (m.set k v).get k = v
-- get_set_other fires: (m.set k v).get k' = m.get k' when k ≠ k'
-- No manual rewriting needed; simp handles both cases
```

When the proof requires `k ≠ k'` (e.g. `transfer_no_creation` showing tokens aren't created from nowhere), `omega` closes the distinctness goal after `simp` has simplified the mapping expressions.

### §11.4 Layer 2 — export bridge helpers

Used when a spec must reason about compiler-generated export wrappers or ABI `Bool` returns. **Counter and default ERC-20 compliance theorems do not need these.** Used for Layer 2 goals (§4 proof layer table).

```lean
namespace Lsc

/-- Strip LogEntry list from compiler-generated export (event logs are proof-erased). -/
theorem lift_logs {S α E : Type} {f : S → Except E (S × α)}
    {g : S → Except E (S × α × List LogEntry)}
    (hg : ∀ s r, f s = some r → ∃ logs, g s = some (r, logs))
    (s : S) (r : S × α) (logs : List LogEntry)
    (h : g s = some (r, logs)) :
    f s = some r := by ...

/-- Export with no Lsc.extern.* sites equals internal fn then load/store. -/
theorem lift_no_extern {S Ret : Type}
    (internal : S → Except E (S × Ret))
    (exportFn : EvmContext → S → Except E (S × Ret × List LogEntry))
    (h : ∀ ctx s s' ret, internal s = some (s', ret) →
         ∃ logs, exportFn ctx s = some (s', ret, logs)) :
    ∀ ctx s s' ret, internal s = some (s', ret) →
    ∃ logs, exportFn ctx s = some (s', ret, logs) :=
  h

end Lsc
```

### §11.5 Layer 3 — cross-contract: `simulate_call`

> **TODO (v2b):** The full `simulate_call` signature threads `World` through the callee and composes callee spec theorems with caller spec theorems. The stub below shows the intended shape; the body is pending correct `World`-threading semantics in `Lsc.Semantics`.

```lean
namespace Lsc

/-- Registered callee: if extern.call simulates invoke on callee model,
    inherit callee spec theorems in the caller's proof.
    TODO v2b: complete World threading; hSim must propagate w' correctly. -/
theorem simulate_call {S CalleeState Ret : Type}
    (callerInternal : S → Except E (S × Ret))
    (calleeInternal : CalleeState → Except CalleeError CalleeState)
    (exportWithCall : EvmContext → World → S → Except E (World × Ret × List LogEntry))
    -- hSim: exportWithCall agrees with running callerInternal then calleeInternal
    -- on the relevant World projection; full signature TBD
    (hSim : True)  -- placeholder; v2b
    : True := trivial

end Lsc
```

### §11.6 Layer 4 — reentrancy: `lift_no_reentrant`

```lean
namespace Lsc

/-- @[lsc.no_reentrant]: when the validator certifies no self-call frames occur,
    the export reduces to the internal contract function. -/
theorem lift_no_reentrant {S Ret E : Type}
    (internal : S → Except E (S × Ret))
    (exportFn : EvmContext → World → S → Except E (S × Ret × List LogEntry))
    (hNoReentry : True)  -- replaced by validator certificate in v2c
    (h : ∀ ctx w s, exportFn ctx w s =
      match internal s with
      | .error e => .error e
      | .ok (s', ret) => .ok (s', ret, [])) :
    ∀ s s' ret, internal s = .ok (s', ret) →
    ∀ ctx w, exportFn ctx w s = .ok (s', ret, []) := by
  intro s s' ret hInt ctx w
  rw [h]; simp [hInt]

end Lsc
```

### §11.7 Tactics

**`export_cases`** — destructs an `Except E (Ret × List LogEntry)` for Layer 2 goals:
```lean
macro "export_cases" h:ident : tactic => `(tactic|
  (cases $(h) with
   | none => simp_all
   | some p =>
       obtain ⟨ret, logs⟩ := p
       simp_all))
```

**`erc_cases`** — destructs `Except E (S × Bool)`:
```lean
macro "erc_cases" h:ident : tactic => `(tactic|
  (cases $(h) with
   | none => simp_all
   | some p =>
       obtain ⟨s', b⟩ := p
       simp_all))
```

> **Why four layers instead of one uniform proof target?**
> The layers reflect increasing complexity: pure functions (Layer 1) are proved by `simp`; compiler-generated wrappers (Layer 2) add log lists; extern calls (Layer 3) add `World`; reentrancy (Layer 4) adds trace quantification. Most contracts never leave Layer 1. The layered structure means authors only pay the complexity cost they actually need.

---

## §12 Compliance Manifests

### §12.1 Opt-in theorem requirements

Projects may opt into named theorem requirements via `foundry.toml`:

```toml
[lsc.compliance.erc20]
spec = "spec/ERC20Spec.lean"
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

**The default proof runner does not impose ERC-20 or any application requirements.** Compliance is always opt-in.

### §12.2 Proof runner verification

When `[lsc.compliance.*]` is present, the proof runner checks for each listed name:

1. A `def <name> … : Prop` exists in the spec file
2. A `theorem <name>` exists in the corresponding `*Proof.lean`
3. The theorem's conclusion is **exactly** the spec `def` applied to the same arguments — not just a theorem of the same name

Check 3 is enforced by the Lean type system: `theorem transfer_no_overdraft … : ERC20Spec.transfer_no_overdraft … h` can only typecheck if the conclusion matches the spec `def`'s unfolded type. A theorem concluding `True` fails this check.

### §12.3 ERC-20 required theorems

The full required theorem list for `[lsc.compliance.erc20]` (enforced only when the manifest is set):

| Group | Theorem | Statement summary |
|-------|---------|------------------|
| Transfer | `transfer_preserves_total_supply` | `totalSupply` unchanged on success |
| Transfer | `transfer_no_overdraft` | insufficient balance → `none` |
| Transfer | `transfer_no_creation` | tokens conserved between distinct parties |
| Transfer | `transfer_self_noop` | `from = to` → state unchanged on success |
| Approve | `approve_sets_allowance` | allowance equals requested amount |
| Approve | `increaseAllowance_additive` | allowance increases by delta |
| Approve | `decreaseAllowance_subtractive` | allowance decreases by delta |
| Approve | `decreaseAllowance_saturates_at_zero` | decrease below zero → allowance 0 |
| TransferFrom | `transferFrom_respects_allowance` | insufficient allowance → `none` |
| TransferFrom | `transferFrom_decrements_allowance` | allowance reduced by transfer amount |
| TransferFrom | `transferFrom_respects_balance` | insufficient balance → `none` |
| Constructor | `constructor_mints_initial_supply` | deployer balance equals `initialSupply` |
| Constructor | `constructor_sets_metadata` | `name`, `symbol`, `decimals` stored correctly |

---

## PART III — TOOLCHAIN BOUNDARY

---

## §13 Validator

The LSC validator runs as a post-elaboration pass over contract modules (`src/*.lean`) and spec modules (`spec/*.lean`). All messages use prefix `lsc:` with file, line, and column.

### §13.1 Contract module errors

| Construct | Error message |
|-----------|--------------|
| `Nat`, `Int`, `Float` | `lsc: type Nat is not allowed; use UInt256` |
| `String`, `Char` | `lsc: String is not allowed; use Bytes[N]` |
| Closures / lambda capturing outer variable | `lsc: closures are not supported; use a top-level function` |
| Partial application | `lsc: partial application is not supported` |
| `IO`, `StateM`, `ST`, stateful monads | `lsc: stateful monads are not allowed; do-notation over Except E is permitted` |
| Higher-order functions | `lsc: functions cannot be passed as arguments` |
| Unbounded recursion | `lsc: recursive function X must be structurally terminating` |
| `List` or `Array` in author code | `lsc: List is not allowed in contract code; use Mapping or Lsc.Event.log for events` |
| `structure … extends` | `lsc: storage inheritance via extends is not supported in v1; define a flat State struct` |
| `LogEntry` constructed in author code | `lsc: LogEntry is compiler-internal; use Lsc.Event.log` |
| Hand-written export wrapper | `lsc: export wrappers are compiler-generated; use @[lsc.external] on contract functions` |
| `EvmContext` in author contract code | `lsc: use Caller for msg.sender; EvmContext is compiler-generated only` |
| Error type `E` in `Except E …` without `@[lsc.error]` | `lsc: error type E must be declared with @[lsc.error]` |
| `@[lsc.error]` on non-inductive | `lsc: @[lsc.error] may only be applied to inductive types` |
| `lsc_errors` keyword | `lsc: lsc_errors is not supported; use @[lsc.error] inductive` |
| Multiple `@[lsc.error]` in one module | `lsc: multiple @[lsc.error] types in one contract; one per module is recommended` |
| Bare `Option State` on mutator | `lsc: use Except E S or Except E (S × V) for mutators` |
| Invalid `@[lsc.external]` return shape | `lsc: @[lsc.external] "f" must return Except E S, Except E (S × V), S (infallible mutator), or V (infallible view)` |
| Unresolved polymorphism | `lsc: polymorphic function X cannot be compiled` |
| `Bytes[N]` literal longer than `N` | `lsc: Bytes literal exceeds declared bound N` |
| More than one `@[lsc.initialize]` | `lsc: at most one @[lsc.initialize] per contract module` |
| Author `sload` / `sstore` / slot indices | `lsc: storage IO is only performed by the emitter at @[lsc.external] boundaries` |
| `World` in contract functions | `lsc: World is not allowed in contract functions; extern calls are compiler-generated` |
| `Lsc.extern.*` in contract functions | `lsc: external calls are only allowed in compiler-generated exports` |
| Malformed event signature | `lsc: invalid event signature "..."; expected form "Name(type,type)"` |
| Event arg count / type mismatch | `lsc: event "Transfer(...)" expects N arguments of types ...; got ...` |
| Multiple `Caller` parameters on one export | `lsc: at most one Caller parameter per export` |
| `Address` named caller/sender/from/owner without `Caller` type | `lsc: parameter looks like a caller address; use type Caller` |
| `assert` in contract function | `lsc: use require for contract guards; assert! is a runtime panic` |
| `@[lsc.public]` not on State struct field | `lsc: @[lsc.public] may only annotate State struct fields` |
| `@[lsc.public]` on unsupported field type | `lsc: @[lsc.public] field has unsupported type` |
| `@[lsc.public]` field name collides with `@[lsc.external]` def | `lsc: field "X" is @[lsc.public] but @[lsc.external] def X already exists` |
| `+?` / `checked` in spec or proof modules | `lsc: checked arithmetic is contract-only; spec uses Fin +` |
| `do` block on infallible function (return type `S` or `V`) | `lsc: do-notation requires Except return type` |
| `Option (S × Ret)` as mutator return | `lsc: use Except E S or Except E (S × V) for mutators` |
| `require` with non-Bool condition | `lsc: require condition must be a Bool or decidable Prop` |

### §13.2 Spec module errors

| Construct | Error message |
|-----------|--------------|
| `theorem` or `lemma` | `lsc: spec modules use def … : Prop, not theorem; put proofs in *Proof.lean` |
| `sorry` | `lsc: sorry is not allowed in spec modules` |
| `by` tactic proof | `lsc: spec modules must not contain proof terms` |
| `def` not returning `Prop` | `lsc: spec definition "f" must return Prop` |
| Missing proof for listed spec `def` (compliance check) | `lsc: spec defines "f" but no matching theorem found in *Proof.lean` |

---

## §14 Compiler-Generated Code

### §14.1 What the emitter produces

Authors write pure functions. At each `@[lsc.external]` boundary (including views synthesized from `@[lsc.public]` fields per §3.5), the emitter generates:

1. **ABI dispatcher** — computes 4-byte selector from `keccak256(canonicalSignature)`; dispatches in Yul
2. **Calldata decode** — ABI-decodes included parameters (§4.5) from calldata
3. **`EvmContext` construction** — binds `ctx.sender := msg.sender`, `ctx.value := msg.value`, etc.
4. **`Caller` binding** — `caller.val := ctx.sender` for each `Caller` parameter
5. **State load** — `sload` all struct fields; decode dynamic `Bytes[N]` tails
6. **Author function call** — invokes the `@[lsc.external]` function with loaded state and decoded args
7. **On `.error e`** — `revert(abi.encode(e))`; no storage writes; no events
8. **On `.ok val`** — `sstore` all fields; collect and emit `Lsc.Event.log` sites in source order via `LOG` opcodes; ABI-encode non-state component of `val` as returndata

View exports (§4.3) omit steps 5-store and 8-store; the emitter may lazy-load only accessed fields if the observable result matches whole-state read.

### §14.2 Auto load/store invariant

The emitter's whole-state load → apply → store semantics are the normative model. Any emitter optimization (diff stores, lazy view loads) must produce observable behavior identical to:

```
load all fields → call author function → store all fields (on `.ok`)
```

This invariant is the bridge between Lean proofs (which reason about pure functions on `State` snapshots) and EVM bytecode (which reads and writes individual slots).

### §14.3 Trust boundary (v1)

v1 ships a tested but **not formally proven** Lean IR → Yul emitter. Dual runtime assurance:

- **Foundry fuzz tests** — `deployCode` + property assertions and log checks in `.t.sol` files
- **Bytecode fuzz** — randomized calldata, check storage and return value consistency

The following are **trusted in v1** (not formally proven):
- Lean IR → Yul emitter correctness
- ABI encoding/decoding fidelity
- `LOG` opcode encoding from `Lsc.Event.log` sites
- `keccak256` selector computation
- `Mapping` slot layout match between Lean model and Yul output

Phase 2 may prove emitter correctness; scope is undefined until v1 lessons are learned.

### §14.4 Gas (non-goal in v1)

Gas estimation, optimization, and EIP-150 gas forwarding rules for `CALL` are outside the v1 proof scope. Gas is fully delegated to the emitter and tested via Foundry. See §1.4 Non-goals.

---

## Appendices

Extended reference patterns, examples, and project history are in **[lsc-appendices.md](lsc-appendices.md)** (Appendices A–F).
