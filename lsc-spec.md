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

**What is restricted in author code:** monads, higher-order functions, closures, unbounded collections in state, `Nat`/`Int`/`String`, `structure … extends`, unbounded recursion, manual storage IO. See §13 for the full validator error table.

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

-- Error type: increment can overflow at UInt256 max
@[lsc.error]
inductive CounterError where
  | arith (e : ArithError)   -- wraps overflow / divisionByZero from Lsc.Prelude
  deriving DecidableEq

structure CounterState where
  number : UInt256

-- Fallible mutator: no return value beyond new state, but overflow is possible.
-- Result CounterState CounterError  (two-param: value type, error type)
@[lsc.external]
def increment (s : CounterState) : Result CounterState CounterError :=
  let n ← s.number.checkedAdd 1   -- ← propagates ArithError as CounterError.arith
  .ok { s with number := n }

-- Infallible view: just returns the value directly, no Result needed.
@[lsc.external]
def number (s : CounterState) : UInt256 :=
  s.number
```

`spec/CounterSpec.lean`:
```lean
import Counter

inductive CounterAction where
  | increment

-- Apply a sequence of actions, skipping any that error.
-- List and Nat are allowed in spec files (banned only in contract code).
def applyActions (s : CounterState) : List CounterAction → CounterState
  | [] => s
  | .increment :: rest =>
      match increment s with
      | .ok s'  => applyActions s'  rest
      | .err _  => applyActions s   rest   -- overflow: state unchanged

/-- On success, increment increases number by exactly 1. -/
def increment_increases_number
    (s s' : CounterState)
    (h : increment s = .ok s') : Prop :=
  s'.number = s.number + 1

/-- increment errors iff number is at UInt256 max (overflow). -/
def increment_overflows_iff
    (s : CounterState)
    (h : increment s = .err (.arith .overflow)) : Prop :=
  s.number = UInt256.max

/-- No sequence of actions can decrease the number. -/
def number_never_decreases
    (s : CounterState) (actions : List CounterAction) : Prop :=
  (applyActions s actions).number ≥ s.number
```

`test/CounterProof.lean`:
```lean
import CounterSpec

theorem increment_increases_number
    (s s' : CounterState)
    (h : increment s = .ok s') :
    CounterSpec.increment_increases_number s s' h := by
  simp [CounterSpec.increment_increases_number, increment, UInt256.checkedAdd] at h
  split_ifs at h with hov
  · simp [Result.err] at h          -- overflow branch contradicts .ok hyp
  · simp [Result.ok] at h; omega    -- success: s'.number = s.number + 1

theorem increment_overflows_iff
    (s : CounterState)
    (h : increment s = .err (.arith .overflow)) :
    CounterSpec.increment_overflows_iff s h := by
  simp [CounterSpec.increment_overflows_iff, increment, UInt256.checkedAdd] at h
  split_ifs at h with hov
  · simp [UInt256.checkedAdd] at hov ⊢; omega
  · simp [Result.ok] at h           -- success branch contradicts .err hyp

theorem number_never_decreases
    (s : CounterState) (actions : List CounterAction) :
    CounterSpec.number_never_decreases s actions := by
  induction actions generalizing s with
  | nil => simp [CounterSpec.number_never_decreases, CounterSpec.applyActions]
  | cons a rest ih =>
      cases a with
      | increment =>
          simp [CounterSpec.applyActions, CounterSpec.number_never_decreases]
          by_cases hov : s.number = UInt256.max
          · -- overflow: state unchanged, ih applies with same s
            have herr : increment s = .err (.arith .overflow) := by
              simp [increment, UInt256.checkedAdd, hov]
            simp [CounterSpec.applyActions, herr]
            exact le_trans (le_refl _) (ih s)
          · -- success: s'.number = s.number + 1
            have hok : increment s = .ok { s with number := s.number + 1 } := by
              simp [increment, UInt256.checkedAdd]; omega
            simp [CounterSpec.applyActions, hok]
            have := ih { s with number := s.number + 1 }
            simp [CounterSpec.number_never_decreases] at this; omega
```

Three theorems matching three spec `def`s: the success property, the overflow condition, and the global monotonicity invariant. The invariant proof case-splits on overflow vs success — both paths are covered.

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
| `@[lsc.external] def increment (s : CounterState) : Result CounterState CounterError` | ABI dispatcher, `sload` all fields, call `increment`, on `.ok s'` → `sstore`, on `.err e` → `revert(abi.encode(e))` |
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

The validator permits exactly these primitive types in contract code. Any other type is a hard error (§13.1).

| LSC type | Lean definition | EVM/ABI type | Notes |
|----------|----------------|--------------|-------|
| `UInt256` | `Fin (2^256)` | `uint256` | Arithmetic wraps mod 2^256; `omega` and `simp` apply directly via `Fin` lemmas |
| `Address` | `structure Address where val : UInt256` | `address` | Distinct newtype; not coercible to `UInt256` without `.val` |
| `Bool` | Lean built-in | `bool` | ABI boundary and internal guards |
| `Bytes32` | `Fin (2^256)` newtype | `bytes32` | Raw 32-byte value |
| `Bytes` | Dynamic byte array | `bytes` / `string` | Metadata and string fields; max 256 bytes in v1 (§2.2) |

`UInt256 = Fin (2^256)` means all arithmetic is definitional modular arithmetic. No custom axioms are needed for overflow; `omega` handles linear arithmetic over `Fin` directly.

`Address` is defined in `Lsc.Prelude`:
```lean
structure Address where
  val : UInt256
  deriving DecidableEq, Repr
```

It is not coercible to `UInt256` without an explicit `.val` projection, preventing accidental arithmetic on addresses.

### §2.2 Bytes

`Bytes` uses Solidity-compatible dynamic storage layout:

- Slot `p` holds the length encoding: if `length ≤ 31`, data is left-aligned in the slot with `length * 2` in the LSB; if `length > 31`, slot holds `length * 2 + 1` and payload lives at `keccak256(p)`.
- **Maximum length in v1: 256 bytes.** Exceeding this is a validator error. Configurability is deferred to v2.

ABI mapping: `Bytes` ↔ `bytes` (or `string` when used for text metadata).

### §2.3 Mapping

`Mapping K V` is the primary keyed storage type. It corresponds to Solidity `mapping(K => V)` with `keccak256(abi.encode(key, slot))` layout.

Nested mappings (e.g. ERC-20 allowances) are `Mapping K (Mapping K' V)`.

The full API and `@[simp]` laws are in §3.2.

### §2.4 Result

`Result Val E` is the return type for all `@[lsc.external]` mutators that can fail.

```lean
-- Defined in Lsc.Prelude
inductive Result (Val E : Type) where
  | ok  : Val → Result Val E   -- success
  | err : E → Result Val E     -- revert with typed error
```

The four return shapes authors use:

| Shape | Meaning | Example |
|-------|---------|---------|
| `S` | Infallible mutator — always succeeds, no error possible | `def setFlag (s : S) : S` |
| `V` | Infallible view — read-only, always returns a value | `def number (s : S) : UInt256` |
| `Result S E` | Fallible mutator — new state or error, no extra return value | `def increment (s : S) : Result S E` |
| `Result (S × V) E` | Fallible mutator with return value | `def swap (s : S) ... : Result (S × UInt256) E` |

`S` must be the contract's `State` type for the emitter to treat it as a mutator. `V` is any primitive or product of primitives. The validator distinguishes shapes by whether `Val` contains the `State` type.

- `.ok val` — success; emitter persists state (extracted from `val`), ABI-encodes the non-state component if present
- `.err e` — EVM revert; emitter ABI-encodes `e` as a Solidity custom error

**Infallible shapes (`S` and `V`):** The emitter wraps these in an unconditional success path. No revert is possible; no error type is needed.

**Views that can fail** (rare): return `Result V E` where `V` is not `State`. The emitter generates a `staticcall`-compatible read-only wrapper that can revert.

The full ABI inference rules are in §4.4.

### §2.5 Error types, `@[lsc.error]`, and arithmetic errors

**`@[lsc.error]` — declaring contract errors:**

```lean
@[lsc.error]
inductive TokenError where
  | insufficientBalance
  | insufficientAllowance
  | unauthorized
  | alreadyInitialized
  | arith (e : ArithError)   -- required if the contract uses checked arithmetic
  deriving DecidableEq
```

The attribute marks a standard Lean `inductive` as the contract's revert/error ABI. It does **not** expand or derive anything — authors write normal Lean and opt into proof helpers via `deriving …` or manual lemmas.

| Responsibility | Owner |
|---|---|
| Declare the inductive | Author (standard Lean) |
| `DecidableEq`, `Repr`, injectivity lemmas | Author via `deriving …` or manual lemmas |
| Register type for revert encoding + ABI `errors` | `@[lsc.error]` attribute |
| Map variants → Solidity `error` entries | Emitter (reads `@[lsc.error]` inductives) |
| Validate `←` / `assert` embedding into `E` | Validator |

**One error type per contract is recommended for most projects** — it keeps specs uniform and proof setup in one place. Use one error type per function only when two functions genuinely share an error name with different semantics (rare; see §9.2).

**`ArithError` — built-in arithmetic failures:**

```lean
-- Lsc.Prelude
inductive ArithError where
  | overflow
  | divisionByZero

-- Checked arithmetic operations — all return Result UInt256 ArithError
def UInt256.checkedAdd (a b : UInt256) : Result UInt256 ArithError
def UInt256.checkedSub (a b : UInt256) : Result UInt256 ArithError
def UInt256.checkedMul (a b : UInt256) : Result UInt256 ArithError
def UInt256.checkedDiv (a b : UInt256) : Result UInt256 ArithError
```

`ArithError` lives in `Lsc.Prelude` and is **not** marked `@[lsc.error]`. Contract error types embed it via `| arith (e : ArithError)` when checked arithmetic is used.

**Every `UInt256` arithmetic operation that can overflow or divide by zero uses checked forms.** Plain `+`, `-`, `*`, `/` on `UInt256` are **disallowed in contract code** — the validator requires `checkedAdd`, `checkedSub`, `checkedMul`, `checkedDiv` at all arithmetic sites. This ensures overflow is always explicitly handled or propagated.

**`←` — error propagation:**

```lean
let v ← expr
rest
```

Desugars to:

```lean
match expr with
| .err e => .err e   -- propagate; E must embed into the function's error type
| .ok v  => rest
```

This is **not a monad** — there is no typeclass, no `bind` instance, no `pure`. It is a syntactic macro rewrite only, allowed in `@[lsc.external]` function bodies. The validator checks that the `E` in `expr : Result _ E` is embeddable into the function's declared error type via a constructor (e.g. `| arith (e : ArithError)` for `ArithError` propagation). If no embedding exists, the validator emits an error at the `←` site.

**`assert` — inline precondition checks:**

```lean
assert (condition) .ErrorVariant
-- desugars to:
if ¬(condition) then return .err .ErrorVariant
```

**Example combining both — forwarding an overflow error:**

```lean
@[lsc.error]
inductive VaultError where
  | insufficientBalance
  | arith (e : ArithError)   -- forwards checkedAdd/checkedMul failures
  deriving DecidableEq

@[lsc.external]
def deposit
    (@[lsc.caller] caller : Address)
    (s : VaultState)
    (amount : UInt256) : Result VaultState VaultError :=
  assert (amount > 0) .insufficientBalance
  -- checkedAdd returns Result UInt256 ArithError;
  -- ← propagates it as VaultError.arith if overflow occurs
  let newBalance ← (s.balances.get caller).checkedAdd amount
  let newTotal   ← s.totalDeposits.checkedAdd amount
  .ok { s with
    balances      := s.balances.set caller newBalance
    totalDeposits := newTotal }
```

If `checkedAdd` overflows, the function immediately returns `.err (.arith .overflow)`. The Lean kernel checks that this is the only way `arith` errors can arise — the spec can then prove:

```lean
def deposit_arith_error_means_overflow
    (caller : Address) (s : VaultState) (amount : UInt256)
    (h : deposit caller s amount = .err (.arith .overflow)) : Prop :=
  s.balances.get caller + amount ≥ 2^256 ∨ s.totalDeposits + amount ≥ 2^256
```

### §2.6 Forbidden types

| Forbidden | Validator error | Use instead |
|-----------|----------------|-------------|
| `Nat`, `Int`, `Float` | `lsc: type Nat is not allowed; use UInt256` | `UInt256` |
| `String`, `Char` | `lsc: String is not allowed; use Bytes` | `Bytes` |
| `List`, `Array` in state | `lsc: List is not allowed in contract code` | `Mapping` |
| `IO`, `StateM`, any monad | `lsc: monadic code is not allowed in contracts` | Explicit state passing |
| Higher-order functions | `lsc: functions cannot be passed as arguments` | Top-level helpers |
| Recursive types / inductives with >2 constructors | `lsc: inductive type X is not allowed` | Struct + `Mapping` (except `@[lsc.error]` error enums) |
| `Option (S × Ret)` on mutator | `lsc: use Result S Ret E for mutators` | `Result S Ret E` |

> **Why not richer types?**
> Lean's proof automation (`simp`, `omega`, `decide`) works best on flat, finite structures. `Nat` requires `omega` extensions that interact poorly with `Fin`; `List` in state makes proof obligations unbounded; monads hide the state threading that theorems need to quantify over. Every restriction here trades expressiveness for a proof that `simp` can close in one step.

> **Why `Result` instead of keeping `Option`?**
> `Option` cannot express *which* error fired — `none` is a single undifferentiated failure. `Result S Ret E` lets specs prove "this specific error fires under these conditions", which is essential for user-facing contracts. Generic `Result` simp lemmas in `Lsc.ProofHelpers` and `assert` desugaring ensure proof bodies are no harder to write than with `Option`. See §11.1.

---

## §3 State

### §3.1 Defining a State struct

Contract storage is a plain Lean 4 struct. Each field is a primitive type or `Mapping`.

```lean
structure CounterState where
  number : UInt256   -- slot 0
```

```lean
structure ERC20State where
  name        : Bytes                                          -- slot 0
  symbol      : Bytes                                          -- slot 1
  decimals    : UInt256                                        -- slot 2
  totalSupply : UInt256                                        -- slot 3
  balances    : Mapping Address UInt256                 -- slot 4
  allowances  : Mapping Address (Mapping Address UInt256)  -- slot 5
```

Fields receive sequential storage slots in declaration order from slot 0. Mappings use `keccak256(abi.encode(key, slot))` per Solidity layout rules.

The **contract name** is the file stem (`Counter` from `src/Counter.lean`). No contract-name attribute exists; the validator requires PascalCase file stems.

### §3.2 Mapping laws

`Mapping` is defined in `Lsc.Prelude` with the following `@[simp]` lemmas. These are **definitional equalities** — not axioms — so `simp` can unfold them without any additional hypotheses:

```lean
-- The four core laws, all @[simp]:

@[simp] theorem Mapping.get_set_same
    {K V : Type} [DecidableEq K] (m : Mapping K V) (k : K) (v : V) :
    (m.set k v).get k = v := by ...

@[simp] theorem Mapping.get_set_other
    {K V : Type} [DecidableEq K] (m : Mapping K V) (k k' : K) (v : V)
    (h : k ≠ k') :
    (m.set k v).get k' = m.get k' := by ...

@[simp] theorem Mapping.get_empty
    {K V : Type} [DecidableEq K] [Inhabited V] (k : K) :
    (Mapping.empty : Mapping K V).get k = default := by ...

@[simp] theorem Mapping.set_set_same
    {K V : Type} [DecidableEq K] (m : Mapping K V) (k : K) (v v' : V) :
    (m.set k v).set k v' = m.set k v' := by ...
```

The one **axiom** (not definitional) is key injectivity for storage slot collision proofs:

```lean
axiom Mapping.key_injective {K V : Type} [DecidableEq K]
    (m : Mapping K V) (a b : K) (s : UInt256) :
    storageKey a s = storageKey b s → a = b
```

This is the sole storage axiom in `Lsc.Prelude`. Struct field slot disjointness (distinct fields → distinct slots) is provable by `decide` from sequential slot assignment and requires no axiom.

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

---

## §4 Functions (Exports)

### §4.1 The `@[lsc.external]` annotation

Public ABI functions are declared by annotating contract functions with `@[lsc.external]` (parameterless). Only annotated functions appear in the deployed ABI.

```lean
@[lsc.external]
def increment (s : CounterState) : Result CounterState CounterError :=
  let n ← s.number.checkedAdd 1
  .ok { s with number := n }
```

The Lean `def` name **is** the ABI function name. The compiler computes the 4-byte selector via `keccak256(canonicalSignature)` from the name and inferred parameter types.

The compiler **generates** the Yul dispatcher entry and export wrapper (§14.2). Authors do not write separate export functions or ABI signature strings.

### §4.2 Mutators

Mutators read and modify state. The return shape depends on fallibility and whether the ABI returns a value:

| Return shape | Meaning |
|---|---|
| `S` | Infallible mutator — always succeeds |
| `Result S E` | Fallible mutator, no ABI return value |
| `Result (S × V) E` | Fallible mutator, ABI returns `V` |

```lean
-- Fallible mutator, no return value (increment can overflow)
@[lsc.external]
def increment (s : CounterState) : Result CounterState CounterError :=
  let n ← s.number.checkedAdd 1
  .ok { s with number := n }

-- Fallible mutator with return value (transfer returns bool)
@[lsc.external]
def transfer
    (@[lsc.caller] caller : Address) (s : TokenState)
    (to : Address) (amount : UInt256) : Result (TokenState × Bool) TokenError :=
  assert (s.balances.get caller ≥ amount) .insufficientBalance
  let newCaller ← (s.balances.get caller).checkedSub amount
  let newTo     ← (s.balances.get to).checkedAdd amount
  Lsc.Event.log (TransferEvent.mk caller to amount)
  .ok ({ s with balances := s.balances.set caller newCaller |>.set to newTo }, true)

-- Infallible mutator (sets a flag, no arithmetic, cannot fail)
@[lsc.external]
def activate (s : FlagState) : FlagState :=
  { s with active := true }
```

### §4.3 Views

Views read state without modifying it:

```lean
-- Infallible view: returns the value directly
@[lsc.external]
def number (s : CounterState) : UInt256 :=
  s.number

-- Fallible view (rare): can error
@[lsc.external]
def price (s : AMMState) : Result UInt256 AMMError :=
  assert (s.reserve1 > 0) .uninitializedPool
  let p ← s.reserve0.checkedDiv s.reserve1
  .ok p
```

The emitter generates a read-only wrapper for all view forms; no `sstore` is emitted.

### §4.4 ABI inference rules

The compiler infers the full ABI from the `@[lsc.external]` function signature.

| Author return shape | Mutability | ABI return | ABI errors |
|--------------------|-----------|------------|------------|
| `S` | nonpayable | none | none |
| `V` (not State) | view | ABI type of `V` | none |
| `Result S E` | nonpayable | none | `E` variants |
| `Result (S × Bool) E` | nonpayable | `bool` | `E` variants |
| `Result (S × UInt256) E` | nonpayable | `uint256` | `E` variants |
| `Result (S × Address) E` | nonpayable | `address` | `E` variants |
| `Result (S × Bytes32) E` | nonpayable | `bytes32` | `E` variants |
| `Result V E` (V not State) | view | ABI type of `V` | `E` variants |
| `Option _` on mutator | **validator error** | — | use `Result` |

Each `@[lsc.error]` variant becomes one Solidity `error` entry in the ABI JSON. `ArithError` variants (`overflow`, `divisionByZero`) are emitted as `error Overflow()` and `error DivisionByZero()` when wrapped via `| arith (e : ArithError)`.

### §4.5 Parameter filtering

The compiler excludes certain parameters from ABI calldata automatically:

| Parameter kind | ABI | Rule |
|---------------|-----|------|
| `s : SomeState` (contract State struct) | excluded | Loaded by compiler from storage |
| `@[lsc.caller] caller : Address` | excluded | Bound to `msg.sender` by wrapper |
| `UInt256`, `Address`, `Bool`, `Bytes32`, `Bytes` (no annotation) | included | In declaration order |

Parameters are included in the ABI in the order they appear after the excluded ones are removed.

### §4.6 State threading

State is threaded **explicitly** through every function. Monads are disallowed (§2.6).

```lean
-- Correct: explicit state threading with Result
@[lsc.external]
def increment (s : CounterState) : Result CounterState Unit CounterError :=
  .ok { s with number := s.number + 1 } ()

-- Rejected: monadic state
def increment : StateM CounterState Unit := ...  -- lsc: monadic code is not allowed
```

All proofs are written against the same `@[lsc.external]` signatures that get deployed.

> **Why infer the ABI instead of requiring an explicit signature string?**
> Explicit ABI strings duplicate information already in the type. They drift, have typos, and create a second proof surface. Inferring from types keeps the contract module as the single source of truth — including error types, which map to Solidity `error` declarations automatically.

> **Why `Result S Unit E` and not a bare `Result S E` for void mutators?**
> Uniform `Result S Ret E` means every mutator success uses one hypothesis form: `(h : f … s = .ok s' ret)`. Proofs ignore `ret` with `_` when only state matters. A separate bare form would fork the proof pattern and break `SpecTemplates` skeletons.

---

## §5 Caller Identity

### §5.1 The `@[lsc.caller]` annotation

When a function needs to know who called it (e.g. for authorization), the caller's address is passed as an explicit parameter annotated with `@[lsc.caller]`:

```lean
@[lsc.external]
def transfer
    (@[lsc.caller] caller : Address)
    (s : ERC20State)
    (to : Address)
    (amount : UInt256) : Result (ERC20State × Bool) TokenError := ...
```

The compiler binds this parameter to `msg.sender` in the generated export wrapper. It is excluded from ABI calldata (§4.5).

### §5.2 Validator rules

- **`@[lsc.caller]` must have type `Address`** — any other type is a validator error.
- **At most one `@[lsc.caller]` per function** — validator error if more than one.
- **If `Address` appears as the first non-state parameter without `@[lsc.caller]`, the validator emits an error** — this prevents silent bugs where a caller address accidentally becomes an ABI argument.
- **`@[lsc.caller]` may appear in any position** — it does not have to be first.

```lean
-- Correct
@[lsc.external]
def withdraw (@[lsc.caller] caller : Address) (s : VaultState) (amount : UInt256) : ...

-- Validator error: Address first parameter, no @[lsc.caller]
@[lsc.external]
def withdraw (caller : Address) (s : VaultState) (amount : UInt256) : ...
-- lsc: parameter 'caller : Address' looks like a caller address but has no @[lsc.caller] annotation;
--      add @[lsc.caller] to exclude from ABI, or rename to avoid confusion

-- Validator error: two @[lsc.caller] annotations
@[lsc.external]
def foo (@[lsc.caller] a : Address) (@[lsc.caller] b : Address) (s : S) : ...
-- lsc: at most one @[lsc.caller] parameter per export
```

### §5.3 EvmContext (compiler-generated only)

The full `EvmContext` struct is used by the compiler-generated export wrapper only. Authors never write it in contract functions.

```lean
-- Compiler-internal; not available in src/*.lean
structure EvmContext where
  sender  : Address
  value   : UInt256
  address : Address   -- executing contract (self)
  origin  : Address   -- tx.origin
```

The wrapper binds `@[lsc.caller] caller := ctx.sender` before invoking the author function.

> **Why an annotation instead of a positional or naming convention?**
> Positional rules ("first `Address` is always the caller") break when a function genuinely takes an address as an ABI argument in the first position. Naming conventions (`caller`, `sender`, `from`) are ambiguous across codebases. An explicit annotation is unambiguous, self-documenting, and gives the validator a clear rule to enforce.

> **Why not implicit `msg.sender` as a global?**
> Implicit globals make theorems non-uniform — you need to reason about an injected context variable that isn't in the function signature. Explicit `@[lsc.caller] caller : Address` means theorems quantify over `caller` directly: `∀ caller, transfer caller s to amount = …`.

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
def transfer
    (@[lsc.caller] caller : Address)
    (s : ERC20State)
    (to : Address)
    (amount : UInt256) : Result (ERC20State × Bool) TokenError :=
  if s.balances.get caller < amount then
    none
  else
    let s' := { s with
      balances := s.balances.set caller (s.balances.get caller - amount)
                    |>.set to (s.balances.get to + amount) }
    Lsc.Event.log (TransferEvent.mk caller to amount)
    .ok (s', true)
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

Each `Lsc.Event.log` on a path to `some _` is collected independently. No logs fire on paths that return `none`.

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

As a result, `simp [transfer]` in a proof unfolds `transfer` as if `Lsc.Event.log` were absent. Spec theorems quantify only over `Option` returns; `transfer … = some (s', _)` has the same meaning whether or not the body contains log calls.

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

### §7.1 `.err e` = EVM REVERT

Fallible `@[lsc.external]` functions return `Result Val E`. `.err e` models EVM revert with a typed custom error; `.ok val` models success.

```lean
@[lsc.external]
def transfer
    (@[lsc.caller] caller : Address) (s : TokenState)
    (to : Address) (amount : UInt256) : Result (TokenState × Bool) TokenError :=
  assert (s.balances.get caller >= amount) .insufficientBalance
  let newCaller <- (s.balances.get caller).checkedSub amount
  let newTo     <- (s.balances.get to).checkedAdd amount
  Lsc.Event.log (TransferEvent.mk caller to amount)
  .ok ({ s with balances := s.balances.set caller newCaller |>.set to newTo }, true)
```

Infallible functions (`S` or `V` return shapes) never revert.

### §7.2 Lean to EVM mapping

| Lean return | EVM behavior |
|-------------|-------------|
| `.err e` | `REVERT` with `abi.encode(e)` — no storage commit, no events |
| `.ok s'` (infallible mutator `S`) | persist `s'`; no ABI returndata |
| `.ok (s', v)` (fallible `Result (S x V) E`) | persist `s'`, emit events, ABI-encode `v` |
| `val` (infallible view `V`) | read-only; ABI-encode `val`; no store |
| `.ok v` (fallible view `Result V E`) | read-only; ABI-encode `v`; no store |

### §7.3 Error specs

Error specs use `(h : f ... = .err .Variant)` as the hypothesis:

```lean
/-- transfer reverts with insufficientBalance when caller has too little. -/
def transfer_no_overdraft
    (caller to : Address) (amount : UInt256) (s : TokenState)
    (h : transfer caller s to amount = .err .insufficientBalance) : Prop :=
  s.balances.get caller < amount

/-- transfer overflows only when the recipient addition wraps. -/
def transfer_arith_overflow
    (caller to : Address) (amount : UInt256) (s : TokenState)
    (h : transfer caller s to amount = .err (.arith .overflow)) : Prop :=
  s.balances.get caller >= amount /\
  s.balances.get to + amount >= 2^256
```

Specs can now distinguish *which* error fired. The matching theorem proves each condition with `simp [transfer] + omega`.

> **Why Result with typed errors instead of Option?**
> `Option` cannot express which error fired. `Result Val E` lets specs prove exact error conditions — essential for user-facing contracts. The `@[simp]` discriminators and `assert`/`<-` desugaring ensure proof bodies are no harder to write than with `Option`. See §11.1 for the helpers.

> **Why not partial functions?**
> Lean requires totality for kernel checking. Partial functions break `simp` and LLM proof generation.
---

## §8 External Calls

> **v1 status:** `World`, `invoke`, and `Lsc.extern.*` are specified here for completeness and to support the composition demo (Appendix B), but are **not** part of the v1 Counter smoke tests. Full emitter support lands in v2b. See Appendix C for the versioning roadmap.

### §8.1 World and accounts

Single-contract `State → Result S E` is insufficient when bytecode calls other contracts. Multi-contract storage lives in `World` in `Lsc.Semantics`:

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

Author contract functions remain `State → Result S E` (or infallible `S`) — they never take `World`. `World` threading happens only in compiler-generated export bodies.

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
  : Result (World × Bool) ExternError
```

Interface typeclasses (`IERC20`, etc.) live in `Lsc.Interfaces` or project `interfaces/*.lean`.

### §8.4 Registered vs assumed callees

| Callee kind | Resolution | Proof strength |
|-------------|-----------|----------------|
| **Registered** | Same repo `src/*.lean` + `[lsc.contracts]` address table | Compose callee spec theorems via `simulate_call` (§11.5) |
| **Assumed** | `@[extern_assume "IERC20"]` + axioms in `spec/` | Trust interface axioms (human-reviewed) |

### §8.5 Reentrancy

`@[lsc.no_reentrant]` on an export is a validator-checked annotation: no `Lsc.extern.call` (mutating) may appear in the dynamic call graph of this export while a frame for `self` is on the stack. Proofs may use `lift_no_reentrant` (§11.6) to reduce to `State → Result S E` without trace quantification.

### §8.6 Unsafe escape hatch (v3)

```lean
Lsc.unsafe.call (addr : Address) (value : UInt256) (calldata : Bytes)
  : Result (World × Bytes) ExternError
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

/-- increment increases the stored number by exactly 1. -/
def increment_increases_number
    (s s' : CounterState) (ret : Unit)
    (h : increment s = some (s', ret)) : Prop :=
  s'.number = s.number + 1

/-- Global invariant: no sequence of user actions can decrease the number.
    applyActions and CounterAction are defined in the spec file alongside these defs. -/
def number_never_decreases
    (s : CounterState) (actions : List CounterAction) : Prop :=
  (applyActions s actions).number ≥ s.number
```

The RHS is the proposition body — what must hold given the hypothesis. Single-call specs use `(h : f … s = some (s', ret))` for success and `(h : f … = none)` for revert. **Sequence specs** (like `number_never_decreases`) take a `List Action` and a helper `applyActions` function defined in the same spec file — both are plain Lean `def`s. `Nat` and `List` are allowed in spec files; they are banned only in contract code (§2.5).

### §9.2 Naming convention

Spec `def` names follow `{function}_{property}` for single-call specs, and `{subject}_{invariant}` for sequence specs, e.g.:
- `increment_increases_number` (single-call)
- `transfer_no_overdraft` (single-call revert)
- `transfer_preserves_total_supply` (single-call)
- `number_never_decreases` (sequence invariant)

The proof file uses the **same name** for the proving `theorem`. The compliance manifest and proof runner key off these shared names (§12).

### §9.3 Checklist

Every mutating export should have at least:
1. One **success property** using `(h : f … s = some (s', _))` — what holds after the call
2. One **revert property** using `(h : f … = none)` — what inputs cause revert

Views typically need one success property.

Contracts with global invariants (properties that must hold across any sequence of calls) should additionally have at least one **sequence spec** using `List Action` and an `applyActions` helper. See the Counter example in §1.2 for the pattern.

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
    (h : transfer caller s to amount = some (s', ret)) : Prop :=
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
    (s s' : CounterState) (ret : Unit)
    (h : increment s = some (s', ret)) :
    CounterSpec.increment_increases_number s s' ret h := by
  simp [CounterSpec.increment_increases_number, increment] at h
  exact h

-- Sequence theorem: proved by induction over the action list.
theorem number_never_decreases
    (s : CounterState) (actions : List CounterAction) :
    CounterSpec.number_never_decreases s actions := by
  induction actions generalizing s with
  | nil => simp [CounterSpec.number_never_decreases, CounterSpec.applyActions]
  | cons a rest ih =>
      cases a with
      | increment =>
          simp [CounterSpec.applyActions, increment]
          have := ih { number := s.number + 1 }
          simp [CounterSpec.number_never_decreases] at this
          omega
```

Each `theorem`:
- Has the **same name** as the spec `def`
- Takes the **same arguments** as the spec `def`
- Concludes that the spec `def` applied to those arguments holds (`CounterSpec.<name> …`)

Sequence theorems are proved by induction over the `List Action` — a standard Lean pattern that LLM proof generation handles well.

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

```lean
namespace Lsc

-- ── Result discriminators (Lsc.ProofHelpers) ──

@[simp] theorem Result.ok_ne_err {Val E : Type} (v : Val) (e : E) :
    (Result.ok v : Result Val E) ≠ Result.err e := by simp [Result.ok, Result.err]

@[simp] theorem Result.err_ne_ok {Val E : Type} (v : Val) (e : E) :
    (Result.err e : Result Val E) ≠ Result.ok v := by simp [Result.ok, Result.err]

@[simp] theorem Result.ok_inj {Val E : Type} {v v' : Val} :
    (Result.ok v : Result Val E) = Result.ok v' ↔ v = v' := by simp [Result.ok]

@[simp] theorem Result.err_inj {Val E : Type} {e e' : E} :
    (Result.err e : Result Val E) = Result.err e' ↔ e = e' := by simp [Result.err]

-- ── Layer 1 core helpers ──────────────────────────────────────────────────────

/-- Two successive successful mutator calls: extract intermediate state. -/
theorem compose {S E : Type} (f g : S → Result S E) (s s'' s' : S)
    (hf : f s = .ok s') (hg : g s' = .ok s'') :
    ∃ smid, f s = .ok smid ∧ g smid = .ok s'' :=
  ⟨s', hf, hg⟩

/-- Success state extraction (val ignored when only state matters). -/
theorem success_state {Val E : Type} {f : α → Result Val E} {v : Val}
    (h : f x = .ok v) : f x = .ok v := h

/-- Error helper: given f errors with e, derive any P provable from inputs. -/
theorem err_implies {Val E : Type} {f : α → Result Val E} {e : E}
    {P : Prop} (h : f x = .err e) (hp : P) : P := hp

/-- Sequence monotonicity: reduce sequence specs to per-step specs. -/
theorem applyActions_monotone
    {S Action : Type}
    (apply : S → Action → S)
    (field : S → UInt256)
    (hstep : ∀ (s : S) (a : Action), field (apply s a) ≥ field s)
    (s : S) (actions : List Action) :
    field (actions.foldl apply s) ≥ field s := by
  induction actions generalizing s with
  | nil  => simp
  | cons a rest ih =>
      simp [List.foldl]
      exact le_trans (hstep s a) (ih (apply s a))

end Lsc
```

The `Result.ok_ne_err` and `Result.err_ne_ok` simp lemmas fire automatically during `simp [myFunction]`, eliminating the `.ok ≠ .err` case work that would otherwise appear in every error proof. With these in place, error proofs have the same `simp + omega` structure as success proofs.

### §11.2 Worked example: `transfer_no_overdraft`

This is a complete proof of a revert property using Layer 1 helpers and `Mapping` simp lemmas.

**Spec** (`spec/ERC20Spec.lean`):
```lean
def transfer_no_overdraft
    (@[lsc.caller] caller to : Address) (amount : UInt256) (s : ERC20State)
    (h : transfer caller s to amount = none) : Prop :=
  s.balances.get caller < amount
```

**Proof** (`test/ERC20Proof.lean`):
```lean
theorem transfer_no_overdraft
    (caller to : Address) (amount : UInt256) (s : ERC20State)
    (h : transfer caller s to amount = none) :
    ERC20Spec.transfer_no_overdraft caller to amount s h := by
  -- Unfold the spec def (it's just s.balances.get caller < amount)
  simp [ERC20Spec.transfer_no_overdraft]
  -- Unfold transfer; the only path that returns none is the guard branch
  simp [transfer] at h
  -- h is now: s.balances.get caller < amount = True (from the if-guard)
  -- omega closes the arithmetic goal
  omega
```

**Step by step:**
1. `simp [ERC20Spec.transfer_no_overdraft]` — unfolds the spec `def`, reducing the goal to `s.balances.get caller < amount`
2. `simp [transfer] at h` — unfolds `transfer`; the `if s.balances.get caller < amount then none` branch is the only `none` path; `simp` extracts the guard condition from `h`
3. `omega` — closes the linear arithmetic goal

If the function body used `Mapping.get` or `set`, the `@[simp]` lemmas from §3.2 (`get_set_same`, `get_set_other`) would fire automatically during `simp [transfer]`.

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
theorem lift_logs {S α E : Type} {f : S → Result (S × α) E}
    {g : S → Result (S × α × List LogEntry) E}
    (hg : ∀ s r, f s = some r → ∃ logs, g s = some (r, logs))
    (s : S) (r : S × α) (logs : List LogEntry)
    (h : g s = some (r, logs)) :
    f s = some r := by ...

/-- Export with no Lsc.extern.* sites equals internal fn then load/store. -/
theorem lift_no_extern {S Ret : Type}
    (internal : S → Result (S × Ret) E)
    (exportFn : EvmContext → S → Result (S × Ret × List LogEntry) E)
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
    (callerInternal : S → Result (S × Ret) E)
    (calleeInternal : CalleeState → Result CalleeState CalleeError)
    (exportWithCall : EvmContext → World → S → Result (World × Ret × List LogEntry) E)
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
theorem lift_no_reentrant {S Ret : Type}
    (internal : S → Result (S × Ret) E)
    (exportFn : EvmContext → World → S → Result (S × Ret × List LogEntry) E)
    (hNoReentry : True)  -- replaced by validator certificate in v2c
    (h : ∀ ctx w s, exportFn ctx w s =
      match internal s with
      | none => none
      | some (s', ret) => some (s', ret, [])) :
    ∀ s s' ret, internal s = some (s', ret) →
    ∀ ctx w, exportFn ctx w s = some (s', ret, []) := by
  intro s s' ret hInt ctx w
  rw [h]; simp [hInt]

end Lsc
```

### §11.7 Tactics

**`export_cases`** — destructs a `Result (Ret × List LogEntry) E` for Layer 2 goals:
```lean
macro "export_cases" h:ident : tactic => `(tactic|
  (cases $(h) with
   | none => simp_all
   | some p =>
       obtain ⟨ret, logs⟩ := p
       simp_all))
```

**`erc_cases`** — destructs `Result (S × Bool) E`:
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
| `String`, `Char` | `lsc: String is not allowed; use Bytes` |
| Closures / lambda capturing outer variable | `lsc: closures are not supported; use a top-level function` |
| Partial application | `lsc: partial application is not supported` |
| `IO`, `StateM`, any monad | `lsc: monadic code is not allowed in contracts; use explicit state passing` |
| Higher-order functions | `lsc: functions cannot be passed as arguments` |
| Unbounded recursion | `lsc: recursive function X must be structurally terminating` |
| `List` or `Array` in author code | `lsc: List is not allowed in contract code; use Mapping or Lsc.Event.log for events` |
| `structure … extends` | `lsc: storage inheritance via extends is not supported in v1; define a flat State struct` |
| `LogEntry` constructed in author code | `lsc: LogEntry is compiler-internal; use Lsc.Event.log` |
| Hand-written export wrapper | `lsc: export wrappers are compiler-generated; use @[lsc.external] on contract functions` |
| `EvmContext` in author contract code | `lsc: use @[lsc.caller] caller : Address; EvmContext is compiler-generated only` |
| Error type `E` in `Result … E` without `@[lsc.error]` | `lsc: error type E must be declared with @[lsc.error]` |
| `@[lsc.error]` on non-inductive | `lsc: @[lsc.error] applies only to inductive declarations` |
| Multiple `@[lsc.error]` in one module | `lsc: multiple @[lsc.error] types in one contract; one per module is recommended` |
| Bare `Option State` on mutator | `lsc: use Result S E or Result (S × V) E for mutators` |
| Invalid `@[lsc.external]` return shape | `lsc: @[lsc.external] "f" must return Result S E, Result (S × V) E, S (infallible mutator), or V (infallible view)` |
| Unresolved polymorphism | `lsc: polymorphic function X cannot be compiled` |
| `Bytes` longer than 256 bytes | `lsc: Bytes literal exceeds max length of 256 bytes` |
| Author `sload` / `sstore` / slot indices | `lsc: storage IO is only performed by the emitter at @[lsc.external] boundaries` |
| `World` in contract functions | `lsc: World is not allowed in contract functions; extern calls are compiler-generated` |
| `Lsc.extern.*` in contract functions | `lsc: external calls are only allowed in compiler-generated exports` |
| Malformed event signature | `lsc: invalid event signature "..."; expected form "Name(type,type)"` |
| Event arg count / type mismatch | `lsc: event "Transfer(...)" expects N arguments of types ...; got ...` |
| `@[lsc.caller]` with non-Address type | `lsc: @[lsc.caller] parameter must have type Address` |
| Multiple `@[lsc.caller]` on one export | `lsc: at most one @[lsc.caller] parameter per export` |
| `Address` parameter first, no `@[lsc.caller]` | `lsc: parameter looks like a caller address but has no @[lsc.caller] annotation` |
| Plain `+`, `-`, `*`, `/` on `UInt256` in contract code | `lsc: use checkedAdd/checkedSub/checkedMul/checkedDiv; plain arithmetic is not allowed` |
| `←` on non-`Result` expression | `lsc: <- propagation requires a Result return type` |
| `←` with incompatible error type | `lsc: error type E in expr does not embed into the function's error type; add \| arith (e : ArithError) or similar` |
| `Option (S × Ret)` as mutator return | `lsc: use Result S E or Result (S × V) E for mutators; Option is for infallible views` |
| `assert` with non-Bool condition | `lsc: assert condition must be a Bool or decidable Prop` |

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

Authors write pure functions. At each `@[lsc.external]` boundary, the emitter generates:

1. **ABI dispatcher** — computes 4-byte selector from `keccak256(canonicalSignature)`; dispatches in Yul
2. **Calldata decode** — ABI-decodes included parameters (§4.5) from calldata
3. **`EvmContext` construction** — binds `ctx.sender := msg.sender`, `ctx.value := msg.value`, etc.
4. **`@[lsc.caller]` binding** — `caller := ctx.sender`
5. **State load** — `sload` all struct fields; decode dynamic `Bytes` tails
6. **Author function call** — invokes the `@[lsc.external]` function with loaded state and decoded args
7. **On `none`** — `revert(0, 0)`; no storage writes; no events
8. **On `some (s', ret)`** — `sstore` all fields; collect and emit `Lsc.Event.log` sites in source order via `LOG` opcodes; ABI-encode `ret` as returndata

View exports (§4.3) omit steps 5-store and 8-store; the emitter may lazy-load only accessed fields if the observable result matches whole-state read.

### §14.2 Auto load/store invariant

The emitter's whole-state load → apply → store semantics are the normative model. Any emitter optimization (diff stores, lazy view loads) must produce observable behavior identical to:

```
load all fields → call author function → store all fields (on some)
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

## Appendix A — ERC-20 Pattern

This appendix documents the **[forge-lean-erc20](https://github.com/forge-lean/forge-lean-erc20)** showcase. It is not part of the core `Lsc` package or default proof runner behavior. The demo enables `[lsc.compliance.erc20]` (§12) to require the theorem list there.

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
  name        : Bytes
  symbol      : Bytes
  decimals    : UInt256
  totalSupply : UInt256
  balances    : Mapping Address UInt256
  allowances  : Mapping Address (Mapping Address UInt256)
```

### A.2 Key exports

```lean
@[lsc.external]
def transfer
    (@[lsc.caller] caller : Address)
    (s : ERC20State)
    (to : Address)
    (amount : UInt256) : Result (ERC20State × Bool) TokenError :=
  if s.balances.get caller < amount then
    none
  else
    let s' := { s with
      balances := s.balances.set caller (s.balances.get caller - amount)
                    |>.set to (s.balances.get to + amount) }
    Lsc.Event.log (TransferEvent.mk caller to amount)
    .ok (s', true)

@[lsc.external]
def approve
    (@[lsc.caller] caller : Address)
    (s : ERC20State)
    (spender : Address)
    (amount : UInt256) : Result (ERC20State × Bool) TokenError :=
  let s' := { s with
    allowances := s.allowances.set caller
      (s.allowances.get caller |>.set spender amount) }
  Lsc.Event.log (ApprovalEvent.mk caller spender amount)
  .ok (s', true)
```

### A.3 Example spec and proof

```lean
-- spec/ERC20Spec.lean
/-- transfer reverts when caller has insufficient balance. -/
def transfer_no_overdraft
    (caller to : Address) (amount : UInt256) (s : ERC20State)
    (h : transfer caller s to amount = none) : Prop :=
  s.balances.get caller < amount

/-- transfer preserves total supply. -/
def transfer_preserves_total_supply
    (caller to : Address) (amount : UInt256)
    (s s' : ERC20State) (ret : Bool)
    (h : transfer caller s to amount = some (s', ret)) : Prop :=
  s'.totalSupply = s.totalSupply
```

```lean
-- test/ERC20Proof.lean
theorem transfer_no_overdraft
    (caller to : Address) (amount : UInt256) (s : ERC20State)
    (h : transfer caller s to amount = none) :
    ERC20Spec.transfer_no_overdraft caller to amount s h := by
  simp [ERC20Spec.transfer_no_overdraft, transfer] at *
  omega

theorem transfer_preserves_total_supply
    (caller to : Address) (amount : UInt256)
    (s s' : ERC20State) (ret : Bool)
    (h : transfer caller s to amount = some (s', ret)) :
    ERC20Spec.transfer_preserves_total_supply caller to amount s s' ret h := by
  simp [ERC20Spec.transfer_preserves_total_supply, transfer] at *
  exact h.2
```

---

## Appendix B — Composition Pattern

This appendix documents the **[forge-lean-composition](https://github.com/forge-lean/forge-lean-composition)** demo — the reference application for `Lsc.extern.call`, reentrancy-aware `World`/`invoke`, and multi-contract composition. It is the primary driver for v2a–v2b extern support.

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
  MyToken->>TC: Lsc.extern.call onTransfer
  TC->>TC: count + 1
  TC-->>MyToken: success
  MyToken-->>User: true
```

### B.2 MyToken state (flat struct — no `extends`)

```lean
-- src/MyToken.lean
structure MyTokenState where
  name        : Bytes
  symbol      : Bytes
  decimals    : UInt256
  totalSupply : UInt256
  balances    : Mapping Address UInt256
  allowances  : Mapping Address (Mapping Address UInt256)
  counter     : Address   -- 0 = hook disabled
```

### B.3 TransferCounter

```lean
-- src/TransferCounter.lean
structure TransferCounterState where
  count : UInt256

@[lsc.error]
inductive TransferCounterError where
  | arith (e : ArithError)
  deriving DecidableEq

@[lsc.external]
def onTransfer (s : TransferCounterState) : Result TransferCounterState TransferCounterError :=
  let c ← s.count.checkedAdd 1
  .ok { s with count := c }
```

### B.4 Required theorems

**ERC-20 compliance** (`[lsc.compliance.erc20]`): same table as §12.3, stated over `MyToken` functions.

**Hook compliance** (`[lsc.compliance.hook]`):

| Theorem | Statement summary |
|---------|------------------|
| `transfer_increments_counter_when_hooked` | `counter ≠ 0`, successful export ⇒ `count` increases by 1 |
| `transfer_skips_counter_when_zero` | `counter = 0` ⇒ behavior matches export without extern |
| `transfer_self_noop_skips_counter` | `from = to` ⇒ counter unchanged |
| `hook_revert_implies_transfer_none` | counter call reverts ⇒ MyToken export `none` |

**TransferCounter** (`spec/TransferCounterSpec.lean`):

| Theorem | Statement summary |
|---------|------------------|
| `onTransfer_increments_count` | `onTransfer` increments `count` by exactly 1 |

### B.5 Proof strategy

| Layer | What | Files |
|-------|------|-------|
| 1 | TransferCounter closed-world | `TransferCounterSpec` / `TransferCounterProof` |
| 2 | MyToken ERC-20 properties | `MyTokenSpec` / `MyTokenProof` — no `World` |
| 3 | Hook composition | `MyTokenSpec` / `MyTokenProof` — `simulate_call` (v2b) |
| 4 | EVM | `Composition.t.sol` — `deployCode` both contracts; assert `count` after transfers |

---

## Appendix C — Versioning Roadmap

All v2+ content is removed from the main spec body. This appendix records what each phase adds.

| Phase | Status | Deliverables |
|-------|--------|-------------|
| **v1** | Current | Counter + ERC-20 demo; no `Lsc.extern.*` in core tests; `World`/`invoke` in `Lsc.Semantics` but not emitted |
| **v2a** | Planned | `World`, `Account`, `invoke` fully wired in Foundry multi-contract tests |
| **v2b** | Planned | `Lsc.extern.call` / `staticcall` emitter; `CALL` lowering; registered callees; `simulate_call` complete |
| **v2c** | Planned | `@[lsc.no_reentrant]` validator enforcement; trace templates; `lift_*` refinement lemmas |
| **v3** | Future | `delegatecall`; `Lsc.unsafe.call`; `CREATE` / `SELFDESTRUCT` in `World` |

| Feature | First available | Proof stance |
|---------|----------------|-------------|
| `CALL` | v2b | Compose registered contracts; assume interfaces otherwise |
| `STATICCALL` | v2b | `lift_staticcall_view` |
| `DELEGATECALL` | v3 | Proxy specs |
| Arbitrary calldata | v3 (`unsafe.call`) | Fuzz only |
| `CREATE` / `SELFDESTRUCT` | v3 | After CALL stable |
| `structure … extends` | TBD | If clear v2 use case emerges |
| Gas forwarding proof | Phase 2 | Emitter correctness proof |

---

## Appendix D — Decision Log

| Version | Topic | Decision |
|---------|-------|---------|
| v1.1 | EVM context | Explicit `EvmContext`; wrappers bind `msg.sender` |
| v1.1 | Verification | Full-stack intent; Phase 2 scope TBD; v1 trusts emitter + Foundry fuzz |
| v1.1 | Spec format | Lean `def` propositions + proof-module theorems |
| v1.1 | Foundry | Native via fork first |
| v1.1 | ERC-20 demo | Reference app (external repo; Appendix A) |
| v1.1 | Proofs | No `lsc prove` in v1; kernel is arbiter |
| v1.1 | Compliance | Proof check on `forge test`, not `forge build` |
| v1.1 | Storage | Auto load/store at export boundary; whole-state proof model |
| v1.2 | State vocabulary | `set` / `State` / `store`; reject author storage IO |
| v1.2 | Invocation | `Lsc.Semantics.invoke`, `CallFrame`, revert/reentrancy semantics |
| v1.2 | Externals | `Lsc.extern.*`, interfaces, assumed callees, phased roadmap |
| v1.2 | Proof helpers | `lift_no_extern`, `lift_staticcall_view`, `simulate_call`, `@[lsc.no_reentrant]` |
| v1.2 | Rejected | `ContractM` in contracts; `World` in contract functions; raw arbitrary `call` |
| v1.3 | Platform scope | Spec is toolchain-first; ERC-20 is external demo |
| v1.3 | Compliance | Optional `[lsc.compliance.*]`; no global ERC-20 gate |
| v1.4 | Composition demo | `forge-lean-composition`; TransferCounter hook |
| LSC 1.0 | Caller identity | `@[lsc.caller]` annotation (replaces positional/name convention) |
| LSC 1.0 | Mutator returns | `Result Val E` two-param; infallible `S` / `V`; `Option` banned on mutators |
| LSC 1.0 | `extends` | Removed from v1; flat State structs only |
| LSC 1.0 | `max_bytes` | Fixed at 256 in v1; configurability deferred to v2 |
| LSC 1.0 | `UInt256` | `Fin (2^256)`; `omega`/`simp` apply directly |
| LSC 1.0 | Event erasure | `Lsc.Event.log` desugars to identity; explicit in §6.3 |
| LSC 1.0 | `revert_on_none` | Rewritten to conclude caller-supplied `P` (was: `True`) |
| LSC 1.0 | `simulate_call` | Stub with TODO; full World threading in v2b |
| LSC 1.0 | Compliance check | Runner verifies conclusion shape, not just theorem name |
| LSC 1.0 | LLM workflow | Removed from spec; kernel is arbiter; proof generation is external |
| LSC 1.0 | Gas forwarding | Non-goal in v1; added to §1.4 |
| LSC 1.0 | Contract errors | `@[lsc.error]` on inductive; `lsc_errors` macro removed |
| LSC 1.0 | `@[lsc.extern_hook]` | Removed from v1; v2b feature |
| LSC 1.0 | `Option (Bool × List LogEntry)` in ABI table | Removed; compiler-internal |
| LSC 1.0 | `sorry` in §6.4.4 example | Replaced with `by exact?` + skeleton comment |

---

## Appendix E — ERC-20 with Mint/Burn

This appendix is a complete, self-contained ERC-20 implementation with owner-controlled mint and burn. It demonstrates `Mapping`, `@[lsc.caller]`, events, authorization proofs, construction pattern, and the compliance manifest.

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
  owner       : Address                                                  -- slot 0
  name        : Bytes                                                    -- slot 1
  symbol      : Bytes                                                    -- slot 2
  decimals    : UInt256                                                  -- slot 3
  totalSupply : UInt256                                                  -- slot 4
  balances    : Mapping Address UInt256                           -- slot 5
  allowances  : Mapping Address (Mapping Address UInt256)  -- slot 6

@[lsc.error]
inductive TokenError where
  | insufficientBalance
  | insufficientAllowance
  | unauthorized
  | alreadyInitialized
  | arith (e : ArithError)
  deriving DecidableEq

-- Construction: call initialize once; reverts if already initialized.
-- owner = Address.zero means uninitialized.
@[lsc.external]
def initialize
    (@[lsc.caller] caller : Address)
    (s : TokenState)
    (name : Bytes) (symbol : Bytes) (decimals : UInt256)
    (initialSupply : UInt256) : Result TokenState TokenError :=
  if s.owner.val ≠ 0 then none   -- already initialized
  else
    let s' := { s with
      owner       := caller
      name        := name
      symbol      := symbol
      decimals    := decimals
      totalSupply := initialSupply
      balances    := s.balances.set caller initialSupply }
    Lsc.Event.log (TransferEvent.mk { val := 0 } caller initialSupply)
    .ok s'

-- Transfer
@[lsc.external]
def transfer
    (@[lsc.caller] caller : Address)
    (s : TokenState)
    (to : Address) (amount : UInt256) : Result (TokenState × Bool) TokenError :=
  if s.balances.get caller < amount then none
  else
    let s' := { s with balances :=
      s.balances.set caller (s.balances.get caller - amount)
                    |>.set to   (s.balances.get to   + amount) }
    Lsc.Event.log (TransferEvent.mk caller to amount)
    .ok (s', true)

-- Approve
@[lsc.external]
def approve
    (@[lsc.caller] caller : Address)
    (s : TokenState)
    (spender : Address) (amount : UInt256) : Result (TokenState × Bool) TokenError :=
  let s' := { s with allowances :=
    s.allowances.set caller (s.allowances.get caller |>.set spender amount) }
  Lsc.Event.log (ApprovalEvent.mk caller spender amount)
  .ok (s', true)

-- TransferFrom
@[lsc.external]
def transferFrom
    (@[lsc.caller] caller : Address)
    (s : TokenState)
    (from to : Address) (amount : UInt256) : Result (TokenState × Bool) TokenError :=
  let allowed := s.allowances.get from |>.get caller
  if s.balances.get from < amount then none
  else if allowed < amount then none
  else
    let s' := { s with
      balances   := s.balances.set from (s.balances.get from - amount)
                              |>.set to   (s.balances.get to   + amount)
      allowances := s.allowances.set from
                      (s.allowances.get from |>.set caller (allowed - amount)) }
    Lsc.Event.log (TransferEvent.mk from to amount)
    .ok (s', true)

-- Mint (owner only)
@[lsc.external]
def mint
    (@[lsc.caller] caller : Address)
    (s : TokenState)
    (to : Address) (amount : UInt256) : Result TokenState TokenError :=
  if caller ≠ s.owner then none
  else
    let s' := { s with
      totalSupply := s.totalSupply + amount
      balances    := s.balances.set to (s.balances.get to + amount) }
    Lsc.Event.log (TransferEvent.mk { val := 0 } to amount)
    .ok s'

-- Burn (owner only)
@[lsc.external]
def burn
    (@[lsc.caller] caller : Address)
    (s : TokenState)
    (from : Address) (amount : UInt256) : Result TokenState TokenError :=
  if caller ≠ s.owner then none
  else if s.balances.get from < amount then none
  else
    let s' := { s with
      totalSupply := s.totalSupply - amount
      balances    := s.balances.set from (s.balances.get from - amount) }
    Lsc.Event.log (TransferEvent.mk from { val := 0 } amount)
    .ok s'

-- Views
@[lsc.external]
def balanceOf (s : TokenState) (account : Address) : Option UInt256 :=
  some (s.balances.get account)

@[lsc.external]
def allowance (s : TokenState) (owner spender : Address) : Option UInt256 :=
  some (s.allowances.get owner |>.get spender)

@[lsc.external]
def totalSupply (s : TokenState) : Option UInt256 :=
  some s.totalSupply
```

### E.2 Spec (`spec/TokenSpec.lean`)

```lean
import Token

-- ── Authorization ────────────────────────────────────────────────────────────

/-- mint reverts when caller is not the owner. -/
def mint_requires_owner
    (caller : Address) (s : TokenState) (to : Address) (amount : UInt256)
    (h : mint caller s to amount = none) : Prop :=
  caller ≠ s.owner ∨ True  -- first branch is the authorization guard

/-- burn reverts when caller is not the owner. -/
def burn_requires_owner
    (caller : Address) (s : TokenState) (from : Address) (amount : UInt256)
    (h : burn caller s from amount = none) : Prop :=
  caller ≠ s.owner ∨ s.balances.get from < amount

-- ── Supply conservation ───────────────────────────────────────────────────────

/-- transfer preserves total supply. -/
def transfer_preserves_supply
    (caller to : Address) (amount : UInt256)
    (s s' : TokenState) (ret : Bool)
    (h : transfer caller s to amount = some (s', ret)) : Prop :=
  s'.totalSupply = s.totalSupply

/-- transferFrom preserves total supply. -/
def transferFrom_preserves_supply
    (caller from to : Address) (amount : UInt256)
    (s s' : TokenState) (ret : Bool)
    (h : transferFrom caller s from to amount = some (s', ret)) : Prop :=
  s'.totalSupply = s.totalSupply

/-- mint increases total supply by exactly amount. -/
def mint_increases_supply
    (caller to : Address) (amount : UInt256)
    (s s' : TokenState) (ret : Unit)
    (h : mint caller s to amount = some (s', ret)) : Prop :=
  s'.totalSupply = s.totalSupply + amount

/-- burn decreases total supply by exactly amount. -/
def burn_decreases_supply
    (caller from : Address) (amount : UInt256)
    (s s' : TokenState) (ret : Unit)
    (h : burn caller s from amount = some (s', ret)) : Prop :=
  s'.totalSupply = s.totalSupply - amount

-- ── Balance correctness ───────────────────────────────────────────────────────

/-- transfer reverts when caller has insufficient balance. -/
def transfer_no_overdraft
    (caller to : Address) (amount : UInt256) (s : TokenState)
    (h : transfer caller s to amount = none) : Prop :=
  s.balances.get caller < amount

/-- transfer moves tokens from caller to recipient. -/
def transfer_moves_tokens
    (caller to : Address) (amount : UInt256)
    (s s' : TokenState) (ret : Bool)
    (h : transfer caller s to amount = some (s', ret)) : Prop :=
  caller ≠ to →
    s'.balances.get caller = s.balances.get caller - amount ∧
    s'.balances.get to     = s.balances.get to   + amount

/-- transfer to self leaves balances unchanged. -/
def transfer_self_noop
    (caller : Address) (amount : UInt256)
    (s s' : TokenState) (ret : Bool)
    (h : transfer caller s caller amount = some (s', ret)) : Prop :=
  s'.balances.get caller = s.balances.get caller

/-- transferFrom reverts when allowance is insufficient. -/
def transferFrom_no_allowance_overdraft
    (caller from to : Address) (amount : UInt256) (s : TokenState)
    (h : transferFrom caller s from to amount = none) : Prop :=
  s.balances.get from < amount ∨
  s.allowances.get from |>.get caller < amount

/-- transferFrom decrements allowance by amount. -/
def transferFrom_decrements_allowance
    (caller from to : Address) (amount : UInt256)
    (s s' : TokenState) (ret : Bool)
    (h : transferFrom caller s from to amount = some (s', ret)) : Prop :=
  s'.allowances.get from |>.get caller =
    s.allowances.get from |>.get caller - amount

-- ── Initialization ────────────────────────────────────────────────────────────

/-- initialize reverts if called a second time. -/
def initialize_once
    (caller : Address) (s : TokenState)
    (name symbol : Bytes) (decimals initialSupply : UInt256)
    (h : initialize caller s name symbol decimals initialSupply = none) : Prop :=
  s.owner.val ≠ 0

/-- initialize sets caller as owner. -/
def initialize_sets_owner
    (caller : Address) (s s' : TokenState)
    (name symbol : Bytes) (decimals initialSupply : UInt256) (ret : Unit)
    (h : initialize caller s name symbol decimals initialSupply = some (s', ret)) : Prop :=
  s'.owner = caller

/-- initialize grants initial supply to caller. -/
def initialize_grants_supply
    (caller : Address) (s s' : TokenState)
    (name symbol : Bytes) (decimals initialSupply : UInt256) (ret : Unit)
    (h : initialize caller s name symbol decimals initialSupply = some (s', ret)) : Prop :=
  s'.balances.get caller = initialSupply ∧
  s'.totalSupply = initialSupply

-- ── Sequence invariant ────────────────────────────────────────────────────────

inductive TokenAction where
  | transfer     (caller to : Address) (amount : UInt256)
  | transferFrom (caller from to : Address) (amount : UInt256)
  | approve      (caller spender : Address) (amount : UInt256)
  | mint         (caller to : Address) (amount : UInt256)
  | burn         (caller from : Address) (amount : UInt256)

def applyTokenAction (s : TokenState) : TokenAction → TokenState
  | .transfer caller to amount =>
      match transfer caller s to amount with
      | some (s', _) => s' | none => s
  | .transferFrom caller from to amount =>
      match transferFrom caller s from to amount with
      | some (s', _) => s' | none => s
  | .approve caller spender amount =>
      match approve caller s spender amount with
      | some (s', _) => s' | none => s
  | .mint caller to amount =>
      match mint caller s to amount with
      | some (s', _) => s' | none => s
  | .burn caller from amount =>
      match burn caller s from amount with
      | some (s', _) => s' | none => s

def applyTokenActions (s : TokenState) (actions : List TokenAction) : TokenState :=
  actions.foldl applyTokenAction s

/-- No sequence of transfer/approve/transferFrom actions changes the total supply.
    Mint and burn are excluded from this variant to isolate conservation. -/
def non_mint_burn_actions_preserve_supply
    (s : TokenState)
    (actions : List TokenAction)
    (hSafe : actions.All (fun a => match a with
      | .mint _ _ _ => False
      | .burn _ _ _ => False
      | _ => True)) : Prop :=
  (applyTokenActions s actions).totalSupply = s.totalSupply
```

### E.3 Proof (`test/TokenProof.lean`)

```lean
import TokenSpec

theorem transfer_preserves_supply
    (caller to : Address) (amount : UInt256)
    (s s' : TokenState) (ret : Bool)
    (h : transfer caller s to amount = some (s', ret)) :
    TokenSpec.transfer_preserves_supply caller to amount s s' ret h := by
  simp [TokenSpec.transfer_preserves_supply, transfer] at *
  split_ifs at h with hbal
  · simp at h
  · simp at h; obtain ⟨hs', _⟩ := h; simp [← hs']

theorem transfer_no_overdraft
    (caller to : Address) (amount : UInt256) (s : TokenState)
    (h : transfer caller s to amount = none) :
    TokenSpec.transfer_no_overdraft caller to amount s h := by
  simp [TokenSpec.transfer_no_overdraft, transfer] at *
  split_ifs at h with hbal
  · exact hbal
  · simp at h

theorem transfer_self_noop
    (caller : Address) (amount : UInt256)
    (s s' : TokenState) (ret : Bool)
    (h : transfer caller s caller amount = some (s', ret)) :
    TokenSpec.transfer_self_noop caller amount s s' ret h := by
  simp [TokenSpec.transfer_self_noop, transfer] at *
  split_ifs at h with hbal
  · simp at h
  · simp at h; obtain ⟨hs', _⟩ := h
    simp [← hs', Mapping.get_set_same, Mapping.get_set_other]
    omega

theorem mint_requires_owner
    (caller : Address) (s : TokenState) (to : Address) (amount : UInt256)
    (h : mint caller s to amount = none) :
    TokenSpec.mint_requires_owner caller s to amount h := by
  simp [TokenSpec.mint_requires_owner, mint] at *
  split_ifs at h with hown
  · left; exact hown
  · simp at h

theorem mint_increases_supply
    (caller to : Address) (amount : UInt256)
    (s s' : TokenState) (ret : Unit)
    (h : mint caller s to amount = some (s', ret)) :
    TokenSpec.mint_increases_supply caller to amount s s' ret h := by
  simp [TokenSpec.mint_increases_supply, mint] at *
  split_ifs at h with hown
  · simp at h
  · simp at h; obtain ⟨hs', _⟩ := h; simp [← hs']

theorem initialize_sets_owner
    (caller : Address) (s s' : TokenState)
    (name symbol : Bytes) (decimals initialSupply : UInt256) (ret : Unit)
    (h : initialize caller s name symbol decimals initialSupply = some (s', ret)) :
    TokenSpec.initialize_sets_owner caller s s' name symbol decimals initialSupply ret h := by
  simp [TokenSpec.initialize_sets_owner, initialize] at *
  split_ifs at h with hinit
  · simp at h
  · simp at h; obtain ⟨hs', _⟩ := h; simp [← hs']

theorem initialize_grants_supply
    (caller : Address) (s s' : TokenState)
    (name symbol : Bytes) (decimals initialSupply : UInt256) (ret : Unit)
    (h : initialize caller s name symbol decimals initialSupply = some (s', ret)) :
    TokenSpec.initialize_grants_supply caller s s' name symbol decimals initialSupply ret h := by
  simp [TokenSpec.initialize_grants_supply, initialize] at *
  split_ifs at h with hinit
  · simp at h
  · simp at h; obtain ⟨hs', _⟩ := h
    simp [← hs', Mapping.get_set_same]

-- Sequence invariant: transfer/approve/transferFrom don't change totalSupply.
theorem non_mint_burn_actions_preserve_supply
    (s : TokenState) (actions : List TokenAction)
    (hSafe : actions.All (fun a => match a with
      | .mint _ _ _ => False | .burn _ _ _ => False | _ => True)) :
    TokenSpec.non_mint_burn_actions_preserve_supply s actions hSafe := by
  simp [TokenSpec.non_mint_burn_actions_preserve_supply]
  induction actions generalizing s with
  | nil => simp [TokenSpec.applyTokenActions]
  | cons a rest ih =>
      simp [List.All] at hSafe
      obtain ⟨ha, hrest⟩ := hSafe
      simp [TokenSpec.applyTokenActions, TokenSpec.applyTokenAction]
      cases a with
      | transfer caller to amount =>
          simp at ha
          simp [transfer]
          split_ifs with hbal
          · exact ih s hrest
          · simp; exact ih _ hrest
      | transferFrom caller from to amount =>
          simp at ha
          simp [transferFrom]
          split_ifs <;> simp <;> exact ih _ hrest
      | approve caller spender amount =>
          simp at ha
          simp [approve]
          exact ih _ hrest
      | mint => simp at ha
      | burn  => simp at ha
```

### E.4 Compliance manifest (`foundry.toml` excerpt)

```toml
[lsc.compliance.erc20_mintburn]
spec = "spec/TokenSpec.lean"
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
  "initialize_once",
  "initialize_sets_owner",
  "initialize_grants_supply",
  "non_mint_burn_actions_preserve_supply",
]
```

### E.5 What this example demonstrates

| Feature | Where |
|---------|-------|
| `Mapping` with `Address` keys | `balances`, `allowances` |
| Nested `Mapping` | `allowances : Mapping Address (Mapping Address UInt256)` |
| `@[lsc.caller]` authorization | `mint`, `burn`: revert if `caller ≠ s.owner` |
| Construction pattern (initialize once) | `initialize`: revert if `s.owner.val ≠ 0` |
| Revert spec (`h : f … = none`) | `transfer_no_overdraft`, `mint_requires_owner`, `initialize_once` |
| Success spec (`h : f … = some (s', _)`) | `transfer_moves_tokens`, `mint_increases_supply` |
| Sequence invariant over `List TokenAction` | `non_mint_burn_actions_preserve_supply` |
| Compliance manifest | `[lsc.compliance.erc20_mintburn]` |


---

## Appendix F — UniV2-Style AMM

This appendix is a complete constant-product AMM with `swap`, `addLiquidity`, and `removeLiquidity`. It demonstrates multi-field state invariants, the `k = x * y` preservation proof, overflow preconditions in specs, and a sequence monotonicity invariant over all three actions.

### F.1 Design notes

**`k = reserve0 * reserve1` and overflow:** `UInt256` multiplication can overflow for large reserves. The spec states `k`-preservation under an explicit no-overflow precondition (`reserve0 * reserve1 < 2^256`). This is honest — UniV2 itself relies on practical reserve bounds. The precondition appears in the spec `def` as a hypothesis; proofs discharge it with `omega` when the inputs are bounded.

**No-fee swap for `k`-preservation:** The preservation proof uses a no-fee swap. Fees only make `k` larger (proved separately as `k_never_decreases`). The no-fee version is the clean mathematical core.

**LP tokens:** `lpBalances` tracks each address's share. `addLiquidity` mints LP tokens proportional to the liquidity added; `removeLiquidity` burns them and returns the proportional reserves.

**Integer division:** `removeLiquidity` uses integer division for the reserve amounts returned. The spec states `≥` rather than `=` for `k` after removal, because rounding may leave a fractional unit in the pool.

### F.2 Contract (`src/AMM.lean`)

```lean
import Lsc.Prelude
open Lsc

structure AMMState where
  reserve0    : UInt256                         -- slot 0: token0 reserves
  reserve1    : UInt256                         -- slot 1: token1 reserves
  totalLP     : UInt256                         -- slot 2: total LP tokens outstanding
  lpBalances  : Mapping Address UInt256  -- slot 3: LP token balances

-- ── Swap (no fee, constant product) ──────────────────────────────────────────
-- Given amountIn of token0, compute amountOut of token1 such that
-- (reserve0 + amountIn) * (reserve1 - amountOut) = reserve0 * reserve1
-- Solved: amountOut = reserve1 - (reserve0 * reserve1) / (reserve0 + amountIn)
-- Integer division floors, so amountOut is conservative (pool keeps the rounding).

@[lsc.external]
def swap
    (s : AMMState)
    (amountIn : UInt256) : Result (AMMState × UInt256) AMMError :=
  if s.reserve0 = 0 ∨ s.reserve1 = 0 then none          -- pool not initialized
  else if amountIn = 0 then none                          -- zero input
  else
    let newReserve0 := s.reserve0 + amountIn
    let k           := s.reserve0 * s.reserve1
    let newReserve1 := k / newReserve0                    -- floors: newReserve1 ≤ k/newReserve0
    if newReserve1 = 0 then none                          -- degenerate output
    else
      let amountOut := s.reserve1 - newReserve1
      let s' := { s with reserve0 := newReserve0, reserve1 := newReserve1 }
      some (s', amountOut)

-- ── Add Liquidity ─────────────────────────────────────────────────────────────
-- Deposit token0 and token1 in the current ratio.
-- LP minted = totalLP * amount0 / reserve0  (or proportional for token1).
-- First liquidity: LP minted = amount0 (arbitrary seed).

@[lsc.external]
def addLiquidity
    (@[lsc.caller] caller : Address)
    (s : AMMState)
    (amount0 amount1 : UInt256) : Result (AMMState × UInt256) AMMError :=
  if amount0 = 0 ∨ amount1 = 0 then none
  else if s.totalLP = 0 then
    -- First deposit: seed the pool
    let lpMinted := amount0                               -- seed LP = amount0
    let s' := { s with
      reserve0   := amount0
      reserve1   := amount1
      totalLP    := lpMinted
      lpBalances := s.lpBalances.set caller lpMinted }
    some (s', lpMinted)
  else
    -- Subsequent deposits: must match ratio; LP proportional to token0 deposited
    if s.reserve0 = 0 then none
    else
      let lpMinted := s.totalLP * amount0 / s.reserve0
      if lpMinted = 0 then none                           -- dust deposit
      else
        let s' := { s with
          reserve0   := s.reserve0 + amount0
          reserve1   := s.reserve1 + amount1
          totalLP    := s.totalLP + lpMinted
          lpBalances := s.lpBalances.set caller
                          (s.lpBalances.get caller + lpMinted) }
        some (s', lpMinted)

-- ── Remove Liquidity ──────────────────────────────────────────────────────────
-- Burn lpAmount LP tokens; receive proportional reserves back.
-- amount0Out = reserve0 * lpAmount / totalLP
-- amount1Out = reserve1 * lpAmount / totalLP

@[lsc.external]
def removeLiquidity
    (@[lsc.caller] caller : Address)
    (s : AMMState)
    (lpAmount : UInt256) : Result (AMMState × UInt256 × UInt256) AMMError :=
  if lpAmount = 0 then none
  else if s.totalLP = 0 then none
  else if s.lpBalances.get caller < lpAmount then none    -- insufficient LP balance
  else
    let amount0Out := s.reserve0 * lpAmount / s.totalLP
    let amount1Out := s.reserve1 * lpAmount / s.totalLP
    if amount0Out = 0 ∨ amount1Out = 0 then none          -- dust removal
    else
      let s' := { s with
        reserve0   := s.reserve0 - amount0Out
        reserve1   := s.reserve1 - amount1Out
        totalLP    := s.totalLP  - lpAmount
        lpBalances := s.lpBalances.set caller
                        (s.lpBalances.get caller - lpAmount) }
      some (s', amount0Out, amount1Out)

-- Views
@[lsc.external]
def getReserves (s : AMMState) : UInt256 × UInt256 :=
  (s.reserve0, s.reserve1)

@[lsc.external]
def lpBalance (s : AMMState) (account : Address) : Option UInt256 :=
  some (s.lpBalances.get account)
```

### F.3 Spec (`spec/AMMSpec.lean`)

```lean
import AMM

-- ── Helper: k value ───────────────────────────────────────────────────────────

def k (s : AMMState) : UInt256 := s.reserve0 * s.reserve1

-- ── Swap specs ────────────────────────────────────────────────────────────────

/-- swap reverts on zero input. -/
def swap_revert_zero_input
    (s : AMMState)
    (h : swap s 0 = none) : Prop :=
  True   -- always holds; zero input always reverts by construction

/-- swap reverts on uninitialized pool. -/
def swap_revert_uninitialized
    (s : AMMState) (amountIn : UInt256)
    (h : swap s amountIn = none) : Prop :=
  s.reserve0 = 0 ∨ s.reserve1 = 0 ∨ amountIn = 0 ∨ True
  -- disjunctive: one of the guard conditions fired

/-- swap output is positive when it succeeds. -/
def swap_positive_output
    (s s' : AMMState) (amountOut : UInt256)
    (h : swap s amountIn = some (s', amountOut)) : Prop :=
  amountOut > 0

/-- Core: swap preserves k (no-fee version, integer arithmetic).
    reserve0 * reserve1 only grows (floor division leaves dust in pool).
    Precondition: no overflow on k computation. -/
def swap_preserves_k
    (s s' : AMMState) (amountIn amountOut : UInt256)
    (hOverflow : s.reserve0 * s.reserve1 < 2^256 - s.reserve0)  -- no overflow
    (h : swap s amountIn = some (s', amountOut)) : Prop :=
  k s' ≥ k s

/-- swap increases reserve0 by exactly amountIn. -/
def swap_increases_reserve0
    (s s' : AMMState) (amountIn amountOut : UInt256)
    (h : swap s amountIn = some (s', amountOut)) : Prop :=
  s'.reserve0 = s.reserve0 + amountIn

/-- swap decreases reserve1 (amountOut leaves the pool). -/
def swap_decreases_reserve1
    (s s' : AMMState) (amountIn amountOut : UInt256)
    (h : swap s amountIn = some (s', amountOut)) : Prop :=
  s'.reserve1 = s.reserve1 - amountOut

-- ── addLiquidity specs ────────────────────────────────────────────────────────

/-- addLiquidity reverts on zero amounts. -/
def addLiquidity_revert_zero
    (caller : Address) (s : AMMState) (amount0 amount1 : UInt256)
    (h : addLiquidity caller s amount0 amount1 = none) : Prop :=
  amount0 = 0 ∨ amount1 = 0 ∨ True

/-- addLiquidity increases both reserves (subsequent deposit). -/
def addLiquidity_increases_reserves
    (caller : Address) (s s' : AMMState) (amount0 amount1 lpMinted : UInt256)
    (hNotFirst : s.totalLP > 0)
    (h : addLiquidity caller s amount0 amount1 = some (s', lpMinted)) : Prop :=
  s'.reserve0 ≥ s.reserve0 ∧ s'.reserve1 ≥ s.reserve1

/-- addLiquidity increases totalLP. -/
def addLiquidity_increases_totalLP
    (caller : Address) (s s' : AMMState) (amount0 amount1 lpMinted : UInt256)
    (h : addLiquidity caller s amount0 amount1 = some (s', lpMinted)) : Prop :=
  s'.totalLP ≥ s.totalLP

/-- addLiquidity mints LP to caller. -/
def addLiquidity_mints_to_caller
    (caller : Address) (s s' : AMMState) (amount0 amount1 lpMinted : UInt256)
    (h : addLiquidity caller s amount0 amount1 = some (s', lpMinted)) : Prop :=
  s'.lpBalances.get caller ≥ s.lpBalances.get caller

-- ── removeLiquidity specs ─────────────────────────────────────────────────────

/-- removeLiquidity reverts when caller has insufficient LP. -/
def removeLiquidity_revert_insufficient_lp
    (caller : Address) (s : AMMState) (lpAmount : UInt256)
    (h : removeLiquidity caller s lpAmount = none) : Prop :=
  lpAmount = 0 ∨ s.totalLP = 0 ∨ s.lpBalances.get caller < lpAmount ∨ True

/-- removeLiquidity decreases totalLP by lpAmount. -/
def removeLiquidity_burns_lp
    (caller : Address) (s s' : AMMState) (lpAmount amount0Out amount1Out : UInt256)
    (h : removeLiquidity caller s lpAmount = some (s', amount0Out, amount1Out)) : Prop :=
  s'.totalLP = s.totalLP - lpAmount

/-- removeLiquidity decreases caller LP balance by lpAmount. -/
def removeLiquidity_decreases_caller_lp
    (caller : Address) (s s' : AMMState) (lpAmount amount0Out amount1Out : UInt256)
    (h : removeLiquidity caller s lpAmount = some (s', amount0Out, amount1Out)) : Prop :=
  s'.lpBalances.get caller = s.lpBalances.get caller - lpAmount

/-- removeLiquidity: k may decrease slightly (integer division rounding)
    but is bounded below by k - totalLP (worst-case rounding loss). -/
def removeLiquidity_k_bounded
    (caller : Address) (s s' : AMMState) (lpAmount amount0Out amount1Out : UInt256)
    (h : removeLiquidity caller s lpAmount = some (s', amount0Out, amount1Out)) : Prop :=
  k s' ≤ k s  -- k can only decrease on removal (reserves shrink)

-- ── Sequence invariant: k never decreases under swap-only sequences ───────────

inductive AMMAction where
  | swap          (amountIn : UInt256)
  | addLiquidity  (caller : Address) (amount0 amount1 : UInt256)
  | removeLiquidity (caller : Address) (lpAmount : UInt256)

def applyAMMAction (s : AMMState) : AMMAction → AMMState
  | .swap amountIn =>
      match swap s amountIn with
      | some (s', _) => s' | none => s
  | .addLiquidity caller amount0 amount1 =>
      match addLiquidity caller s amount0 amount1 with
      | some (s', _) => s' | none => s
  | .removeLiquidity caller lpAmount =>
      match removeLiquidity caller s lpAmount with
      | some (s', _, _) => s' | none => s

def applyAMMActions (s : AMMState) (actions : List AMMAction) : AMMState :=
  actions.foldl applyAMMAction s

/-- k never decreases under any sequence of swaps and addLiquidity calls.
    Precondition: no removeLiquidity in the sequence (which can decrease k by rounding).
    Precondition: no overflow (k fits in UInt256 throughout). -/
def k_never_decreases_swap_add
    (s : AMMState)
    (actions : List AMMAction)
    (hNoRemove : actions.All (fun a => match a with
      | .removeLiquidity _ _ => False | _ => True))
    (hNoOverflow : k s < 2^255) : Prop :=
  k (applyAMMActions s actions) ≥ k s
```

### F.4 Proof (`test/AMMProof.lean`)

```lean
import AMMSpec

-- ── Helper lemma: swap step increases k ──────────────────────────────────────

theorem swap_preserves_k
    (s s' : AMMState) (amountIn amountOut : UInt256)
    (hOverflow : s.reserve0 * s.reserve1 < 2^256 - s.reserve0)
    (h : swap s amountIn = some (s', amountOut)) :
    AMMSpec.swap_preserves_k s s' amountIn amountOut hOverflow h := by
  simp [AMMSpec.swap_preserves_k, AMMSpec.k, swap] at *
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

theorem swap_increases_reserve0
    (s s' : AMMState) (amountIn amountOut : UInt256)
    (h : swap s amountIn = some (s', amountOut)) :
    AMMSpec.swap_increases_reserve0 s s' amountIn amountOut h := by
  simp [AMMSpec.swap_increases_reserve0, swap] at *
  split_ifs at h <;> simp_all

theorem swap_decreases_reserve1
    (s s' : AMMState) (amountIn amountOut : UInt256)
    (h : swap s amountIn = some (s', amountOut)) :
    AMMSpec.swap_decreases_reserve1 s s' amountIn amountOut h := by
  simp [AMMSpec.swap_decreases_reserve1, swap] at *
  split_ifs at h <;> simp_all

theorem addLiquidity_increases_reserves
    (caller : Address) (s s' : AMMState) (amount0 amount1 lpMinted : UInt256)
    (hNotFirst : s.totalLP > 0)
    (h : addLiquidity caller s amount0 amount1 = some (s', lpMinted)) :
    AMMSpec.addLiquidity_increases_reserves caller s s' amount0 amount1 lpMinted hNotFirst h := by
  simp [AMMSpec.addLiquidity_increases_reserves, addLiquidity] at *
  split_ifs at h <;> simp_all <;> omega

theorem addLiquidity_increases_totalLP
    (caller : Address) (s s' : AMMState) (amount0 amount1 lpMinted : UInt256)
    (h : addLiquidity caller s amount0 amount1 = some (s', lpMinted)) :
    AMMSpec.addLiquidity_increases_totalLP caller s s' amount0 amount1 lpMinted h := by
  simp [AMMSpec.addLiquidity_increases_totalLP, addLiquidity] at *
  split_ifs at h <;> simp_all <;> omega

theorem removeLiquidity_burns_lp
    (caller : Address) (s s' : AMMState) (lpAmount amount0Out amount1Out : UInt256)
    (h : removeLiquidity caller s lpAmount = some (s', amount0Out, amount1Out)) :
    AMMSpec.removeLiquidity_burns_lp caller s s' lpAmount amount0Out amount1Out h := by
  simp [AMMSpec.removeLiquidity_burns_lp, removeLiquidity] at *
  split_ifs at h <;> simp_all

-- ── Sequence invariant: k never decreases under swap + addLiquidity ───────────

theorem k_never_decreases_swap_add
    (s : AMMState)
    (actions : List AMMAction)
    (hNoRemove : actions.All (fun a => match a with
      | .removeLiquidity _ _ => False | _ => True))
    (hNoOverflow : AMMSpec.k s < 2^255) :
    AMMSpec.k_never_decreases_swap_add s actions hNoRemove hNoOverflow := by
  simp [AMMSpec.k_never_decreases_swap_add]
  induction actions generalizing s with
  | nil => simp [AMMSpec.applyAMMActions]
  | cons a rest ih =>
      simp [List.All] at hNoRemove
      obtain ⟨ha, hrest⟩ := hNoRemove
      simp [AMMSpec.applyAMMActions, AMMSpec.applyAMMAction]
      cases a with
      | swap amountIn =>
          simp [swap]
          split_ifs with h0 hAmt hDeg
          · -- swap reverted: state unchanged, k unchanged, apply ih
            exact le_trans (le_refl _) (ih s hrest hNoOverflow)
          · exact le_trans (le_refl _) (ih s hrest hNoOverflow)
          · exact le_trans (le_refl _) (ih s hrest hNoOverflow)
          · -- swap succeeded: k s' ≥ k s (from swap_preserves_k)
            -- then ih: k (applyAMMActions s' rest) ≥ k s'
            -- combine: k (applyAMMActions s' rest) ≥ k s
            have hk : AMMSpec.k { s with
                reserve0 := s.reserve0 + amountIn
                reserve1 := s.reserve0 * s.reserve1 / (s.reserve0 + amountIn) } ≥
                AMMSpec.k s := by
              simp [AMMSpec.k]; omega
            exact le_trans hk (ih _ hrest (by simp [AMMSpec.k] at *; omega))
      | addLiquidity caller amount0 amount1 =>
          simp [addLiquidity]
          split_ifs
          · exact le_trans (le_refl _) (ih s hrest hNoOverflow)
          · -- first deposit: k goes from 0 to amount0 * amount1
            simp [AMMSpec.k]
            exact Nat.zero_le _  -- k was 0 (totalLP = 0 implies reserves = 0)
          · exact le_trans (le_refl _) (ih s hrest hNoOverflow)
          · -- subsequent deposit: both reserves increase, k increases
            have hk : AMMSpec.k { s with
                reserve0   := s.reserve0 + amount0
                reserve1   := s.reserve1 + amount1
                totalLP    := s.totalLP + s.totalLP * amount0 / s.reserve0
                lpBalances := _ } ≥ AMMSpec.k s := by
              simp [AMMSpec.k]; nlinarith
            exact le_trans hk (ih _ hrest (by simp [AMMSpec.k] at *; nlinarith))
      | removeLiquidity => simp at ha
```

### F.5 What this example demonstrates

| Feature | Where |
|---------|-------|
| Multi-field state with invariant | `reserve0`, `reserve1`, `totalLP`, `lpBalances` |
| `Mapping` for LP balances | `lpBalances : Mapping Address UInt256` |
| Multi-scalar return | `removeLiquidity` returns `Result (AMMState × UInt256 × UInt256) AMMError` |
| Overflow precondition in spec | `hOverflow : s.reserve0 * s.reserve1 < 2^256 - s.reserve0` |
| Integer division honesty | `k s' ≥ k s` (not `=`) for swap; `k s' ≤ k s` for remove |
| Named invariant helper | `def k (s : AMMState) : UInt256 := s.reserve0 * s.reserve1` |
| `nlinarith` for nonlinear arithmetic | `k_never_decreases_swap_add` — `k` is a product, not linear |
| Sequence invariant with action filter | `hNoRemove` excludes `removeLiquidity` from the monotonicity claim |
| Mixed revert conditions | `swap`: zero input, uninitialized, degenerate output |

### F.6 Key proof observations

**Why `≥` and not `=` for `swap_preserves_k`:** Integer division floors `newReserve1 = k / newReserve0`. The true mathematical `k` would require `newReserve1 = k / newReserve0` exactly, but integer division leaves `k mod newReserve0` as dust in the pool. So `newReserve0 * newReserve1 ≥ k` — the pool keeps the rounding error. This is the correct and honest spec.

**`nlinarith` for the sequence invariant:** `k` is a product of two `UInt256` values, making the invariant nonlinear. `omega` handles only linear arithmetic; `nlinarith` (nonlinear arithmetic) is needed for goals involving products. Both are available in Lean 4's `Mathlib`-derived tactic set.

**Overflow as a spec precondition, not a validator rule:** The overflow bound appears in the spec `def` as `hOverflow`, not as a validator error. This is intentional — the validator cannot know at compile time what the runtime reserve values will be. The spec makes the assumption explicit; Foundry fuzz tests verify it holds for realistic inputs.

**`removeLiquidity` and `k`:** Removal proportionally reduces both reserves, so `k` decreases. The sequence invariant therefore excludes `removeLiquidity` via `hNoRemove`. A more complete spec could prove `k_after_remove ≥ k_before - totalLP` (bounded loss), but that requires more careful arithmetic and is left as an exercise.

