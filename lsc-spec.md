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

**What is restricted in author code:** stateful monads (`StateM`, `IO`), higher-order functions, closures, unbounded collections in state, `Nat`/`Int`/`String`, `structure … extends`, unbounded recursion, manual storage IO. `do`-notation over `Result E` is allowed for fallible exports. See §13 for the full validator error table.

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
open Lsc Lsc.Arith

-- Error type: increment can overflow at UInt256 max
@[lsc.error]
inductive CounterError where
  | overflow   -- checkedAdd only; no division in Counter

structure CounterState where
  @[lsc.public]
  number : UInt256

-- Fallible mutator: no return value beyond new state, but overflow is possible.
-- Result CounterState CounterError  (two-param: value type, error type)
@[lsc.external]
def increment (s : CounterState) : Result CounterState CounterError := do
  let n ← s.number + 1
  return .ok { s with number := n }

-- Compiler generates @[lsc.external] def number (s : CounterState) : UInt256 := s.number (§3.5)
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
    (h : increment s = .err .overflow) : Prop :=
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
  · simp [UInt256.checkedAdd_ok, hov] at h; omega

theorem increment_overflows_iff
    (s : CounterState)
    (h : increment s = .err .overflow) :
    CounterSpec.increment_overflows_iff s h := by
  simp [CounterSpec.increment_overflows_iff, increment, UInt256.checkedAdd] at h
  split_ifs at h with hov
  · simp [UInt256.checkedAdd_overflow, hov] at h; omega
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
            have herr : increment s = .err .overflow := by
              simp [increment, UInt256.checkedAdd_overflow, hov]
            simp [CounterSpec.applyActions, herr]
            exact le_trans (le_refl _) (ih s)
          · -- success: s'.number = s.number + 1
            have hok : increment s = .ok { s with number := s.number + 1 } := by
              simp [increment, UInt256.checkedAdd_ok]; omega
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

The validator permits exactly these primitive types in contract code. Any other type is a hard error (§13.1).

| LSC type | Lean definition | EVM/ABI type | Notes |
|----------|----------------|--------------|-------|
| `UInt256` | `Fin (2^256)` | `uint256` | Arithmetic wraps mod 2^256; `omega` and `simp` apply directly via `Fin` lemmas |
| `Address` | `structure Address where val : UInt256` | `address` | Distinct newtype; not coercible to `UInt256` without `.val` |
| `Bool` | Lean built-in | `bool` | ABI boundary and internal guards |
| `Bytes32` | `Fin (2^256)` newtype | `bytes32` | Raw 32-byte value |
| `Bytes` | Dynamic byte array | `bytes` / `string` | Metadata and string fields; max 256 bytes in v1 (§2.2) |

`UInt256 = Fin (2^256)` means all arithmetic is definitional modular arithmetic. No custom axioms are needed for overflow; `omega` handles linear arithmetic over `Fin` directly.

In **spec and proof** modules, plain `+`, `-`, `*`, `/` on `UInt256` mean this modular (`Fin`) semantics. In **contract** modules (`src/*.lean`), fallible `@[lsc.export]` functions use **`do`-notation** over `Result E`; inside **`do`** blocks, `+ - * /` desugar to **checked** operations and **`←`** propagates errors. Outside **`do`** blocks, use explicit `checkedAdd` / … or **`unchecked do`** for wrapping **`Fin`** math (same as spec **`Prop`s**).

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

**`Monad (Result · E)`** — fallible contract functions use standard Lean 4 `do`-notation. The only monad permitted in contract code; it threads the error channel only (not state):

```lean
-- Lsc.Prelude (confirm or add)
instance : Monad (Result · E) where
  pure v    := .ok v
  bind ma f := match ma with
    | .err e => .err e
    | .ok v  => f v
```

### §2.5 Error types, `@[lsc.error]`, and arithmetic errors

**`@[lsc.error]` — declaring contract error types:**

```lean
@[lsc.error]
inductive TokenError where
  | insufficientBalance
  | insufficientAllowance
  | unauthorized
  | alreadyInitialized
  | overflow        -- enables checkedAdd/Sub/Mul
  | divisionByZero  -- enables checkedDiv
```

`@[lsc.error]` is a Lean 4 attribute that fires at elaboration time.
When applied to an inductive, it immediately generates:
- `@[simp]` discriminator lemmas (`Result.ok_ne_err`, per-variant injectivity)
- `DecidableEq` instance
- `HasArithErrors` instance when `overflow` and/or `divisionByZero`
  variants are present

The inductive itself is plain Lean 4 — authors can add doc comments,
derive additional instances, and pattern match normally.

| Responsibility | Owner |
|---|---|
| Declare the inductive | Author (standard Lean) |
| `@[simp]` discriminators, `DecidableEq`, `HasArithErrors` | `@[lsc.error]` at elaboration |
| Register type for revert encoding + ABI `errors` | `@[lsc.error]` attribute |
| Map variants → Solidity `error` entries | Emitter (reads `@[lsc.error]` inductives) |
| Surface missing `HasArithErrors` at `checkedAdd` sites | Lean elaborator → LSC validator message |

**One error type per contract is recommended for most projects.**
Every function in the contract uses the same error type, simp lemmas
are generated once, and LLM proof generation has a single error
vocabulary for the whole contract. Use per-function error types only
when two functions have genuinely incompatible error vocabularies (rare).

**`HasArithErrors` — arithmetic error typeclass:**

```lean
-- Lsc.Prelude
class HasArithErrors (E : Type) where
  overflow       : E
  divisionByZero : E
```

When `@[lsc.error]` sees `overflow` and/or `divisionByZero` variants,
it generates the `HasArithErrors` instance automatically at elaboration
time. This makes `checkedAdd`, `checkedSub`, `checkedMul`, and
`checkedDiv` usable with that error type — no wrapping or `mapErr`
required. The checked operations are polymorphic:

```lean
def UInt256.checkedAdd [HasArithErrors E] (a b : UInt256) : Result UInt256 E
```

If the contract does not need arithmetic checking, omit `overflow` and
`divisionByZero`. The Lean elaborator will emit a typeclass resolution
error at any `checkedAdd` site, which the LSC validator surfaces as:
`lsc: no HasArithErrors instance for E; add | overflow to your error type`

#### Arithmetic surface syntax (`Lsc.Arith`)

Contract and spec code share `UInt256 = Fin (2^256)`, but **surface syntax differs by module role** so overflow intent is visible to authors and the validator.

**Module conventions**

| Module | Required | Forbidden |
|--------|----------|-----------|
| `src/*.lean` (contract) | `do` / `unchecked do` in `@[lsc.export]` bodies; explicit `checkedAdd` outside `do` | `open Lsc.Arith` in `spec/` or `test/` |
| `spec/*.lean`, `test/*Proof.lean` | Plain `+ - * /` on `UInt256` (`Fin`) | `unchecked`, `open Lsc.Arith`, checked `+` in `do` |

**Wrapping — `unchecked do` (Solidity-style):** Only way to use modular **`+ - * /`** on `UInt256` in contracts. Inside the block, operators desugar to **`Fin`** ops (same as spec `+`). Not allowed in spec or proof modules.

```lean
-- Lsc.Prelude (Lsc.Arith) — internal / prelude only; authors use unchecked do
def UInt256.add  (a b : UInt256) : UInt256 := a + b   -- Fin HAdd
def UInt256.sub  (a b : UInt256) : UInt256 := a - b
def UInt256.mul  (a b : UInt256) : UInt256 := a * b
def UInt256.div  (a b : UInt256) : UInt256 := a / b

-- Macro: inside unchecked do, `+` uses UInt256.add; body is proof-erased to plain Fin math
unchecked do
  let newReserve0 := s.reserve0 + amountIn
  let k           := s.reserve0 * s.reserve1
  ...
```

**Checked operations** — revert via `Result` / `HasArithErrors E` (authoritative API; macros desugar here):

```lean
def UInt256.checkedAdd [HasArithErrors E] (a b : UInt256) : Result UInt256 E :=
  if a.val + b.val >= 2^256 then .err HasArithErrors.overflow
  else .ok ⟨a.val + b.val⟩

def UInt256.checkedSub [HasArithErrors E] (a b : UInt256) : Result UInt256 E :=
  if a.val < b.val then .err HasArithErrors.overflow
  else .ok ⟨a.val - b.val⟩

def UInt256.checkedMul [HasArithErrors E] (a b : UInt256) : Result UInt256 E :=
  if a.val != 0 && b.val > (2^256 - 1) / a.val then .err HasArithErrors.overflow
  else .ok ⟨a.val * b.val⟩

def UInt256.checkedDiv [HasArithErrors E] (a b : UInt256) : Result UInt256 E :=
  if b.val = 0 then .err HasArithErrors.divisionByZero
  else .ok ⟨a.val / b.val⟩
```

**Checked operators in `do` blocks** — inside `do` blocks in `@[lsc.export]` function bodies, the LSC validator rewrites arithmetic on `UInt256`:

| Author writes (in `do` block) | Desugars to |
|-------------------------------|-------------|
| `a + b` | `a.checkedAdd b` |
| `a - b` | `a.checkedSub b` |
| `a * b` | `a.checkedMul b` |
| `a / b` | `a.checkedDiv b` |

These return `Result UInt256 E`; `←` propagates via `Monad (Result · E)`. Outside `do` blocks and in spec/proof files, `+ - * /` retain standard Lean 4 meanings on `UInt256` (Fin arithmetic). Outside `do` in contract code, use `checkedAdd` / … explicitly. Raw kernel `HAdd` / `HSub` / `HMul` / `HDiv` on `UInt256` without these forms is a **validator error** (§13.1).

**Bridge lemmas** (`Lsc.Prelude`, all `@[simp]`):

```lean
@[simp] theorem UInt256.checkedAdd_ok [HasArithErrors E] (a b : UInt256)
    (h : a.val + b.val < 2^256) :
    UInt256.checkedAdd (E := E) a b = .ok ⟨a.val + b.val⟩ := by
  simp [UInt256.checkedAdd, h]

@[simp] theorem UInt256.checkedAdd_overflow [HasArithErrors E] (a b : UInt256)
    (h : a.val + b.val >= 2^256) :
    UInt256.checkedAdd (E := E) a b = .err HasArithErrors.overflow := by
  simp [UInt256.checkedAdd, h]

-- analogous checkedSub_ok, checkedSub_overflow
-- checkedMul_ok, checkedMul_overflow
-- checkedDiv_ok, checkedDiv_divisionByZero
```

Proofs: prefer `simp [increment, UInt256.checkedAdd_ok]` over unfolding `checkedAdd` (§11.1).

**When to use which (contracts)**

- **`do` / `←` (checked)** — fallible mutators and views; balances, counters, user-facing paths where overflow or division-by-zero should return `.err .overflow` or `.err .divisionByZero`; e.g. `let n ← s.number + 1` inside `do`.
- **`unchecked do`** — inner steps where linked spec `def`s prove bounds and overflow should not revert; plain `let` with `+ * / -` (`+` returns `UInt256`, not `Result`).
- **Spec `Prop`s** — always `a + b`, `a * b`, etc. on `UInt256`; link checked paths via `checkedAdd_ok`; inside `unchecked`, contract `+` matches spec `+` definitionally after `simp [swap, …]`.

**Error propagation — `do`-notation:**

Functions that can fail use standard Lean 4 `do`-notation over `Result E`. The `←` operator is monadic bind — it unwraps a `Result Val E`, propagating `.err e` automatically if the computation fails:

```lean
def increment (s : CounterState) : Result CounterState CounterError := do
  let n ← s.number + 1   -- + is checkedAdd; ← propagates overflow
  return .ok { s with number := n }
```

Inside `do` blocks in contract functions, arithmetic operators on `UInt256` desugar to their checked forms (`+` → `checkedAdd`, etc.). This requires a `HasArithErrors` instance for the function's error type `E` — provided automatically by `@[lsc.error]` when `overflow` and/or `divisionByZero` variants are present.

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
  | overflow   -- checkedAdd on balances and totalDeposits

@[lsc.external]
def deposit
    (@[lsc.caller] caller : Address)
    (s : VaultState)
    (amount : UInt256) : Result VaultState VaultError := do
  assert (amount > 0) .insufficientBalance
  let newBalance ← s.balances.get caller + amount
  let newTotal   ← s.totalDeposits + amount
  return .ok { s with
    balances      := s.balances.set caller newBalance
    totalDeposits := newTotal }
```

If checked `+` overflows, the function immediately returns `.err .overflow`. The spec can then prove:

```lean
def deposit_arith_error_means_overflow
    (caller : Address) (s : VaultState) (amount : UInt256)
    (h : deposit caller s amount = .err .overflow) : Prop :=
  s.balances.get caller + amount ≥ 2^256 ∨ s.totalDeposits + amount ≥ 2^256
```

### §2.6 Forbidden types

| Forbidden | Validator error | Use instead |
|-----------|----------------|-------------|
| `Nat`, `Int`, `Float` | `lsc: type Nat is not allowed; use UInt256` | `UInt256` |
| `String`, `Char` | `lsc: String is not allowed; use Bytes` | `Bytes` |
| `List`, `Array` in state | `lsc: List is not allowed in contract code` | `Mapping` |
| `IO`, `StateM`, `ST`, or any monad that threads implicit state | `lsc: stateful monads are not allowed in contracts; use explicit state passing` | Explicit state passing |
| Higher-order functions | `lsc: functions cannot be passed as arguments` | Top-level helpers |
| Recursive types / inductives with >2 constructors | `lsc: inductive type X is not allowed` | Struct + `Mapping` (except `@[lsc.error]` error enums) |
| `Option (S × Ret)` on mutator | `lsc: use Result S Ret E for mutators` | `Result S Ret E` |

**`do`-notation over `Result E` is allowed and recommended** for functions that can fail. This is the only monad permitted in contract code. It does not thread implicit state — `s` remains an explicit parameter, `s'` is an explicit return value — so theorems are unaffected.

```lean
-- Allowed: do-notation over Result E (error-only monad)
@[lsc.export]
def increment (s : CounterState) : Result CounterState CounterError := do
  let n ← s.number + 1   -- + desugars to checkedAdd inside do
  return .ok { s with number := n }

-- Banned: StateM or any monad that hides s
def increment : StateM CounterState Unit := ...
-- lsc: stateful monads are not allowed in contracts
```

> **Why not richer types?**
> Lean's proof automation (`simp`, `omega`, `decide`) works best on flat, finite structures. `Nat` requires `omega` extensions that interact poorly with `Fin`; `List` in state makes proof obligations unbounded; stateful monads hide the state threading that theorems need to quantify over (`s` and `s'` must stay explicit). `do` over `Result E` only threads errors. Every restriction here trades expressiveness for a proof that `simp` can close in one step.

> **Why `Result` instead of keeping `Option`?**
> `Option` cannot express *which* error fired — `none` is a single undifferentiated failure. `Result S Ret E` lets specs prove "this specific error fires under these conditions", which is essential for user-facing contracts. Generic `Result` simp lemmas in `Lsc.ProofHelpers` and `assert` desugaring ensure proof bodies are no harder to write than with `Option`. See §11.1.

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
| Scalar (`UInt256`, `Address`, `Bool`, `Bytes32`, `Bytes`) | `def fieldName (s : State) : T` | `s.fieldName` |
| `Mapping K V` | `def fieldName (s : State) (k : K) : V` | `s.fieldName.get k` |
| Nested `Mapping` | one key parameter per mapping level, left-to-right | nested `.get` |

Generated exports are infallible views (§4.3): return type `T` directly, not `Result` or `Option`. The emitter treats them like author-written views — no `sstore`, `s : State` excluded from ABI calldata (§4.5).

**Naming:** the ABI function name equals the Lean field name. v1 has no alias attribute. When the standard ABI name differs from the field name (e.g. IERC-20 `balanceOf` vs field `balances`), omit `@[lsc.public]` on that field and write a manual `@[lsc.external]` export instead.

**Proofs:** theorems continue to use `s.field` directly. Generated getters exist for deploy/ABI parity; spec modules need not reference them.

**Validator rules:** see §13.1.

> **Why an annotation instead of exposing all fields?**
> Most storage is internal. Opt-in `@[lsc.public]` mirrors Solidity `public` without generating getters for every field (mappings, internal counters, etc.). Proofs stay on record fields; the compiler only adds ABI surface where requested.

---

## §4 Functions (Exports)

### §4.1 The `@[lsc.external]` annotation

Public ABI functions are declared by annotating contract functions with `@[lsc.external]` (parameterless). Fields marked `@[lsc.public]` also produce `@[lsc.external]` view exports at elaboration time (§3.5). Only these exports appear in the deployed ABI.

```lean
@[lsc.external]
def increment (s : CounterState) : Result CounterState CounterError := do
  let n ← s.number + 1
  return .ok { s with number := n }
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
def increment (s : CounterState) : Result CounterState CounterError := do
  let n ← s.number + 1
  return .ok { s with number := n }

-- Fallible mutator with return value (transfer returns bool)
@[lsc.external]
def transfer
    (@[lsc.caller] caller : Address) (s : TokenState)
    (to : Address) (amount : UInt256) : Result (TokenState × Bool) TokenError := do
  assert (s.balances.get caller ≥ amount) .insufficientBalance
  let newCaller ← s.balances.get caller - amount
  let newTo     ← s.balances.get to + amount
  let s' := { s with balances := s.balances.set caller newCaller |>.set to newTo }
  Lsc.Event.log (TransferEvent.mk caller to amount)
  return .ok (s', true)

-- Infallible mutator (sets a flag, no arithmetic, cannot fail)
@[lsc.external]
def activate (s : FlagState) : FlagState :=
  { s with active := true }
```

### §4.3 Views

Views read state without modifying it:

```lean
-- Infallible view from @[lsc.public] on CounterState.number (§3.5); compiler-generated:
-- def number (s : CounterState) : UInt256 := s.number

-- Fallible view (rare): author-written
@[lsc.external]
def price (s : AMMState) : Result UInt256 AMMError := do
  assert (s.reserve1 > 0) .uninitializedPool
  let p ← s.reserve0 / s.reserve1
  return .ok p
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

Each `@[lsc.error]` variant becomes one Solidity `error` entry in the ABI JSON — including `overflow` and `divisionByZero` when present on the contract error inductive.

### §4.5 Parameter filtering

The compiler excludes certain parameters from ABI calldata automatically:

| Parameter kind | ABI | Rule |
|---------------|-----|------|
| `s : SomeState` (contract State struct) | excluded | Loaded by compiler from storage |
| `@[lsc.caller] caller : Address` | excluded | Bound to `msg.sender` by wrapper |
| `UInt256`, `Address`, `Bool`, `Bytes32`, `Bytes` (no annotation) | included | In declaration order |

Parameters are included in the ABI in the order they appear after the excluded ones are removed.

### §4.6 State threading

State is threaded **explicitly** through every function. Stateful monads are disallowed (§2.6); `do` over `Result E` is allowed.

```lean
-- Correct: explicit state threading with do-notation over Result
@[lsc.external]
def increment (s : CounterState) : Result CounterState CounterError := do
  let n ← s.number + 1   -- + desugars to checkedAdd inside do block
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
> `do` over `Result E` only threads the error channel — `s` stays an explicit parameter, `s'` stays an explicit return value. Theorems quantify over both as before: `(h : f s = .ok s')`. `StateM` hides `s` inside the monad, making it impossible to state theorems of that form. The ban is on implicit state, not on `do`-notation itself.

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
    (amount : UInt256) : Result (ERC20State × Bool) TokenError := do
  assert (s.balances.get caller ≥ amount) .insufficientBalance
  let newCaller ← s.balances.get caller - amount
  let newTo     ← s.balances.get to + amount
  let s' := { s with balances := s.balances.set caller newCaller |>.set to newTo }
  Lsc.Event.log (TransferEvent.mk caller to amount)
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

Each `Lsc.Event.log` on a path to `.ok _` is collected independently. No logs fire on paths that return `.err _`.

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

As a result, `simp [transfer]` in a proof unfolds `transfer` as if `Lsc.Event.log` were absent. Spec theorems quantify only over `Result` returns; `transfer … = .ok (s', _)` has the same meaning whether or not the body contains log calls.

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
    (to : Address) (amount : UInt256) : Result (TokenState × Bool) TokenError := do
  assert (s.balances.get caller >= amount) .insufficientBalance
  let newCaller ← s.balances.get caller - amount
  let newTo     ← s.balances.get to + amount
  Lsc.Event.log (TransferEvent.mk caller to amount)
  return .ok ({ s with balances := s.balances.set caller newCaller |>.set to newTo }, true)
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
    (h : transfer caller s to amount = .err .overflow) : Prop :=
  s.balances.get caller >= amount /\
  s.balances.get to + amount >= 2^256
```

Specs can now distinguish *which* error fired. The matching theorem proves each condition with `simp [transfer] + omega`.

> **Why Result with typed errors instead of Option?**
> `Option` cannot express which error fired. `Result Val E` lets specs prove exact error conditions — essential for user-facing contracts. The `@[simp]` discriminators and `assert`/`do` desugaring ensure proof bodies are no harder to write than with `Option`. See §11.1 for the helpers.

> **Why not partial functions?**
> Lean requires totality for kernel checking. Partial functions break `simp` and LLM proof generation.
---

## §8 External Calls

> **v1 status:** `World`, `invoke`, and `Lsc.extern.*` are specified here for completeness and to support the composition demo ([Appendix B](lsc-appendices.md#appendix-b--composition-pattern)), but are **not** part of the v1 Counter smoke tests. Full emitter support lands in v2b. See [Appendix C](lsc-appendices.md#appendix-c--versioning-roadmap) for the versioning roadmap.

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
    (s s' : CounterState)
    (h : increment s = .ok s') : Prop :=
  s'.number = s.number + 1

/-- Global invariant: no sequence of user actions can decrease the number.
    applyActions and CounterAction are defined in the spec file alongside these defs. -/
def number_never_decreases
    (s : CounterState) (actions : List CounterAction) : Prop :=
  (applyActions s actions).number ≥ s.number
```

The RHS is the proposition body — what must hold given the hypothesis. Single-call specs use `(h : f … s = .ok s')` or `(h : f … = .ok (s', ret))` for success and `(h : f … = .err e)` for revert. **Sequence specs** (like `number_never_decreases`) take a `List Action` and a helper `applyActions` function defined in the same spec file — both are plain Lean `def`s. `Nat` and `List` are allowed in spec files; they are banned only in contract code (§2.5). Specs use plain `Fin` `+` on `UInt256`, not `unchecked` or `open Lsc.Arith`.

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
2. One **revert property** using `(h : f … = .err e)` — what inputs cause revert

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

Per-variant injectivity lemmas and `HasArithErrors` field projections are generated by `@[lsc.error]` at elaboration time. `HasArithErrors` fields resolve to concrete constructors via `@[simp]` — so `simp [myFunction, UInt256.checkedAdd]` will automatically simplify `HasArithErrors.overflow` to `.overflow` (or whatever the concrete variant is) without any extra simp lemmas from the author.

#### Checked arithmetic in proofs

Inside `do` blocks, `+` in `increment` elaborates to `UInt256.checkedAdd`. Specs still use **`Fin` `+`** on `UInt256`. Bridge lemmas reconnect the two:

```lean
-- After simp [increment] at h : increment s = .ok s':
simp [UInt256.checkedAdd_ok, hov] at h   -- yields s'.number = s.number + 1

-- Overflow case at h : increment s = .err .overflow:
simp [UInt256.checkedAdd_overflow, hov] at h   -- Nat-level bound for omega
```

**Recipe:** unfold the export with `simp [f, …]`; use `checkedAdd_ok` / `checkedSub_ok` with overflow bounds on `.ok` hypotheses from `do`/`←` lines (desugared to `checkedAdd`); use `checkedAdd_overflow` / `checkedSub_overflow` / `checkedDiv_divisionByZero` on `.err .overflow` / `.err .divisionByZero` goals. For `unchecked do` bodies, `simp` exposes the same `+` as in the spec `Prop`.

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
| `IO`, `StateM`, `ST`, stateful monads | `lsc: stateful monads are not allowed; do-notation over Result E is permitted` |
| Higher-order functions | `lsc: functions cannot be passed as arguments` |
| Unbounded recursion | `lsc: recursive function X must be structurally terminating` |
| `List` or `Array` in author code | `lsc: List is not allowed in contract code; use Mapping or Lsc.Event.log for events` |
| `structure … extends` | `lsc: storage inheritance via extends is not supported in v1; define a flat State struct` |
| `LogEntry` constructed in author code | `lsc: LogEntry is compiler-internal; use Lsc.Event.log` |
| Hand-written export wrapper | `lsc: export wrappers are compiler-generated; use @[lsc.external] on contract functions` |
| `EvmContext` in author contract code | `lsc: use @[lsc.caller] caller : Address; EvmContext is compiler-generated only` |
| Error type `E` in `Result … E` without `@[lsc.error]` | `lsc: error type E must be declared with @[lsc.error]` |
| `@[lsc.error]` on non-inductive | `lsc: @[lsc.error] may only be applied to inductive types` |
| `lsc_errors` keyword | `lsc: lsc_errors is not supported; use @[lsc.error] inductive` |
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
| `@[lsc.public]` not on State struct field | `lsc: @[lsc.public] may only annotate State struct fields` |
| `@[lsc.public]` on unsupported field type | `lsc: @[lsc.public] field has unsupported type` |
| `@[lsc.public]` field name collides with `@[lsc.external]` def | `lsc: field "X" is @[lsc.public] but @[lsc.external] def X already exists` |
| Raw `HAdd` / `HSub` / `HMul` / `HDiv` on `UInt256` outside `do` and `unchecked do` | `lsc: arithmetic outside do blocks must use checkedAdd/Sub/Mul/Div explicitly, or unchecked do for wrapping; raw Fin operators are not allowed` |
| `unchecked` in spec or proof modules | `lsc: unchecked is contract-only; use + on UInt256 in spec` |
| `wrapAdd` / `UInt256.add` called directly in contract | `lsc: use unchecked do for wrapping arithmetic; wrapAdd is not allowed in contracts` |
| `open Lsc.Arith` in spec or proof modules | `lsc: Lsc.Arith is for contract modules only; spec uses Fin +` |
| `←` in `do` block where `E` has no `HasArithErrors` instance | `lsc: arithmetic in do block requires HasArithErrors; add \| overflow to your @[lsc.error] inductive` |
| `do` block on infallible function (return type `S` or `V`) | `lsc: do-notation requires Result return type` |
| Plain `+` `-` `*` `/` on `UInt256` outside `do` block in contract code | `lsc: arithmetic outside do blocks must use checkedAdd/Sub/Mul/Div explicitly` |
| Postfix `?` on `Result` | `lsc: ? operator is removed; use do-notation and ←` |
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

Authors write pure functions. At each `@[lsc.external]` boundary (including views synthesized from `@[lsc.public]` fields per §3.5), the emitter generates:

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

## Appendices

Extended reference patterns, examples, and project history are in **[lsc-appendices.md](lsc-appendices.md)** (Appendices A–F).
