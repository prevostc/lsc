# LSC — Lean Smart Contracts Language Specification

**Language version:** LSC 1.0
**Lean baseline:** `leanprover/lean4:stable` (pinned per project)
**Execution target:** EVM (bytecode via formally-verified lowering; standard JSON ABI)
**Companion document:** [lsc-toolchain.md](lsc-toolchain.md) — reference compiler, Foundry integration, artifacts, demos

---

## §1 Overview

### §1.1 What LSC is

**LSC (Lean Smart Contracts)** is a strict subset of Lean 4 for writing smart contracts whose correctness properties are machine-checked by the Lean kernel before deployment.

Authors write **functions over `ContractM E S α`** — a concrete state-transformer monad (`StateT World (Except (ContractError E))`) parameterized by the error type `E` and a phantom state type `S`. The compiler generates everything the EVM needs — ABI wrappers, `SLOAD`/`SSTORE` opcodes, `LOG` opcodes, `CALL` lowering. Authors never touch raw EVM opcodes or storage slot numbers directly.

Contract state is declared with the **`state!` macro**. The resulting struct (`Counter.State`, …) is a **schema** — it declares what the contract owns and determines storage layout. Fields are accessed via `get`/`set` using typed slot constants derived from the schema.

The `state!` schema gives authors named, typed fields without manual slot numbering. Contract functions use `get`/`set` for storage access; the same struct is the **proof snapshot** in theorem files (`s s' : Counter.State`, `s'.number`). The phantom type `S` on `ContractM` keeps distinct contracts' monads incompatible at the type level without any extra wrapping.

**What you can deploy:** persistent storage, events/logs, standard ABIs, ETH transfers, cross-contract calls, revert semantics, full EVM bytecode.

**What is restricted in author code:** stateful monads (`StateM`, `IO`), higher-order functions, closures, unbounded collections in state, `Nat`/`Int`/`String`, `structure … extends`, unbounded recursion, manual storage IO.

### §1.2 The three modules

Every LSC project produces three module kinds per contract:

| File | Role | Kernel-checked |
|---|---|---|
| `src/Counter.lean` | Contract — `state!` + `contract!` + `@[lsc.external]` functions | Yes (types) |
| `test/CounterProofs.lean` | Lemma — tactic proofs | Yes (full proof check) |
| `test/CounterTheorem.lean` | Theorem — high-level requirements, one-line lemma delegations | Yes (full proof check) |

The **contract** is what deploys. The **theorem** file is the requirements document — written and reviewed by humans. Each `theorem` states a readable business property inline and delegates to a homonymous `lemma` in exactly one line. The **lemma** file is AI-generated and holds all tactic proofs; humans do not review it. The Lean kernel checks both files.

**End-to-end Counter example:**

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
import CounterProofs
import Lsc.Prelude
open Lsc

/-- On success, pause sets `paused` to `true` and leaves `number` unchanged. -/
theorem pause_sets_paused (s s' : Counter.State) (h : runS pause s = .ok ((), s')) :
    s'.paused = true ∧ s'.number = s.number :=
  CounterProofs.pause_sets_paused s s' h

/-- On success, unpause clears `paused` and leaves `number` unchanged. -/
theorem unpause_clears_paused (s s' : Counter.State) (h : runS unpause s = .ok ((), s')) :
    s'.paused = false ∧ s'.number = s.number :=
  CounterProofs.unpause_clears_paused s s' h

/-- When unpaused, increment increases `number` by exactly 1. -/
theorem increment_increases_number_when_unpaused (s s' : Counter.State) (hp : ¬s.paused)
    (h : runS increment s = .ok ((), s')) :
    s'.number.val = s.number.val + 1 ∧ s'.paused = s.paused :=
  CounterProofs.increment_increases_number_when_unpaused s s' hp h

/-- When paused, increment reverts with `.IsPausedError`. -/
theorem increment_reverts_when_paused (s : Counter.State) (hp : s.paused) :
    runS increment s = .error (.contract .IsPausedError) :=
  CounterProofs.increment_errors_when_paused s hp
```

`test/CounterProofs.lean`:
```lean4
import Counter
import Lsc.Prelude
open Lsc

namespace CounterProofs

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

end CounterProofs
```

---

## PART I — THE CONTRACT LANGUAGE

---

## §2 Types

### §2.1 Primitive types

| LSC type | Lean definition | EVM/ABI type | Notes |
|---|---|---|---|
| `UInt256` | `{ n : ℕ // n < 2^256 }` | `uint256` | Bounded; no default `+ - * /` — use `+?` |
| `Address` | `structure Address where val : UInt256` | `address` | Not coercible to `UInt256` without `.val` |
| `Bool` | Lean built-in | `bool` | |
| `Bytes32` | `structure Bytes32 where val : UInt256` | `bytes32` | Opaque 32-byte word; not coercible to `UInt256` |
| `Bytes[N]` | `{ b : ByteArray // b.size ≤ N }` | `bytes` / `string` | Bounded; see §2.2 |

#### Arithmetic semantics

`UInt256` is a bounded natural subtype. Plain `+ - * /` on `UInt256` are a **type error** in author code. The only supported arithmetic family currently is **checked** operators that revert on overflow:

| Mode | Syntax | Returns | Use when |
|---|---|---|---|
| Checked | `a +? b` | `ContractM E S UInt256` | **default** — overflow reverts |
| Wrapping | `a +↻ b` | `UInt256` | Intentional mod-2²⁵⁶ *(planned)* |

`-?`, `*?`, `/?`, and wrapping operators (`-↻`, `*↻`) are planned; only `+?` is currently implemented. `+?` also accepts a `Nat` literal on the right (`n +? 1`).

**Comparisons:** `=`, `≤`, `≥`, `<`, `>` on `UInt256` compare via `.val` (prelude instances).

### §2.2 Bytes[N]

`Bytes[N]` is a bounded byte array (planned — not yet in the prelude).

```lean4
abbrev Bytes (n : Nat) := { b : ByteArray // b.size ≤ n }
notation "Bytes[" n "]" => Bytes n
```

**Storage layout:**
- `b.size ≤ 31`: left-aligned in slot, `b.size * 2` in LSB.
- `b.size > 31`: slot `p` holds `b.size * 2 + 1`; payload at `keccak256(p)` in 32-byte chunks.

**Validator rules:** `N` must be a numeric literal. `N = 0` is a warning.

### §2.3 Mapping

`Mapping K V` is a plain Lean 4 function (planned):

```lean4
abbrev Mapping (K V : Type) := K → V
```

**Storage layout (within a namespace):** mapping root at offset; entry at key `k` lives at `keccak256(abi.encode(k, root + offset))` — identical to Solidity rules.

### §2.4 The `ContractM` monad

`ContractM E S α` is the contract monad. It is a concrete state transformer:

```lean4
-- Lsc.ContractM
abbrev ContractM (E : Type) (S : Type) (α : Type) :=
  StateT World (Except (ContractError E)) α
```

`S` is a **phantom type** — it pins the `ContractState` instance per contract, keeping `Counter α` and `Vault α` distinct at the type level without any runtime overhead.

`World` is the chain state: all accounts' storage, balances, and code:

```lean4
-- Lsc.World
structure World where
  storage : Address → Nat → UInt256
  balance : Address → UInt256
  code    : Address → ByteArray
```

**`runS`** — the proof interpreter for **state-snapshot theorems**. Embeds a typed state struct into a fresh `World`, runs the contract function, and projects the result back:

```lean4
-- Lsc.Run
def runS {E S α : Type} [ContractState S] (f : ContractM E S α) (s : S) :
    Except (ContractError E) (α × S) :=
  match f (ContractState.embed s World.empty) with
  | .ok (v, w') => .ok (v, ContractState.view w')
  | .error e    => .error e
```

**Success hypothesis shapes** for `runS`:

| Return type | Hypothesis form |
|---|---|
| `ContractM E S Unit` | `runS f s = .ok ((), s')` |
| `ContractM E S α` (α ≠ Unit) | `runS f s = .ok (v, s')` |

**Two proof modes:**

| Mode | State type | When |
|---|---|---|
| **State snapshot** (default) | `Counter.State`, … | Property mentions only this contract's fields |
| **World snapshot** | `World` | Reasoning about raw storage, multiple contracts |

State-snapshot theorems quantify over `Module.State` values and use `runS`. World-snapshot theorems work directly against the `ContractM` function applied to a `World` value:

```lean4
-- state-snapshot (default)
theorem increment_increases_number_when_unpaused (s s' : Counter.State) (hp : ¬s.paused)
    (h : runS increment s = .ok ((), s')) : s'.number.val = s.number.val + 1 := ...

-- world-snapshot
theorem increment_increases_number_world_when_unpaused (w w' : World)
    (hp : ¬(Counter.view w).paused)
    (h : increment w = .ok ((), w')) :
    (Counter.view w').number.val = (Counter.view w).number.val + 1 := ...
```

**Rollback on error** — `Except` short-circuits; any storage writes before a revert are discarded because `World` is threaded as a value, not mutated in place.

**`ContractError`** — wraps contract-specific errors alongside universal ones:

```lean4
inductive ContractError (E : Type) where
  | contract : E           → ContractError E
  | arith    : ArithError  → ContractError E
```

> **v2 planned:** `| extern : ExternError → ContractError E` for cross-contract call failures.

### §2.5 Error types and `LscError`

#### `error!` macro — declaring contract error types

The `error!` macro generates the inductive, derives `DecidableEq` and `Repr`, emits the `LscError` instance, and tags with `[lsc.error]`. The `| arith : ArithError → E` constructor **must** be present:

```lean4
error! CounterError where
  | IsPausedError
  | arith : ArithError → CounterError
-- expands to:
-- inductive CounterError where | IsPausedError | arith : ArithError → CounterError
--   deriving DecidableEq, Repr
-- instance : LscError CounterError where arith := .arith
-- attribute [lsc.error] CounterError
```

For contracts with external calls (planned), an `| extern : ExternError → E` constructor will also be required.

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

#### `UInt256` definition and projections

```lean4
abbrev UInt256 := { n : ℕ // n < 2^256 }

namespace UInt256
def val (a : UInt256) : ℕ := a.1
def zero : UInt256 := mk 0 (by decide)
def one  : UInt256 := mk 1 (by decide)
def max  : UInt256 := mk (2^256 - 1) (by omega)

@[simp] theorem eq_iff {a b : UInt256} : a = b ↔ a.val = b.val := Subtype.ext_iff
@[simp] theorem le_iff {a b : UInt256} : a ≤ b ↔ a.val ≤ b.val := Iff.rfl
@[simp] theorem lt_iff {a b : UInt256} : a < b ↔ a.val < b.val := Iff.rfl
end UInt256
```

> **Note:** `HAdd UInt256 ℕ UInt256` is intentionally **not** provided. Contract code must use checked operators (`+?`); theorem statements reason via `.val` or `UInt256.addNat` with an explicit overflow bound.

#### The `+?` operator family (checked, lifted into `ContractM`)

Currently only addition is implemented:

```lean4
def UInt256.addChecked {E S : Type} (a b : UInt256) : ContractM E S UInt256 :=
  if h : a.val + b.val < 2^256 then pure (mk (a.val + b.val) h)
  else ContractM.arithFail .overflow

def UInt256.addCheckedNat {E S : Type} (a : UInt256) (n : Nat) : ContractM E S UInt256 :=
  if h : a.val + n < 2^256 then pure (mk (a.val + n) h)
  else ContractM.arithFail .overflow

macro a:term " +? " n:num  : term => `(UInt256.addCheckedNat $a $n)
macro a:term " +? " b:term : term => `(UInt256.addChecked $a $b)
```

`-?`, `*?`, `/?` follow the same pattern (planned).

**Proof recipe:** In lemma proofs, unfold `+?` with `UInt256.addCheckedNat` (for literal rhs) or `UInt256.addChecked`, then split on the bound condition with `dif_pos`/`dif_neg` and close with `omega`.

#### The `+↻` operator family (wrapping) — planned

```lean4
def UInt256.addMod (a b : UInt256) : UInt256 := ⟨(a.val + b.val) % 2^256, by omega⟩
-- same pattern for -↻, *↻
```

### §2.6 Forbidden types

| Forbidden | Validator error | Use instead |
|---|---|---|
| `Nat`, `Int`, `Float` | `lsc: use UInt256` | `UInt256` |
| `String`, `Char` | `lsc: use Bytes[N]` | `Bytes[N]` |
| `List`, `Array` in state | `lsc: use Mapping` | `Mapping` |
| `IO`, `StateM`, `ST` | `lsc: stateful monads not allowed` | `ContractM E S` |
| Higher-order functions | `lsc: functions cannot be passed as arguments` | Top-level helpers |
| `structure … extends` | `lsc: storage inheritance not supported in v1` | Compose structs manually |
| Raw storage ops in author code | `lsc: storage IO is emitter-only` | `get` / `set` |

### §2.7 Fixed-point arithmetic (`Lsc.Ray` / `Lsc.Wad`) — planned

DeFi contracts routinely multiply and divide `UInt256` values that represent decimal fractions. `Lsc.Ray` and `Lsc.Wad` are the planned fixed-point libraries (scale 10²⁷ and 10¹⁸).

```lean4
def WAD : ℕ := 10^18
def RAY : ℕ := 10^27
```

Three explicit rounding variants per operation — no default aliases. All return `ContractM E S UInt256`:

```lean4
def rayMulDown   [LscError E] (a b : UInt256) : ContractM E S UInt256
def rayMulUp     [LscError E] (a b : UInt256) : ContractM E S UInt256
def rayMulHalfUp [LscError E] (a b : UInt256) : ContractM E S UInt256
-- same six defs with wad* prefix for Lsc.Wad
```

Bracket-pair notation: `a ⌊*⌋? b` (down), `a ⌈*⌉? b` (up), `a ⸢*⸣? b` (half-up). Scale from namespace — `open scoped Lsc.Ray` or `open scoped Lsc.Wad`.

---

## §3 State

### §3.1 Declaring contract state (`state!` and `contract!`)

Contract state is declared with **`state!`** and the monad alias with **`contract!`**. These are two separate macros.

```lean4
state! Counter where
  number : UInt256 @public
  paused : Bool

contract! Counter CounterError
-- expands to: abbrev Counter (α : Type) := ContractM CounterError Counter.State α
--             @[simp] def Counter.view : World → Counter.State := ContractState.view
```

`state! ModuleName where …` generates:
1. **`ModuleName.State` structure** — one field per declaration.
2. **`fields.x : Field ModuleName.State T`** — typed slot witnesses (offset only; used by `get`/`set`).
3. **`[ContractState ModuleName.State]` instance** — `self` (fixed to `defaultSelf` for now), `view` (projects `World` → `S`), `embed` (`S` → `World`).
4. **`[lsc.public]` tags** — `@public` fields are tagged for ABI getter synthesis.
5. **`@[simp]` unfolding theorems** — `view_unfold`, `embed_unfold`, `self_eq` so `simp` can fully reduce `ContractState.view` / `ContractState.embed`.

`contract! Mod Err` generates the monad alias and a `@[simp] def Mod.view` alias.

> **ERC-7201 namespacing** (planned — §3.3): the current implementation uses simple sequential offsets (0, 1, 2, …) via `Field S σ` with no namespace computation. ERC-7201 roots will replace raw offsets in the emitter.

**Default** (uses module name as namespace id when ERC-7201 is introduced):

```lean4
-- src/AMM.lean  →  namespace "AMM" (planned)
state! AMM where
  reserve0 reserve1 totalLP : UInt256
  lpBalances : Mapping Address UInt256
contract! AMM AMMError
```

**`@public` field annotation:** marks a field for ABI getter synthesis. Currently tags the `Field` constant with `[lsc.public]`; the codegen walker discovers it without generating extra functions.

```lean4
state! Counter where
  number : UInt256 @public   -- tagged [lsc.public]
  paused : Bool
```

### §3.2 Field access: `get` and `set`

Authors access contract storage via **`get`** (read) and **`set`** (write). These are typed wrappers over `ContractM.get` / `ContractM.set`, which resolve slot constants through the in-scope `ContractState` instance.

```lean4
-- single read
let n ← get .number

-- write
set .number n'
set .paused true
```

`get .field` and `set .field val` are macros that desugar to `ContractM.get fields.field` and `ContractM.set fields.field val`. The `fields.*` namespace is generated by `state!`.

**Bridge lemmas** (`@[simp]`):

```lean4
@[simp] def ContractM.get {E S σ} [ContractState S] [FromWord σ] (field : Field S σ) :
    ContractM E S σ :=
  fun w => .ok (FromWord.fromWord (World.getStorage w cs.self field.offset), w)

@[simp] def ContractM.set {E S σ} [ContractState S] [ToWord σ] (field : Field S σ) (val : σ) :
    ContractM E S Unit :=
  fun w => .ok ((), World.setStorage w cs.self field.offset (ToWord.toWord val))
```

**Word encoding** — `ToWord`/`FromWord` typeclasses bridge between Lean types and EVM storage words:

```lean4
class ToWord   (α : Type) where toWord   : α → UInt256
class FromWord (α : Type) where fromWord : UInt256 → α

instance : ToWord   UInt256 where toWord   := id
instance : FromWord UInt256 where fromWord := id
instance : ToWord   Bool    where toWord   := Bool.toWord   -- 0 or 1
instance : FromWord Bool    where fromWord := UInt256.toBool
```

**`require` — inline precondition guard:**

```lean4
require cond err
-- desugars to: unless cond do ContractM.revert err
```

**`failWhen` — revert when a flag is set:**

```lean4
def failWhen {E S} (b : Bool) (err : E) : ContractM E S Unit :=
  if b then ContractM.revert err else pure ()

-- Usage:
failWhen (← get .paused) .IsPausedError
```

Attempting to `get`/`set` on a name not declared in the schema is a validator error.

### §3.3 ERC-7201 namespaced storage (planned default layout)

Every `state!` block will be rooted at an **ERC-7201 namespace** in the emitter. Fields occupy sequential **offsets** `0, 1, 2, …` within that namespace.

**Namespace root formula** ([ERC-7201](https://eips.ethereum.org/EIPS/eip-7201)):
```
erc7201(id) = keccak256( keccak256(bytes(id)) − 1 ) & ~bytes32(0xff)
```

**Namespace id resolution:**

| Form | Namespace id |
|---|---|
| `state! Counter where` | module name (`"Counter"`) |
| `state! Counter @namespace "foo" where` *(planned)* | `"foo"` |

The current proof layer uses `defaultSelf : Address := Address.zero` and sequential slot offsets directly — no namespace root computation. The emitter will compute `erc7201(id)` once per namespace and lower `get`/`set` to `SLOAD`/`SSTORE` at `root + offset`.

**Compiler-reserved namespaces** (not in author `state!`): `"lsc.reentrancy.lock"` (reentrancy guard, §13.1), `"lsc.initialized"` (proxy init flag, §3.8).

`structure … extends` is **not supported**. Shared storage shapes are composed via nested layout fields (§3.7, planned).

### §3.4 State in contract functions vs theorems

| Context | How state is accessed | Form |
|---|---|---|
| Contract function body | `get` / `set` via typed slot constants | `let r ← get .reserve0` |
| Theorem statements (state snapshot) | `state!` struct fields directly | `s.number`, `s'.paused` |
| Theorem statements (world snapshot) | `Counter.view w` | `(Counter.view w).number` |
| Lemma bodies | `runS` + `simp [runS, increment, ...]` | unfold monad + `omega` |

The state struct never appears as a **contract function** parameter.

### §3.5 `@[lsc.initialize]` — planned

At most one initialization function per contract, called at deployment:

```lean4
@[lsc.initialize]
def initialize (name symbol : Bytes[32]) (decimals initialSupply : UInt256)
    (ctx : MsgContext) : ERC20 Unit := do
  set .name   name
  set .symbol symbol
  ...
```

The emitter generates an ABI constructor (not a named function).

### §3.6 Nested layout fields — planned

Lib modules declare reusable field shapes with `state!`. Deployable contracts nest layout types as fields to compose owned sub-state. Each nested field gets its own ERC-7201 namespace root.

```lean4
-- lib/VaultLedger.lean
state! VaultLedger where
  balances      : Mapping Address UInt256
  totalDeposits : UInt256

-- src/DualVault.lean
state! DualVault where
  vaultA : VaultLedger    -- erc7201:"DualVault.vaultA" (auto)
  vaultB : VaultLedger    -- erc7201:"DualVault.vaultB" (auto)
```

### §3.7 Proxy storage (`@proxy`) — planned

Proxy modules declare state with **`state! @proxy where`**. This is **not** ERC-7201. The compiler assigns **EIP-1967** standard slots by field name.

```lean4
state! @proxy where
  implementation : Address
  admin : Address
```

### §3.8 Schema versioning and migration — planned

Upgradeable implementations may carry `@[lsc.schema "Module/N"]` on `state!`. The validator enforces per-namespace migration rules: append-only (no reorder, retype, or remove). Artifact records each namespace with `id`, computed `root`, `fields`, `schemaId`, and `layout`.

---

## §4 Functions (Exports)

### §4.1 The `@[lsc.external]` annotation

Public ABI functions are declared with `@[lsc.external]`. The Lean `def` name **is** the ABI function name.

**Reentrancy lock (default, planned):** All `@[lsc.external]` functions will be **non-reentrant by default**. The emitter wraps each export with a contract-wide reentrancy lock (ERC-7201 namespace `"lsc.reentrancy.lock"`). Use `@[lsc.allow_reentrant]` to opt out.

```lean4
@[lsc.external]
def increment : Counter Unit := do
  failWhen (← get .paused) .IsPausedError
  let n ← get .number
  let n' ← n +? 1
  set .number n'
```

### §4.2 Mutators and views

| Return shape | Meaning |
|---|---|
| `ContractM E S Unit` | Mutator, no ABI return value |
| `ContractM E S V` | Mutator or view with return value |

Whether a function is a **mutator** or **view** is inferred from its operations:
- Functions with only `get` (no `set`, no `call`) → view; emitter generates `STATICCALL`-safe wrapper.
- Functions with any `set` or `call` → mutator; nonpayable by default.

### §4.3 ABI inference rules

| Return shape | Mutability | ABI return | ABI errors |
|---|---|---|---|
| `ContractM E S Unit` (stores only) | nonpayable | none | `E` variants |
| `ContractM E S UInt256` (stores) | nonpayable | `uint256` | `E` variants |
| `ContractM E S Bool` (stores) | nonpayable | `bool` | `E` variants |
| `ContractM E S UInt256` (reads only) | view | `uint256` | `E` variants |

### §4.4 Parameter filtering

| Parameter kind | ABI | Rule |
|---|---|---|
| `ctx : MsgContext` | excluded | Bound to message/block context (§5.1) |
| All primitive types | included | In declaration order |

---

## §5 Message Context and ETH Handling

### §5.1 The `MsgContext` type — planned

```lean4
structure MsgContext where
  caller    : Address
  value     : UInt256   -- msg.value
  timestamp : UInt256   -- block.timestamp
  number    : UInt256   -- block.number
```

Any parameter of type `MsgContext` is excluded from ABI calldata. The emitter binds all fields from EVM opcodes at each export boundary. Parameter name convention: `ctx`.

`self : Address` is an **ambient identifier** — the executing contract's own address (Solidity `address(this)`). Not a `state!` field.

### §5.2 ETH handling — planned

Payable functions: `@[lsc.payable]` on `@[lsc.external]`.
ETH transfers out: `native_transfer! to amount` (reverts on failure).
Receive/fallback: `@[lsc.receive]` / `@[lsc.fallback]`.

---

## §6 Events — planned

Events are declared as structs with `deriving Lsc.Event.EvmEvent`, emitted via `Free.liftF (.emit ...)` in `do`-blocks. Each call on a path that reaches `.ok` fires its `LOG` opcodes in source order.

Proof mode: `World.runCollect` accumulates logs in source order for event correctness theorems.

---

## §7 Revert

`.error e` paths produce `REVERT` with `abi.encode(e)`; no storage is committed. This falls out of the `Except` short-circuit — the `World` value is not returned on error paths.

`require cond e` desugars to `unless cond do ContractM.revert e`.

`failWhen b e` desugars to `if b then ContractM.revert e else pure ()`.

---

## §8 External Calls — planned (v2b)

> **v1 status:** external call plumbing (`call`, `staticcall`, `native_transfer!`) is specified here but full emitter support lands in v2b.

### §8.1 World and accounts

```lean4
structure World where
  storage : Address → Nat → UInt256
  balance : Address → UInt256
  code    : Address → ByteArray
```

### §8.2 Interface cast, `staticcall`, `call`

```lean4
let bal ← staticcall (tokenAddr : IERC20).balanceOf who   -- read-only
let ok  ← call (tokenAddr : IERC20).transferFrom from to amount  -- mutating
```

Callee revert maps to `.error (.extern ...)` via the `extern` constructor (required on the error type when `call` is used).

### §8.3–8.7

Proof tiers (state snapshot / scene snapshot / full simulation), reentrancy and CEI, registered vs assumed callees, and `delegatecall` / upgradeable proxies — see original spec sections; no implementation changes yet.

---

## PART II — THE PROOF SYSTEM

---

## §9 Proof Files

### §9.1 Lemma files (`test/*Lemma.lean`)

Lemma files are **AI-generated**. They import the contract module and contain:

- **`lemma` proofs** with full tactic bodies
- Action model scaffolding (`inductive Action`, `applyAction`, `applyActions`) for sequence invariants

No `sorry`. Kernel-checked.

**Proof recipe for state-snapshot theorems:**

```lean4
lemma increment_increases_number_when_unpaused
    (s s' : Counter.State) (hp : ¬s.paused)
    (h : runS increment s = .ok ((), s')) :
    s'.number.val = s.number.val + 1 := by
  by_cases hlt : s.number.val + 1 < 2 ^ 256
  · simp [runS, increment, failWhen, hp, UInt256.addCheckedNat, dif_pos hlt] at h
    subst h; rfl
  · exfalso
    simp [runS, increment, failWhen, hp, UInt256.addCheckedNat, dif_neg hlt,
          ContractM.arithFail] at h
```

**Proof recipe for revert conditions:**

```lean4
lemma increment_errors_when_paused
    (s : Counter.State) (hp : s.paused) :
    runS increment s = .error (.contract .IsPausedError) := by
  have hpt : s.paused = true := hp
  simp [runS, increment, failWhen, hpt, ContractM.revert, ContractM.revertFail]
```

**`simp` set for unfolding contract `do` blocks:** `[runS, functionName, get, set, ContractState.view, ContractState.embed, ...]`. The `@[simp]` lemmas generated by `state!` (`view_unfold`, `embed_unfold`, `self_eq`) plus `World.getStorage_setStorage` / `World.getStorage_setStorage_ne` close most goals after `omega`.

#### Sequence invariants and `Lsc.Invariant` — planned

```lean4
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
/-- When unpaused, increment increases number by exactly 1. -/
theorem increment_increases_number_when_unpaused (s s' : Counter.State) (hp : ¬s.paused)
    (h : runS increment s = .ok ((), s')) :
    s'.number.val = s.number.val + 1 ∧ s'.paused = s.paused :=
  CounterProofs.increment_increases_number_when_unpaused s s' hp h
```

### §9.3 Naming convention

- `{function}_{property}` for single-call properties: `increment_increases_number_when_unpaused`, `increment_errors_when_paused`
- `{subject}_{invariant}` for sequence invariants: `k_nondecreasing`, `totalSupply_constant`

### §9.4 Requirements checklist

Every mutating export should have at minimum:

1. A **success theorem** — `(h : runS f s = .ok ((), s'))` — what holds after the call
2. A **revert theorem** — `(h : runS f s = .error e)` — what inputs cause each revert

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

### §9.7 Writing theorem statements

Theorem files should read like a protocol specification. Use `Module.State` field names directly (`s'.number`, `s.paused`). Reasoning about `.val` is fine inside theorem statements when needed for numeric properties. Named invariant helpers (like `def k (s : AMM.State) : ℕ := ...`) belong in `*Theorem.lean`.

---

## §10 Proof Helpers

### §10.1 Layer 1 — Pure (default)

Lemmas proved directly over `@[lsc.external]` functions using `simp [runS, f, ContractM.get, ContractM.set, ...]`, `omega`, and `Mapping` lemmas (when available).

**Useful simp lemmas from `Lsc.World`:**
```lean4
@[simp] theorem World.getStorage_setStorage (w : World) (addr : Address) (slot : Nat) (v : UInt256) :
    getStorage (setStorage w addr slot v) addr slot = v

@[simp] theorem World.getStorage_setStorage_ne (w : World) (addr : Address)
    {s₁ s₂ : Nat} (v : UInt256) (h : s₁ ≠ s₂) :
    getStorage (setStorage w addr s₁ v) addr s₂ = getStorage w addr s₂
```

**`Except` discriminators:**
```lean4
@[simp] theorem Except.ok_ne_error {E A : Type} (a : A) (e : E) :
    (Except.ok a : Except E A) ≠ Except.error e := by simp
```

### §10.2 Layer 2 — Wrapped (export bridge) — planned

Used when a lemma must reason about compiler-generated export wrappers. Most contracts do not need this layer.

### §10.3 Layer 3 — Composed (cross-contract, v2b) — planned

> **TODO v2b:** `simulate_call` threads `World` through callees and composes callee theorems with caller theorems.

---

## §11 Compliance Manifests — planned

```toml
[lsc.compliance.erc20]
theorems = "test/ERC20Theorem.lean"
required = [
  "transfer_preserves_total_supply",
  "transfer_no_overdraft",
  ...
]
```

For each listed name the runner checks: a `theorem <name>` exists in the corresponding `*Theorem.lean`; the body is a one-line `*Lemma.<name>` delegation; and the homonymous `lemma` typechecks.

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
| `IO`, `StateM`, `ST` | error | `lsc: stateful monads not allowed; use ContractM E S` |
| Higher-order functions | error | `lsc: functions cannot be passed as arguments` |
| Unbounded recursion | error | `lsc: recursive function must be structurally terminating` |
| `List` or `Array` in author code | error | `lsc: use Mapping` |
| `structure … extends` | error | `lsc: storage inheritance not supported in v1` |
| Hand-written export wrapper | error | `lsc: use @[lsc.external]` |
| Raw `sload`/`sstore`/etc. in author code | error | `lsc: storage IO is emitter-only; use get/set` |
| `error!` type missing `arith` constructor | error | `lsc: error type must include arith : ArithError → E` |
| `error!` type missing `extern` constructor when `call` used | error | `lsc: error type must include extern : ExternError → E` |
| Invalid `@[lsc.external]` return shape | error | `lsc: must return ContractM E S α` |
| `state!` with zero fields | warning | `lsc: empty state struct` |
| `get`/`set` on name not in `state!` schema | error | `lsc: unknown storage slot` |
| More than one `state!` per module | error | `lsc: at most one state! per contract module` |
| More than one `@[lsc.initialize]` | error | `lsc: at most one @[lsc.initialize] per contract module` |
| `call`/`staticcall` in proof files | error | `lsc: extern calls not allowed in proof files` |
| `store` after interaction in export transitive closure | warning | `lsc: set after call violates CEI; add @[lsc.allow_store_after_call]` |

### §12.2 Proof module rules

| Condition | Severity |
|---|---|
| `sorry` | error |
| `axiom` without `@[extern_assume]` | warning |
| `theorem` with no homonymous `lemma` | error (typecheck) |
| `lemma` with no matching `theorem` | warning (helper lemma) |

---

## §13 Emitter and Lowering

### §13.1 Export wrapper generation

For each `@[lsc.external] def f : ContractM E S α`, the emitter generates:

1. **ABI dispatcher** — 4-byte selector; ABI-decode calldata.
2. **`MsgContext` binding** — `ctx.caller := CALLER`, etc.
3. **Reentrancy lock** (unless `@[lsc.allow_reentrant]`) — one contract-wide slot in `"lsc.reentrancy.lock"`.
4. **Execute** — lower `f`'s `ContractM` term to Yul in source order.
5. **On `.ok (v, w')`** — ABI-encode `v`; `RETURN`.
6. **On `.error e`** — `REVERT` with `abi.encode(e)`; lock cleared; no storage from the failing path persists.

### §13.2 Storage layout derivation

**Sequential slot offsets (current):** fields map to offset `0, 1, 2, …` at `defaultSelf` in declaration order.

**ERC-7201 namespaces (planned):** each namespace id maps to root `erc7201(id)`. Fields map to `root + offset`. Mapping entries at `keccak256(abi.encode(key, root + offset))` — identical to Solidity layout.

**Proxy modules** (`@proxy`, planned): fields map to EIP-1967 fixed slots.

### §13.3 Formal verification of lowering — planned

```lean4
-- State: compiled export matches ContractM run
theorem lowering_correct {E S α : Type} (f : ContractM E S α) (w : World) :
    evmExecute (compile f) w = f w

-- Logs: compiled LOG opcodes match runCollect (source order)
theorem lowering_logs_correct ...

-- Storage layout matches Solidity for all field types
theorem slot_layout_matches_solidity ...
```

---

## §14 Full AMM Example

```lean4
import Lsc.Prelude
open Lsc

error! AMMError where
  | uninitializedPool
  | zeroInput
  | zeroOutput
  | insufficientLp
  | arith : ArithError → AMMError
  -- planned: | extern : ExternError → AMMError

state! AMM where
  reserve0 reserve1 totalLP : UInt256
  lpBalances : Mapping Address UInt256
  -- planned: token0 token1 : IERC20  (external refs)

contract! AMM AMMError

private def computeAmountOut (reserveIn reserveOut amountIn : UInt256) : AMM UInt256 := do
  -- planned: use *? and /? when implemented
  sorry

@[lsc.external]
def swap (ctx : MsgContext) (zeroForOne : Bool) (amountIn : UInt256) : AMM UInt256 := do
  require (amountIn > 0) .zeroInput
  let r0 ← get .reserve0
  let r1 ← get .reserve1
  require (r0 > 0 ∧ r1 > 0) .uninitializedPool
  -- ... (external call support planned for v2b)
  sorry
```

The theorem file structure follows §9.2 — one theorem per requirement, each delegating to a homonymous lemma.

---

## Appendix A — Design Decisions

### A.1 Why `ContractM E S α = StateT World (Except (ContractError E)) α` instead of a free monad

The original spec called for a free monad (`World E α = Free WorldF E`). After implementation, we chose the concrete `StateT` formulation. Both model state access and rollback-on-error. The key trade-offs:

| | Free monad | `StateT World (Except E)` |
|---|---|---|
| Rollback on error | ✓ | ✓ |
| Multiple interpreters | ✓ | — |
| EVM codegen handler | ✓ (planned) | ✓ (direct lowering) |
| `simp` reduces cleanly | ✓ (via bridge lemmas) | ✓ (directly) |
| Proof ergonomics | needs bridge lemmas | `simp [runS, f, ...]` + `omega` |
| Lean elaboration complexity | higher | lower |

The `StateT` formulation is simpler to elaborate in Lean 4 and reduces proof friction — `simp [runS, f, ...]` + `omega` closes most goals without needing intermediate bridge lemmas for each operator. The phantom type `S` preserves the strong per-contract typing that the free monad's `E` parameter provided.

Future: if multiple-interpreter semantics (trace, EVM, test) become compelling, we may introduce a thin free monad layer on top while keeping the `StateT` proof model intact.

### A.2 Why `state!` struct as schema, not passed state in contract functions

Passing `s : AMM.State` as a **contract function parameter** was clean for proofs but mismatched EVM semantics. The `state!` model aligns authoring with EVM reality:

- Authors think in named fields (`get .reserve0`, `set .reserve0 v`) not slot numbers
- The compiler owns the slot assignment
- The same struct is the **proof snapshot** in theorem files (`s s' : AMM.State`, `s'.reserve0`)
- The schema is the single source of truth for both codegen and proofs

### A.3 Why no inheritance

`structure … extends` creates slot-layout ambiguity in upgradeable proxy patterns. LSC composes storage via nested layout fields (§3.6) with per-instance ERC-7201 namespaces — explicit, collision-free, and proof-friendly. Vyper takes the same position on `extends`.

### A.4 Why contract-wide lock + CEI linter (not type-level CEI)

Type-level enforcement of checks-effects-interactions was considered and rejected for v1. It adds elaborator complexity, hurts `do`-notation ergonomics, and fights the common guarded pattern that the reentrancy lock already makes safe.

| Layer | Mechanism | Role |
|---|---|---|
| **Primary** | Contract-wide reentrancy lock on default exports | Blocks reentry during external calls |
| **Guidance** | CEI linter (warning, interprocedural) | Nudges toward effects-before-interactions |
| **Opt-out** | `@[lsc.allow_store_after_call]` + `cei:` comment | Suppresses warning when non-CEI is intentional |

### A.5 Why ERC-7201 namespaced storage

Sequential slot-0 layout makes multi-layout composition and upgrades fragile. ERC-7201 gives each namespace an isolated root derived from a string id — lib layouts, nested instances, and contract scalars coexist without collision. Authors keep `get`/`set` syntax; the compiler owns root computation.
