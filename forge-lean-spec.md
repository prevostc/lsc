# forge-lean — Full System Specification

**Version:** 1.0  
**Lean toolchain:** `leanprover/lean4:stable` (pinned at project init time, recorded in `lean-toolchain`)  
**ERC scope:** ERC-20 only  
**Status:** This document is complete and decision-free. Every ambiguity has been resolved.

---

## 1. Overview

`forge-lean` is a Foundry plugin that allows smart contracts to be written in Lean 4, compiled to EVM bytecode via Yul, and formally verified using human-authored theorem statements and LLM-generated proofs. It mirrors the design philosophy of `forge-vyper`.

The system has three concerns that are kept strictly separate:

1. **Contracts** — Lean 4 source files that define contract logic as pure state transition functions
2. **Specs** — Human-authored Lean 4 theorem statements (no proof terms) that express what the contract must guarantee
3. **Proofs** — LLM-generated Lean 4 proof terms that discharge the theorem statements

Specs are reviewed by humans. Proofs are trusted to Lean's kernel — if Lean accepts them, they are correct.

---

## 2. Repository Layout

A Foundry project with `forge-lean` follows this layout:

```
my-project/
├── foundry.toml
├── lean-toolchain              # pinned Lean toolchain string, e.g. leanprover/lean4:v4.x.0
├── src/
│   ├── Token.sol               # Solidity contracts (unchanged)
│   └── Token.lean              # Lean 4 contracts (new)
├── spec/
│   └── Token.spec.lean         # Human-authored theorem statements (no proof terms)
├── test/
│   ├── Token.t.sol             # Solidity/Foundry tests (unchanged)
│   └── Token.proof.lean        # LLM-generated proof terms
└── out/
    ├── Token.sol/              # Solidity build artifacts (unchanged)
    └── Token.lean/             # Lean build artifacts
        ├── Token.yul           # emitted Yul (intermediate, inspectable)
        ├── Token.bin           # EVM bytecode
        └── Token.abi           # ABI JSON
```

### Rules

- Every `.lean` file under `src/` is a contract. One contract per file.
- Every `.spec.lean` file under `spec/` corresponds to a contract of the same base name under `src/`.
- Every `.proof.lean` file under `test/` corresponds to a `.spec.lean` file of the same base name under `spec/`.
- The `lean-toolchain` file at the project root pins the exact Lean version used. `forge-lean init` creates it. `forge-lean` refuses to run if this file is missing.

---

## 3. The Lean Contract Model

### 3.1 Primitive Types

The validator permits exactly the following primitive types. Any other type is a hard error.

| Lean 4 type | EVM / Yul type | Notes |
|---|---|---|
| `UInt256` | `uint256` | all arithmetic is `mod 2^256` |
| `Address` | `uint256` | distinct newtype, not interchangeable with `UInt256` |
| `Bool` | `uint256` (0 or 1) | only at ABI boundary |
| `Bytes32` | `uint256` | raw 32-byte value, no string ops |

`Address` is defined in the `ForgeLean.Prelude` library as:

```lean
structure Address where
  val : UInt256
  deriving DecidableEq, Repr
```

It is not coercible to `UInt256` without an explicit `.val` projection. This prevents accidental mixing in proofs.

### 3.2 Composite Types

Only the following composite forms are allowed:

- **Structs** whose fields are all primitive or allowed composite types → storage state
- **`Option α`** where `α` is a struct or primitive → represents revert (`none`) or success (`some`)
- **`α × β`** (products/tuples) **only at the ABI boundary** — disallowed in internal functions
- **`StorageMapping K V`** where `K` and `V` are primitives → EVM mapping

Recursive types, inductive types with more than 2 constructors, and type parameters are not allowed.

### 3.3 Storage State

Contract storage is modeled as a plain Lean 4 struct. Fields are assigned sequential storage slots in declaration order, starting at slot 0. Mappings use Solidity's `keccak256(abi.encode(key, slot))` scheme.

```lean
structure ERC20State where
  totalSupply : UInt256          -- slot 0
  balances    : StorageMapping Address UInt256   -- slot 1 (keys hashed as keccak256(addr ++ 1))
  allowances  : StorageMapping Address (StorageMapping Address UInt256)  -- slot 2
```

The slot layout is deterministic and declared in the ABI output so external tools can read storage directly.

**Non-aliasing is trivially provable** by the sequential slot assignment: `slot(totalSupply) = 0 ≠ 1 = slot(balances)` by `decide`.

The single axiom governing mapping key injection is:

```lean
axiom StorageMapping.key_injective {K V : Type} [DecidableEq K]
    (m : StorageMapping K V) (a b : K) (s : UInt256) :
    storageKey a s = storageKey b s → a = b
```

This axiom is stated once in `ForgeLean.Prelude` and is the only axiom in the system.

### 3.4 State Threading

State is threaded **explicitly** as a pure function argument and return value. Monads are not allowed. Every internal function that reads or writes state takes the state struct as its first argument and returns `Option StateStruct`.

```lean
-- ✅ Correct — explicit state threading
def transfer (s : ERC20State) (from to : Address) (amount : UInt256) : Option ERC20State

-- ❌ Rejected by validator — monadic style
def transfer (from to : Address) (amount : UInt256) : StateM ERC20State Unit
```

This is the canonical form. All proofs are written against this shape.

### 3.5 The `@[evm_export]` Annotation

Functions that are part of the contract's public ABI are annotated with `@[evm_export]`. These functions are the only ones that appear in the generated ABI JSON. Internal helpers are not annotated.

The `@[evm_export]` annotation carries the ABI selector explicitly:

```lean
@[evm_export "transfer(address,address,uint256)"]
def transfer (s : ERC20State) (from to : Address) (amount : UInt256)
    : Option (ERC20State × Bool) :=
  match transferInternal s from to amount with
  | none    => none
  | some s' => some (s', true)
```

The string argument is the canonical ABI signature. `forge-lean` computes the 4-byte selector from it via `keccak256` and inserts it into the Yul dispatcher. If the string is malformed, `forge-lean build` fails with an error.

### 3.6 ABI Wrapper Convention

The ERC-20 ABI requires several functions to return `Bool`. The pattern is:

- Write the internal logic as `Option ERC20State`
- Write a thin `@[evm_export]` wrapper that lifts to `Option (ERC20State × Bool)` where the `Bool` is always `true`

The `Bool` in `Option (ERC20State × Bool)` is **always discarded by the emitter** and compiled to `mstore(0, 1); return(0, 32)`. It exists solely for ABI compatibility.

### 3.7 Rejected Constructs

The validator hard-rejects the following with a descriptive error message. These are not warnings.

| Construct | Error message |
|---|---|
| Closures / lambda capturing an outer variable | `forge-lean: closures are not supported; use a top-level function` |
| Partial application (`pap` IR node) | `forge-lean: partial application is not supported` |
| `Nat`, `Int`, `Float`, `String`, `Char` | `forge-lean: type Nat is not allowed; use UInt256` |
| `IO`, `StateM`, any monad | `forge-lean: monadic code is not allowed; use explicit state passing` |
| Higher-order functions | `forge-lean: functions cannot be passed as arguments` |
| Unbounded recursion | `forge-lean: recursive function X must be structurally terminating` |
| Tuples in internal functions | `forge-lean: tuples are only allowed in @[evm_export] return types` |
| Type parameters unresolved after monomorphization | `forge-lean: polymorphic function X cannot be compiled` |

---

## 4. The Spec File

### 4.1 Purpose and Authorship

The spec file (`spec/Token.spec.lean`) contains **only theorem statements**. It has no proof terms. It is written and reviewed by humans. It is the artifact that encodes what the contract is supposed to do.

### 4.2 Format

A spec file is a valid Lean 4 file that:

- Imports the contract file: `import src.Token`
- Imports the proof helpers: `import ForgeLean.ProofHelpers`
- Contains only `theorem` declarations with `sorry` as the proof term

```lean
import src.Token
import ForgeLean.ProofHelpers

-- Every theorem uses sorry as a placeholder.
-- The actual proof terms live in test/Token.proof.lean.

theorem transfer_preserves_total_supply
    (s : ERC20State) (from to : Address) (amount : UInt256)
    (s' : ERC20State)
    (h : transferInternal s from to amount = some s') :
    s'.totalSupply = s.totalSupply := by
  sorry

theorem transfer_no_overdraft
    (s : ERC20State) (from to : Address) (amount : UInt256)
    (h : s.balances.get from < amount) :
    transferInternal s from to amount = none := by
  sorry

theorem transfer_no_creation
    (s : ERC20State) (from to : Address) (amount : UInt256)
    (hne : from ≠ to) (s' : ERC20State)
    (h : transferInternal s from to amount = some s') :
    s'.balances.get from + s'.balances.get to =
    s.balances.get from + s.balances.get to := by
  sorry
```

`forge-lean check-spec spec/Token.spec.lean` verifies that the spec file is well-formed (valid Lean, all theorems typecheck with `sorry`, no proof terms present). This command is run in CI.

### 4.3 What Specs Must Cover for ERC-20 Compliance

For a contract to be considered ERC-20 compliant by `forge-lean`, its spec file **must** contain theorems for the following properties. The names are fixed — `forge-lean` looks them up by name.

| Required theorem name | What it states |
|---|---|
| `transfer_preserves_total_supply` | `totalSupply` is unchanged after a successful transfer |
| `transfer_no_overdraft` | transfer fails if sender balance is insufficient |
| `transfer_no_creation` | sender balance decrease equals receiver balance increase |
| `approve_sets_allowance` | allowance is set to the exact requested amount |
| `transferFrom_respects_allowance` | transferFrom fails if allowance is insufficient |
| `transferFrom_decrements_allowance` | allowance decreases by the transferred amount |

Missing any of these causes `forge-lean build` to print a warning (not an error).

---

## 5. The Proof File

### 5.1 Purpose and Authorship

The proof file (`test/Token.proof.lean`) contains the proof terms that discharge the theorems declared in the spec file. It is generated by an LLM and **not reviewed by humans**. Correctness is guaranteed by Lean's kernel — if the file compiles without errors and without `sorry`, the proofs are valid.

### 5.2 Format

```lean
import spec.Token
-- No sorry allowed in this file. forge-lean enforces this.

theorem transfer_preserves_total_supply
    (s : ERC20State) (from to : Address) (amount : UInt256)
    (s' : ERC20State)
    (h : transferInternal s from to amount = some s') :
    s'.totalSupply = s.totalSupply := by
  simp [transferInternal] at h
  split_ifs at h <;> simp_all

-- ... remaining proofs
```

`forge-lean` enforces that proof files contain no `sorry`. A proof file containing `sorry` is treated as a proof failure.

---

## 6. Proof Helper Library (`ForgeLean.ProofHelpers`)

This library ships with `forge-lean` and is automatically available. It provides the membrane between the multi-return ABI layer and the clean single-return internal model.

### 6.1 Core Helpers

```lean
namespace ForgeLean

-- Strip the ceremonial Bool from a StateBool result.
-- Use this to lift proofs from the internal model to the ABI wrapper.
theorem lift_to_abi {S : Type} {f : S → Option S} {g : S → Option (S × Bool)}
    (hg : ∀ s s', f s = some s' → g s = some (s', true))
    (s s' : S) (b : Bool)
    (h : g s = some (s', b)) :
    f s = some s' := by
  have := hg s s'
  simp [Option.map] at h ⊢
  cases b <;> simp_all

-- Compose two successful state transitions.
theorem compose {S : Type} (f g : S → Option S)
    (s s'' : S) (s' : S)
    (hf : f s = some s')
    (hg : g s' = some s'') :
    ∃ smid, f s = some smid ∧ g smid = some s'' :=
  ⟨s', hf, hg⟩

-- The revert case needs no proof — EVM guarantees state is unchanged.
-- This theorem documents that intent explicitly.
theorem revert_preserves_state {S : Type} {f : S → Option S} {s : S}
    (h : f s = none) : True := trivial

end ForgeLean
```

### 6.2 The `erc_cases` Tactic

This tactic handles the standard proof shape for ERC functions: destruct the `Option`, dismiss the `none` branch automatically, and leave the `some` branch as the goal.

```lean
macro "erc_cases" h:ident : tactic => `(tactic|
  (cases $(h) with
   | none => simp_all
   | some p =>
       obtain ⟨s', b⟩ := p
       cases b <;> simp_all))
```

Usage:

```lean
theorem transfer_preserves_supply ... (h : transfer_abi s from to amount = some (s', true)) := by
  erc_cases h
  -- goal is now about s' : ERC20State with no Option or Bool noise
  simp [transferInternal]
  omega
```

### 6.3 `StorageMapping` API

```lean
structure StorageMapping (K V : Type) where
  -- opaque; only accessed via get/set
  inner : K → V

def StorageMapping.get {K V : Type} (m : StorageMapping K V) (k : K) : V :=
  m.inner k

def StorageMapping.set {K V : Type} (m : StorageMapping K V) (k : K) (v : V)
    : StorageMapping K V :=
  { inner := fun k' => if k' == k then v else m.inner k' }

-- Key lemma: get after set returns the set value
@[simp] theorem StorageMapping.get_set_same {K V : Type} [DecidableEq K]
    (m : StorageMapping K V) (k : K) (v : V) :
    (m.set k v).get k = v := by simp [StorageMapping.get, StorageMapping.set]

-- Key lemma: get after set for a different key is unchanged
@[simp] theorem StorageMapping.get_set_other {K V : Type} [DecidableEq K]
    (m : StorageMapping K V) (k k' : K) (v : V) (h : k' ≠ k) :
    (m.set k v).get k' = m.get k' := by simp [StorageMapping.get, StorageMapping.set, h]
```

These `@[simp]` lemmas mean that most mapping-related goals discharge with `simp` alone.

---

## 7. The Compiler Pipeline

### 7.1 Stages

```
src/Token.lean
      │
      ▼  stage 1: Lean 4 type checking + elaboration
      │           (lean --make, standard Lean toolchain)
      ▼
  Lean IR (λRC)
      │
      ▼  stage 2: forge-lean validator
      │           (rejects disallowed constructs, hard errors)
      ▼
  Validated IR
      │
      ▼  stage 3: forge-lean Yul emitter
      │           (Lean IR → Yul text)
      ▼
  out/Token.lean/Token.yul
      │
      ▼  stage 4: solc (bundled with Foundry via foundry-compilers)
      │           solc --strict-assembly Token.yul
      ▼
  out/Token.lean/Token.bin
  out/Token.lean/Token.abi
```

### 7.2 Yul Emitter Mapping

| Lean IR construct | Yul output |
|---|---|
| `UInt256` literal `n` | `0xN` (hex) |
| Local variable `x` | `x` |
| `if c then t else f` | `switch c case 1 { ... } default { ... }` |
| `match opt with \| none => ... \| some x => ...` | `switch iszero(opt_tag) case 1 { ... } default { let x := opt_val ... }` |
| Function call `f a b` | `f(a, b)` |
| Struct field read `s.field` | `sload(add(s_base, field_offset))` |
| Struct field write (returns new struct) | `sstore(add(s_base, field_offset), val)` |
| `StorageMapping.get m k` | `sload(storageKey(k, m_slot))` |
| `StorageMapping.set m k v` (returns new mapping) | `sstore(storageKey(k, m_slot), v)` |
| `Option.none` | `0` in tag position |
| `Option.some x` | `1` in tag position, `x` in value position |
| `none` in `@[evm_export]` function | `revert(0, 0)` |
| `some (s', true)` in `@[evm_export]` function | storage writes for `s'`, then `mstore(0, 1); return(0, 32)` |

### 7.3 Yul Object Structure

Every contract compiles to a standard two-object Yul structure:

```yul
object "Token" {
  code {
    datacopy(0, dataoffset("runtime"), datasize("runtime"))
    return(0, datasize("runtime"))
  }
  object "runtime" {
    code {
      -- ABI dispatcher
      let sel := shr(224, calldataload(0))
      switch sel
      case 0xSELECTOR1 { ... }
      case 0xSELECTOR2 { ... }
      default { revert(0, 0) }

      -- Internal functions
      function funcName(arg0, arg1) -> ret { ... }

      -- Storage key helper (always emitted)
      function storageKey(key, slot) -> h {
        mstore(0, key)
        mstore(32, slot)
        h := keccak256(0, 64)
      }
    }
  }
}
```

### 7.4 ABI JSON Generation

The ABI JSON is generated from the `@[evm_export]` annotations. The format follows the standard Ethereum ABI JSON specification. Types map as follows:

| Lean 4 type | ABI type |
|---|---|
| `UInt256` | `uint256` |
| `Address` | `address` |
| `Bool` | `bool` |
| `Bytes32` | `bytes32` |
| `Option (S × Bool)` (return) | `bool` (only the Bool is in the ABI) |
| `Option S` where S is a state struct (return) | no return value (void, reverts on failure) |

---

## 8. The `forge-lean` CLI

### 8.1 Binary

`forge-lean` is a Rust binary. It is distributed as a Foundry plugin following the same convention as `forge-vyper`: a binary named `forge-lean` on `PATH` that Foundry discovers automatically.

### 8.2 Commands

#### `forge-lean build`

Runs the full pipeline (stages 1–4) for all `.lean` files under `src/`. Outputs artifacts to `out/<name>.lean/`.

- Fails if stage 2 (validator) rejects any construct.
- Fails if stage 1 (Lean type checking) fails.
- Fails if stage 4 (solc) fails.
- Warns (does not fail) if required ERC-20 compliance theorems are missing from the corresponding spec file.
- Exits 0 on success, 1 on any error.

#### `forge-lean test`

Runs proof checking for all `.proof.lean` files under `test/`.

- Invokes `lean --make` on each proof file.
- Fails if any proof file contains `sorry`.
- Fails if Lean rejects any proof term.
- Reports each theorem as PASS or FAIL, mirroring `forge test` output format.
- Does **not** block or affect `forge-lean build`. Proof failures are reported independently.
- Exits 0 if all proofs pass, 1 if any fail.

#### `forge-lean check-spec <file>`

Validates a spec file:

- All theorems typecheck with `sorry`.
- No proof terms are present (only `sorry` is allowed as proof).
- File imports are correct.
- Exits 0 on success, 1 on failure.

#### `forge-lean init`

Initializes a Foundry project for `forge-lean`:

- Creates `lean-toolchain` with the current stable Lean version.
- Creates `spec/` and `test/` directories if absent.
- Adds `forge-lean build` to the `[build]` hook in `foundry.toml`.
- Adds `forge-lean test` to the `[test]` hook in `foundry.toml`.

### 8.3 Integration with Foundry Hooks

After `forge-lean init`, `foundry.toml` contains:

```toml
[build]
extra_output = ["forge-lean build"]

[test]
extra_output = ["forge-lean test"]
```

This means:

- `forge build` runs `forge-lean build` automatically for `.lean` files.
- `forge test` runs both Solidity tests and `forge-lean test` (Lean proof checking). Results are shown in separate sections. Lean proof failures do not affect the Solidity test exit code and vice versa.

### 8.4 solc Dependency

`forge-lean` uses the `solc` binary that ships with the user's Foundry installation, accessed via the `foundry-compilers` crate. No separate `solc` installation is required. The Foundry-pinned `solc` version is used. If Foundry is not installed, `forge-lean build` fails with: `forge-lean: foundry not found; install foundry to use forge-lean`.

---

## 9. ERC-20 Prelude

`forge-lean` ships a `ForgeLean.ERC20` module that provides the standard types and the ERC-20 typeclass. Contracts import this instead of writing boilerplate.

```lean
import ForgeLean.Prelude

-- Standard ERC-20 state. Contracts may extend this struct.
structure ERC20State where
  totalSupply : UInt256
  balances    : StorageMapping Address UInt256
  allowances  : StorageMapping Address (StorageMapping Address UInt256)

-- Typeclass encoding the ERC-20 interface
-- A contract satisfies ERC20 if it provides these functions with these types.
class ERC20 (S : Type) where
  transfer     : S → Address → Address → UInt256 → Option S
  transferFrom : S → Address → Address → Address → UInt256 → Option S
  approve      : S → Address → Address → UInt256 → Option S
  balanceOf    : S → Address → UInt256
  totalSupply  : S → UInt256
  allowance    : S → Address → Address → UInt256
```

---

## 10. Error Message Reference

All error messages from `forge-lean` are prefixed with `forge-lean:` and include the file, line, and column of the offending construct.

| Condition | Message |
|---|---|
| Closure in contract code | `forge-lean: closures are not supported; use a top-level function` |
| Partial application | `forge-lean: partial application is not supported` |
| Disallowed type `T` | `forge-lean: type T is not allowed; use UInt256, Address, Bool, or Bytes32` |
| Monadic code | `forge-lean: monadic code is not allowed; use explicit state passing` |
| Higher-order function | `forge-lean: functions cannot be passed as arguments` |
| Non-structural recursion | `forge-lean: recursive function X must be structurally terminating` |
| Tuple in internal function | `forge-lean: tuples are only allowed in @[evm_export] return types` |
| Unresolved polymorphism | `forge-lean: polymorphic function X cannot be compiled` |
| `sorry` in proof file | `forge-lean: proof file contains sorry; proofs must be complete` |
| Malformed ABI signature | `forge-lean: invalid ABI signature "..."; expected form "name(type,type)"` |
| Missing `lean-toolchain` | `forge-lean: lean-toolchain file not found; run forge-lean init` |
| Foundry not found | `forge-lean: foundry not found; install foundry to use forge-lean` |
| Missing ERC-20 theorem | `forge-lean: warning: spec/X.spec.lean is missing required theorem Y` |

---

## 11. Complete ERC-20 Example

This is the canonical example that ships with `forge-lean` as a template. It is fully self-contained and correct.

### `src/Token.lean`

```lean
import ForgeLean.ERC20
import ForgeLean.ProofHelpers

open ForgeLean

-- Internal transfer logic. All proofs are written against this function.
def transferInternal (s : ERC20State) (from to : Address) (amount : UInt256)
    : Option ERC20State :=
  if s.balances.get from < amount then none
  else some { s with
    balances :=
      s.balances
        |>.set from (s.balances.get from - amount)
        |>.set to   (s.balances.get to   + amount) }

def approveInternal (s : ERC20State) (owner spender : Address) (amount : UInt256)
    : Option ERC20State :=
  some { s with
    allowances := s.allowances.set owner
      (s.allowances.get owner |>.set spender amount) }

def transferFromInternal (s : ERC20State) (caller from to : Address) (amount : UInt256)
    : Option ERC20State :=
  let allowed := s.allowances.get from |>.get caller
  let bal     := s.balances.get from
  if bal < amount then none
  else if allowed < amount then none
  else some { s with
    balances :=
      s.balances
        |>.set from (bal - amount)
        |>.set to   (s.balances.get to + amount),
    allowances := s.allowances.set from
      (s.allowances.get from |>.set caller (allowed - amount)) }

-- ABI-facing wrappers. Thin by design — no logic here.

@[evm_export "transfer(address,address,uint256)"]
def transfer (s : ERC20State) (from to : Address) (amount : UInt256)
    : Option (ERC20State × Bool) :=
  transferInternal s from to amount |>.map (·, true)

@[evm_export "approve(address,address,uint256)"]
def approve (s : ERC20State) (owner spender : Address) (amount : UInt256)
    : Option (ERC20State × Bool) :=
  approveInternal s owner spender amount |>.map (·, true)

@[evm_export "transferFrom(address,address,address,uint256)"]
def transferFrom (s : ERC20State) (caller from to : Address) (amount : UInt256)
    : Option (ERC20State × Bool) :=
  transferFromInternal s caller from to amount |>.map (·, true)

@[evm_export "balanceOf(address)"]
def balanceOf (s : ERC20State) (who : Address) : UInt256 :=
  s.balances.get who

@[evm_export "totalSupply()"]
def totalSupply (s : ERC20State) : UInt256 :=
  s.totalSupply
```

### `spec/Token.spec.lean`

```lean
import src.Token
import ForgeLean.ProofHelpers

-- All proofs are sorry. Proof terms live in test/Token.proof.lean.

theorem transfer_preserves_total_supply
    (s : ERC20State) (from to : Address) (amount : UInt256)
    (s' : ERC20State)
    (h : transferInternal s from to amount = some s') :
    s'.totalSupply = s.totalSupply := by sorry

theorem transfer_no_overdraft
    (s : ERC20State) (from to : Address) (amount : UInt256)
    (h : s.balances.get from < amount) :
    transferInternal s from to amount = none := by sorry

theorem transfer_no_creation
    (s : ERC20State) (from to : Address) (amount : UInt256)
    (hne : from ≠ to) (s' : ERC20State)
    (h : transferInternal s from to amount = some s') :
    s'.balances.get from + s'.balances.get to =
    s.balances.get from + s.balances.get to := by sorry

theorem approve_sets_allowance
    (s : ERC20State) (owner spender : Address) (amount : UInt256)
    (s' : ERC20State)
    (h : approveInternal s owner spender amount = some s') :
    s'.allowances.get owner |>.get spender = amount := by sorry

theorem transferFrom_respects_allowance
    (s : ERC20State) (caller from to : Address) (amount : UInt256)
    (h : s.allowances.get from |>.get caller < amount) :
    transferFromInternal s caller from to amount = none := by sorry

theorem transferFrom_decrements_allowance
    (s : ERC20State) (caller from to : Address) (amount : UInt256)
    (s' : ERC20State)
    (h : transferFromInternal s caller from to amount = some s') :
    s'.allowances.get from |>.get caller =
    s.allowances.get from |>.get caller - amount := by sorry
```

### `test/Token.proof.lean`

```lean
import spec.Token
-- No sorry allowed in this file.

theorem transfer_preserves_total_supply
    (s : ERC20State) (from to : Address) (amount : UInt256)
    (s' : ERC20State)
    (h : transferInternal s from to amount = some s') :
    s'.totalSupply = s.totalSupply := by
  simp [transferInternal] at h
  split_ifs at h <;> simp_all

theorem transfer_no_overdraft
    (s : ERC20State) (from to : Address) (amount : UInt256)
    (h : s.balances.get from < amount) :
    transferInternal s from to amount = none := by
  simp [transferInternal]
  omega

theorem transfer_no_creation
    (s : ERC20State) (from to : Address) (amount : UInt256)
    (hne : from ≠ to) (s' : ERC20State)
    (h : transferInternal s from to amount = some s') :
    s'.balances.get from + s'.balances.get to =
    s.balances.get from + s.balances.get to := by
  simp [transferInternal] at h
  split_ifs at h <;> simp_all
  omega

theorem approve_sets_allowance
    (s : ERC20State) (owner spender : Address) (amount : UInt256)
    (s' : ERC20State)
    (h : approveInternal s owner spender amount = some s') :
    s'.allowances.get owner |>.get spender = amount := by
  simp [approveInternal] at h
  simp_all [StorageMapping.get_set_same]

theorem transferFrom_respects_allowance
    (s : ERC20State) (caller from to : Address) (amount : UInt256)
    (h : s.allowances.get from |>.get caller < amount) :
    transferFromInternal s caller from to amount = none := by
  simp [transferFromInternal]
  omega

theorem transferFrom_decrements_allowance
    (s : ERC20State) (caller from to : Address) (amount : UInt256)
    (s' : ERC20State)
    (h : transferFromInternal s caller from to amount = some s') :
    s'.allowances.get from |>.get caller =
    s.allowances.get from |>.get caller - amount := by
  simp [transferFromInternal] at h
  split_ifs at h <;> simp_all
  omega
```

---

## 12. Implementation Checklist

This checklist defines the complete v1 scope. Nothing outside this list is in scope.

### Rust binary (`forge-lean`)

- [ ] `forge-lean init` command
- [ ] `forge-lean build` command (stages 1–4)
- [ ] `forge-lean test` command (proof checking)
- [ ] `forge-lean check-spec` command
- [ ] Validator: all rejected constructs in section 3.7
- [ ] Yul emitter: all construct mappings in section 7.2
- [ ] Yul object wrapper (section 7.3)
- [ ] ABI JSON generation (section 7.4)
- [ ] ABI selector computation from signature string
- [ ] `solc` invocation via `foundry-compilers`
- [ ] `forge test` hook integration (section 8.3)
- [ ] All error messages in section 10

### Lean library (`ForgeLean`)

- [ ] `ForgeLean.Prelude`: `Address`, `Bytes32`, `StorageMapping`
- [ ] `StorageMapping.get`, `StorageMapping.set`
- [ ] `StorageMapping.get_set_same` (simp lemma)
- [ ] `StorageMapping.get_set_other` (simp lemma)
- [ ] `StorageMapping.key_injective` (axiom)
- [ ] `ForgeLean.ProofHelpers`: `lift_to_abi`, `compose`, `revert_preserves_state`
- [ ] `erc_cases` tactic macro
- [ ] `ForgeLean.ERC20`: `ERC20State`, `ERC20` typeclass
- [ ] `@[evm_export]` attribute declaration

### Templates

- [ ] Full ERC-20 example (section 11) as `forge-lean init --template erc20`
