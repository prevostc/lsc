# Formally Verified EVM Smart Contract Language — Design Document

> **Purpose**: This document is the single authoritative reference for all design decisions. It is intended for developers implementing the system and reviewers evaluating the design. Every significant decision is stated explicitly with its rationale. No prior knowledge of formal verification is assumed, but familiarity with Lean 4 and EVM internals is expected.

---

## 1. Goals and Non-Goals

### Goals

- Allow DeFi developers to write smart contracts with **machine-checked formal proofs** of safety properties (no reentrancy, no value loss, access control, conservation invariants).
- Produce **EVM-deployable bytecode** from those contracts via an auditable, explicit compilation path.
- Make proofs **tractable**: a typical safety theorem should be provable with `simp` + `omega` or a short LLM-assisted proof. If a straightforward property requires more than ~10 lines of proof, the definitions are wrong.
- Replace or significantly reduce the need for manual security audits by providing a stronger, foundational guarantee.

### Non-Goals

- General-purpose smart contract language. This is a **restricted, DeFi-oriented language**. Features that cannot be proved about are excluded.
- Gas optimality. Gas inefficiency is acceptable in exchange for provability.
- Verifying existing Solidity/Vyper contracts. This is a new language, not a verifier for existing ones.
- Full compiler correctness proof in v1. The compilation path is **auditable and tested**, not fully proved end-to-end initially.

### The Guarantee

> *Your contract logic is proved correct at the semantic level. The compilation to EVM bytecode is faithful by construction, with an explicit and auditable trusted layer. Proofs are tractable: you state what your contract should do as Lean propositions, and the proof follows structurally from the contract definition.*

---

## 2. Architecture Overview

```
┌─────────────────────────────────────────────────────┐
│  Source  (Lean macros / syntax extension)           │  ← user writes this
├─────────────────────────────────────────────────────┤
│  AST     (inductive Lean types)                     │  ← macro output
│  + Linearity check pass                             │
│  + DAG check pass (no recursion)                    │
│  + Selector collision check                         │
├─────────────────────────────────────────────────────┤
│  ContractM semantics  (state monad)                 │  ← proofs live here
│  auto-derived from AST via Stmt.eval                │
├─────────────────────────────────────────────────────┤
│  IR  (flat, explicit, no sugar)                     │
├─────────────────────────────────────────────────────┤
│  Yul  (EvmYulLean's Yul.Program type)               │  ← trusted boundary
├─────────────────────────────────────────────────────┤
│  EVM bytecode  (via EvmYulLean)                     │  ← trusted
└─────────────────────────────────────────────────────┘
```

### Trust Boundary

Everything above the Yul layer is **formally proved in Lean**. The Yul emitter is **trusted but tested** against EvmYulLean's conformance suite. EvmYulLean itself is treated as ground truth (validated against 99.99% of Ethereum tests). Users can audit the Yul output directly — it is human-readable and generated deterministically.

The trust surface is:
1. The Yul emitter (tested, not proved in v1)
2. The `storageKey` injectivity axioms (see §9)
3. EvmYulLean's EVM model

---

## 3. The Source Layer — Lean Macros

### Design

The user writes contracts using **Lean 4 syntax extensions** (`declare_syntax_cat` + `macro_rules`). There is no separate compilation step, no external toolchain. Everything is Lean.

```lean
contract Counter where
  storage:
    number : UInt256 := 0
    paused : Bool    := false
    owner  : Address

  errors:
    | Paused
    | NotOwner
    | Overflow

  events:
    | Incremented (newValue : UInt256)

  def increment : Tx := do
    require (¬ storage.paused) .Paused
    let n ← storage.number.addChecked 1 |>.orRevert .Overflow
    storage.number := n
    emit (.Incremented n)
```

### What the Macro Generates

The macro is **syntax-to-AST only**. It never validates, never errors on domain rules, never runs logic. It produces pure data:

```lean
-- 1. Storage struct
structure CounterStorage where
  number : UInt256 := 0
  paused : Bool    := false
  owner  : Address

-- 2. Error inductive
inductive CounterError | Paused | NotOwner | Overflow

-- 3. Event inductive
inductive CounterEvent | Incremented (newValue : UInt256)

-- 4. AST value
def Counter.increment.ast : Stmt := 
  Stmt.seq
    (Stmt.require (Expr.not (Expr.storageGet "paused")) (Expr.err .Paused))
    (Stmt.seq
      (Stmt.letBind "n" (Expr.addChecked (Expr.storageGet "number") (Expr.lit 1) .Overflow))
      (Stmt.seq
        (Stmt.storageSet "number" (Expr.var "n"))
        (Stmt.emit (Expr.event .Incremented [Expr.var "n"]))))

-- 5. ContractM semantics (auto-derived, not macro-generated)
def Counter.increment : ContractM CounterStorage CounterEvent CounterError Unit :=
  Stmt.eval Counter.increment.ast
```

The user writes proofs against `Counter.increment` (the ContractM version). The AST version exists for the compiler. The connection is definitional: `Counter.increment = Stmt.eval Counter.increment.ast` holds by `rfl`.

### Error Reporting

Domain-specific validation (selector clashes, linearity violations, DAG violations) runs in an `elab_rules` elaboration step, not in `macro_rules`. This gives access to `Lean.logErrorAt : Syntax → String → CommandElabM Unit`, which attaches errors to exact source positions and displays them in the IDE at the relevant line.

```lean
elab_rules : command
  | `(contract $name where $body) => do
    let def ← parseContractDef body
    match validateContract def with
    | .error (pos, msg) => Lean.logErrorAt pos msg; return
    | .ok validated     => generateDefinitions validated
```

Type errors in generated Lean code surface as normal Lean type errors, which are generally readable.

### User Workflow

```lean
-- Write the contract (macro expands automatically)
-- Write proofs in the same file or a separate file
-- #check Counter.increment.ast     -- inspect the AST
-- #eval  Counter.increment.ast.toYul  -- generate Yul
-- #eval  Counter.increment.ast.toABI  -- generate ABI JSON
-- The Lean kernel validates all proofs on file load
```

No build system, no CLI, no external compiler. Everything is a Lean command.

---

## 4. The AST Layer

### Core Types

```lean
inductive Ty
  | uint256 | bool | address
  | wad | ray                    -- fixed-point numeric types
  | tokenAmount                  -- linear type (see §7)
  | mapping (k v : Ty)           -- opaque, no user iteration
  | struct (fields : List (Ident × Ty))

inductive Expr : Ty → Type
  | lit      : UInt256 → Expr .uint256
  | litBool  : Bool → Expr .bool
  | var      : Ident → Expr t
  | storageGet : Ident → Expr t
  -- arithmetic (all explicit about rounding/overflow)
  | addChecked  : Expr .uint256 → Expr .uint256 → Ident → Expr .uint256
  | addWrapping : Expr .uint256 → Expr .uint256 → Expr .uint256
  | mulDiv      : Expr .uint256 → Expr .uint256 → Expr .uint256 → Expr .uint256
  | wadMul      : Expr .wad → Expr .wad → Expr .wad
  | rayMul      : Expr .ray → Expr .ray → Expr .ray
  -- logic
  | not  : Expr .bool → Expr .bool
  | and  : Expr .bool → Expr .bool → Expr .bool
  | eq   : Expr t → Expr t → Expr .bool
  | lt   : Expr .uint256 → Expr .uint256 → Expr .bool
  -- context (implicit tx context, read-only)
  | caller    : Expr .address
  | callvalue : Expr .uint256
  | timestamp : Expr .uint256
  -- linear type operations (see §7)
  | tokenMint   : Expr .uint256 → Expr .tokenAmount  -- restricted
  | tokenBurn   : Expr .tokenAmount → Expr .uint256  -- restricted
  | tokenSplit  : Expr .tokenAmount → Expr .uint256 → Expr (.tokenAmount × .tokenAmount)
  | tokenMerge  : Expr .tokenAmount → Expr .tokenAmount → Expr .tokenAmount
  -- mapping (no iteration exposed)
  | mappingGet  : Expr (.mapping k v) → Expr k → Expr v
  | mappingSet  : Expr (.mapping k v) → Expr k → Expr v → Expr (.mapping k v)

inductive Stmt
  | skip
  | seq         : Stmt → Stmt → Stmt
  | letBind     : Ident → Expr t → Stmt
  | storageSet  : Ident → Expr t → Stmt
  | require     : Expr .bool → Expr t → Stmt   -- second arg is error value
  | ifThenElse  : Expr .bool → Stmt → Stmt → Stmt
  | call        : Ident → List (Sigma Expr) → Stmt  -- internal call by name
  | externalCall: Ident → Ident → List (Sigma Expr) → Stmt  -- interface, method, args
  | emit        : Expr t → Stmt
  | revert      : Expr t → Stmt
```

### What Is Excluded

No raw memory access, no inline assembly, no `delegatecall`, no `selfdestruct`, no recursion, no dynamic dispatch, no raw `keccak256` calls, no direct storage slot access, no loops without termination measures (v1: no loops at all; add bounded loops in v2).

---

## 5. The ContractM Semantics Layer

### Definition

```lean
def ContractM (S E Err : Type) (A : Type) : Type :=
  ContractState S → Except Err (A × ContractState S × List E)
```

`S` is the contract-specific storage struct. `E` is the contract-specific event type. `Err` is the contract-specific error type. `A` is the return value. `List E` is the list of events emitted during execution — implicit in source syntax, explicit in Lean.

### ContractState

```lean
structure TxContext where
  caller    : Address
  callvalue : UInt256
  timestamp : UInt256
  origin    : Address  -- tx.origin, available but use discouraged

structure ContractState (S : Type) where
  storage  : S
  context  : TxContext
  locked   : Bool      -- reentrancy guard, framework-managed
```

`locked` is never directly accessible to user code. It is managed exclusively by the framework's external call primitives.

### ContractBase

Rather than a typeclass, every contract state is a concrete instantiation of `ContractBase`:

```lean
abbrev ContractBase (S E Err : Type) := ContractState S
-- E and Err appear in ContractM's type, not in state
```

Framework lemmas are stated over `ContractM S E Err` with explicit type variables. User theorems are stated over their concrete types (e.g., `CounterStorage`, `CounterEvent`, `CounterError`).

### Monad Operations with `@[simp]` Lemmas

Every primitive monad operation must have a corresponding `@[simp]` lemma so that `simp [runS, myFunction, ...]` reduces proof goals automatically:

```lean
@[simp] theorem runS_pure   ...
@[simp] theorem runS_bind   ...
@[simp] theorem runS_get    ...
@[simp] theorem runS_set    ...
@[simp] theorem runS_emit   ...
@[simp] theorem runS_require_true  ...
@[simp] theorem runS_require_false ...
@[simp] theorem runS_revert ...
```

If a proof of a straightforward property cannot be closed by `simp [runS, theFunction, ...]` followed by `omega`, the simp lemma set is incomplete — add lemmas until it can.

### Deriving ContractM from AST

```lean
-- Framework provides this once
def Stmt.eval (s : Stmt) : ContractM S E Err Unit := ...

-- Macro generates AST, framework derives semantics
def Counter.increment : ContractM CounterStorage CounterEvent CounterError Unit :=
  Stmt.eval Counter.increment.ast

-- Connection is definitional
theorem Counter.increment.eval_correct :
    Counter.increment = Stmt.eval Counter.increment.ast := rfl
```

---

## 6. Execution Model

### Functions and Dispatch

Each contract declares a list of `FunctionDef`s. Entry points (`kind = .external`) are callable from outside. The ABI dispatcher is **generated by the framework** — users never write it. Users only write function bodies.

```lean
inductive FunctionKind
  | external    -- ABI entry point
  | internal    -- only callable within contract
  | view        -- no storage mutation allowed (enforced by type)
  | constructor -- runs at deployment, not callable after

structure FunctionDef where
  name       : Ident
  kind       : FunctionKind
  params     : List (Ident × Ty)
  body       : Stmt
  permits    : Finset LinearPermission  -- declared capabilities

inductive LinearPermission
  | canMint (tokenType : Ident)
  | canBurn (tokenType : Ident)
  | canAcquireLock
  | canFlashBorrow
```

The framework generates a Yul dispatcher that routes calls by 4-byte selector. Selector collision is checked at elaboration time and reported as a positioned error.

### No Recursion — DAG Enforcement

Recursive function calls are **banned in v1**. The call graph (built from `Stmt.call` nodes) must be a DAG. This is checked at elaboration time. Every function call terminates by structural argument. This eliminates the need for termination proofs and prevents a large class of reentrancy patterns.

Bounded loops may be added in v2 with explicit loop invariants as a language-level construct (the programmer supplies the invariant in source syntax).

### Transaction Context

`msg.sender`, `msg.value`, and `block.timestamp` are available as read-only framework primitives within `ContractM`. They are stored in `TxContext` which is populated at the start of each transaction by the dispatcher. Users never construct `TxContext` directly.

### Reverts and Error Handling

```lean
-- Framework errors (generated by framework primitives)
inductive FrameworkError
  | Reentrant
  | Unauthorized
  | ArithmeticOverflow
  | ArithmeticDivByZero

-- User's error type must embed framework errors
class ContractErrors (Err : Type) where
  fromFramework : FrameworkError → Err
```

Arithmetic operations return `Except Err` where `Err` is the contract's error type. The user must explicitly handle or propagate arithmetic errors. This makes every arithmetic operation an explicit proof obligation site.

```lean
-- User code (in source syntax, expanded by macro):
let n ← storage.number.addChecked 1 |>.orRevert .Overflow
-- Proof obligation: on success, n = storage.number + 1 and no overflow occurred
```

On revert, all storage changes and emitted events are discarded. This matches EVM semantics.

### Events

Events are declared per contract as an inductive type. In source syntax, `emit` looks like a statement. In the ContractM type, events are implicit in the `List E` return component. Users only interact with events in proof statements:

```lean
theorem increment_emits_incremented
    (s s' : CounterState) (log : List CounterEvent)
    (h : runS increment s = .ok ((), s', log)) :
    log = [CounterEvent.Incremented s'.storage.number] := ...
```

Events compile to raw EVM logs. The event inductive type is erased at the IR level; the compiler generates the ABI event signature and topic encoding. This is part of the trusted compilation layer.

### Constructors and Deployment

Each contract may declare one `constructor` function. Default field values in the storage struct are used if no constructor is declared. The constructor is not callable post-deployment. The ABI includes constructor parameter encoding. Storage layout is initialized at deployment by the generated dispatcher.

---

## 7. Linear Types

### Purpose

Linear types enforce that certain values representing **permissions, obligations, or custody** are used exactly once per execution path. They eliminate entire categories of theorems that would otherwise need to be proved manually.

### Enforcement Mechanism

Linearity is enforced at the **AST level by a linearity check pass**, not by Lean's type system (which does not support linear types natively). The pass runs after macro expansion, before IR generation.

The algorithm: for each function body, track each variable of a linear type. Verify it appears on exactly one branch of every control flow path — neither dropped (used zero times on some path) nor duplicated (used more than once). Report positioned errors for violations.

At the IR level and below, linear types are **completely erased**. A `FlashLoanReceipt` compiles to a boolean storage slot. A `ReentrancyLock` compiles to the existing `locked` field. The type existed only to constrain what the programmer could express.

### The Linear Type Library

The framework ships the following linear types. Each one eliminates a named category of proof obligations.

#### `TokenAmount`

Represents custody of fungible tokens. Cannot be constructed from a raw `UInt256` by user code — only created via `tokenMint` (restricted to functions with `canMint` permission) or received from an external call interface. Cannot be implicitly dropped.

Operations: `split`, `merge`, `burn` (restricted). No `add`, no `sub` — you must split and merge explicitly.

Eliminates: `transfer_conserves_balances`, `no_phantom_minting`.

Compiles to: `UInt256` value in Yul.

#### `Allowance`

Represents a granted permission to spend tokens on behalf of another address. Created by `Allowance.grant`. Consumed by `Allowance.consume` which returns the remainder. Cannot exceed granted amount by construction (`h : amount ≤ a.value` in the consume signature).

Eliminates: `transferFrom_cannot_exceed_allowance`.

Compiles to: storage slot holding remaining allowance value.

#### `FlashLoanReceipt`

Represents an outstanding flash loan obligation. Created by `FlashLoan.borrow`. Must be consumed by `FlashLoan.repay` — no other consumer exists. Any function that borrows must repay on all code paths or the linearity check fails.

Eliminates: `flashloan_always_repaid`.

Compiles to: boolean storage slot `loan_outstanding`.

#### `ReentrancyLock`

Represents exclusive execution access. Created by `Lock.acquire`. Must be passed to `externalCall` (the only way to make external calls). Released by `Lock.release`. Cannot acquire a second lock while holding one (the acquire checks `locked = false` and sets it to `true`).

Eliminates: `external_calls_always_locked`, `no_reentrant_call_succeeds`.

Compiles to: the `locked : Bool` field in `ContractState`.

#### `Capability`

Represents a verified permission (e.g., admin rights). Created by the framework based on `caller` identity check. Passed to privileged functions as a required argument — those functions cannot be called without one.

Eliminates: all `only_X_can_do_Y` theorems.

Compiles to: nothing in Yul (the identity check was already performed when the capability was created; the capability itself has no runtime representation).

#### `OracleReading`

Represents a fresh price reading. Created by `Oracle.fetch` which internally checks the reading's timestamp against a `maxAge` parameter. Consumed by `Oracle.consume` which returns the price as `UInt256`. Cannot be reused across transactions.

Eliminates: `price_is_fresh`.

Compiles to: `(UInt256, UInt256)` — price and timestamp.

#### `WithdrawalRequest`

Represents a staged withdrawal — state has been updated, funds have not yet moved. Created by `Withdrawal.stage` which updates internal accounting. Consumed by `Withdrawal.execute` which performs the external transfer. Enforces checks-effects-interactions order structurally.

Eliminates: `state_updated_before_transfer`.

Compiles to: a pending withdrawal storage record.

#### `PositionTicket`

Represents an open debt position. Created by `Position.open`. Must be consumed by either `Position.close` (requires full repayment, `h : repayment.value ≥ ticket.debt`) or `Position.liquidate` (requires proof of undercollateralization). Cannot be dropped.

Eliminates: `bad_debt_impossible`, `positions_always_resolved`.

Compiles to: position storage record (collateral, debt, owner).

---

## 8. The World Model

### Purpose

The `World` models the full deployment context: your contract plus external contracts it interacts with. It is used for multi-contract theorems (e.g., AMM swap correctness depends on ERC20 token behavior).

### Definition

```lean
class WorldSpec (W : Type) where
  Self    : Type                   -- your contract's storage type
  Env     : Type                   -- external contract states
  getSelf : W → ContractState Self
  getEnv  : W → Env
  setSelf : W → ContractState Self → W
  -- laws
  get_set : ∀ w s, getSelf (setSelf w s) = s
  set_get : ∀ w, setSelf w (getSelf w) = w
```

`WorldSpec` is a typeclass because the execution engine (`runWorld`, external call dispatch) must be generic over deployment topology. Contract-specific theorems are stated over concrete world types.

### Per-Deployment World Types

Each deployment scenario defines its own concrete world:

```lean
structure AMMWorld where
  self   : ContractState AMMStorage
  token0 : ERC20State
  token1 : ERC20State

instance : WorldSpec AMMWorld where
  Self := AMMStorage
  Env  := AMMEnv  -- bundles token0, token1
  ...

structure BridgeWorld where
  self    : ContractState BridgeStorage
  token   : ERC20State
  relayer : Unit  -- modeled abstractly
```

### Call Stack and msg.sender

The `World` carries a call stack to correctly model `msg.sender` in nested calls:

```lean
structure World (S : Type) (Env : Type) where
  self      : ContractState S
  env       : Env
  msgStack  : List TxContext     -- top = current call context
  ethBalances : Finmap Address UInt256
```

When your contract makes an external call, the framework pushes a new `TxContext` onto `msgStack` with `caller = your_contract_address`. When the call returns, it pops. User code reads `caller` from the top of the stack via the `ContractM.caller` primitive.

### External Contract Interfaces

External contracts are modeled as **typed interfaces**, not concrete implementations:

```lean
class IERC20 (T : Type) where
  balanceOf   : T → Address → UInt256
  transfer    : Address → UInt256 → T → Except ExternalError T
  transferFrom: Address → Address → UInt256 → T → Except ExternalError T
  totalSupply : T → UInt256
```

The AMM's external calls are typed against `IERC20`. Theorems about the AMM are parameterized over any `T` that implements `IERC20`, conditional on honesty hypotheses.

### Bundling Assumptions — `HonestWorld`

Instead of threading individual hypotheses through every theorem, bundle them:

```lean
class HonestWorld (W : Type) [WorldSpec W] where
  token0_conserves  : transferConserves (getEnv w).token0
  token1_conserves  : transferConserves (getEnv w).token1
  oracle_fresh      : oracleAge (getEnv w).oracle ≤ MAX_STALENESS
  no_hostile_reentry : ∀ call, externalCallSafe call

-- theorem signature uses one instance instead of many hypotheses
theorem swap_conserves_product
    [HonestWorld AMMWorld]
    (w w' : AMMWorld) (amountIn : UInt256) ... :
    w'.self.storage.reserve0 * w'.self.storage.reserve1 ≥
    w.self.storage.reserve0  * w.self.storage.reserve1 := ...
```

Weaker partial variants can be defined for theorems that only rely on a subset of assumptions.

### Reentrancy in the World Model

During an external call: your contract's `locked` field is `true`. Any reentrant call into your contract hits the `ReentrancyLock` check and reverts before modifying your state. The external contract's state (in `env`) may change during the call. When control returns, your state is unchanged and the updated `env` is available.

This must be explicitly modeled in the `runWorld` execution semantics. The theorem you get for free from `ReentrancyLock` is: if `locked = true` in `w.self`, any call to your contract reverts with `FrameworkError.Reentrant`.

---

## 9. Storage Model

### Abstract Storage

Each contract's storage is a plain Lean struct with typed fields:

```lean
structure AMMStorage where
  reserve0  : UInt256
  reserve1  : UInt256
  lpSupply  : Wad
  fee       : UInt256
  paused    : Bool
  owner     : Address
```

At the proof level, reading and writing fields is handled by Lean's struct update syntax. Field independence (`set reserve0` does not affect `reserve1`) holds by `rfl` — no proof needed. This is alias-freedom by construction.

### Mappings

Mappings are exposed as an **opaque `Mapping k v` type** backed by `Finmap`:

```lean
opaque Mapping (k v : Type) : Type
-- implemented as Finmap k v but opaque to users

namespace Mapping
  def get    : Mapping k v → k → v
  def set    : Mapping k v → k → v → Mapping k v
  def getD   : Mapping k v → k → v → v  -- with default
  -- no toList, no fold, no iteration
end Mapping
```

Iteration is deliberately excluded. Users cannot loop over a mapping. This prevents a class of gas griefing bugs and simplifies proofs (no need to reason about all keys). If a protocol genuinely needs global invariants over all mapping entries (e.g., sum of all balances), use **Option B: conservation proofs** (see §10).

### Storage Layout Compilation

The mapping from struct fields to EVM storage slots is handled by the trusted Yul emitter. The emitter assigns each field a deterministic slot index. For `Mapping k v`, the emitter uses `keccak256(abi.encode(key, slotIndex))` — standard Solidity layout.

The following axioms are admitted (tested against EvmYulLean, not proved):

```lean
-- Fields map to distinct slots
axiom storageKey_injective :
    ∀ (f1 f2 : StorageField), f1 ≠ f2 → storageKey f1 ≠ storageKey f2

-- Mapping keys map to distinct slots
axiom mappingKey_injective :
    ∀ (slot : Nat) (k1 k2 : Word), k1 ≠ k2 →
    mappingKey slot k1 ≠ mappingKey slot k2

-- Mapping slot does not collide with field slots
axiom mappingKey_ne_storageKey :
    ∀ slot k f, mappingKey slot k ≠ storageKey f
```

These three axioms are the complete statement of "storage is alias-free." All separation lemmas in user proofs derive from these axioms. Keccak is never exposed to user code or user proofs.

---

## 10. Arithmetic and Numeric Types

### Principles

- No implicit overflow. Every arithmetic operation forces an explicit choice about overflow behavior.
- No implicit precision loss. Fixed-point operations use appropriate intermediate precision.
- Operations that can fail return `Except Err` where `Err` is the contract's error type.

### UInt256 Operations

```lean
namespace UInt256
  -- checked: returns error on overflow
  def addChecked  : UInt256 → UInt256 → Except FrameworkError UInt256
  def subChecked  : UInt256 → UInt256 → Except FrameworkError UInt256
  def mulChecked  : UInt256 → UInt256 → Except FrameworkError UInt256

  -- wrapping: explicit modular arithmetic
  def addWrapping : UInt256 → UInt256 → UInt256
  def subWrapping : UInt256 → UInt256 → UInt256

  -- saturating: clamp to min/max
  def addSaturating : UInt256 → UInt256 → UInt256

  -- division: EVM truncates toward zero
  def divFloor    : UInt256 → UInt256 → Except FrameworkError UInt256  -- errors on div/0

  -- full-precision multiply-then-divide with 512-bit intermediate
  -- critical for AMM math (Uniswap-style mulDiv)
  def mulDiv      : UInt256 → UInt256 → UInt256 → Except FrameworkError UInt256
end UInt256
```

### Fixed-Point Types: Wad and Ray

```lean
-- 1 Wad = 1e18. Represents a decimal with 18 places.
structure Wad where raw : UInt256

-- 1 Ray = 1e27. Represents a decimal with 27 places.
structure Ray where raw : UInt256

namespace Wad
  def WAD : UInt256 := 1_000_000_000_000_000_000

  def mul (a b : Wad) : Except FrameworkError Wad :=
    (UInt256.mulDiv a.raw b.raw WAD).map Wad.mk

  def div (a b : Wad) : Except FrameworkError Wad :=
    (UInt256.mulDiv a.raw WAD b.raw).map Wad.mk

  def toRay (w : Wad) : Ray := ⟨w.raw * 1_000_000_000⟩  -- exact

  -- Key theorems (proved once, available to all users):
  theorem mul_comm (a b : Wad) : Wad.mul a b = Wad.mul b a
  theorem mul_le_left (a b : Wad) (h : b.raw ≤ WAD) :
      ∀ r, Wad.mul a b = .ok r → r.raw ≤ a.raw
end Wad
```

Users write `price.mul amount` instead of `price * amount / 1e18`. The precision model is part of the type, not implicit. AMM invariant theorems are stated in terms of `Wad` and `Ray` operations, making them easier to read and prove.

---

## 11. The Compilation Pipeline

### AST → IR

The IR is a flat, explicit intermediate with no syntactic sugar. One AST construct maps to one or more IR constructs. The IR does not know about linear types — they have been erased by this stage.

```lean
inductive IR
  | sload   (slot : Word)
  | sstore  (slot : Word) (value : IRExpr)
  | call    (target : Word) (selector : Word) (args : List IRExpr)
  | if_     (cond : IRExpr) (thn els : IR)
  | seq     (a b : IR)
  | revert  (data : IRExpr)
  | log     (topics : List IRExpr) (data : IRExpr)
  | checkFlag (slot : Word) (expected : Bool)  -- from linear type erasure
  | setFlag   (slot : Word) (value : Bool)
```

### IR → Yul

The Yul emitter targets **EvmYulLean's `Yul.Program` type directly**, not a string. This means the output is a structured Lean value that EvmYulLean can interpret and test. `#eval contract.toYul` produces this value. Rendering to a Yul string is a separate display function.

The emitter is trusted in v1. Correctness is validated by running EvmYulLean's test suite against the emitted programs.

### Compilation Correctness — What Is Proved in v1

One semantic preservation theorem per major AST construct:

```lean
-- For each core Stmt constructor:
theorem Stmt.eval_storageSet_correct ...
theorem Stmt.eval_require_correct ...
theorem Stmt.eval_ifThenElse_correct ...
-- etc.
```

And one per linear type primitive:

```lean
theorem FlashLoan.borrow_yul_correct ...
theorem FlashLoan.repay_yul_correct ...
theorem ReentrancyLock.acquire_yul_correct ...
-- etc.
```

These are proved once by the framework. User contracts inherit them for free.

The full end-to-end compilation correctness theorem (AST semantics match Yul execution for all inputs) is a **v2 goal**, not v1. The v1 guarantee is: per-construct correctness + conformance tests on the emitter.

### Deliverables Per Contract

When a user's Lean file compiles successfully:

1. **Lean source** — the contract definition and all proofs, checked by the Lean kernel
2. **Yul source** — human-readable, generated by `#eval contract.toYul.render`
3. **ABI JSON** — generated by `#eval contract.toABI`
4. **Proof certificate** — the Lean `.olean` file implicitly certifies that all stated theorems hold

---

## 12. Proof Ergonomics — Design Invariants

These are not features — they are **design constraints** that must be maintained as the system evolves.

### The simp + omega invariant

Any theorem of the form "on success, storage field X has value V" must be provable by:

```lean
simp [runS, theFunction, fieldName, ...]
omega  -- for arithmetic goals
```

If this fails, add missing `@[simp]` lemmas to the monad operations or storage accessors. Do not work around it by making proofs longer.

### The field independence invariant

Any theorem of the form "function F does not change field X" must be provable by `rfl` or `simp` with no arithmetic. If it requires case analysis or induction, the storage model is wrong.

### The error separation invariant

Success-case and failure-case theorems must be provable independently. Do not write theorems that simultaneously handle both outcomes. Pattern:

```lean
-- Prove these separately, never together:
theorem increment_succeeds_when_not_paused ...
theorem increment_errors_when_paused ...
```

### The hypothesis minimality invariant

A theorem should state exactly the hypotheses it needs — no more. If a theorem about `increment` doesn't need the `owner` field, `owner` should not appear in its statement. Use `HonestWorld` and similar bundles only when the theorem genuinely needs all bundled assumptions.

---

## 13. Reference: The Pausable Counter

The minimal reference contract. Every framework feature should be exercised by this contract before any DeFi contract is attempted.

```lean
contract Counter where
  storage:
    number : UInt256 := 0
    paused : Bool    := false
    owner  : Address

  errors:
    | Paused | NotOwner | Overflow

  events:
    | Incremented (n : UInt256)
    | Paused | Unpaused

  def increment : Tx := do
    require (¬ storage.paused) .Paused
    let n ← storage.number.addChecked 1 |>.orRevert .Overflow
    storage.number := n
    emit (.Incremented n)

  def pause : Tx := do
    require (caller == storage.owner) .NotOwner
    require (¬ storage.paused) .Paused
    storage.paused := true
    emit .Paused

  def unpause : Tx := do
    require (caller == storage.owner) .NotOwner
    require storage.paused .Paused
    storage.paused := false
    emit .Unpaused
```

Required theorems (these must all be provable by `simp` + `omega` + at most 5 lines):

```lean
theorem increment_increases_number_when_not_paused ...
theorem increment_errors_when_paused ...
theorem increment_does_not_change_paused ...
theorem increment_does_not_change_owner ...
theorem increment_emits_incremented ...
theorem pause_sets_paused_when_owner ...
theorem pause_errors_when_not_owner ...
theorem pause_errors_when_already_paused ...
theorem unpause_clears_paused_when_owner ...
```

## 14. Reference: The Constant Product AMM

The target DeFi contract that validates the full design. Must exercise: `Wad`/`Ray` math, `TokenAmount` linear type, `IERC20` external interface, `HonestWorld` assumptions, `ReentrancyLock`, multi-field storage, and conservation invariants.

Key required theorems:

```lean
-- Core AMM invariant
theorem swap_preserves_k
    [HonestWorld AMMWorld] ... :
    w'.reserve0 * w'.reserve1 ≥ w.reserve0 * w.reserve1

-- No value created from nothing
theorem addLiquidity_conserves_tokens
    [HonestWorld AMMWorld] ... :
    totalTokensIn w' = totalTokensIn w + deposited

-- Reentrancy impossibility  
theorem swap_not_reentrant ... :
    ∀ reentrantCall, reentrantCall.reverts

-- Access control
theorem setFee_requires_owner (cap : Capability .Owner) ... :
    setFee fee cap s = .ok ...  -- can only succeed with capability
```

---

## Appendix A: What Is Not in This Document

The following are **implementation details** left to the implementer:

- Specific Lean module structure and file organization
- Exact `macro_rules` syntax for the source DSL
- EvmYulLean API usage details
- ABI encoding implementation
- Selector computation (standard `keccak256` of signature string)
- `Finmap` library choice (Mathlib vs custom)
- Test harness structure for Yul conformance tests

These should be decided during implementation based on what Lean's ecosystem provides at that time.

## Appendix B: Relationship to Prior Work

- **lsc** (author's prior prototype): established the `ContractM` monad shape and proof workflow. Abandoned due to opaque bytecode emission via Lean reflection. This design replaces that emission path with an explicit Yul target.
- **dss2024**: the `declare_syntax_cat` + `macro_rules` pattern for building a DSL that compiles to a verified AST. Directly inspirational — the macro layer follows this pattern exactly.
- **EvmYulLean** (Nethermind): provides the Yul and EVM semantics. Treated as trusted ground truth.
- **Move Prover**: demonstrated that a restricted, DeFi-oriented language with co-designed verification is practical and adopted in production (Aptos Framework, Liquidswap). Key lessons: resource types, alias-free memory, static dispatch, minimal language surface. This design independently converges on all four.
