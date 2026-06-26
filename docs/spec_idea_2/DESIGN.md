# LSC — Design Document

> **Purpose**: Single authoritative reference for all design decisions. Intended for implementers and reviewers. Every significant decision is stated with its rationale. Familiarity with Lean 4 and EVM internals is expected.

---

## 1. Goals and Non-Goals

### Goals

- Allow DeFi developers to write smart contracts with **machine-checked formal proofs** of safety properties (no reentrancy, no value loss, access control, conservation invariants).
- Produce **EVM-deployable bytecode** via an auditable, explicit compilation path.
- Make proofs **tractable**: a typical safety theorem should close with `simp` + `omega` or a short LLM-assisted proof.
- Replace or significantly reduce the need for manual security audits.

### Non-Goals

- General-purpose smart contract language. This is a **restricted, DeFi-oriented** language.
- Gas optimality. Gas inefficiency is acceptable in exchange for provability.
- Verifying existing Solidity/Vyper contracts.
- Full compiler correctness proof in v1 (see §11 for what is and isn't proved).

---

## 2. Architecture and Trust Boundary

```
┌──────────────────────────────────────────────────┐
│  Source  (Lean macros / syntax extension)        │  ← user writes this
├──────────────────────────────────────────────────┤
│  AST     (inductive Lean types)                  │  ← macro output (pure data)
│  + Linearity check pass                          │
│  + DAG check pass (no recursion)                 │
│  + Selector collision check                      │
├──────────────────────────────────────────────────┤
│  ContractM semantics  (state monad)              │  ← proofs live here
│  auto-derived via Stmt.eval                      │
├──────────────────────────────────────────────────┤
│  IR  (flat, linear-types erased)                 │
├──────────────────────────────────────────────────┤
│  Yul  (EvmYulLean Yul.Program type)              │  ← trust boundary
├──────────────────────────────────────────────────┤
│  EVM bytecode  (via EvmYulLean)                  │  ← trusted
└──────────────────────────────────────────────────┘
```

### What is proved in v1

- Per-construct semantic preservation theorems (one per major `Stmt` constructor and per linear-type primitive). See §11.
- All user-stated propositions about their contract functions, via the Lean kernel.

### What is trusted in v1 (not proved)

- The **Yul emitter**: generates `Yul.Program` values; tested against EvmYulLean's conformance suite but not proved.
- The **`storageKey` injectivity axioms** (§9): tested, not proved.
- **EvmYulLean** itself: treated as ground truth, validated against 99.99% of Ethereum tests.

The end-to-end compilation correctness theorem (AST semantics match Yul execution for all inputs) is a **v2 goal**. The Yul output is human-readable and generated deterministically — users can audit it directly.

---

## 3. The Source Layer — Lean Macros

The user writes contracts using **Lean 4 syntax extensions** (`declare_syntax_cat` + `macro_rules`). There is no separate compiler, no external toolchain. Everything is Lean.

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
    | Paused
    | Unpaused

  def increment : Tx := do
    require (¬ $.paused) else revert Paused;
    let n ← $.number +? 1;
    $.number := n;
    emit Incremented(n);
```

### What the macro generates

The macro is **syntax-to-AST only**: pure structural translation, no validation, no domain logic.

```lean
-- 1. Storage struct
structure CounterStorage where
  number : UInt256 := 0
  paused : Bool    := false
  owner  : Address

-- 2. Error inductive
inductive CounterError | Paused | NotOwner | Overflow

-- 3. Event inductive
inductive CounterEvent | Incremented (newValue : UInt256) | Paused | Unpaused

-- 4. AST value (pure data, used by compiler)
def Counter.increment.ast : Stmt := Stmt.seq ...

-- 5. ContractM definition (semantic ground truth for proofs)
def Counter.increment : ContractM CounterStorage CounterEvent CounterError Unit :=
  Stmt.eval Counter.increment.ast
```

The definitional equality `Counter.increment = Stmt.eval Counter.increment.ast` holds by `rfl`. This means proofs about `Counter.increment` and proofs about the AST are interchangeable at zero proof cost.

### Validation and error reporting

Domain validation (selector clashes, linearity violations, DAG violations) runs in an `elab_rules` elaboration step, not in `macro_rules`. This attaches errors to exact source positions via `Lean.logErrorAt`.

### User workflow

```lean
-- Write the contract (macro expands automatically on file load)
-- Write proofs in the same file or a sibling file

#check Counter.increment.ast     -- inspect the AST
#eval  Counter.increment.ast.toYul  -- generate Yul
#eval  Counter.increment.ast.toABI  -- generate ABI JSON
```

No build system, no CLI, no separate compiler invocation.

---

## 4. The AST Layer

### Core types

```lean
inductive Ty
  | uint256 | bool | address
  | wad | ray
  | tokenAmount             -- linear type
  | mapping (k v : Ty)     -- opaque; no iteration exposed

inductive Expr : Ty → Type
  | lit         : UInt256 → Expr .uint256
  | litBool     : Bool → Expr .bool
  | var         : Ident → Expr t
  | storageGet  : Ident → Expr t
  -- Arithmetic — always explicit about overflow and rounding
  | addChecked  : Expr .uint256 → Expr .uint256 → Expr .uint256
  | addWrapping : Expr .uint256 → Expr .uint256 → Expr .uint256
  | mulDiv      : Expr .uint256 → Expr .uint256 → Expr .uint256 → Expr .uint256
  | wadMulHalfUp | wadMulDown | wadDivDown | wadDivHalfUp   -- Wad variants
  | rayMulHalfUp | rayMulDown | rayDivDown | rayDivHalfUp   -- Ray variants
  -- Context (read-only, populated by dispatcher)
  | caller | callvalue | timestamp
  -- Linear type operations
  | tokenMint   : Expr .uint256 → Expr .tokenAmount
  | tokenBurn   : Expr .tokenAmount → Expr .uint256
  | tokenSplit  : Expr .tokenAmount → Expr .uint256 → Expr (.tokenAmount × .tokenAmount)
  | tokenMerge  : Expr .tokenAmount → Expr .tokenAmount → Expr .tokenAmount
  -- Mappings
  | mappingGet  : Expr (.mapping k v) → Expr k → Expr v

inductive Stmt
  | skip | seq : Stmt → Stmt → Stmt
  | letBind    : Ident → Expr t → Stmt
  | storageSet : Ident → Expr t → Stmt
  | require    : Expr .bool → Ident → Stmt   -- Ident is error variant name
  | ifThenElse : Expr .bool → Stmt → Stmt → Stmt
  | emit       : Ident → List (Sigma Expr) → Stmt
  | revert     : Ident → Stmt
  | call       : Ident → List (Sigma Expr) → Stmt
  | externalCall : Ident → Ident → List (Sigma Expr) → Stmt
```

### Deliberate exclusions

No raw memory access, no inline assembly, no `delegatecall`, no `selfdestruct`, no recursion, no dynamic dispatch, no raw `keccak256`, no direct slot access, no loops (v1; bounded loops with invariants in v2).

---

## 5. The ContractM Semantics Layer

```lean
-- S = storage struct, E = event type, Err = error type, A = return value
def ContractM (S E Err : Type) (A : Type) : Type :=
  ContractState S → Except Err (A × ContractState S × List E)

structure ContractState (S : Type) where
  storage : S
  context : TxContext
  locked  : Bool := false    -- reentrancy guard; never accessible to user code
```

`List E` (emitted events) is implicit in source syntax, explicit in Lean proofs and theorems.

### Required `@[simp]` lemmas

Every primitive monad operation must have a `@[simp]` lemma:

```lean
@[simp] theorem runS_pure   ...
@[simp] theorem runS_bind   ...
@[simp] theorem runS_get    ...
@[simp] theorem runS_modifyStorage ...
@[simp] theorem runS_emit   ...
@[simp] theorem runS_require_true  ...
@[simp] theorem runS_require_false ...
@[simp] theorem runS_revert ...
```

**Design invariant**: if a proof of a straightforward property cannot be closed by `simp [runS, theFunction, ...]` followed by `omega`, the simp lemma set is incomplete — add lemmas until it can.

---

## 6. Execution Model

### Functions and dispatch

Each `FunctionDef` has a `kind` (`external`, `internal`, `view`, `constructor`) and a `permits` list declaring which linear permissions it requires. The ABI dispatcher is **generated by the framework**; users never write it.

Selector collision is checked at elaboration time and reported as a positioned error.

### No recursion — DAG enforcement

Recursive function calls are **banned in v1**. The call graph (built from `Stmt.call` nodes) must be a DAG. Checked at elaboration time. Every function call terminates by construction, which eliminates a large class of reentrancy patterns.

### Arithmetic errors — strict 1:1 mapping

User error types must embed framework arithmetic errors via `ContractErrors.arith`. The mapping is **strict 1:1**:

| `ArithError` variant | Required user error name |
|----------------------|--------------------------|
| `Overflow` | `Overflow` |
| `Underflow` | `Underflow` |
| `DivisionByZero` | `DivByZero` |

The elaborator checks that every `ArithError` variant reachable from operations in the contract body has a same-named entry in the `errors:` block. Collapsing multiple `ArithError` variants to one user error is a compile error. This makes every arithmetic operation an explicit proof obligation site.

```lean
-- Counter uses only +?; only Overflow is reachable → only Overflow required
errors:
  | Overflow

-- AMM uses +?, -?, /?; all three are reachable → all three required
errors:
  | Overflow
  | Underflow
  | DivByZero
```

`@math` functions called via `|>.orRevert` use the same `ContractErrors.arith` table — not a separate per-call argument.

### Framework errors

```lean
class ContractErrors (Err : Type) where
  arith         : ArithError → Err        -- strict 1:1 (see above)
  fromFramework : FrameworkError → Err    -- reentrancy, unauthorized, etc.
```

On revert, all storage changes and emitted events are discarded (EVM semantics).

### Events

In source syntax, `emit` looks like a statement. In ContractM, events are the `List E` return component. Users interact with events only in theorem hypotheses:

```lean
theorem increment_emits_incremented
    (s s' : CounterState) (log : List CounterEvent)
    (h : runS increment s = .ok ((), s', log)) :
    log = [CounterEvent.Incremented s'.storage.number] := ...
```

---

## 7. Linear Types

### Purpose

Linear types enforce that certain values are used **exactly once** per execution path. They eliminate named categories of theorems that would otherwise need to be proved manually.

### Enforcement mechanism

Linearity is enforced at the **AST level** by a post-macro check pass, not by Lean's type system. The pass verifies each linear variable appears on exactly one branch of every control flow path — neither dropped nor duplicated. Violations are reported as positioned errors.

At the IR level and below, linear types are **completely erased**. A `FlashLoanReceipt` compiles to a boolean storage slot. The type existed only to constrain what the programmer could express.

### Linear type library

Each linear type eliminates a named category of proof obligations:

| Type | Created by | Consumed by | Eliminates |
|------|-----------|-------------|------------|
| `TokenAmount` | `tokenMint` (restricted) or external receive | `tokenBurn`, `externalCall` | `transfer_conserves_balances`, `no_phantom_minting` |
| `Allowance` | `Allowance.grant` | `Allowance.consume` (with `h : amount ≤ a.value`) | `transferFrom_cannot_exceed_allowance` |
| `FlashLoanReceipt` | `FlashLoan.borrow` | `FlashLoan.repay` (only consumer) | `flashloan_always_repaid` |
| `ReentrancyLock` | `Lock.acquire` | `Lock.release`; required by `externalCall` | `external_calls_always_locked` |
| `Capability` | Framework identity check | Passed to privileged function | All `only_X_can_do_Y` theorems |
| `OracleReading` | `Oracle.fetch` (checks timestamp) | `Oracle.consume` | `price_is_fresh` |
| `WithdrawalRequest` | `Withdrawal.stage` | `Withdrawal.execute` | `state_updated_before_transfer` |
| `PositionTicket` | `Position.open` | `Position.close` or `Position.liquidate` | `bad_debt_impossible` |

Detailed per-type specs: [extensions/linear-types/](extensions/linear-types/).

### Relationship to HonestWorld

Linear types eliminate per-function obligations about **your contract's behavior**. `HonestWorld` (§8) eliminates per-theorem hypotheses about **external contracts' behavior**. Both are needed for cross-contract theorems like `swap_preserves_k`.

---

## 8. The World Model

### Purpose

The `World` models the full deployment context — your contract plus external contracts it interacts with — for multi-contract theorems.

### WorldSpec typeclass

```lean
class WorldSpec (W : Type) where
  Self    : Type                   -- your contract's storage type
  Env     : Type                   -- external contract states
  getSelf : W → ContractState Self
  getEnv  : W → Env
  setSelf : W → ContractState Self → W
  -- roundtrip laws
  get_set : ∀ w s, getSelf (setSelf w s) = s
  set_get : ∀ w, setSelf w (getSelf w) = w
```

`WorldSpec` is a typeclass so the execution engine (`runWorld`, external call dispatch) can be generic over deployment topology.

### Per-deployment worlds

```lean
structure AMMWorld where
  self   : ContractState AMMStorage
  token0 : ERC20State
  token1 : ERC20State
```

### Bundling assumptions — HonestWorld

```lean
class HonestWorld (W : Type) [WorldSpec W] where
  token0_conserves   : transferConserves (getEnv w).token0
  token1_conserves   : transferConserves (getEnv w).token1
  oracle_fresh       : oracleAge (getEnv w).oracle ≤ MAX_STALENESS
  no_hostile_reentry : ∀ call, externalCallSafe call
```

Use `[HonestWorld AMMWorld]` instead of threading four individual hypotheses through every theorem.

### Reentrancy in the world model

During an external call: `locked = true`. Any reentrant call into your contract reverts with `FrameworkError.Reentrant` before modifying state. The external contract's state in `env` may change; your state is unchanged when control returns.

---

## 9. Storage Model

### Storage struct

```lean
structure AMMStorage where
  reserve0 : Wad
  reserve1 : Wad
  lpSupply : Wad
  fee      : Wad
  paused   : Bool
  owner    : Address
```

Field independence (`set reserve0` does not affect `reserve1`) holds by `rfl` — alias-free by construction.

### Mappings

```lean
opaque Mapping (k v : Type) : Type   -- backed by Finmap, iteration deliberately excluded

namespace Mapping
  def get  : Mapping k v → k → v
  def set  : Mapping k v → k → v → Mapping k v
  -- no toList, no fold, no filter
end Mapping
```

Excluding iteration prevents gas-griefing bugs and simplifies proofs. For sum-of-all-entries invariants (e.g. "total supply = sum of balances"), track the total separately and prove a conservation theorem instead.

### Storage layout axioms (trusted, not proved)

```lean
axiom storageKey_injective  : ∀ f1 f2, f1 ≠ f2 → storageKey f1 ≠ storageKey f2
axiom mappingKey_injective  : ∀ slot k1 k2, k1 ≠ k2 → mappingKey slot k1 ≠ mappingKey slot k2
axiom mappingKey_ne_storageKey : ∀ slot k f, mappingKey slot k ≠ storageKey f
```

These three axioms are the complete statement of "storage is alias-free." All separation lemmas derive from them. Keccak is never exposed to user code or user proofs.

---

## 10. Arithmetic and Numeric Types

### Principles

No implicit overflow. No implicit precision loss. Operations that can fail return `Except Err`.

### UInt256 operations

```lean
namespace UInt256
  def addChecked  : UInt256 → UInt256 → Except ArithError UInt256
  def subChecked  : UInt256 → UInt256 → Except ArithError UInt256
  def mulChecked  : UInt256 → UInt256 → Except ArithError UInt256
  def addWrapping : UInt256 → UInt256 → UInt256   -- never fails; pure mod-2²⁵⁶
  def subWrapping : UInt256 → UInt256 → UInt256
  def mulWrapping : UInt256 → UInt256 → UInt256
  def divFloor    : UInt256 → UInt256 → Except ArithError UInt256
  def mulDiv      : UInt256 → UInt256 → UInt256 → Except ArithError UInt256
                 -- computes (a * b) / c with 512-bit intermediate; critical for AMM math
end UInt256
```

### Fixed-point types

```lean
structure Wad where raw : UInt256   -- 1 Wad = 1e18

namespace Wad
  def mulDown   : Wad → Wad → Except ArithError Wad   -- floor
  def mulHalfUp : Wad → Wad → Except ArithError Wad   -- round to nearest
  def divDown   : Wad → Wad → Except ArithError Wad
  def divHalfUp : Wad → Wad → Except ArithError Wad
  -- Key theorems proved once, available to all users:
  theorem mul_comm   : Wad.mulHalfUp a b = Wad.mulHalfUp b a
  theorem mul_le_left : b.raw ≤ WAD → Wad.mulHalfUp a b = .ok r → r.raw ≤ a.raw
end Wad
```

`Ray` follows the same pattern with `1 Ray = 1e27`.

### Fixed-point surface syntax

In contract bodies, use bracket-pair syntax (requires `open scoped Lsc.Wad` or `Lsc.Ray`):

| Bracket pair | Maps to | Rounding |
|---|---|---|
| `⌊a * b⌋?` | `wadMulDown` | floor |
| `⸢a * b⸣?` | `wadMulHalfUp` | half-up |
| `⌊a / b⌋?` | `wadDivDown` | floor |
| `⸢a / b⸣?` | `wadDivHalfUp` | half-up |

Inside `@math` functions, use the named forms (`Wad.mulHalfUp`, etc.) directly. The bracket pairs and named forms compile to the same AST node.

### The `WayRayMath` dependency

Proofs connecting on-chain fixed-point operations to their ℝ counterparts require the **`WayRayMath` library**, which provides error-bound lemmas:

```lean
theorem WayRayMath.wadMulHalfUp_error (a b : ℕ) :
    |decode (wadMulHalfUp a b) - decode a * decode b| ≤ WAD_ERROR
-- where WAD_ERROR = 10⁻¹⁸
```

See [extensions/MATH.md](extensions/MATH.md) for the full proof workflow.

---

## 11. The Compilation Pipeline

### Compilation correctness — what is proved in v1

One semantic preservation theorem per major AST construct:

```lean
theorem Stmt.eval_storageSet_correct ...
theorem Stmt.eval_require_correct ...
theorem Stmt.eval_ifThenElse_correct ...
```

And one per linear-type primitive:

```lean
theorem FlashLoan.borrow_yul_correct ...
theorem ReentrancyLock.acquire_yul_correct ...
```

These are proved once by the framework. User contracts inherit them.

The full end-to-end theorem is a **v2 goal**. See §2 for the complete trust boundary.

### Deliverables per contract

When a user's Lean file compiles:

1. **Lean source** — contract + proofs, kernel-checked
2. **Yul source** — human-readable, from `#eval contract.toYul.render`
3. **ABI JSON** — from `#eval contract.toABI`
4. **Proof certificate** — `.olean` file; certifies all stated theorems hold

---

## 12. Proof Ergonomics — Design Invariants

These are **design constraints**, not features. They must be maintained as the system evolves.

### The `simp + omega` invariant

Any theorem of the form "on success, storage field X has value V" must close with:

```lean
simp [runS, theFunction, fieldName, ...]
omega
```

If this fails, add missing `@[simp]` lemmas. Do not work around it with longer proofs.

### The field independence invariant

Any theorem of the form "function F does not change field X" must close with `rfl` or `simp` with no arithmetic. If it requires case analysis or induction, the storage model is wrong.

### The error separation invariant

Prove success-case and failure-case theorems separately:

```lean
theorem increment_succeeds_when_not_paused ...  -- prove independently
theorem increment_errors_when_paused ...        -- prove independently
```

Never write a theorem that simultaneously handles both outcomes.

### The hypothesis minimality invariant

A theorem should state exactly the hypotheses it needs. If a theorem about `increment` doesn't need the `owner` field, `owner` should not appear in its statement. Use `HonestWorld` only when the theorem genuinely needs all bundled assumptions.

---

## 13. Reference Contracts

The canonical contracts live in [reference/COUNTER.md](reference/COUNTER.md) and [reference/AMM.md](reference/AMM.md). Key constraints:

**Counter**: every framework feature must be exercisable against this contract before any DeFi contract is attempted. All required theorems must close with `simp` + `omega` in at most ~5 lines.

**AMM**: validates Wad/Ray math, `TokenAmount`, `IERC20` interface, `HonestWorld`, `ReentrancyLock`, multi-field storage, and conservation invariants. Key required theorems:

```lean
theorem swap_preserves_k      [HonestWorld AMMWorld] ... : w'.reserve0 * w'.reserve1 ≥ w.reserve0 * w.reserve1
theorem addLiquidity_conserves_tokens [HonestWorld AMMWorld] ...
theorem swap_not_reentrant    ... : ∀ reentrantCall, reentrantCall.reverts
theorem setFee_only_owner     ... (cap : Capability .Owner) ...
```

---

## Appendix A: Relationship to Prior Work

- **lsc** (prior prototype): established the `ContractM` monad shape. Abandoned due to opaque bytecode emission via Lean reflection. This design replaces that path with an explicit Yul target.
- **dss2024**: the `declare_syntax_cat` + `macro_rules` pattern for a DSL that compiles to a verified AST. The macro layer follows this pattern exactly.
- **EvmYulLean** (Nethermind): provides Yul and EVM semantics; treated as trusted ground truth.
- **Move Prover**: demonstrated that a restricted, DeFi-oriented language with co-designed verification is practical. Key lessons: resource types, alias-free memory, static dispatch, minimal language surface. This design independently converges on all four.

## Appendix B: Implementation Details Intentionally Omitted

The following are left to the implementer and should not be added to this document:

- Lean module structure and file organization (see IMPLEMENTATION.md)
- Exact `macro_rules` syntax for the surface DSL (see IMPLEMENTATION.md)
- EvmYulLean API usage details
- ABI encoding implementation
- Selector computation
- `Finmap` library choice
- Test harness structure
