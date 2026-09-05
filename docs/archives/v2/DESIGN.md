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
- A full compiler correctness proof end-to-end (see §11 for what is and isn't currently proved).

---

## 2. Architecture and Trust Boundary

```
┌──────────────────────────────────────────────────┐
│  Source  (plain Lean structure/inductive         │  ← user writes this
│  + `deriving ContractStorage/ContractError/      │  ← thin reflection-based
│    ContractEvent` + `tx { ... }` function bodies │     glue + a small
│    + a single trailing `derive_contract` call)   │     purpose-built grammar
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

### What is currently proved

- Per-construct semantic preservation theorems (one per major `Stmt` constructor and per linear-type primitive). See §11.
- All user-stated propositions about their contract functions, via the Lean kernel.

### What is currently trusted (not proved)

- The **Yul emitter**: generates `Yul.Program` values; tested against EvmYulLean's conformance suite but not proved.
- The **`storageKey` injectivity axioms** (§9): tested, not proved.
- **EvmYulLean** itself: treated as ground truth, validated against 99.99% of Ethereum tests.

The end-to-end compilation correctness theorem (AST semantics match Yul execution for all inputs) is **future work**, tracked separately from the current implementation. The Yul output is human-readable and generated deterministically — users can audit it directly.

---

## 3. The Source Layer — Plain Lean + Three `deriving` Handlers

> **This section describes the current, live implementation.** An earlier design called for a bespoke surface grammar (`contract … where`, `declare_syntax_cat lsc_*`, `macro_rules` synthesizing raw `Syntax.node` trees). That first attempt was implemented, found to be ~700 lines of brittle codegen (`Contract.lean`, `ContractGen.lean`, `ContractTypes.lean`), and deleted. It was replaced first by a `do`-notation-over-`TxM` surface (see the history in §3.4), and then by the current design: contracts are written as **plain Lean `structure`/`inductive` declarations** with custom `deriving` handlers, plus function bodies written in a small, dss2024-style bracket-delimited `tx <name> { ... }` grammar of its own (`declare_syntax_cat lscExpr`/`lscStmt`, in `Lsc/Lang/Syntax.lean`) — fresh syntax categories that are inert everywhere outside the `tx { ... }` delimiter, not layered on Lean's `term`/`doElem`. There is still no separate compiler or external toolchain — everything is Lean — but there is also no general-purpose custom parser either: every contract-author-facing construct below is either a real Lean declaration, a real `deriving` clause, or a production of this small, purpose-built statement/expression grammar.

```lean
structure CounterStorage where
  number : Wei := ⟨0⟩
  paused : Bool := false
  owner  : Address := 0
  deriving Repr, Lsc.Deriving.ContractStorage

inductive CounterError where
  | Paused
  | NotOwner
  | Overflow
  deriving Repr, DecidableEq, Lsc.Deriving.ContractError

inductive CounterEvent where
  | Incremented (n : Wei)
  | Paused
  | Unpaused
  deriving Repr, DecidableEq, Lsc.Deriving.ContractEvent

tx increment {
  require(!σ.paused) else revert Paused();
  let n = σ.number +? 1;
  σ.number = n;
  emit Incremented(n);
}

-- ... `pause`/`unpause` tx blocks omitted here, see full contract ...

derive_contract "Counter" CounterStorage CounterError CounterEvent
```

Each `tx <name> { ... }` block is buffered by the elaborator; the single trailing `derive_contract "Counter" ...` command flushes all buffered `tx` bodies into plain top-level `def name : Lsc.Stmt := ...` declarations, auto-collecting them into the contract's function list — so `increment` above ends up as an ordinary `Stmt` value with no separate `TxM.run`/`Stmt.eval` wrapper step needed at the use site, and no need to name the function list by hand.

(Full contract: `examples/counter/src/Counter.lean`.)

### 3.1 What the three `deriving` handlers generate

These are **true Lean `deriving` handlers** (`Lean.Elab.registerDerivingHandler`), attached directly to the `structure`/`inductive` the contract author already writes — there is no separate command for this part, and the handlers use plain quasiquotes (`` `(term| …) ``), not hand-built `Syntax.node` trees.

- **`deriving ContractStorage`** (on the storage `structure`, e.g. `CounterStorage`): introspects the structure's fields via `Lean.getStructureFields`/projection types and emits two top-level defs, `CounterStorage.getField`/`CounterStorage.setField`, each a `match` on a `(Ty, field-name)` pair.
- **`deriving ContractEvent`** (on the event `inductive`, e.g. `CounterEvent`): introspects constructors (0 or 1 parameter each — multi-param events aren't supported by the rest of the pipeline yet, and are rejected at `deriving` time with a clear error) and emits `CounterEvent.buildEvent`.
- **`deriving ContractError`** (on the error `inductive`, e.g. `CounterError`): emits `CounterError.resolveError` (one arm per constructor) plus an `instance : ContractErrors CounterError`, whose `arith`/`fromFramework` arms are filled in by **name-matching** against `ArithError` (`Overflow`/`Underflow`/`DivisionByZero`) and `FrameworkError` (`Reentrant`/`Unauthorized`/`InvalidSelector`) constructor names — a same-named constructor in the user's error type maps directly; an unmatched case falls back to `ContractErrors.unreachableArith` (for `arith`) or to a single fixed fallback constructor (for `fromFramework`), exactly like `Counter.lean`'s hand-written instance.

All three are plain top-level `def`s/`instance`s, named by convention (`<TypeName>.getField`/`setField`/`resolveError`/`buildEvent`) — there is nothing hidden behind opaque reflection at proof time; `CounterTheorem.lean`'s proofs `simp` straight through them.

The `derive_contract`/`derive_contract_def` command (§3.4/§3.6) assembles the three derived pieces (found by the naming convention above) plus the `ContractErrors Err` instance (found by ordinary typeclass resolution) into the `ContractDSL` instance, and auto-emits the `CounterM := ContractM CounterStorage CounterEvent CounterError` abbreviation — a contract author does not write this assembly step by hand.

### 3.2 Why `deriving ContractError` alone isn't the whole safety story

`deriving ContractError` runs immediately after the error inductive is declared — **before any function body has been flushed** (`tx` bodies are buffered as they're parsed and only turned into real `def`s once the trailing `derive_contract`/`derive_contract_def` command runs). So at `deriving` time the handler can only check "does a same-named constructor exist for each `ArithError`/`FrameworkError` variant" — it cannot yet know which cases are actually *reachable* from the contract's real function bodies.

The loud, can't-silently-panic-in-production guarantee comes from a **separate, later** pass: `Lsc.Lang.Checks.checkArithErrorCoverage` (in `Lsc/Lang/Checks.lean`), which walks every function body (and storage-field initializer) once they're all known, finds every `ArithError` actually reachable through a `+?`/`-?`/`/?` operator (via `arithErrorsByFunction`/`arithErrorOp`), and fails with a clear per-function message (e.g. *"`increment` uses `+?`, which can raise `ArithError.Overflow`, but `Counter`'s error type has no `Overflow` constructor — add one or write `ContractErrors` by hand"*) if any reachable case has no matching constructor. This check is wired into `Lsc.Compile.contractToBytecode`/`deployToBytecode` (via `Lsc.Lang.Checks.validateAll`), so it runs at compile/lowering time — `lake build`-time, not deploy-time or runtime. `FrameworkError` reachability is **not** checked the same way: there is no AST node that "raises" a `FrameworkError` (unlike `Wei.Expr.addChecked` raising `Overflow`), since framework guards like reentrancy locks live outside the `Stmt`/`Expr` data a contract author writes, so there's no decidable reachability signal to walk yet.

### 3.3 The `Address`/`UInt256` disambiguation — a non-issue in practice

The original plan worried that `deriving ContractStorage` couldn't tell an `Address`-typed field from a `UInt256`-typed one, since both are literally `abbrev`s for `Word := BitVec 256`. This turned out not to be a real problem: empirically (against this project's Lean 4.30/4.31 toolchain), a structure field's *stored* projection type (as recorded in the `ConstantInfo` Lean adds when elaborating the `structure`) is **not** auto-unfolded through reducible `abbrev`s — it stays the literal constant `Lsc.Address` (resp. `Lsc.UInt256`) until something explicitly calls `whnf`. `Lsc.Deriving.fieldKindOfExpr` relies on exactly this and never calls `whnf`, so `Address` and `UInt256` (and `Wei`/`Bool`) are distinguishable from the unreduced type alone. The one real limitation: a field spelled out as some *other* alias of `BitVec 256` (not literally `Lsc.Address`/`Lsc.UInt256`/`Lsc.Wei`/`Bool`) is rejected with a clear "unsupported field type" error at `deriving` time, rather than silently miscategorized.

### 3.4 Function bodies: a fresh `tx { ... }` statement/expression grammar

Function bodies are written in a small, dss2024-style bracket-delimited grammar (`Lsc/Lang/Syntax.lean`): `declare_syntax_cat lscExpr` and `declare_syntax_cat lscStmt` introduce two **brand-new** syntax categories that are inert everywhere except inside the explicit `tx <name> { ... }` command-level delimiter, which is itself the only production that parses into them from top-level Lean syntax. Because nothing outside `tx { ... }` ever parses into `lscExpr`/`lscStmt`, there is no possibility of colliding with any existing Lean notation (`:=`, `=`, `doElem`, etc.) — the elaborator (`elabLscStmt`/`elabLscExpr`) has full `TermElabM` control over the whole block, threading a `locals : List (String × FieldKind)` association list by hand through statement elaboration. Each `tx` block is buffered when parsed, and the trailing `derive_contract`/`derive_contract_def` command later flushes it into a plain `def <name> : Lsc.Stmt := ...`.

This grammar replaced an earlier `do`-notation-over-`TxM` surface, dropped after repeated parser
conflicts with Lean's builtin `doElem`/`term` productions — see
[`docs/decisions/0001-txm-superseded-by-syntax.md`](decisions/0001-txm-superseded-by-syntax.md)
for the full history. `TxM.lean` remains in the codebase as the underlying builder/combinator
layer `tx { ... }` desugars into, still directly exercised by `Lang/TxMTest.lean`.

What the current `tx { ... }` grammar actually provides (see `Syntax.lean` and `Counter.lean` for the working source):

- **`σ.field` reads and writes.** `σ.field` is not its own dedicated grammar production — like `msg.sender`, Lean's lexer already tokenises a dotted identifier as a single compound `Name`, so a single `ident` production in `lscExpr` (for reads) and `lscStmt`'s `ident " = " lscExpr ";"` production (for writes, e.g. `σ.number = n;`) both dispatch on the parsed `Name`'s shape. The field's storage `Ty`/`FieldKind` is resolved by directly introspecting the contract's real storage `structure` (`Lsc.Deriving.getStructureFieldKinds`, via a `contractStorageExt` registry populated by `derive_contract_dsl`) — no per-field generated `σ.field` constants and no type-tag prefix (`wei`/`bool`/`addr`/`u256`) are needed anymore; the elaborator already knows each field's kind statically.
- **`require(cond) else revert ErrCtor();`** and standalone **`revert ErrCtor();`** resolve `ErrCtor` against the contract's real `Err` inductive (via `currContractTypes`/`elabErrorCtorName`, same lookup the old sugar used) — a typo or wrong constructor name is a genuine compile error. The parenthesized condition mirrors Solidity's `require(condition, "reason")`; `else` mirrors Swift's `guard cond else { ... }` precedent; the call-style `ErrCtor()` mirrors Solidity's own custom-error `revert Ctor();` syntax (0.8.4+).
- **`emit Ctor();` / `emit Ctor(arg);`** resolve the constructor's arity/expected `Ty` by reflection against the real `Event` inductive (`getCtorFieldKind`) — 0-argument and 1-argument forms are distinct grammar productions, both call-style for consistency (and, again, to match Solidity's own event/error constructor-call shape).
- **`σ.field = e;`** is plain assignment syntax (no separate `set` keyword needed, since this grammar isn't competing with anything else for the `=` token).
- **`let x = e;`** is an evaluate-once local binding, unconditionally emitting a real `Stmt.letBind` — implemented directly (not deferred, and not dispatched via a typeclass on a Lean-level value type) because the elaborator already threads `locals` through the whole block by hand. Spelled with Rust's `let` keyword and a plain `=` (rather than Lean's own `let x := e`): unlike the old `do`-notation attempts, this binding form doesn't compete with `Eq`/`doReassign` at all (it's a fresh grammar category), so there's no correctness reason to prefer `:=` here — `=` was chosen for the more familiar, Rust-like read. `σ.field = e;` (assignment) intentionally keeps the same `=` rather than switching to `:=`, so mutation and binding read consistently within `tx { ... }` blocks.
- **`if (cond) { ... } else { ... }`** and the no-`else` form `if (cond) { ... }` are real statement-list productions, compiling to `Stmt.ifThenElse`.
- **Operators**: `+?`/`-?` (checked `Wei` add/sub, left-associative, accepting a bare `Nat` literal on the right via `Wei.Expr.addCheckedNat`), `==` (equality between any two operands of matching `FieldKind`, pinned to an explicit `Ty` rather than relying on implicit inference — see `elabLscExpr`'s `==` case for why), `!` (boolean negation), and `msg.sender` (the caller address, same dotted-identifier trick as `σ.field`).
- **Boolean literals** `true`/`false` are declared via `Lean.Parser.nonReservedSymbol` rather than plain fresh `syntax` atoms — the plain-atom approach was verified to break `true`/`false`'s pre-existing meaning as Lean's builtin `Bool` literal terms everywhere else in the same file (e.g. a plain `structure`'s `paused : Bool := false` field default would stop parsing); `nonReservedSymbol` registers them as usable `lscExpr` leading tokens without reserving/shadowing them for any other syntax category.

Only `Wei` has checked add/sub today (no checked multiply/divide constructors yet, so `*?`/`/?` are not defined); `Wad`/`Ray` can follow the same pattern once needed.

### 3.5 Validation and error reporting

Domain validation (selector clashes, the linearity stub, DAG/cycle checks, the UInt256-bare-arithmetic check, and the arith-error-coverage check from §3.2) lives in `Lsc.Lang.Checks.validateAll` (`Lsc/Lang/Checks.lean`) and runs as part of `Compile.contractToBytecode`/`deployToBytecode`, returning `Except String ContractDef` — a build-time, not source-position-attached, error today (no `Lean.logErrorAt` integration yet; errors surface as plain `Except String` failures from the compile call). This also means selector-collision checking is a compile-time (`lake build`) check, not an elaboration-time positioned error — see §6 below for the same caveat applied to selector collisions specifically.

### 3.6 User workflow

```lean
-- Write storage/errors/events as plain `structure`/`inductive` + `deriving`
-- Write function bodies as `tx name { ... }` blocks
-- Write a single trailing `derive_contract "Name" Storage Err Event` to assemble the contract
-- Write proofs in the same file or a sibling file (see CounterTheorem.lean)

#check increment                             -- inspect the built Stmt AST
#eval  Compile.stmtToYul compileConfig increment      -- generate Yul (Except String)
#eval  Compile.contractToBytecodeHex counterDslDef stubEventTopic0  -- generate bytecode hex
```

No build system beyond `lake build`, no CLI, no separate compiler invocation.

---

## 4. The AST Layer

### Core types — current implementation

The actual `Lsc/Lang/AST.lean` is deliberately smaller than originally planned: core types/statements only, with `Wad`/`Ray`/linear types/mappings/calls **not yet integrated into the AST** (tracked as future work below).

```lean
/-- Core type tags. Extension types (wad, ray, linear) live in optional libs but are not
yet wired into `Ty`/`Stmt` below. -/
inductive Ty
  | uint256 | bool | address | wei | unit

/-- Core expression AST for primitive types (bool, address, uint256, unit); `Wei`'s own
expression type (`Wei.Expr`, in `Lsc/Lib/Wei/Syntax.lean`) is spliced in via `Expr`. -/
inductive CoreExpr : Ty → Type
  | lit  (t : Ty) : Lit t → CoreExpr t
  | var  (t : Ty) : Ident → CoreExpr t
  | storageGet (t : Ty) : Ident → CoreExpr t
  | txField (f : TxField) : CoreExpr (txFieldTy f)   -- caller / callvalue / timestamp
  | eq (t : Ty) : CoreExpr t → CoreExpr t → CoreExpr .bool
  | lt : CoreExpr .uint256 → CoreExpr .uint256 → CoreExpr .bool
  | le : CoreExpr .uint256 → CoreExpr .uint256 → CoreExpr .bool
  | not : CoreExpr .bool → CoreExpr .bool
  | and | or : CoreExpr .bool → CoreExpr .bool → CoreExpr .bool
  | unit : CoreExpr .unit

/-- `Expr .wei` is `Wei.Expr` (with its own checked-arithmetic constructors); every other
`Ty` delegates to `CoreExpr`. -/
def Expr : Ty → Type
  | .wei => Wei.Expr
  | .uint256 | .bool | .address | .unit => CoreExpr t

inductive Stmt
  | skip
  | seq        : Stmt → Stmt → Stmt
  | letBind    : Ident → (t : Ty) × Expr t → Stmt
  | storageSet : Ident → (t : Ty) × Expr t → Stmt
  | require    : Expr .bool → Ident → Stmt   -- Ident is error variant name
  | ifThenElse : Expr .bool → Stmt → Stmt → Stmt
  | emit       : Ident → List (Sigma Expr) → Stmt
  | revert     : Ident → Stmt
```

Checked arithmetic today only exists on `Wei` (`+?`/`-?`, via `Wei.Expr`); `Wad`/`Ray` are implemented as standalone numeric libraries (§10) but their `Expr`/`Stmt` integration, along with `tokenAmount`, `mapping`, and any `call`/`externalCall` statement forms, are **not yet part of the AST** — see the "Deliberate exclusions" list below and §7 (linear types) for what's still planned vs. implemented.

### Deliberate exclusions

No raw memory access, no inline assembly, no `delegatecall`, no `selfdestruct`, no recursion, no dynamic dispatch, no raw `keccak256`, no direct slot access, no loops today (bounded loops with invariants are potential future work, not yet designed in detail).

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

Each `FunctionDef` has a `kind` (`external`, `internal`, `view`, `constructor`). The ABI dispatcher is **generated by the framework**; users never write it.

> **Note:** Function-level `permits` lists and `LinearPermission` were removed from the AST during the lib refactor. Linearity is planned to return as a `Lib/Linear` capability model — not function-level permit lists — but today `Lsc/Lib/Linear/TokenAmount.lean` is only a minimal, non-enforcing structure stub with no capability model or AST integration yet. See [extensions/linear-types/README.md](extensions/linear-types/README.md).

Selector collision is currently checked by `Lsc.Lang.Checks.validateAll` at `Compile.contractToBytecode`/`deployToBytecode` (build/compile) time, returning a plain `Except String` error — not at Lean elaboration time, and not yet a source-position-attached error (see §3.5).

### No recursion — currently no function calls between contract functions

The current AST (`Lsc/Lang/AST.lean`) has no `call`/`externalCall` `Stmt` constructor at all, so there is no function-call graph to check for cycles today — every `tx` body is a flat sequence of statements over its own contract's storage. Cross-function/cross-contract calls, and the DAG-enforcement / no-recursion check described in earlier design iterations, are not yet implemented in the AST or `Checks.lean`.

### Arithmetic errors — strict 1:1 mapping

User error types must embed framework arithmetic errors via `ContractErrors.arith`. The mapping is **name-matched, 1:1**:

| `ArithError` variant | Required user error constructor name |
|----------------------|--------------------------|
| `Overflow` | `Overflow` |
| `Underflow` | `Underflow` |
| `DivisionByZero` | `DivisionByZero` |

(Implementation note: the originally-planned shorter name `DivByZero` was dropped in favor of matching `ArithError.DivisionByZero`'s spelling exactly — see `arithErrorCtorNames` in `Lsc/Lang/Derive.lean` and `arithErrorName` in `Lsc/Lang/Checks.lean`, which both must agree on these three strings.)

`Lsc.Lang.Checks.checkArithErrorCoverage` checks that every `ArithError` variant reachable from checked-arithmetic operations (`+?`/`-?`/`/?`) in the contract's function bodies (and storage initializers) has a same-named constructor in the user's error inductive — this runs as part of `Compile.contractToBytecode`/`deployToBytecode`, after `deriving ContractError` has already run (see §3.2 for why it can't run at `deriving` time). Collapsing multiple `ArithError` variants onto one user error constructor is a compile error. This makes every arithmetic operation an explicit proof obligation site.

```lean
-- Counter uses only +?; only Overflow is reachable → only Overflow required
inductive CounterError where
  | Paused | NotOwner | Overflow
  deriving Repr, DecidableEq, Lsc.Deriving.ContractError

-- A contract using +?, -?, /? would need all three reachable variants declared:
-- | Overflow | Underflow | DivisionByZero
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

No implicit overflow. No implicit precision loss. Operations that can fail return `Except Err`. **No arithmetic on bare `UInt256` in contract code** — all numeric computation uses `Wei`, `Wad`, or `Ray`.

### UInt256 — representation only

`UInt256` is the underlying word type for EVM storage and ABI encoding. It is **not** a numeric domain type in contract code: there are no `+?`, `-?`, `*?`, `/?`, or wrapping operators on bare `UInt256` in `Tx`/`View` bodies. Use it for opaque words (selectors, `block.timestamp`, mapping keys, external call calldata) and for ordering comparisons (`<`, `≤`, `==`).

Framework-internal primitives (used to implement `Wei`/`Wad`/`Ray`, linear types, and `@math` lowering) live in a private `UInt256` namespace:

```lean
namespace UInt256  -- framework-internal; not in contract surface syntax
  def addChecked  : UInt256 → UInt256 → Except ArithError UInt256
  def subChecked  : UInt256 → UInt256 → Except ArithError UInt256
  def mulChecked  : UInt256 → UInt256 → Except ArithError UInt256
  def divFloor    : UInt256 → UInt256 → Except ArithError UInt256
  def mulDiv      : UInt256 → UInt256 → UInt256 → Except ArithError UInt256
                 -- 512-bit intermediate; used by Wad/Ray mul/div
end UInt256
```

Contract authors never call these directly. All user-facing arithmetic goes through `Wei`, `Wad`, or `Ray`.

### Integer numeric type (`Wei`)

`Wei` is the 0-decimal counterpart to `Wad` and `Ray`: a newtype over `UInt256` that makes integer quantities explicit in storage and events. `1 Wei = 1` raw unit — no scaling factor.

```lean
structure Wei where raw : UInt256   -- 1 Wei = 1 (identity encoding)

namespace Wei
  def addChecked : Wei → Wei → Except ArithError Wei
  def subChecked : Wei → Wei → Except ArithError Wei
  def mulChecked : Wei → Wei → Except ArithError Wei
  def divFloor   : Wei → Wei → Except ArithError Wei
  -- each delegates to the corresponding UInt256 op on `.raw`
end Wei
```

Use `Wei` for counts, token amounts in base units, and other whole-number domain values. Reserve bare `UInt256` for protocol-level primitives (selectors, timestamps, mapping keys) where the type carries no unit meaning — **compare and pass through only, never arithmetic**. Checked ops (`+?`, `-?`, `*?`, `/?`) are available on `Wei` and `Wad`/`Ray` (add/sub on fixed-point types; mul/div via bracket pairs or named forms). There are no bracket-pair rounding ops on `Wei`.

### Fixed-point types

```lean
structure Wad where raw : UInt256   -- 1 Wad = 1e18

namespace Wad
  def addChecked : Wad → Wad → Except ArithError Wad
  def subChecked : Wad → Wad → Except ArithError Wad
  def mulDown   : Wad → Wad → Except ArithError Wad   -- floor
  def mulHalfUp : Wad → Wad → Except ArithError Wad   -- round to nearest
  def divDown   : Wad → Wad → Except ArithError Wad
  def divHalfUp : Wad → Wad → Except ArithError Wad
  -- Key theorems proved once, available to all users:
  theorem mul_comm   : Wad.mulHalfUp a b = Wad.mulHalfUp b a
  theorem mul_le_left : b.raw ≤ WAD → Wad.mulHalfUp a b = .ok r → r.raw ≤ a.raw
end Wad
```

`Ray` follows the same pattern with `1 Ray = 1e27` (`addChecked`, `subChecked`, and mul/div variants like `Wad`).

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

### Compilation correctness — what is currently proved

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

The full end-to-end theorem is **future work**. See §2 for the complete trust boundary.

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

### The human-statement-first invariant

**Every theorem must be writable, in English, as a sentence a non-Lean-reading reviewer would
recognize as "the property I asked for" — before a line of Lean is written.** Concretely, follow
this order every time:

1. **State it like a human would say it.** E.g. "transferring debits the sender and credits the
   recipient, and this holds for every account and every amount" — not "there exists a `Nat` `n`
   such that some `if`/`then`/`else` tree evaluates to `n`". If you can't say the property in one
   plain sentence, it isn't ready to formalize yet.
2. **Transcribe that sentence into a Lean theorem statement**, universally quantified over
   whatever the human sentence quantified over (every state, every address, every amount — not
   one fixed witness). Read the *statement* back against the sentence from step 1 before writing
   any proof.
3. **Only then prove it.**

This was violated early in `Escrow`/`Token`'s test suites in two specific, recurring ways — watch
for both when reviewing new proofs:

- **Concrete-witness tests standing in for theorems.** A theorem like `runS (transfer bob 30) s₀
  = .ok (...)` for one hand-picked `s₀`/`bob`/`30` is a unit test, not a proof of "`transfer`
  debits the sender" — it says nothing about any other state/address/amount. Escrow's
  `EscrowTheorem.lean`/`TokenTheorem.lean` and Interest's `InterestTheorems.lean` `deposit`/
  `setRate` theorems were rewritten from `native_decide`-on-a-witness to fully `∀`-quantified
  statements once a tractable symbolic proof existed (`simp` unfolding + `omega`, composed through
  `PairM`'s `bind_apply`/`liftCaller_apply`/`exec_unlocked_ok` lemmas for cross-contract calls).
  `native_decide` on a concrete state remains the pragmatic fallback *only* where a fully symbolic
  characterization genuinely isn't tractable (e.g. `Interest.accrueInterest`'s chained
  multiply-then-divide-then-add — see `INTEREST.md`); that tradeoff must be stated explicitly in
  the surrounding doc comment, not left implicit.
- **Dense `∀ a, if .. then .. else if .. then .. else ..` formulas masquerading as readable
  theorems.** A single theorem correctly characterizing *every* address at once
  (`EscrowProofs.runTransferOk`/`TokenProofs.runTransferOk`, `EscrowProofs.runReleaseOk`) is the
  right **Tier 1** building block, but is not itself something a human would ever say out loud —
  don't expose it as one of the "required theorems" a reviewer reads. Split it into the separate,
  named claims a human actually makes (`release_debits_escrow`, `release_credits_recipient`,
  `release_preserves_other_balances`, `release_self_release_is_noop`; `transfer_debits_sender`,
  `transfer_credits_recipient`, `transfer_preserves_other_balances`,
  `transfer_self_transfer_is_noop`), each a one-line corollary of the Tier 1 lemma via `obtain`
  + `simp`/`simpa`. This is the standard **two-tier proof structure**: Tier 1
  (`*Proofs.lean`) proves one dense, fully general characterization lemma per contract function;
  Tier 2 (`*Theorem.lean`) states every human-readable required property as a short corollary of
  the matching Tier 1 lemma, and is the only file a reviewer should need to read to know *what*
  was proved. `EscrowProofs.lean`/`EscrowTheorem.lean`, `TokenProofs.lean`/`TokenTheorem.lean`, and
  `InterestProofs.lean`/`InterestTheorems.lean` are the reference examples of this split.

---

## 13. Reference Contracts

The canonical contracts live in [reference/COUNTER.md](reference/COUNTER.md) and [reference/AMM.md](reference/AMM.md). Key constraints:

**Counter**: every framework feature must be exercisable against this contract before any DeFi contract is attempted. Uses `Wei` for the counter value (0-decimal numeric type). All required theorems must close with `simp` + `omega` in at most ~5 lines.

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
- **dss2024**: the `declare_syntax_cat` + `macro_rules` pattern for a DSL that compiles to a verified AST. The `Lang/AST.lean`/`Lang/Eval.lean` (typed `Expr`/`Stmt` + `ContractM`/`Stmt.eval`) layers still follow this pattern. An earlier *surface syntax* attempt (a `declare_syntax_cat lsc_*` custom grammar building raw `Syntax.node` trees by hand, following dss2024's `Syntax.lean` pattern but reimplementing its machinery from scratch) was implemented and then deleted for being ~700 lines of brittle codegen; it was replaced first by the plain-Lean-plus-`deriving` + `TxM` do-notation approach, and then again by the current `tx { ... }` grammar (§3.4, `Lsc/Lang/Syntax.lean`) — a fresh `declare_syntax_cat lscExpr`/`lscStmt` pair, inert outside an explicit `tx { ... }` delimiter, much closer in spirit and size to dss2024's own `Syntax.lean` than the deleted first attempt was. dss2024's bracket-delimited-fresh-syntax-category pattern is therefore **not just** a reference for the AST/eval split anymore — it is now also the actual mechanism by which contracts are authored.
- **EvmYulLean** (Nethermind): provides Yul and EVM semantics; treated as trusted ground truth.
- **Move Prover**: demonstrated that a restricted, DeFi-oriented language with co-designed verification is practical. Key lessons: resource types, alias-free memory, static dispatch, minimal language surface. This design independently converges on all four.

## Appendix B: Implementation Details Intentionally Omitted

The following are left to the implementer and should not be added to this document:

- Lean module structure and file organization (see `framework/IMPLEMENTATION.md`)
- Exact `macro_rules` syntax for the surface DSL (see `framework/IMPLEMENTATION.md`)
- EvmYulLean API usage details
- ABI encoding implementation
- Selector computation
- `Finmap` library choice
- Test harness structure
