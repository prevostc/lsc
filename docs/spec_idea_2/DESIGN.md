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
│  Source  (plain Lean structure/inductive/do)     │  ← user writes this
│  + `deriving ContractStorage/ContractError/      │  ← thin reflection-based
│    ContractEvent` + `derive_contract_dsl`        │     glue, not a custom parser
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

## 3. The Source Layer — Plain Lean + Three `deriving` Handlers

> **This section was rewritten to describe what was actually built.** The original design called for a bespoke surface grammar (`contract … where`, `declare_syntax_cat lsc_*`, `macro_rules` synthesizing raw `Syntax.node` trees). That approach was implemented, found to be ~700 lines of brittle codegen (`LscV2/Lang/Syntax.lean`, `Contract.lean`, `ContractGen.lean`, `ContractTypes.lean`), and **deleted**. What replaced it: contracts are written as **plain Lean `structure`/`inductive` declarations** with custom `deriving` handlers, plus function bodies written in a small, dss2024-style bracket-delimited `tx <name> { ... }` grammar of its own (`declare_syntax_cat lscExpr`/`lscStmt`, `LscV2/Lang/Syntax2.lean`) — fresh syntax categories that are inert everywhere outside the `tx { ... }` delimiter, not layered on Lean's `term`/`doElem`. There is still no separate compiler or external toolchain — everything is Lean — but there is also no general-purpose custom parser either: every contract-author-facing construct below is either a real Lean declaration, a real `deriving` clause, or a production of this small, purpose-built statement/expression grammar.

```lean
structure CounterStorage where
  number : Wei := Wei.mkNat 0
  paused : Bool := false
  owner  : Address := 0
  deriving Repr, LscV2.Deriving.ContractStorage

inductive CounterError where
  | Paused
  | NotOwner
  | Overflow
  deriving Repr, DecidableEq, LscV2.Deriving.ContractError

inductive CounterEvent where
  | Incremented (n : Wei)
  | Paused
  | Unpaused
  deriving Repr, DecidableEq, LscV2.Deriving.ContractEvent

derive_contract_dsl CounterStorage CounterError CounterEvent
abbrev CounterM := ContractM CounterStorage CounterEvent CounterError

tx increment {
  require(!σ.paused, Paused);
  var n := σ.number +? 1;
  σ.number = n;
  emit Incremented(n);
}
```

Each `tx <name> { ... }` block expands to a plain top-level `def name : LscV2.Stmt := ...`, so `increment` above is an ordinary `Stmt` value usable anywhere one is expected (e.g. directly in `derive_contract_def`'s function list) — no separate `TxM.run`/`Stmt.eval` wrapper step is needed at the use site.

(Full contract: `v2/examples/counter/src/Counter.lean`.)

### 3.1 What the three `deriving` handlers generate

Unlike the deleted macro, these are **true Lean `deriving` handlers** (`Lean.Elab.registerDerivingHandler`), attached directly to the `structure`/`inductive` the contract author already writes — there is no separate command for this part, and (because this file imports neither the old `Syntax.lean` nor `Contract.lean`) there is no tokeniser conflict to dodge, so the handlers use plain quasiquotes (`` `(term| …) ``), not hand-built `Syntax.node` trees.

- **`deriving ContractStorage`** (on the storage `structure`, e.g. `CounterStorage`): introspects the structure's fields via `Lean.getStructureFields`/projection types and emits two top-level defs, `CounterStorage.getField`/`CounterStorage.setField`, each a `match` on a `(Ty, field-name)` pair.
- **`deriving ContractEvent`** (on the event `inductive`, e.g. `CounterEvent`): introspects constructors (0 or 1 parameter each — multi-param events aren't supported by the rest of the pipeline yet, and are rejected at `deriving` time with a clear error) and emits `CounterEvent.buildEvent`.
- **`deriving ContractError`** (on the error `inductive`, e.g. `CounterError`): emits `CounterError.resolveError` (one arm per constructor) plus an `instance : ContractErrors CounterError`, whose `arith`/`fromFramework` arms are filled in by **name-matching** against `ArithError` (`Overflow`/`Underflow`/`DivisionByZero`) and `FrameworkError` (`Reentrant`/`Unauthorized`/`InvalidSelector`) constructor names — a same-named constructor in the user's error type maps directly; an unmatched case falls back to `ContractErrors.unreachableArith` (for `arith`) or to a single fixed fallback constructor (for `fromFramework`), exactly like `Counter.lean`'s hand-written instance.

All three are plain top-level `def`s/`instance`s, named by convention (`<TypeName>.getField`/`setField`/`resolveError`/`buildEvent`) — there is nothing hidden behind opaque reflection at proof time; `CounterTheorem.lean`'s proofs `simp` straight through them.

One final explicit line, `derive_contract_dsl FooStorage FooError FooEvent`, assembles the three derived pieces (found by the naming convention above) plus the `ContractErrors Err` instance (found by ordinary typeclass resolution) into the `ContractDSL` instance — this one line was kept explicit rather than folded into the last `deriving` clause, since doing so would require the three types to be named consistently and saves only one line.

### 3.2 Why `deriving ContractError` alone isn't the whole safety story

`deriving ContractError` runs immediately after the error inductive is declared — **before any function body exists** (function bodies are written later in the file, since they need `CounterM`, which needs `derive_contract_dsl`, which needs the error type to already be fully elaborated). So at `deriving` time the handler can only check "does a same-named constructor exist for each `ArithError`/`FrameworkError` variant" — it cannot yet know which cases are actually *reachable* from the contract's real function bodies.

The loud, can't-silently-panic-in-production guarantee comes from a **separate, later** pass: `LscV2.Lang.Checks.checkArithErrorCoverage` (in `v2/LscV2/Lang/Checks.lean`), which walks every function body (and storage-field initializer) once they're all known, finds every `ArithError` actually reachable through a `+?`/`-?`/`/?` operator (via `arithErrorsByFunction`/`arithErrorOp`), and fails with a clear per-function message (e.g. *"`increment` uses `+?`, which can raise `ArithError.Overflow`, but `Counter`'s error type has no `Overflow` constructor — add one or write `ContractErrors` by hand"*) if any reachable case has no matching constructor. This check is wired into `LscV2.Compile.contractToBytecode`/`deployToBytecode` (via `Checks.validateAll`), so it runs at compile/lowering time — `lake build`-time, not deploy-time or runtime. `FrameworkError` reachability is **not** checked the same way: there is no AST node that "raises" a `FrameworkError` (unlike `Wei.Expr.addChecked` raising `Overflow`), since framework guards like reentrancy locks live outside the `Stmt`/`Expr` data a contract author writes, so there's no decidable reachability signal to walk yet.

### 3.3 The `Address`/`UInt256` disambiguation — a non-issue in practice

The original plan worried that `deriving ContractStorage` couldn't tell an `Address`-typed field from a `UInt256`-typed one, since both are literally `abbrev`s for `Word := BitVec 256`. This turned out not to be a real problem: empirically (against this project's Lean 4.30/4.31 toolchain), a structure field's *stored* projection type (as recorded in the `ConstantInfo` Lean adds when elaborating the `structure`) is **not** auto-unfolded through reducible `abbrev`s — it stays the literal constant `LscV2.Address` (resp. `LscV2.UInt256`) until something explicitly calls `whnf`. `LscV2.Deriving.fieldKindOfExpr` relies on exactly this and never calls `whnf`, so `Address` and `UInt256` (and `Wei`/`Bool`) are distinguishable from the unreduced type alone. The one real limitation: a field spelled out as some *other* alias of `BitVec 256` (not literally `LscV2.Address`/`LscV2.UInt256`/`LscV2.Wei`/`Bool`) is rejected with a clear "unsupported field type" error at `deriving` time, rather than silently miscategorized.

### 3.4 Function bodies: a fresh `tx { ... }` statement/expression grammar

Function bodies are written in a small, dss2024-style bracket-delimited grammar (`LscV2/Lang/Syntax2.lean`): `declare_syntax_cat lscExpr` and `declare_syntax_cat lscStmt` introduce two **brand-new** syntax categories that are inert everywhere except inside the explicit `tx <name> { ... }` command-level delimiter, which is itself the only production that parses into them from top-level Lean syntax. Because nothing outside `tx { ... }` ever parses into `lscExpr`/`lscStmt`, there is no possibility of colliding with any existing Lean notation (`:=`, `=`, `doElem`, etc.) — the elaborator (`elabLscStmt`/`elabLscExpr`) has full `TermElabM` control over the whole block, threading a `locals : List (String × FieldKind)` association list by hand through statement elaboration, and produces a plain `def <name> : LscV2.Stmt := ...` at the end.

**Why this replaced the earlier `do`-notation-over-`TxM` approach.** The previous surface (`v2/LscV2/Lang/TxM.lean`) built `Stmt` values via ordinary Lean `do`-notation over a small writer monad (`TxM α := WriterT Stmt Id α`), reusing Lean's stdlib `term`/`doElem` categories instead of declaring new ones. That approach worked, but every piece of "assignment-shaped" or "keyword-shaped" sugar it wanted had to route around a real, empirically-verified parser conflict with an *existing* Lean production, rather than being a clean grammar choice:

- A generic `σ.field := e` write notation was tried twice (as a `doElem`-level macro, and later as a lower-level raw-`Syntax`-indexed macro) and dropped both times: `:=` is already claimed by Lean's builtin mutable-local-reassignment `doElem` (`doReassign`), so a second `doElem` with the identical `ident := term` shape either failed to declare at all (a quotation pattern-match rejection) or produced an ambiguous `choice` node at every `:=`-assignment site that Lean's `do`-block elaborator refused to resolve (`unexpected do-element of kind choice`).
- `σ.field = e` was tried next, on the theory that a term-level `=` (an ordinary `infix:50` notation, not a `doElem`) might fare better, since term-level ambiguity *can* sometimes be resolved by type-checking each alternative. It didn't: a second `ident " = " term : term` production doesn't even produce a resolvable `choice` node — the parser deterministically shadows `Eq` for *every* `ident = term` occurrence project-wide, breaking ordinary equality checks and proof hypotheses (`b = false`, `... = rfl`) throughout the codebase. This was reverted immediately.
- A generic type-tagged read family (`wei σ.field`, `bool σ.field`, `addr σ.field`, `u256 σ.field`) and a `set σ.field e` write family stood in as the workaround for the two failed attempts above, plus a `var x := e` binder (dispatching via a `LetBindable` typeclass on the bound value's Lean type) to force an evaluate-once `Stmt.letBind` instead of a plain, storage-read-re-evaluating Lean `let`.
- Even `emit`'s naming had a parser-conflict history: sharing the `emit` spelling between the real-constructor sugar and its underlying raw primitive caused declaration-site ambiguity, resolved only by renaming the primitive out of the way (`emitEvent`) rather than the sugar.

These were genuine, hard-won empirical findings (documented in full in `TxM.lean`'s docstrings) about the limits of layering new notation onto Lean's existing `term`/`doElem` grammar — not mistakes, and not wasted effort: they are exactly what motivated moving to fresh `declare_syntax_cat`s instead of trying to patch the `do`-notation approach further. With a fresh, purpose-built grammar, none of these workarounds are needed: `tx { ... }` has its own `σ.field = e;` assignment production, its own `var x := e;` binder, and its own `require`/`revert`/`emit` statement forms, none of which compete with any Lean builtin because `lscStmt`/`lscExpr` are categories Lean's core parser never enters except through the `tx { ... }` delimiter.

What the current `tx { ... }` grammar actually provides (see `Syntax2.lean` and `Counter.lean` for the working source):

- **`σ.field` reads and writes.** `σ.field` is not its own dedicated grammar production — like `msg.sender`, Lean's lexer already tokenises a dotted identifier as a single compound `Name`, so a single `ident` production in `lscExpr` (for reads) and `lscStmt`'s `ident " = " lscExpr ";"` production (for writes, e.g. `σ.number = n;`) both dispatch on the parsed `Name`'s shape. The field's storage `Ty`/`FieldKind` is resolved by directly introspecting the contract's real storage `structure` (`LscV2.Deriving.getStructureFieldKinds`, via a `contractStorageExt` registry populated by `derive_contract_dsl`) — no per-field generated `σ.field` constants and no type-tag prefix (`wei`/`bool`/`addr`/`u256`) are needed anymore; the elaborator already knows each field's kind statically.
- **`require(cond, ErrCtor);`** and **`revert(ErrCtor);`** resolve `ErrCtor` against the contract's real `Err` inductive (via `currContractTypes`/`elabErrorCtorName`, same lookup the old sugar used) — a typo or wrong constructor name is a genuine compile error.
- **`emit Ctor;` / `emit Ctor(arg);`** resolve the constructor's arity/expected `Ty` by reflection against the real `Event` inductive (`getCtorFieldKind`) — 0-argument and 1-argument forms are distinct grammar productions.
- **`σ.field = e;`** is plain assignment syntax (no separate `set` keyword needed, since this grammar isn't competing with anything else for the `=` token).
- **`var x := e;`** is an evaluate-once local binding, unconditionally emitting a real `Stmt.letBind` — implemented directly (not deferred, and not dispatched via a typeclass on a Lean-level value type) because the elaborator already threads `locals` through the whole block by hand.
- **`if (cond) { ... } else { ... }`** and the no-`else` form `if (cond) { ... }` are real statement-list productions, compiling to `Stmt.ifThenElse`.
- **Operators**: `+?`/`-?` (checked `Wei` add/sub, left-associative, accepting a bare `Nat` literal on the right via `Wei.Expr.addCheckedNat`), `==` (equality between any two operands of matching `FieldKind`, pinned to an explicit `Ty` rather than relying on implicit inference — see `elabLscExpr`'s `==` case for why), `!` (boolean negation), and `msg.sender` (the caller address, same dotted-identifier trick as `σ.field`).
- **Boolean literals** `true`/`false` are declared via `Lean.Parser.nonReservedSymbol` rather than plain fresh `syntax` atoms — the plain-atom approach was verified to break `true`/`false`'s pre-existing meaning as Lean's builtin `Bool` literal terms everywhere else in the same file (e.g. a plain `structure`'s `paused : Bool := false` field default would stop parsing); `nonReservedSymbol` registers them as usable `lscExpr` leading tokens without reserving/shadowing them for any other syntax category.

Only `Wei` has checked add/sub today (no checked multiply/divide constructors yet, so `*?`/`/?` are not defined); `Wad`/`Ray` can follow the same pattern once needed.

### 3.5 Validation and error reporting

Domain validation (selector clashes, the linearity stub, DAG/cycle checks, the UInt256-bare-arithmetic check, and the arith-error-coverage check from §3.2) lives in `LscV2.Checks.validateAll` (`v2/LscV2/Lang/Checks.lean`) and runs as part of `Compile.contractToBytecode`/`deployToBytecode`, returning `Except String ContractDef` — a build-time, not source-position-attached, error today (no `Lean.logErrorAt` integration yet; errors surface as plain `Except String` failures from the compile call).

### 3.6 User workflow

```lean
-- Write storage/errors/events as plain `structure`/`inductive` + `deriving`
-- Write `derive_contract_dsl`, the `CounterM` abbrev, and function bodies as `tx name { ... }`
-- Write proofs in the same file or a sibling file (see CounterTheorem.lean)

#check increment                             -- inspect the built Stmt AST
#eval  Compile.stmtToYul compileConfig increment      -- generate Yul (Except String)
#eval  Compile.contractToBytecodeHex counterDslDef stubEventTopic0  -- generate bytecode hex
```

No build system beyond `lake build`, no CLI, no separate compiler invocation.

---

## 4. The AST Layer

### Core types

```lean
inductive Ty
  | uint256 | bool | address
  | wei | wad | ray
  | tokenAmount             -- linear type
  | mapping (k v : Ty)     -- opaque; no iteration exposed

inductive Expr : Ty → Type
  | lit         : UInt256 → Expr .uint256
  | litBool     : Bool → Expr .bool
  | var         : Ident → Expr t
  | storageGet  : Ident → Expr t
  -- Arithmetic — only on typed numerics (Wei / Wad / Ray); never on bare UInt256
  | weiAddChecked | weiSubChecked | weiMulChecked | weiDivFloor
  | wadAddChecked | wadSubChecked
  | wadMulDown | wadMulUp | wadMulHalfUp | wadDivDown | wadDivHalfUp
  | rayAddChecked | raySubChecked
  | rayMulDown | rayMulUp | rayMulHalfUp | rayDivDown | rayDivHalfUp
  -- Comparisons (UInt256 allowed for ordering only — timestamps, etc.)
  | eq   : Expr t → Expr t → Expr .bool
  | lt   : Expr .uint256 → Expr .uint256 → Expr .bool
  | le   : Expr .uint256 → Expr .uint256 → Expr .bool
  -- Context (read-only, populated by dispatcher)
  | caller | callvalue | timestamp
  -- Linear type operations
  | tokenMint   : Expr .wei → Expr .tokenAmount
  | tokenBurn   : Expr .tokenAmount → Expr .wei
  | tokenSplit  : Expr .tokenAmount → Expr .wei → Expr (.tokenAmount × .tokenAmount)
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

Each `FunctionDef` has a `kind` (`external`, `internal`, `view`, `constructor`). The ABI dispatcher is **generated by the framework**; users never write it.

> **Note (v2):** Function-level `permits` lists and `LinearPermission` were removed from the AST during the lib refactor. Linearity will return as a `Lib/Linear` capability model — not function-level permit lists. See [extensions/linear-types/README.md](extensions/linear-types/README.md).

Selector collision is checked at elaboration time and reported as a positioned error.

### No recursion — DAG enforcement

Recursive function calls are **banned in v1**. The call graph (built from `Stmt.call` nodes) must be a DAG. Checked at elaboration time. Every function call terminates by construction, which eliminates a large class of reentrancy patterns.

### Arithmetic errors — strict 1:1 mapping

User error types must embed framework arithmetic errors via `ContractErrors.arith`. The mapping is **name-matched, 1:1**:

| `ArithError` variant | Required user error constructor name |
|----------------------|--------------------------|
| `Overflow` | `Overflow` |
| `Underflow` | `Underflow` |
| `DivisionByZero` | `DivisionByZero` |

(Implementation note: the originally-planned shorter name `DivByZero` was dropped in favor of matching `ArithError.DivisionByZero`'s spelling exactly — see `arithErrorCtorNames` in `LscV2/Lang/Derive.lean` and `arithErrorName` in `LscV2/Lang/Checks.lean`, which both must agree on these three strings.)

`LscV2.Lang.Checks.checkArithErrorCoverage` checks that every `ArithError` variant reachable from checked-arithmetic operations (`+?`/`-?`/`/?`) in the contract's function bodies (and storage initializers) has a same-named constructor in the user's error inductive — this runs as part of `Compile.contractToBytecode`/`deployToBytecode`, after `deriving ContractError` has already run (see §3.2 for why it can't run at `deriving` time). Collapsing multiple `ArithError` variants onto one user error constructor is a compile error. This makes every arithmetic operation an explicit proof obligation site.

```lean
-- Counter uses only +?; only Overflow is reachable → only Overflow required
inductive CounterError where
  | Paused | NotOwner | Overflow
  deriving Repr, DecidableEq, LscV2.Deriving.ContractError

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
- **dss2024**: the `declare_syntax_cat` + `macro_rules` pattern for a DSL that compiles to a verified AST. The `Lang/AST.lean`/`Lang/Eval.lean` (typed `Expr`/`Stmt` + `ContractM`/`Stmt.eval`) layers still follow this pattern. An earlier *surface syntax* attempt (a `declare_syntax_cat lsc_*` custom grammar building raw `Syntax.node` trees by hand, following dss2024's `Syntax.lean` pattern but reimplementing its machinery from scratch) was implemented and then deleted for being ~700 lines of brittle codegen; it was replaced first by the plain-Lean-plus-`deriving` + `TxM` do-notation approach, and then again by the current `tx { ... }` grammar (§3.4, `LscV2/Lang/Syntax2.lean`) — a fresh `declare_syntax_cat lscExpr`/`lscStmt` pair, inert outside an explicit `tx { ... }` delimiter, much closer in spirit and size to dss2024's own `Syntax.lean` than the deleted first attempt was. dss2024's bracket-delimited-fresh-syntax-category pattern is therefore **not just** a reference for the AST/eval split anymore — it is now also the actual mechanism by which contracts are authored.
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
