import Lsc.Lang.AST
import Lsc.Lang.Eval
import Lsc.Lib.Wei.Syntax
import Lsc.Lib.Wad.Syntax
import Mathlib.Control.Monad.Writer
import Lean

open Lean

/-!
# `TxM`: a free-monad-style builder for `Stmt`

This is step 1 of the Lean-first DSL redesign (see
`docs/DESIGN.md` and the migration plan). The goal is to let
contract authors build `Stmt` values using ordinary Lean `do`-notation
instead of a bespoke custom grammar (`Lsc.Lang.Syntax`, kept around for
now but superseded by this file).

`TxM` does not *execute* anything — it is a "writer" that accumulates a
`Stmt` fragment via `Stmt.seq`/`Stmt.skip` as its monoid operations. Once a
`TxM Unit` computation is `run`, the result is a pure `Stmt` data value, fed
into the existing `Stmt.eval`/`Compile.*` pipeline exactly as the
hand-written ASTs in `examples/counter/src/Counter.lean` are today.

## Storage-field notation (`σ.field`) — approach and limitations

The plan suggests a typed, fully-generic `σ.field` notation that picks the
right constructor (`Wei.Expr.storageGet` vs. `CoreExpr.storageGet t`)
based on the *declared type* of `field` in some contract's storage
structure. Doing this in full generality requires either:

- a per-contract `FieldMap`/typeclass populated by the (not-yet-implemented,
  step 2) `deriving ContractStorage` handler, or
- expected-type-directed elaboration sophisticated enough to distinguish
  `Wei.Expr` from `CoreExpr .bool`/`.address`/`.uint256` results.

Neither exists yet at this step, so — per the task's explicit allowance to
prioritize "something working with good ergonomics" — storage-field *reads*
are implemented here as a small family of *type-tagged* notations: `wei
σ.field`, `bool σ.field`, `addr σ.field`, `u256 σ.field`. Writes use plain
function calls (`setWei "field" e`, etc.) rather than a `σ.field := e`
do-notation sugar — see the comment above the storage-writes section for why
that sugar had to be dropped (a parser ambiguity with the read notation).
This is slightly more verbose than a bare `σ.field` but is fully
type-correct today and gives a single, obvious place (the leading type tag)
for the future `deriving` handler to special-case or eventually subsume
with full inference.

## Plain `let` vs. `letWei`/`letBool`/`letAddr`/`letU256` — IMPORTANT

A `TxM` `do`-block is *building* a `Stmt` AST, not executing one. A plain
Lean `let n := wei σ.number +? 1` only binds `n` to an *AST term*
(`Wei.Expr.addCheckedNat (Wei.Expr.storageGet "number") 1`) at
*elaboration* time — it does **not** emit any `Stmt` and does **not**
evaluate anything. If that same term is referenced again later in the
same function body, evaluation re-runs the whole term — including any
`storageGet`s inside it — against whatever the *current* storage is at
that later point. Concretely:

```
let n := wei σ.number +? 1
setWei "number" n         -- evaluates `σ.number +? 1` against OLD storage: fine
emitEvent "Incremented" [⟨Ty.wei, n⟩]  -- evaluates `σ.number +? 1` AGAIN, now against
                                   -- the storage `setWei` just wrote: WRONG (double-counts)
```

So: a plain `let` is only safe when the right-hand side either (a)
doesn't transitively read any storage field at all, or (b) reads fields
that are never written-to again before the `let`-bound name is reused.

Whenever a storage-derived value will be referenced again *after* a
write to a field it transitively reads, use `letWei`/`letBool`/
`letAddr`/`letU256` instead: `let n ← letWei "n" (wei σ.number +? 1)`.
These emit a real `Stmt.letBind name ⟨ty, e⟩` (which `Stmt.evalWith`
evaluates exactly once, at that point in the statement sequence, and
binds into `LocalEnv`) and hand back not `e` itself but a `var`
reference (`Wei.Expr.var name` / `CoreExpr.var ty name`) resolved
through `LocalEnv` at eval time. Reusing that reference after subsequent
storage writes is then safe, since it always resolves to the
once-computed, bind-time value — exactly the pattern
`examples/counter/src/Counter.lean`'s hand-written `incrementAst` uses
(`Stmt.letBind "n" ...` then `Wei.Expr.var "n"` in both the storage-set
and the `emit`).

`TxM`'s `do`-notation supports `let n ← letWei ...` cleanly because the
base monad of `WriterT Stmt Id` is `Id`, a real (if trivial) monad: `n`
is bound to the *pure result value* `letWei` returns (the `var`
reference), while the `Stmt.letBind` it emits via `tellStmt` is
accumulated into the writer output exactly like every other statement
combinator in this file.
-/

namespace Lsc

/-- `Stmt.seq` as the `Append` monoid operation, so `Stmt` can back a
`WriterT`-style accumulator. -/
instance : Append Stmt where
  append := Stmt.seq

/-- `Stmt.skip` as the `Append` monoid's identity element. -/
instance : EmptyCollection Stmt where
  emptyCollection := Stmt.skip

/-- The statement-builder monad: `do`-notation over `TxM` constructs a
`Stmt` value (via `tell`/`Stmt.seq`/`Stmt.skip`), it does not run anything.
Reuses Lean's/Mathlib's stdlib `WriterT` (`Mathlib.Control.Monad.Writer`,
since plain `WriterT` is no longer bundled in Lean core) — `Monad`/`Bind`/
`Pure` come for free from the `[EmptyCollection Stmt] [Append Stmt]`
instances above. -/
abbrev TxM (α : Type) : Type := WriterT Stmt Id α

namespace TxM

/-- Run a `TxM` computation, extracting the `Stmt` it built (and any
result value). Pure, since the base monad is `Id`. -/
def runWith (m : TxM α) : α × Stmt := Id.run (WriterT.run m)

/-- Run a `TxM Unit` computation down to the `Stmt` it accumulated. This is
the bridge back into the existing `Stmt`/`Compile.*` pipeline: a function
body written as `do ...` in `TxM` becomes a plain `Stmt` value exactly like
`Counter.lean`'s hand-written `incrementAst`. -/
def run (m : TxM Unit) : Stmt := (runWith m).2

end TxM

/-- Lets a bare `def foo : TxM Unit := do ...` be spliced directly wherever a
`Stmt` is expected (e.g. `FunctionDef.body`), without a separately-named
`fooAst := TxM.run foo` wrapper. Named (rather than an anonymous `fun`
directly in the `Coe` instance) and `@[simp]` so proofs can unfold the
coercion by name, e.g. `simp [increment, TxM.toStmt, TxM.run]`. -/
@[simp] def TxM.toStmt (t : TxM Unit) : Stmt := TxM.run t

instance : Coe (TxM Unit) Stmt := ⟨TxM.toStmt⟩

/-- Lets a bare `def foo : TxM Unit := do ...` be spliced directly wherever a
`ContractM S E Err Unit` action is expected (e.g. `runS foo s`), without a
separately-named `foo : ContractM S E Err Unit := Stmt.eval fooAst` wrapper.
Named + `@[simp]` for the same reason as `TxM.toStmt` above. -/
@[simp] def TxM.toContractM {S E Err : Type} [ContractErrors Err] [ContractDSL S E Err]
    (t : TxM Unit) : ContractM S E Err Unit :=
  Stmt.eval (TxM.run t)

instance {S E Err : Type} [ContractErrors Err] [ContractDSL S E Err] :
    Coe (TxM Unit) (ContractM S E Err Unit) :=
  ⟨TxM.toContractM⟩

/-- Lets a bare `def foo : Stmt := ..` (e.g. a `Syntax.lean`
`tx foo { .. }` block) be used directly wherever a `ContractM S E Err Unit`
action is expected (e.g. `runS foo s`), mirroring `TxM.toContractM` above
for `Stmt`-typed defs that never went through `TxM`'s `do`-notation at
all. -/
@[simp] def Stmt.toContractM {S E Err : Type} [ContractErrors Err] [ContractDSL S E Err]
    (s : Stmt) : ContractM S E Err Unit :=
  Stmt.eval s

instance {S E Err : Type} [ContractErrors Err] [ContractDSL S E Err] :
    Coe Stmt (ContractM S E Err Unit) :=
  ⟨Stmt.toContractM⟩

-- `@[simp]` on `TxM.runWith`/`TxM.run` plus every statement-builder
-- combinator below lets proofs that need to reduce a `TxM`-built
-- `incrementAst`/`pauseAst`/... down to its concrete `Stmt` shape just call
-- plain `simp [TxM.run]` (or even bare `simp`, since these are global simp
-- lemmas now) instead of repeating a long `simp only [...]` allowlist of
-- every combinator name at each call site — see
-- `examples/counter/test/CounterTheorem.lean` for where this matters
-- (proofs there unfold `incrementAst`/`pauseAst`/`unpauseAst` this way).
attribute [simp] TxM.runWith TxM.run

/-- Append one raw `Stmt` fragment to the computation being built. The
primitive all other statement combinators below are defined in terms of. -/
@[simp] def tellStmt (s : Stmt) : TxM Unit := MonadWriter.tell s

/-! ## Storage reads -/

/-- `wei σ.field` reads a `Wei`-typed storage field. -/
@[simp] def weiField (field : Ident) : Wei.Expr := .storageGet field

/-- `wad σ.field` reads a `Wad`-typed storage field. -/
@[simp] def wadField (field : Ident) : Wad.Expr := .storageGet field

/-- `bool σ.field` reads a `Bool`-typed storage field. -/
@[simp] def boolField (field : Ident) : CoreExpr .bool := .storageGet .bool field

/-- `addr σ.field` reads an `Address`-typed storage field. -/
@[simp] def addrField (field : Ident) : CoreExpr .address := .storageGet .address field

/-- `u256 σ.field` reads a `UInt256`-typed storage field. -/
@[simp] def u256Field (field : Ident) : CoreExpr .uint256 := .storageGet .uint256 field

/-- Extract `field` from a `σ.field`-shaped identifier, or fail with a
clear error otherwise. Used directly by `Lang/Syntax.lean`'s `lscExpr`/
`lscStmt` field resolution — the `wei σ.field`/`bool σ.field`/... prefix
notation family that used to call this from `term`-level `macro_rules` was
removed, since `Syntax.lean` resolves `σ.field` via its own grammar
instead. -/
def sigmaFieldName? (n : Lean.Name) : Option String :=
  match n with
  | .str (.str .anonymous "σ") field => some field
  | _ => none

/-! ## Evaluate-once `let`-binding (`letWei`/`letBool`/`letAddr`/`letU256`)

See the module docstring ("Plain `let` vs. ...") for *why* these exist:
a plain Lean `let` only binds an AST term, which gets re-evaluated (and
can silently re-read mutated storage) every time it's referenced. These
combinators instead emit a real `Stmt.letBind`, evaluated exactly once
at that point in the sequence, and hand back a `var` reference to the
bound result — safe to reuse after subsequent storage writes.

One variant per `Ty` tag, matching the `weiField`/`boolField`/`addrField`/
`u256Field` read-notation family above. Use as `let n ← letWei "n" e` in
a `TxM` `do`-block. -/

/-- `let n ← letWei name e` emits `Stmt.letBind name ⟨Ty.wei, e⟩` (evaluated
once, at this point in the sequence) and returns `Wei.Expr.var name`, a
reference safe to reuse even after later writes to fields `e` reads. -/
@[simp] def letWei (name : Ident) (e : Wei.Expr) : TxM Wei.Expr := do
  tellStmt (Stmt.letBind name ⟨Ty.wei, e⟩)
  pure (Wei.Expr.var name)

/-- `let w ← letWad name e`, the `Wad`-typed analogue of `letWei`. -/
@[simp] def letWad (name : Ident) (e : Wad.Expr) : TxM Wad.Expr := do
  tellStmt (Stmt.letBind name ⟨Ty.wad, e⟩)
  pure (Wad.Expr.var name)

/-- `let b ← letBool name e`, the `Bool`-typed analogue of `letWei`. -/
@[simp] def letBool (name : Ident) (e : CoreExpr .bool) : TxM (CoreExpr .bool) := do
  tellStmt (Stmt.letBind name ⟨Ty.bool, e⟩)
  pure (CoreExpr.var .bool name)

/-- `let a ← letAddr name e`, the `Address`-typed analogue of `letWei`. -/
@[simp] def letAddr (name : Ident) (e : CoreExpr .address) : TxM (CoreExpr .address) := do
  tellStmt (Stmt.letBind name ⟨Ty.address, e⟩)
  pure (CoreExpr.var .address name)

/-- `let u ← letU256 name e`, the `UInt256`-typed analogue of `letWei`. -/
@[simp] def letU256 (name : Ident) (e : CoreExpr .uint256) : TxM (CoreExpr .uint256) := do
  tellStmt (Stmt.letBind name ⟨Ty.uint256, e⟩)
  pure (CoreExpr.var .uint256 name)

/-! ## Storage writes -/

@[simp] def setWei (field : Ident) (e : Wei.Expr) : TxM Unit :=
  tellStmt (Stmt.storageSet field ⟨Ty.wei, e⟩)

@[simp] def setWad (field : Ident) (e : Wad.Expr) : TxM Unit :=
  tellStmt (Stmt.storageSet field ⟨Ty.wad, e⟩)

@[simp] def setBool (field : Ident) (e : CoreExpr .bool) : TxM Unit :=
  tellStmt (Stmt.storageSet field ⟨Ty.bool, e⟩)

@[simp] def setAddr (field : Ident) (e : CoreExpr .address) : TxM Unit :=
  tellStmt (Stmt.storageSet field ⟨Ty.address, e⟩)

@[simp] def setU256 (field : Ident) (e : CoreExpr .uint256) : TxM Unit :=
  tellStmt (Stmt.storageSet field ⟨Ty.uint256, e⟩)

-- Storage writes are plain `TxM Unit` actions (`setWei`/`setBool`/...
-- above), e.g. `setWei "number" n`, used directly as a `do`-block statement.
-- The generic `set σ.field e` sugar and the `var x := e` binder that used to
-- live here (both do-notation-only workarounds) were removed in favor of
-- `Lang/Syntax.lean`'s `tx { ... }` grammar, which has its own `σ.field =
-- e;`/`let x = e;` productions with direct access to the field's `FieldKind`
-- (no `SetSigma`/`LetBindable` typeclass dispatch needed there).

/-! ## `require`/`revert`/`emitEvent`

Errors are still referenced by bare `Ident` (a `String`), matching `Stmt`'s
existing shape (`Stmt.require`/`Stmt.revert` both take an `Ident`). These are
the low-level primitives — the recommended contract-author-facing surface is
`revert .Ctor` / `require <cond> else revert .Ctor` / `emit Ctor args`
(real-constructor sugar, elaborated against the contract's actual
`Err`/`Event` inductive), declared in `Lsc.Deriving` (`Lang/Derive.lean`)
since it needs `derive_contract_dsl`'s namespace → `(errName, eventName)`
registry. These bare-`Ident` primitives remain directly usable (e.g. by
`TxMTest.lean`, which builds `Stmt`s without a real derived contract).

The event-emission primitive is named `emitEvent`, not `emit`: `emit` itself is
reserved for the real-constructor sugar above, since (unlike `require`/
`revert`, whose bare-`Ident` primitives (`requireE`/`revertE`) already have
distinct names from their sugar) an earlier attempt at sharing the `emit`
spelling between this primitive and the sugar ran into a genuine parser
conflict — declaring `emit`-keyword-led syntax while a same-named plain
identifier already existed made every existing use of that identifier
ambiguous. See `Lang/Derive.lean`'s docstring above the `emit` sugar
elaborator for the empirical history. -/

@[simp] def requireE (cond : CoreExpr .bool) (err : Ident) : TxM Unit :=
  tellStmt (Stmt.require cond err)

@[simp] def revertE (err : Ident) : TxM Unit :=
  tellStmt (Stmt.revert err)

/-- Generic event-emission combinator. The recommended surface is `emit
Ctor args` (see module docstring above); `emitEvent` remains the primitive it
compiles down to, and stays directly usable for the rare case of a
dynamically-built event name/arg list. -/
@[simp] def emitEvent (name : Ident) (args : List ExprAny) : TxM Unit :=
  tellStmt (Stmt.emit name args)

/-! ## Conditional branching

A contract-level `if` branches on an `Expr Ty.bool` *data* value evaluated
later (inside `Stmt.eval`/on-chain), not on a `Bool` known at build time, so
it cannot be plain Lean `if`. `ifE` runs both branches through `TxM.run`
(pure, since the base monad is `Id`) to extract their `Stmt`s and wraps the
result in `Stmt.ifThenElse`. -/
@[simp] def ifE (cond : CoreExpr .bool) (thn els : TxM Unit) : TxM Unit :=
  tellStmt (Stmt.ifThenElse cond (TxM.run thn) (TxM.run els))

/-! ## `CoreExpr.eqAuto`

`Lang/Syntax.lean`'s `==` elaborator calls this directly (with an explicit
`t` argument, not relying on implicit inference — see its docstring), so the
function stays; the `+?`/`-?`/`===`/`!`/`msg.sender` *notations* that used to
live here (for building `Wei.Expr`/`CoreExpr` terms directly in `do`-blocks)
were removed, since `Syntax.lean`'s `lscExpr` grammar has its own,
independent `+?`/`-?`/`==`/`!`/`msg.sender` productions that elaborate
straight to `Wei.Expr.addChecked`/`CoreExpr.not`/`CoreExpr.txField`/etc.
without going through any of these `term`-level notations. -/
@[simp] def CoreExpr.eqAuto {t : Ty} (a b : CoreExpr t) : CoreExpr Ty.bool := CoreExpr.eq t a b

end Lsc
