import Mathlib.Logic.Equiv.Defs
import Lsc.Lang.Amount
import Lsc.Lang.Tx
import Lean.Elab.Term

/-!
# External-contract interface: `Interface`, `Binding`, `Tx.call`

A declared interface is a deterministic may-model plus ABI metadata. A `Binding` names
the storage field that holds the callee address and the ghost field that the model
updates. `Tx.call` takes no address: the compiled call `sload`s the bound field.
-/

namespace Lsc

/-- How the compiler lowers a successful CALL's return data. -/
inductive AbiRet
  | word
  | boolOpt
  | none
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Compiler-only ABI of one interface method. -/
structure AbiSpec where
  selector : Nat
  arity : Nat
  ret : AbiRet
  deriving DecidableEq, Repr, Lean.ToExpr

/-- A foreign-contract may-model. `n` is the method count (`idx : Method ≃ Fin n`). -/
structure Interface where
  Ghost : Type
  Method : Type
  n : Nat
  model : Method → Address → List Nat → Ghost → Option (Nat × Ghost)
  abi : Method → AbiSpec
  idx : Method ≃ Fin n

/-- A storage slot holding a callee of interface `I` that denominates asset `a`.
One-field structure so `Ref I token0` and `Ref I token1` do not unify. -/
structure Ref (I : Interface) (a : Asset) where
  addr : Address
  deriving Repr

namespace Ref
variable {I : Interface} {a : Asset}
instance : DecidableEq (Ref I a) := fun x y =>
  if h : x.addr = y.addr then
    isTrue (by cases x; cases y; subst h; rfl)
  else
    isFalse (by intro h'; cases x; cases y; exact h (Ref.mk.inj h'))
instance : Inhabited (Ref I a) := ⟨⟨(0 : Address)⟩⟩
end Ref

/-- Static binding of an interface: address lives in our storage, ghost in `World.ext`. -/
structure Binding (I : Interface) (S X : Type) where
  addr : S → Address
  get : X → I.Ghost
  set : X → I.Ghost → X

namespace Tx

variable {I : Interface} {S X E ε : Type}

/-- CALL through a binding. Faults and model-`none` revert the caller (`callFailed`).
The model sees `ctx.self` (our address, the token's `msg.sender`); the callee is
implicit in the binding's ghost. The compiler `sload`s `b.addr` for the EVM CALL. -/
def call (b : Binding I S X) (m : I.Method) (args : List Nat) : Tx S X E ε Nat :=
  fun ctx w =>
    if w.faults w.ncalls then .error .callFailed
    else
      match I.model m ctx.self args (b.get w.ext) with
      | none => .error .callFailed
      | some (ret, g') =>
          .ok (ret, { w with ext := b.set w.ext g', ncalls := w.ncalls + 1 })

/-- Statement-position CALL (discard the returned word). Same bind as `Stmt.denote (.call …)`. -/
def callUnit (b : Binding I S X) (m : I.Method) (args : List Nat) : Tx S X E ε Unit :=
  Tx.call b m args >>= fun _ => pure ()

@[simp] theorem run_call (b : Binding I S X) (m : I.Method) (args : List Nat)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (Tx.call (E := E) (ε := ε) b m args) ctx w =
      if w.faults w.ncalls then .error .callFailed
      else
        match I.model m ctx.self args (b.get w.ext) with
        | none => .error .callFailed
        | some (ret, g') =>
            .ok (ret, { w with ext := b.set w.ext g', ncalls := w.ncalls + 1 }) :=
  rfl

/-- `simp` after a `do` block leaves `ReaderT.run` (`.run`), which does not match `Tx.run_call`. -/
@[simp] theorem call_run (b : Binding I S X) (m : I.Method) (args : List Nat)
    (ctx : Ctx) (w : World S X E) :
    (Tx.call (E := E) (ε := ε) b m args).run ctx w =
      if w.faults w.ncalls then .error .callFailed
      else
        match I.model m ctx.self args (b.get w.ext) with
        | none => .error .callFailed
        | some (ret, g') =>
            .ok (ret, { w with ext := b.set w.ext g', ncalls := w.ncalls + 1 }) :=
  rfl

@[simp] theorem run_callUnit (b : Binding I S X) (m : I.Method) (args : List Nat)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (Tx.callUnit (E := E) (ε := ε) b m args) ctx w =
      match Tx.run (Tx.call (E := E) (ε := ε) b m args) ctx w with
      | .ok (_, w') => .ok ((), w')
      | .error e => .error e := by
  simp only [callUnit]
  rw [run_bind]
  cases Tx.run (Tx.call (E := E) (ε := ε) b m args) ctx w with
  | ok _ => simp [run_pure]
  | error _ => rfl

/-- `simp` after a `do` block leaves `ReaderT.run` (`.run`), which does not match `Tx.run_callUnit`. -/
@[simp] theorem callUnit_run (b : Binding I S X) (m : I.Method) (args : List Nat)
    (ctx : Ctx) (w : World S X E) :
    (Tx.callUnit (E := E) (ε := ε) b m args).run ctx w =
      match (Tx.call (E := E) (ε := ε) b m args).run ctx w with
      | .ok (_, w') => .ok ((), w')
      | .error e => .error e :=
  run_callUnit (E := E) (ε := ε) b m args ctx w

theorem call_self (b : Binding I S X) (m : I.Method) (args : List Nat)
    {ctx : Ctx} {w : World S X E} {v : Nat} {w' : World S X E} :
    Tx.run (Tx.call (E := E) (ε := ε) b m args) ctx w = .ok (v, w') → w'.self = w.self := by
  simp [Tx.run_call]
  split
  · intro h; cases h
  · split
    · intro h; cases h
    · intro h; cases h; rfl

end Tx

namespace Lang
variable {S X E ε : Type}

/-- Reverse `worldAfter_map` for `Ref.mk <$>` Core denotations. -/
theorem worldAfter_refMk {I : Interface} {a : Asset} (x : Tx S X E ε Address)
    (ctx : Ctx) (w : World S X E) :
    worldAfter x ctx w = worldAfter (Ref.mk (I := I) (a := a) <$> x) ctx w :=
  (worldAfter_map (Ref.mk (I := I) (a := a)) x ctx w).symm

end Lang

/-! ### `read` / `write` elaborators

`Amount` / `Ref` fields are stored as words in Core. The sugar elaborates to
the same `ofWord` / `.raw` (and `{ addr := · }` / `.addr`) wrappers the schema
uses, so `lsc_reify` certificates close. -/
namespace Syntax
open Lean Elab Term Meta PrettyPrinter

private def isAmount : Expr → Bool := fun ty => ty.isAppOf ``Lsc.Amount
private def isRef : Expr → Bool := fun ty => ty.isAppOf ``Lsc.Ref

/-- Storage type `S` of an expected `Tx S _ _ _ _` (or its `ReaderT` unfold). -/
def txStorage? (ty? : Option Expr) : TermElabM (Option Expr) := do
  let some ty0 := ty? | return none
  let ty ← instantiateMVars ty0
  -- Reducible only: unfold `M` / `Tx`, not `StateT`.
  let ty ← withReducible (whnf ty)
  if ty.isAppOf ``Lsc.Tx then return some (ty.getArg! 0)
  if ty.isAppOf ``ReaderT then
    let st := ty.getArg! 1
    if st.isAppOf ``StateT then
      let w ← withReducible (whnf (st.getArg! 0))
      if w.isAppOf ``Lsc.World then return some (w.getArg! 0)
  return none

def elabFieldProj (f : Ident) (expectedType? : Option Expr) : TermElabM Expr := do
  let some S ← txStorage? expectedType? |
    throwError "read/write: could not infer storage type (use in a `Tx` context)"
  let α ← mkFreshExprMVar none
  let expected ← mkArrow S α
  elabTerm (← `(fun $(sigma) => $(projOf f))) expected

/-- Value type of storage field `f` (scalar / map1 / map2). -/
def fieldValTy (f : Ident) (expectedType? : Option Expr) : TermElabM Expr := do
  forallTelescopeReducing (← inferType (← elabFieldProj f expectedType?)) fun _ body =>
    whnfD body

/-- Number of mapping keys `f` expects (0 = scalar). -/
def fieldKeyCount (f : Ident) (expectedType? : Option Expr) : TermElabM Nat := do
  forallTelescopeReducing (← inferType (← elabFieldProj f expectedType?)) fun xs _ =>
    return xs.size - 1

def wrapLoad (_α : Expr) (load : Term) (expectedType? : Option Expr) : TermElabM Expr :=
  elabTerm load expectedType?

@[term_elab lscRead]
def elabRead : TermElab := fun stx expectedType? => do
  tryPostponeIfNoneOrMVar expectedType?
  match stx with
  | `(read $f:ident) => do
    let n ← fieldKeyCount f expectedType?
    unless n == 0 do throwError "read: `{f.getId}` needs keys"
    let α ← fieldValTy f expectedType?
    let load ← `(Lsc.Tx.load (fun $(sigma) => $(← fieldProj f α)))
    wrapLoad α load expectedType?
  | `(read $f:ident [ $ks:term,* ]) => do
    let keys := ks.getElems
    let n ← fieldKeyCount f expectedType?
    unless n == keys.size do
      throwError "read: `{f.getId}` expects {n} key(s)"
    let α ← fieldValTy f expectedType?
    match keys.toList with
    | [k] =>
      let kk := mkIdent `k
      let load ← `(Lsc.Tx.loadMap (fun $(sigma) $kk =>
        $(← fieldProjKey f kk α)) $k)
      wrapLoad α load expectedType?
    | [k₁, k₂] =>
      let a := mkIdent `k₁
      let b := mkIdent `k₂
      let load ← `(Lsc.Tx.loadMap2 (fun $(sigma) $a $b =>
        $(← fieldProjKey2 f a b α)) $k₁ $k₂)
      wrapLoad α load expectedType?
    | _ => throwError "read: mappings have one or two keys"
  | _ => throwUnsupportedSyntax

where
  fieldProj (f : Ident) (_α : Expr) : TermElabM Term := do
    let p := projOf f
    `($p)
  fieldProjKey (f k : Ident) (_α : Expr) : TermElabM Term := do
    let p := projOf f
    `($p $k)
  fieldProjKey2 (f k₁ k₂ : Ident) (_α : Expr) : TermElabM Term := do
    let p := projOf f
    `($p $k₁ $k₂)

@[term_elab lscWrite]
def elabWrite : TermElab := fun stx expectedType? => do
  tryPostponeIfNoneOrMVar expectedType?
  match stx with
  | `(write $f:ident $v) => do
    let n ← fieldKeyCount f expectedType?
    unless n == 0 do throwError "write: `{f.getId}` needs keys"
    let α ← fieldValTy f expectedType?
    elabTerm (← storeScalar f α v) expectedType?
  | `(write $f:ident [ $ks:term,* ] $v) => do
    let keys := ks.getElems
    let n ← fieldKeyCount f expectedType?
    unless n == keys.size do
      throwError "write: `{f.getId}` expects {n} key(s)"
    let α ← fieldValTy f expectedType?
    match keys.toList with
    | [k] => elabTerm (← storeMap1 f α k v) expectedType?
    | [k₁, k₂] => elabTerm (← storeMap2 f α k₁ k₂ v) expectedType?
    | _ => throwError "write: mappings have one or two keys"
  | _ => throwUnsupportedSyntax

where
  storeScalar (f : Ident) (α : Expr) (v : Term) : TermElabM Term := do
    let α ← whnfD α
    let σ := sigma
    if isAmount α then
      let tyStx ← delab α
      `(Lsc.Tx.store (fun $σ m => { $σ with $f:ident := Lsc.Amount.ofWord m })
          (Lsc.Amount.raw ($v : $tyStx)))
    else if isRef α then
      let tyStx ← delab α
      `(Lsc.Tx.store (fun $σ m => { $σ with $f:ident := { addr := m } })
          (Lsc.Ref.addr ($v : $tyStx)))
    else
      `(Lsc.Tx.store (fun $σ m => { $σ with $f:ident := m }) $v)
  storeMap1 (f : Ident) (α : Expr) (k v : Term) : TermElabM Term := do
    let α ← whnfD α
    let σ := sigma
    let p := projOf f
    let kk := mkIdent `k
    let mm := mkIdent `m
    if isAmount α then
      `(Lsc.Tx.storeMap (fun $σ $kk => Lsc.Amount.raw ($p $kk))
          (fun $σ $mm => { $σ with $f:ident := fun $kk => Lsc.Amount.ofWord ($mm $kk) })
          $k (Lsc.Amount.raw $v))
    else if isRef α then
      `(Lsc.Tx.storeMap (fun $σ $kk => Lsc.Ref.addr ($p $kk))
          (fun $σ $mm => { $σ with $f:ident := fun $kk => { addr := $mm $kk } })
          $k (Lsc.Ref.addr $v))
    else
      `(Lsc.Tx.storeMap (fun $σ => $p) (fun $σ $mm => { $σ with $f:ident := $mm }) $k $v)
  storeMap2 (f : Ident) (α : Expr) (k₁ k₂ v : Term) : TermElabM Term := do
    let α ← whnfD α
    let σ := sigma
    let p := projOf f
    let a := mkIdent `k₁
    let b := mkIdent `k₂
    let mm := mkIdent `m
    if isAmount α then
      `(Lsc.Tx.storeMap2 (fun $σ $a $b => Lsc.Amount.raw ($p $a $b))
          (fun $σ $mm => { $σ with $f:ident := fun $a $b => Lsc.Amount.ofWord ($mm $a $b) })
          $k₁ $k₂ (Lsc.Amount.raw $v))
    else if isRef α then
      `(Lsc.Tx.storeMap2 (fun $σ $a $b => Lsc.Ref.addr ($p $a $b))
          (fun $σ $mm => { $σ with $f:ident := fun $a $b => { addr := $mm $a $b } })
          $k₁ $k₂ (Lsc.Ref.addr $v))
    else
      `(Lsc.Tx.storeMap2 (fun $σ => $p) (fun $σ $mm => { $σ with $f:ident := $mm })
          $k₁ $k₂ $v)

end Syntax

end Lsc
