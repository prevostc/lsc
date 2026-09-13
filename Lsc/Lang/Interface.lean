import Lsc.Lang.Amount
import Lsc.Lang.Word
import KeccakEngine.Sponge
import Lean.Elab.Term

/-!
# External-contract interfaces: `Fn`/`View` signatures, oracle callee, `Ref`

An interface is an ordinary Lean structure whose fields are `Fn`/`View` markers
(the ABI). `deriving Interface` (see `Lsc.Lang.InterfaceDeriving`) generates the
method table, typed calls, a per-interface `I.Ref`, `I.Impl`, and `Impl.ofRef`.

Callee behaviour is a deterministic, memory-blind `Oracle` on `World.ext`.
`Tx.call` / `Tx.view` / `Tx.tryCall` consult `w.oracle` at a concrete address;
a `Fn` revert is `oracle.call = none` (`Err.callFailed`). `View` methods are
pure oracle reads and leave the world unchanged. The oracle field is never
modified by a Tx primitive. Reentrancy during a call is not modelled in this
slice (`self` is unchanged).

`I.Spec` is a user-written `Prop` structure over `T : I.Impl …`, in the same
shape as our theorems (success as hypothesis, state delta as conclusion). The
adversary is the baseline oracle; a `Spec` hypothesis restricts it.

Dot notation `asset.transferFrom …` is `I.Ref.transferFrom` via a generated
`I.Ref` structure. `Ref (I args)` is a macro expanding to `I.Ref args`.
`asset.try.transferFrom` is the non-reverting form
(`Tx … (Except (Err ε) R)`). `asset.impl w` is `I.Impl.ofRef asset`, used as
`(hT : I.Spec (asset.impl w))`.

TODO: payable methods are not modelled yet.
-/

namespace Lsc

/-- Field-type marker: a state-changing ABI method. `τ` is the curried
argument telescope ending at the return type, e.g. `Address → Amount a → Bool`. -/
structure Fn (τ : Type) : Type where

/-- Field-type marker: a pure ABI view. `τ` is the curried argument telescope
ending at the return type, e.g. `Address → Amount a`. -/
structure View (τ : Type) : Type where

/-- How a successful CALL's return data is read. -/
inductive AbiRet
  | word
  | boolOpt
  | none
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Compiler-only ABI of one interface method (selector, arity, return kind). -/
structure AbiSpec where
  selector : Nat
  arity : Nat
  ret : AbiRet
  deriving DecidableEq, Repr, Lean.ToExpr

/-- One ABI method: name, selector (`keccak(name(types))/2^224`), arity, view bit,
return kind. -/
structure MethodSig where
  name : String
  selector : Nat
  arity : Nat
  isView : Bool
  ret : AbiRet
  deriving DecidableEq, Repr, Lean.ToExpr

def MethodSig.toAbiSpec (m : MethodSig) : AbiSpec :=
  ⟨m.selector, m.arity, m.ret⟩

/-! ## ABI hashing (same formula as `selectorOf` in `Contract.lean`) -/

/-- Big-endian bytes as a natural number. -/
def bytesToNat (bytes : ByteArray) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- `keccak256` of a byte string, as a word. -/
def keccakWord (bytes : ByteArray) : Nat :=
  bytesToNat (KeccakEngine.keccak256 bytes)

/-- 4-byte selector: `keccak256("name(type,…)") / 2^224`. Same as `selectorOf`. -/
def methodSelector (name : String) (argTys : List String) : Nat :=
  keccakWord (s!"{name}({String.intercalate "," argTys})").toUTF8 / 2 ^ 224

/-! ## ABI types -/

/-- Solidity ABI name and one-word encoding of a surface type. -/
class AbiType (α : Type) where
  name : String
  encode : α → Word

instance : AbiType Word where
  name := "uint256"
  encode := id

instance {a : Asset} : AbiType (Amount a) where
  name := "uint256"
  encode := Amount.raw

instance : AbiType Address where
  name := "address"
  encode := Address.toWord

instance : AbiType Bool where
  name := "bool"
  encode := fun b => if b then 1 else 0

/-- Decode of a method's return words. Bool uses the `boolOpt` convention:
empty return is `true`, otherwise the word is non-zero. Word/Amount/Address
need exactly one word. `Unit` ignores the payload. -/
class AbiRetType (α : Type) where
  kind : AbiRet
  decode : List Word → Option α

instance : AbiRetType Bool where
  kind := .boolOpt
  decode
    | [] => some true
    | [w] => some (w != 0)
    | _ => none

instance : AbiRetType Word where
  kind := .word
  decode
    | [w] => some w
    | _ => none

instance {a : Asset} : AbiRetType (Amount a) where
  kind := .word
  decode
    | [w] => some ⟨w⟩
    | _ => none

instance : AbiRetType Address where
  kind := .word
  decode
    | [w] => some (w : Address)
    | _ => none

instance : AbiRetType Unit where
  kind := .none
  decode := fun _ => some ()

/-- View/`Impl` reads are total: a malformed ABI payload becomes `default`. -/
def decodeOrDefault {α} [AbiRetType α] [Inhabited α] (rets : List Word) : α :=
  (AbiRetType.decode rets).getD default

/-! ## `Interface` class -/

/-- Method table of an interface type `I` (the ABI structure, e.g. `IERC20 a`). -/
class Interface (I : Type) where
  methods : List MethodSig

/-- Look up a method selector by ABI name. `0` if missing (should not happen
for a derived table). -/
def Interface.selector {I : Type} [Interface I] (name : String) : Nat :=
  match (methods (I := I)).find? (fun m => m.name = name) with
  | some m => m.selector
  | none => 0

/-! ## `Ref (I args)` → `I.Ref args`

Per-interface `I.Ref` is a one-field `{ addr : Address }` structure generated
by `deriving Interface`. This macro makes `Ref (IERC20 vaultAsset)` that type,
so `asset.transferFrom` resolves to `IERC20.Ref.transferFrom`. -/
syntax:arg (name := lscRefTy) "Ref" "(" ident term:arg* ")" : term

macro_rules
  | `(Ref ($f:ident $args:term*)) =>
    let r := Lean.mkIdent (f.getId ++ `Ref)
    `($r $args*)

/-! ## Oracle CALL / STATICCALL primitives

`self` is unchanged: reentrancy during a call is not modelled in this slice. -/

namespace Tx

variable {S X E ε α : Type} [AbiRetType α]

/-- CALL through the world's oracle. `none` or an undecodable payload is
`.callFailed`. Success updates `ext` only. -/
def call (addr : Address) (sel : Nat) (args : List Word) : Tx S X E ε α :=
  fun _ctx w =>
    match w.oracle.call addr sel args w.ext with
    | none => .error .callFailed
    | some (rets, x') =>
      match AbiRetType.decode (α := α) rets with
      | none => .error .callFailed
      | some v => .ok (v, { w with ext := x' })

/-- STATICCALL-like view: `oracle.view`, world unchanged. Undecodable payload
is `.callFailed`. -/
def view (addr : Address) (sel : Nat) (args : List Word) : Tx S X E ε α :=
  fun _ctx w =>
    match AbiRetType.decode (α := α) (w.oracle.view addr sel args w.ext) with
    | none => .error .callFailed
    | some v => .ok (v, w)

/-- Non-reverting CALL: oracle `none` or an undecodable payload becomes
`.ok (.error .callFailed, w)` (world unchanged). A decoded success updates
`ext` and returns `.ok (.ok v, w')`. -/
def tryCall (addr : Address) (sel : Nat) (args : List Word) :
    Tx S X E ε (Except (Err ε) α) :=
  fun _ctx w =>
    match w.oracle.call addr sel args w.ext with
    | none => .ok (.error .callFailed, w)
    | some (rets, x') =>
      match AbiRetType.decode (α := α) rets with
      | none => .ok (.error .callFailed, w)
      | some v => .ok (.ok v, { w with ext := x' })

/-- Non-reverting view: decode failure is `.ok (.error .callFailed, w)`. -/
def tryView (addr : Address) (sel : Nat) (args : List Word) :
    Tx S X E ε (Except (Err ε) α) :=
  fun _ctx w =>
    match AbiRetType.decode (α := α) (w.oracle.view addr sel args w.ext) with
    | none => .ok (.error .callFailed, w)
    | some v => .ok (.ok v, w)

@[simp] theorem run_call (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (call (ε := ε) (α := α) addr sel args) ctx w =
      match w.oracle.call addr sel args w.ext with
      | none => .error .callFailed
      | some (rets, x') =>
        match AbiRetType.decode (α := α) rets with
        | none => .error .callFailed
        | some v => .ok (v, { w with ext := x' }) :=
  rfl

@[simp] theorem call_run (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    (call (ε := ε) (α := α) addr sel args).run ctx w =
      Tx.run (call (ε := ε) (α := α) addr sel args) ctx w :=
  rfl

@[simp] theorem run_view (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (view (ε := ε) (α := α) addr sel args) ctx w =
      match AbiRetType.decode (α := α) (w.oracle.view addr sel args w.ext) with
      | none => .error .callFailed
      | some v => .ok (v, w) :=
  rfl

@[simp] theorem view_run (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    (view (ε := ε) (α := α) addr sel args).run ctx w =
      Tx.run (view (ε := ε) (α := α) addr sel args) ctx w :=
  rfl

@[simp] theorem run_tryCall (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (tryCall (ε := ε) (α := α) addr sel args) ctx w =
      match w.oracle.call addr sel args w.ext with
      | none => .ok (.error .callFailed, w)
      | some (rets, x') =>
        match AbiRetType.decode (α := α) rets with
        | none => .ok (.error .callFailed, w)
        | some v => .ok (.ok v, { w with ext := x' }) :=
  rfl

@[simp] theorem tryCall_run (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    (tryCall (ε := ε) (α := α) addr sel args).run ctx w =
      Tx.run (tryCall (ε := ε) (α := α) addr sel args) ctx w :=
  rfl

@[simp] theorem run_tryView (addr : Address) (sel : Nat) (args : List Word)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (tryView (ε := ε) (α := α) addr sel args) ctx w =
      match AbiRetType.decode (α := α) (w.oracle.view addr sel args w.ext) with
      | none => .ok (.error .callFailed, w)
      | some v => .ok (.ok v, w) :=
  rfl

/-- A successful CALL leaves `self` unchanged (no reentrancy in this slice). -/
theorem call_self (addr : Address) (sel : Nat) (args : List Word)
    {ctx : Ctx} {w : World S X E} {v : α} {w' : World S X E} :
    Tx.run (call (ε := ε) (α := α) addr sel args) ctx w = .ok (v, w') →
      w'.self = w.self := by
  simp [run_call]
  split
  · intro h; cases h
  · split
    · intro h; cases h
    · intro h; cases h; rfl

/-- A successful view returns the pre-world. -/
theorem view_world (addr : Address) (sel : Nat) (args : List Word)
    {ctx : Ctx} {w : World S X E} {v : α} {w' : World S X E} :
    Tx.run (view (ε := ε) (α := α) addr sel args) ctx w = .ok (v, w') →
      w' = w := by
  simp [run_view]
  split
  · intro h; cases h
  · intro h; cases h; rfl

end Tx

/-! ### `read` / `write` elaborators

`Amount` / `*.Ref` fields are stored as words in Core. The sugar elaborates to
the same `ofWord` / `.raw` (and `{ addr := · }` / `.addr`) wrappers the schema
uses, so `lsc_reify` certificates close. -/
namespace Syntax
open Lean Elab Term Meta PrettyPrinter

private def isAmount : Expr → Bool := fun ty => ty.isAppOf ``Lsc.Amount
/-- Per-interface `I.Ref` (and any leftover `Lsc.Ref`) is a one-field address. -/
private def isRef (ty : Expr) : Bool :=
  match ty.getAppFn.constName? with
  | some n => n.getString! == "Ref"
  | none => false

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
          (($v : $tyStx).addr))
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
      `(Lsc.Tx.storeMap (fun $σ $kk => ($p $kk).addr)
          (fun $σ $mm => { $σ with $f:ident := fun $kk => { addr := $mm $kk } })
          $k ($v).addr)
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
      `(Lsc.Tx.storeMap2 (fun $σ $a $b => ($p $a $b).addr)
          (fun $σ $mm => { $σ with $f:ident := fun $a $b => { addr := $mm $a $b } })
          $k₁ $k₂ ($v).addr)
    else
      `(Lsc.Tx.storeMap2 (fun $σ => $p) (fun $σ $mm => { $σ with $f:ident := $mm })
          $k₁ $k₂ $v)

end Syntax

end Lsc
