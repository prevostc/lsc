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
(`Tx … (Except (Err ε) R)`). `asset.impl` is `I.Impl.ofRef asset` over a
`WorldView` (oracle plus `ext`), used as `(hT : I.Spec asset.impl)`. A
contract that *is* the interface (Token) still has `C.impl` over `World`.
Fn fields of `I.Impl` are `Option` (no error parameter): a successful
`Tx.run` is that `some` via `Tx.run_ok_toOption`.

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

end Tx

/-- Decode an oracle CALL on a `WorldView` into `Option (α × WorldView)`.
`I.Impl.ofRef` Fn fields are this definition, so they share a name with
`Tx.run (call …)` projected onto `w.view`. -/
def WorldView.callDecode {X α : Type} [AbiRetType α] (v : WorldView X)
    (addr : Address) (sel : Nat) (args : List Word) :
    Option (α × WorldView X) :=
  match v.oracle.call addr sel args v.ext with
  | none => none
  | some (rets, x') =>
    match AbiRetType.decode (α := α) rets with
    | none => none
    | some ret => some (ret, { v with ext := x' })

/-! ### Core-word wrappers

Core binds `Nat`. `callAsNat .word` is definitionally `Tx.call (α := Nat)`.
`boolOpt` / `none` are `<$>` of the typed `Tx.call` so ABI decode matches
`AbiRetType` exactly. -/
namespace Tx

variable {S X E ε : Type}

/-- Bit encoding of a `Bool` ABI result (`true` ↔ `1`). -/
@[inline] def boolBit (b : Bool) : Nat := if b then 1 else 0

/-- Inverse of `boolBit` on `{0,1}`. Non-zero is `true`, matching
`AbiRetType Bool` (`w != 0`) and ERC20 `boolOpt`. Reify wraps a Core
`boolOpt` word with this (a named function, so certificate `simp` can
match it). -/
@[inline] def natToBool (n : Nat) : Bool := n != 0

/-- `Tx.call` with the result erased to a Core word. -/
def callAsNat (ret : AbiRet) (addr : Address) (sel : Nat) (args : List Word) :
    Tx S X E ε Nat :=
  match ret with
  | .word => call (α := Nat) addr sel args
  | .boolOpt => boolBit <$> call (α := Bool) addr sel args
  | .none => (fun _ : Unit => (0 : Nat)) <$> call (α := Unit) addr sel args

/-- `Tx.view` with the result erased to a Core word. -/
def viewAsNat (ret : AbiRet) (addr : Address) (sel : Nat) (args : List Word) :
    Tx S X E ε Nat :=
  match ret with
  | .word => view (α := Nat) addr sel args
  | .boolOpt => boolBit <$> view (α := Bool) addr sel args
  | .none => (fun _ : Unit => (0 : Nat)) <$> view (α := Unit) addr sel args

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

/-- Monad parameters `(S, X, E, ε, α)` of an expected `Tx` (or `M` / `ReaderT` unfold). -/
def txParams? (ty? : Option Expr) :
    TermElabM (Option (Expr × Expr × Expr × Expr × Expr)) := do
  let some ty0 := ty? | return none
  let ty0 ← instantiateMVars ty0
  let tryTx (ty : Expr) : Option (Expr × Expr × Expr × Expr × Expr) :=
    if ty.isAppOfArity ``Lsc.Tx 5 then
      some (ty.getArg! 0, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4)
    else none
  if let some p := tryTx ty0 then return some p
  -- Reducible only: unfold `M` / `Tx`, not `StateT`.
  let ty ← withReducible (whnf ty0)
  if let some p := tryTx ty then return some p
  if ty.isAppOf ``ReaderT && ty.getAppNumArgs ≥ 3 then
    let α := ty.getArg! 2
    let st ← withReducible (whnf (ty.getArg! 1))
    if st.isAppOf ``StateT && st.getAppNumArgs ≥ 2 then
      let w ← withReducible (whnf (st.getArg! 0))
      if w.isAppOf ``Lsc.World && w.getAppNumArgs ≥ 3 then
        let S := w.getArg! 0
        let X := w.getArg! 1
        let E := w.getArg! 2
        let m ← withReducible (whnf (st.getArg! 1))
        let ε ←
          if m.isAppOf ``Except && m.getAppNumArgs ≥ 1 then
            let err := m.getArg! 0
            if err.isAppOf ``Lsc.Err && err.getAppNumArgs ≥ 1 then
              pure (err.getArg! 0)
            else mkFreshExprMVar none
          else mkFreshExprMVar none
        return some (S, X, E, ε, α)
  return none

/-- Storage type `S` of an expected `Tx S _ _ _ _` (or its `ReaderT` unfold). -/
def txStorage? (ty? : Option Expr) : TermElabM (Option Expr) := do
  return (← txParams? ty?).map (·.1)

/-- Payload of `pure v` / `CoeTail.coe v`. -/
def peelCoePure? (e : Expr) : Option Expr :=
  let e := e.consumeMData
  if e.isAppOf ``Pure.pure && e.getAppNumArgs ≥ 1 then
    some (e.getArg! (e.getAppNumArgs - 1))
  else if e.isAppOf ``CoeTail.coe && e.getAppNumArgs ≥ 1 then
    some (e.getArg! (e.getAppNumArgs - 1))
  else none

/-- `true` if `ty` is `Tx` or its `ReaderT` unfold. -/
def isTxType (ty : Expr) : TermElabM Bool := do
  let ty ← withReducible (whnf ty)
  if ty.isAppOf ``Lsc.Tx then return true
  if ty.isAppOf ``ReaderT then
    let st ← withReducible (whnf (ty.getArg! 1))
    return st.isAppOf ``StateT
  return false

/-- Re-pack a `Tx`/`ReaderT` operand type so instance search sees `Tx S X E ε α`. -/
def packOperandTy (S X E ε ty : Expr) : TermElabM Expr := do
  match ← txParams? (some ty) with
  | some (_, _, _, _, α) =>
    return mkAppN (mkConst ``Lsc.Tx) #[S, X, E, ε, ← instantiateMVars α]
  | none => instantiateMVars ty

/-- Apply a checked-op method with class parameters from the surrounding `Tx`. -/
def applyChecked (className method : Name) (S X E ε γ : Expr) (args : Array Expr) :
    TermElabM Expr := do
  let tys ← args.mapM fun a => do
    packOperandTy S X E ε (← inferType a)
  let instTy := mkAppN (mkConst className) (#[S, X, E, ε] ++ tys ++ #[γ])
  let inst ← synthInstance instTy
  let f := mkAppN (mkConst method)
    (#[S, X, E, ε] ++ tys ++ #[γ, inst])
  return mkAppN f args

/-- Numeral / `OfNat` syntax: no `OfNat Tx`, so do not probe at `Tx`. -/
def isNumeralStx (stx : Syntax) : Bool :=
  (stx.isNatLit?).isSome || stx.isOfKind `num

/-- Inner payload of a `Tx` type, if `ty` is `Tx` / `M`. -/
def txInnerTy? (ty : Expr) : TermElabM (Option Expr) := do
  return (← txParams? (some ty)).map (·.2.2.2.2)

/-- Elaborate one operand. Prefer a `Tx` expected type so `read` elaborates.
Keep a successful `Tx` probe as `Tx` (do not peel `CoeTail`). -/
def elabTxOperand (stx : Term) (S X E ε : Expr) : TermElabM Expr := do
  let τ ← mkFreshExprMVar none
  let txTy := mkAppN (mkConst ``Lsc.Tx) #[S, X, E, ε, τ]
  match ← commitIfNoErrors? (elabTerm stx (some txTy)) with
  | some e => instantiateMVars e
  | none => instantiateMVars (← elabTerm stx none)

/-- Apply `method` after elaborating operands at `Tx` (or as pure values).
Numerals are elaborated last, at the result payload / sibling inner type,
because `OfNat (Tx …) n` does not exist. -/
def elabTxOp (className method : Name) (operands : Array Term)
    (expectedType? : Option Expr) : TermElabM Expr := do
  tryPostponeIfNoneOrMVar expectedType?
  let some (S, X, E, ε, γ) ← txParams? expectedType? |
    throwError "checked op: expected a `Tx` type (use in a contract `do` or `write`)"
  let mut slots : Array (Option Expr) := .replicate operands.size none
  for i in [0:operands.size] do
    unless isNumeralStx operands[i]!.raw do
      slots := slots.set! i (some (← elabTxOperand operands[i]! S X E ε))
  let numTy ← do
    let γ ← instantiateMVars γ
    if !γ.isMVar then
      pure γ
    else
      let mut found : Option Expr := none
      for a? in slots do
        if found.isNone then
          if let some a := a? then
            let ty ← inferType a
            found := some ((← txInnerTy? ty).getD ty)
      pure (found.getD (← mkFreshExprMVar none))
  for i in [0:operands.size] do
    if slots[i]!.isNone then
      slots := slots.set! i (some (← elabTerm operands[i]! (some numTy)))
  let args := slots.map (·.get!)
  let e ← applyChecked className method S X E ε γ args
  ensureHasType expectedType? e

@[term_elab lscHAdd]
def elabHAdd : TermElab := fun stx expectedType? =>
  match stx with
  | `($a:term +? $b:term) =>
    elabTxOp ``Lsc.Tx.HAddChecked ``Lsc.Tx.HAddChecked.hAdd #[a, b] expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab lscHSub]
def elabHSub : TermElab := fun stx expectedType? =>
  match stx with
  | `($a:term -? $b:term) =>
    elabTxOp ``Lsc.Tx.HSubChecked ``Lsc.Tx.HSubChecked.hSub #[a, b] expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab lscHMul]
def elabHMul : TermElab := fun stx expectedType? =>
  match stx with
  | `($a:term *? $b:term) =>
    elabTxOp ``Lsc.Tx.HMulChecked ``Lsc.Tx.HMulChecked.hMul #[a, b] expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab lscHDiv]
def elabHDiv : TermElab := fun stx expectedType? =>
  match stx with
  | `($a:term /? $b:term) =>
    elabTxOp ``Lsc.Tx.HDivChecked ``Lsc.Tx.HDivChecked.hDiv #[a, b] expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab lscHMulFixedDown]
def elabHMulFixedDown : TermElab := fun stx expectedType? =>
  match stx with
  | `($a:term *?↓ $b:term) =>
    elabTxOp ``Lsc.Tx.HMulFixedDown ``Lsc.Tx.HMulFixedDown.hMulFixedDown
      #[a, b] expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab lscHMulFixedUp]
def elabHMulFixedUp : TermElab := fun stx expectedType? =>
  match stx with
  | `($a:term *?↑ $b:term) =>
    elabTxOp ``Lsc.Tx.HMulFixedUp ``Lsc.Tx.HMulFixedUp.hMulFixedUp
      #[a, b] expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab lscMulDivDown]
def elabMulDivDown : TermElab := fun stx expectedType? =>
  match stx with
  | `($a:term mulDiv↓ $b:term / $c:term) =>
    elabTxOp ``Lsc.Tx.HMulDivDown ``Lsc.Tx.HMulDivDown.hMulDivDown
      #[a, b, c] expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab lscMulDivUp]
def elabMulDivUp : TermElab := fun stx expectedType? =>
  match stx with
  | `($a:term mulDiv↑ $b:term / $c:term) =>
    elabTxOp ``Lsc.Tx.HMulDivUp ``Lsc.Tx.HMulDivUp.hMulDivUp
      #[a, b, c] expectedType?
  | _ => throwUnsupportedSyntax

def elabFieldProj (f : Ident) (expectedType? : Option Expr) : TermElabM Expr := do
  let some S ← txStorage? expectedType? |
    throwError "read/write: could not infer storage type (use in a `Tx` context)"
  let α ← mkFreshExprMVar none
  let expected ← mkArrow S α
  elabTerm (← `(fun $(sigma) => $(projOf f))) expected

/-- Value type of storage field `f` (scalar / map1 / map2).
Reducible-only: `Address` is a `def` newtype and must not unfold to `Nat`. -/
def fieldValTy (f : Ident) (expectedType? : Option Expr) : TermElabM Expr := do
  forallTelescopeReducing (← inferType (← elabFieldProj f expectedType?)) fun _ body =>
    withReducible (whnf body)

/-- Number of mapping keys `f` expects (0 = scalar). -/
def fieldKeyCount (f : Ident) (expectedType? : Option Expr) : TermElabM Nat := do
  forallTelescopeReducing (← inferType (← elabFieldProj f expectedType?)) fun xs _ =>
    return xs.size - 1

def wrapLoad (α : Expr) (load : Term) (expectedType? : Option Expr) : TermElabM Expr := do
  let α ← whnfD α
  if isRef α then
    let tyStx ← delab α
    elabTerm (← `(Functor.map (fun n : Nat => ({ addr := n } : $tyStx)) $load))
      expectedType?
  else
    elabTerm load expectedType?

@[term_elab lscRead]
def elabRead : TermElab := fun stx expectedType? => do
  tryPostponeIfNoneOrMVar expectedType?
  match stx with
  | `(read $f:ident) => do
    let n ← fieldKeyCount f expectedType?
    unless n == 0 do throwError "read: `{f.getId}` needs keys"
    let α ← fieldValTy f expectedType?
    let load ←
      if isRef (← whnfD α) then
        `(Lsc.Tx.load (fun $(sigma) =>
            (($(← fieldProj f α)).addr : Nat)))
      else
        `(Lsc.Tx.load (fun $(sigma) => $(← fieldProj f α)))
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
      let load ←
        if isRef (← whnfD α) then
          `(Lsc.Tx.loadMap (fun $(sigma) $kk =>
            (($(← fieldProjKey f kk α)).addr : Nat)) $k)
        else
          `(Lsc.Tx.loadMap (fun $(sigma) $kk =>
            $(← fieldProjKey f kk α)) $k)
      wrapLoad α load expectedType?
    | [k₁, k₂] =>
      let a := mkIdent `k₁
      let b := mkIdent `k₂
      let load ←
        if isRef (← whnfD α) then
          `(Lsc.Tx.loadMap2 (fun $(sigma) $a $b =>
            (($(← fieldProjKey2 f a b α)).addr : Nat)) $k₁ $k₂)
        else
          `(Lsc.Tx.loadMap2 (fun $(sigma) $a $b =>
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

/-- Elaborate `v` at `Tx S X E ε α` (the primary `write` signature). Pure values
coerce via `CoeTail`; if the result is `pure v` we emit the store without a
bind so `write paused Flag.off` stays a tail `store`. Nested `read`s see a
`Tx` expected type, so `write f (read f +? x)` elaborates.

`mkCont` is `fun x => store … x` (no bind). The `Tx` path uses `Bind.bind`
on the already-elaborated argument so we never delab/`re-elab` a `read`. -/
def writeArg (α : Expr) (v : Term) (expectedType? : Option Expr)
    (mkPure : Term → TermElabM Term) (mkCont : TermElabM Term) : TermElabM Expr := do
  let αStx ← delab α
  let (S, X, E, ε) ←
    match ← txParams? expectedType? with
    | some (S, X, E, ε, _) => pure (S, X, E, ε)
    | none => do
      pure (← mkFreshExprMVar none, ← mkFreshExprMVar none,
            ← mkFreshExprMVar none, ← mkFreshExprMVar none)
  let txTy := mkAppN (mkConst ``Lsc.Tx) #[S, X, E, ε, α]
  let saved ← saveState
  match ← commitIfNoErrors? (elabTermEnsuringType v txTy) with
  | some e =>
    let e ← instantiateMVars e
    if (peelCoePure? e).isSome then
      saved.restore
      elabTerm (← mkPure (← `(($v : $αStx)))) expectedType?
    else
      let txU := mkAppN (mkConst ``Lsc.Tx) #[S, X, E, ε, mkConst ``Unit]
      let kTy ← mkArrow α txU
      let k ← elabTerm (← mkCont) (some kTy)
      mkAppM ``Bind.bind #[e, k]
  | none =>
    saved.restore
    elabTerm (← mkPure (← `(($v : $αStx)))) expectedType?

/-- Elaborate `d.f` as `Field S α` using the surrounding `Tx` storage. -/
def elabFieldRef (d f : Ident) (expectedType? : Option Expr) : TermElabM Expr := do
  let some S ← txStorage? expectedType? |
    throwError "read/write: could not infer storage type (use in a `Tx` context)"
  let α ← mkFreshExprMVar none
  let fieldTy := mkAppN (mkConst ``Lsc.Field) #[S, α]
  discard <| elabTerm (← `($d.$f)) (some fieldTy)
  instantiateMVars (← whnfD α)

@[term_elab lscReadField]
def elabReadField : TermElab := fun stx expectedType? => do
  tryPostponeIfNoneOrMVar expectedType?
  match stx with
  | `(read $d:ident.$f:ident) => do
    let α ← elabFieldRef d f expectedType?
    let load ←
      if isRef α then
        `(Lsc.Tx.load (fun $(sigma) =>
            ((Lsc.Field.get ($d.$f) $(sigma)).addr : Nat)))
      else
        `(Lsc.Tx.load (Lsc.Field.get ($d.$f)))
    wrapLoad α load expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab lscWrite]
def elabWrite : TermElab := fun stx expectedType? => do
  tryPostponeIfNoneOrMVar expectedType?
  match stx with
  | `(write $f:ident $v) => do
    let n ← fieldKeyCount f expectedType?
    unless n == 0 do throwError "write: `{f.getId}` needs keys"
    let α ← fieldValTy f expectedType?
    storeScalar f α v expectedType?
  | `(write $f:ident [ $ks:term,* ] $v) => do
    let keys := ks.getElems
    let n ← fieldKeyCount f expectedType?
    unless n == keys.size do
      throwError "write: `{f.getId}` expects {n} key(s)"
    let α ← fieldValTy f expectedType?
    match keys.toList with
    | [k] => storeMap1 f α k v expectedType?
    | [k₁, k₂] => storeMap2 f α k₁ k₂ v expectedType?
    | _ => throwError "write: mappings have one or two keys"
  | _ => throwUnsupportedSyntax

where
  storeScalar (f : Ident) (α : Expr) (v : Term) (expectedType? : Option Expr) :
      TermElabM Expr := do
    let α ← withReducible (whnf α)
    let σ := sigma
    if isAmount α then
      writeArg α v expectedType?
        (fun v =>
          `(Lsc.Tx.store (fun $σ m => { $σ with $f:ident := Lsc.Amount.ofWord m })
              (Lsc.Amount.raw $v)))
        `(fun x =>
          Lsc.Tx.store (fun $σ y => { $σ with $f:ident := Lsc.Amount.ofWord y })
            (Lsc.Amount.raw x))
    else if isRef α then
      writeArg α v expectedType?
        (fun v =>
          `(Lsc.Tx.store (fun $σ m => { $σ with $f:ident := { addr := m } })
              ($v).addr))
        `(fun x =>
          Lsc.Tx.store (fun $σ y => { $σ with $f:ident := { addr := y } })
            x.addr)
    else
      writeArg α v expectedType?
        (fun v => `(Lsc.Tx.store (fun $σ m => { $σ with $f:ident := m }) $v))
        `(fun x => Lsc.Tx.store (fun $σ y => { $σ with $f:ident := y }) x)
  storeMap1 (f : Ident) (α : Expr) (k v : Term) (expectedType? : Option Expr) :
      TermElabM Expr := do
    let α ← withReducible (whnf α)
    let σ := sigma
    let p := projOf f
    let kk := mkIdent `k
    let mm := mkIdent `m
    if isAmount α then
      writeArg α v expectedType?
        (fun v =>
          `(Lsc.Tx.storeMap (fun $σ $kk => Lsc.Amount.raw ($p $kk))
              (fun $σ $mm => { $σ with $f:ident := fun $kk => Lsc.Amount.ofWord ($mm $kk) })
              $k (Lsc.Amount.raw $v)))
        `(fun x =>
          Lsc.Tx.storeMap (fun $σ $kk => Lsc.Amount.raw ($p $kk))
            (fun $σ $mm => { $σ with $f:ident := fun $kk => Lsc.Amount.ofWord ($mm $kk) })
            $k (Lsc.Amount.raw x))
    else if isRef α then
      writeArg α v expectedType?
        (fun v =>
          `(Lsc.Tx.storeMap (fun $σ $kk => ($p $kk).addr)
              (fun $σ $mm => { $σ with $f:ident := fun $kk => { addr := $mm $kk } })
              $k ($v).addr))
        `(fun x =>
          Lsc.Tx.storeMap (fun $σ $kk => ($p $kk).addr)
            (fun $σ $mm => { $σ with $f:ident := fun $kk => { addr := $mm $kk } })
            $k x.addr)
    else
      writeArg α v expectedType?
        (fun v =>
          `(Lsc.Tx.storeMap (fun $σ => $p) (fun $σ $mm => { $σ with $f:ident := $mm })
              $k $v))
        `(fun x =>
          Lsc.Tx.storeMap (fun $σ => $p) (fun $σ $mm => { $σ with $f:ident := $mm })
            $k x)
  storeMap2 (f : Ident) (α : Expr) (k₁ k₂ v : Term) (expectedType? : Option Expr) :
      TermElabM Expr := do
    let α ← withReducible (whnf α)
    let σ := sigma
    let p := projOf f
    let a := mkIdent `k₁
    let b := mkIdent `k₂
    let mm := mkIdent `m
    if isAmount α then
      writeArg α v expectedType?
        (fun v =>
          `(Lsc.Tx.storeMap2 (fun $σ $a $b => Lsc.Amount.raw ($p $a $b))
              (fun $σ $mm => { $σ with $f:ident := fun $a $b => Lsc.Amount.ofWord ($mm $a $b) })
              $k₁ $k₂ (Lsc.Amount.raw $v)))
        `(fun x =>
          Lsc.Tx.storeMap2 (fun $σ $a $b => Lsc.Amount.raw ($p $a $b))
            (fun $σ $mm => { $σ with $f:ident := fun $a $b => Lsc.Amount.ofWord ($mm $a $b) })
            $k₁ $k₂ (Lsc.Amount.raw x))
    else if isRef α then
      writeArg α v expectedType?
        (fun v =>
          `(Lsc.Tx.storeMap2 (fun $σ $a $b => ($p $a $b).addr)
              (fun $σ $mm => { $σ with $f:ident := fun $a $b => { addr := $mm $a $b } })
              $k₁ $k₂ ($v).addr))
        `(fun x =>
          Lsc.Tx.storeMap2 (fun $σ $a $b => ($p $a $b).addr)
            (fun $σ $mm => { $σ with $f:ident := fun $a $b => { addr := $mm $a $b } })
            $k₁ $k₂ x.addr)
    else
      writeArg α v expectedType?
        (fun v =>
          `(Lsc.Tx.storeMap2 (fun $σ => $p) (fun $σ $mm => { $σ with $f:ident := $mm })
              $k₁ $k₂ $v))
        `(fun x =>
          Lsc.Tx.storeMap2 (fun $σ => $p) (fun $σ $mm => { $σ with $f:ident := $mm })
            $k₁ $k₂ x)

@[term_elab lscWriteField]
def elabWriteField : TermElab := fun stx expectedType? => do
  tryPostponeIfNoneOrMVar expectedType?
  match stx with
  | `(write $d:ident.$f:ident $v) => do
    let α ← elabFieldRef d f expectedType?
    let α ← withReducible (whnf α)
    let σ := sigma
    if isAmount α then
      writeArg α v expectedType?
        (fun v =>
          `(Lsc.Tx.store (fun $σ m =>
              Lsc.Field.set ($d.$f) $σ (Lsc.Amount.ofWord m))
            (Lsc.Amount.raw $v)))
        `(fun x =>
          Lsc.Tx.store (fun $σ y =>
              Lsc.Field.set ($d.$f) $σ (Lsc.Amount.ofWord y))
            (Lsc.Amount.raw x))
    else if isRef α then
      writeArg α v expectedType?
        (fun v =>
          `(Lsc.Tx.store (fun $σ m => Lsc.Field.set ($d.$f) $σ { addr := m })
              ($v).addr))
        `(fun x =>
          Lsc.Tx.store (fun $σ y => Lsc.Field.set ($d.$f) $σ { addr := y })
            x.addr)
    else
      writeArg α v expectedType?
        (fun v => `(Lsc.Tx.store (Lsc.Field.set ($d.$f)) $v))
        `(fun x => Lsc.Tx.store (Lsc.Field.set ($d.$f)) x)
  | _ => throwUnsupportedSyntax

end Syntax

end Lsc
