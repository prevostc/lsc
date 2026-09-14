import Lsc.Lang.Interface
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util

/-!
`deriving Interface` handler: from an ABI structure of `Fn`/`View` fields,
emit `I.Ref`, `I.Try`, `I.Impl`, the `Interface` instance, typed CALL/view
functions, `.try` variants, `Impl.ofRef`, and `Ref.impl`.
-/

open Lean Elab Command Meta PrettyPrinter
open Lean.Elab.Deriving
open Lean.Parser.Term
open Lean.Parser.Command

namespace Lsc.InterfaceDeriving

structure DerivedMethod where
  fieldName : Name
  isView : Bool
  sel : Nat
  arity : Nat
  retKind : Lsc.AbiRet
  argIdents : Array Ident
  argTys : Array Term
  retTy : Term

def peelFnView (ty : Expr) : MetaM (Bool × Expr) := do
  let ty ← whnf ty
  if ty.isAppOfArity ``Lsc.Fn 1 then
    return (false, ty.appArg!)
  if ty.isAppOfArity ``Lsc.View 1 then
    return (true, ty.appArg!)
  throwError "interface fields must have type `Fn _` or `View _`{indentD ty}"

def abiNameOf (ty : Expr) : MetaM String := do
  if ty.isConstOf ``Lsc.Address then return "address"
  if ty.isConstOf ``Bool then return "bool"
  if ty.isAppOf ``Lsc.Amount then return "uint256"
  if ty.isConstOf ``Lsc.Word || ty.isConstOf ``Nat then return "uint256"
  let ty ← withReducible (whnf ty)
  if ty.isConstOf ``Lsc.Address then return "address"
  if ty.isConstOf ``Bool then return "bool"
  if ty.isAppOf ``Lsc.Amount then return "uint256"
  if ty.isConstOf ``Nat then return "uint256"
  throwError "unsupported ABI argument type{indentD ty}"

def abiRetOf (ty : Expr) : MetaM Lsc.AbiRet := do
  if ty.isConstOf ``Bool then return .boolOpt
  if ty.isConstOf ``Unit || ty.isConstOf ``PUnit then return .none
  let ty ← withReducible (whnf ty)
  if ty.isConstOf ``Bool then return .boolOpt
  if ty.isConstOf ``Unit || ty.isConstOf ``PUnit then return .none
  return .word

def quoteAbiRet : Lsc.AbiRet → TermElabM Term
  | .word => `(Lsc.AbiRet.word)
  | .boolOpt => `(Lsc.AbiRet.boolOpt)
  | .none => `(Lsc.AbiRet.none)

def mkArrows (args : Array Term) (ret : Term) : TermElabM Term :=
  args.foldrM (init := ret) fun t acc => `($t → $acc)

def toBracketed (stx : Syntax) : TSyntax ``Parser.Term.bracketedBinder := ⟨stx⟩

def identOfFVar (x : Expr) : MetaM Ident := do
  let n := (← x.fvarId!.getUserName).eraseMacroScopes
  return mkIdent n

/-- Header copied from the ABI structure's parameters. -/
structure IfaceHeader where
  paramBinders : Array (TSyntax ``Parser.Term.bracketedBinder)
  paramImplBinders : Array (TSyntax ``Parser.Term.bracketedBinder)
  paramIdents : Array Ident
  ifaceApp : Term

def mkHeader (structName : Name) (indVal : InductiveVal) : TermElabM IfaceHeader :=
  forallTelescope indVal.type fun xs _ => do
    let params := xs.extract 0 indVal.numParams
    let mut paramBinders : Array (TSyntax ``Parser.Term.bracketedBinder) := #[]
    let mut paramImplBinders : Array (TSyntax ``Parser.Term.bracketedBinder) := #[]
    let mut paramIdents : Array Ident := #[]
    for x in params do
      let id ← identOfFVar x
      let ty ← delab (← inferType x)
      paramBinders := paramBinders.push (← toBracketed <$> `(explicitBinderF| ($id:ident : $ty)))
      paramImplBinders := paramImplBinders.push (← toBracketed <$> `(implicitBinderF| {$id:ident : $ty}))
      paramIdents := paramIdents.push id
    let ifaceApp ← `($(mkCIdent structName) $paramIdents*)
    return { paramBinders, paramImplBinders, paramIdents, ifaceApp }

def collectMethods (structName : Name) (indVal : InductiveVal) :
    TermElabM (Array DerivedMethod) :=
  forallTelescope indVal.type fun xs _ => do
    let params := xs.extract 0 indVal.numParams
    let env ← getEnv
    let mut out : Array DerivedMethod := #[]
    for fieldName in getStructureFields env structName do
      let projTy ← inferType (mkAppN (mkConst (structName ++ fieldName)) params)
      let m ← forallBoundedTelescope projTy (some 1) fun _ fieldTy => do
        let (isView, inner) ← peelFnView fieldTy
        forallTelescope inner fun args ret => do
          let mut argIdents : Array Ident := #[]
          let mut argTys : Array Term := #[]
          let mut abiNames : Array String := #[]
          for i in [:args.size] do
            let x := args[i]!
            let id := mkIdent (Name.mkSimple s!"x{i + 1}")
            argIdents := argIdents.push id
            argTys := argTys.push (← delab (← inferType x))
            abiNames := abiNames.push (← abiNameOf (← inferType x))
          let retTy ← delab ret
          let retKind ← abiRetOf ret
          let sel := Lsc.methodSelector fieldName.getString! abiNames.toList
          return {
            fieldName, isView, sel, arity := args.size, retKind
            argIdents, argTys, retTy
          }
      out := out.push m
    return out

def rootIdent (parts : Name) : Ident :=
  mkIdent (`_root_ ++ parts)

def emitMethodSig (m : DerivedMethod) : TermElabM Term := do
  let kind ← quoteAbiRet m.retKind
  let isView := quote m.isView
  `(Lsc.MethodSig.mk
      $(quote m.fieldName.getString!)
      $(quote m.sel)
      $(quote m.arity)
      $isView
      $kind)

def mkWorldBinders : TermElabM (TSyntax ``Parser.Term.bracketedBinder) :=
  toBracketed <$> `(implicitBinderF| {S X E ε : Type})

/-- `Impl` / `ofRef` / `Ref.impl` do not mention `ε` (Fn fields are `Option`). -/
def mkWorldBindersNoε : TermElabM (TSyntax ``Parser.Term.bracketedBinder) :=
  toBracketed <$> `(implicitBinderF| {S X E : Type})

def mkArgBinders (m : DerivedMethod) :
    TermElabM (Array (TSyntax ``Parser.Term.bracketedBinder)) :=
  (m.argIdents.zip m.argTys).mapM fun (n, ty) =>
    toBracketed <$> `(explicitBinderF| ($n:ident : $ty))

def encodeList (m : DerivedMethod) : TermElabM Term := do
  let encs ← m.argIdents.mapM fun id => `(Lsc.AbiType.encode $id)
  `([$encs,*])

def emitCalls (structName : Name) (hdr : IfaceHeader) (m : DerivedMethod) :
    CommandElabM Unit := do
  let worldB ← liftTermElabM mkWorldBinders
  let argB ← liftTermElabM (mkArgBinders m)
  let enc ← liftTermElabM (encodeList m)
  let refApp ← liftTermElabM `($(rootIdent (structName ++ `Ref)) $hdr.paramIdents*)
  let tryApp ← liftTermElabM `($(rootIdent (structName ++ `Try)) $hdr.paramIdents*)
  let rB : TSyntax ``Parser.Term.bracketedBinder :=
    ← toBracketed <$> `(explicitBinderF| (r : $refApp))
  let tB : TSyntax ``Parser.Term.bracketedBinder :=
    ← toBracketed <$> `(explicitBinderF| (t : $tryApp))
  let bindersR := hdr.paramImplBinders ++ #[worldB, rB] ++ argB
  let bindersT := hdr.paramImplBinders ++ #[worldB, tB] ++ argB
  let prim := if m.isView then mkCIdent ``Lsc.Tx.view else mkCIdent ``Lsc.Tx.call
  let tryP := if m.isView then mkCIdent ``Lsc.Tx.tryView else mkCIdent ``Lsc.Tx.tryCall
  let sel := quote m.sel
  let addrR ← `(r.addr)
  let addrT ← `(t.addr)
  let refId := rootIdent (structName ++ `Ref ++ m.fieldName)
  let tryId := rootIdent (structName ++ `Try ++ m.fieldName)
  elabCommand <| ← `(
    def $refId $bindersR:bracketedBinder* : Lsc.Tx S X E ε $(m.retTy) :=
      $prim $addrR $sel $enc)
  elabCommand <| ← `(
    def $tryId $bindersT:bracketedBinder* : Lsc.Tx S X E ε (Except (Lsc.Err ε) $(m.retTy)) :=
      $tryP $addrT $sel $enc)

def implFieldType (m : DerivedMethod) : TermElabM Term := do
  let w ← `(W)
  let ctx ← `(Lsc.Ctx)
  if m.isView then
    mkArrows (m.argTys ++ #[w]) m.retTy
  else
    let ret ← `(Option ($(m.retTy) × W))
    mkArrows (m.argTys ++ #[ctx, w]) ret

def ofRefViewBody (m : DerivedMethod) : TermElabM Term := do
  let enc ← encodeList m
  let sel := quote m.sel
  `(fun $(m.argIdents)* w =>
      Lsc.decodeOrDefault (w.oracle.view r.addr $sel $enc w.ext))

def ofRefFnBody (structName : Name) (_hdr : IfaceHeader) (m : DerivedMethod) :
    TermElabM Term := do
  let f := rootIdent (structName ++ `Ref ++ m.fieldName)
  `(fun $(m.argIdents)* ctx w =>
      (Lsc.Tx.run ($f r $(m.argIdents)* : Lsc.Tx S X E Unit $(m.retTy))
        ctx w).toOption)

def deriveOne (structName : Name) : CommandElabM Unit := do
  unless isStructure (← getEnv) structName do
    throwError "`deriving Interface` requires a structure"
  let indVal ← getConstInfoInduct structName
  let (hdr, methods) ← liftTermElabM do
    let hdr ← mkHeader structName indVal
    let methods ← collectMethods structName indVal
    pure (hdr, methods)
  -- I.Ref / I.Try / I.Impl
  let refId := rootIdent (structName ++ `Ref)
  let tryId := rootIdent (structName ++ `Try)
  let implId := rootIdent (structName ++ `Impl)
  elabCommand <| ← `(
    structure $refId $hdr.paramBinders:bracketedBinder* where
      addr : Lsc.Address
      deriving Repr, DecidableEq)
  elabCommand <| ← `(
    instance $hdr.paramImplBinders:bracketedBinder* : Inhabited ($refId $hdr.paramIdents*) :=
      ⟨⟨(0 : Lsc.Address)⟩⟩)
  elabCommand <| ← `(
    structure $tryId $hdr.paramBinders:bracketedBinder* where
      addr : Lsc.Address)
  let implFields : Array (TSyntax ``Parser.Command.structSimpleBinder) ←
    liftTermElabM do
      methods.mapM fun m => do
        let ty ← implFieldType m
        let n := mkIdent m.fieldName
        `(Parser.Command.structSimpleBinder| $n:ident : $ty)
  elabCommand <| ← `(
    structure $implId $hdr.paramBinders:bracketedBinder* (W : Type) where
      $[$implFields]*
      step : Lsc.Ctx → W → W → Prop)
  -- Interface instance
  let sigs ← liftTermElabM <| methods.mapM emitMethodSig
  elabCommand <| ← `(
    instance $hdr.paramImplBinders:bracketedBinder* : Lsc.Interface $(hdr.ifaceApp) where
      methods := [$sigs,*])
  -- typed calls
  for m in methods do
    emitCalls structName hdr m
  -- I.Ref.try / I.Ref.impl / I.Impl.ofRef
  let tryFn := rootIdent (structName ++ `Ref ++ `try)
  let implFn := rootIdent (structName ++ `Ref ++ `impl)
  let ofRefId := rootIdent (structName ++ `Impl ++ `ofRef)
  let refApp ← liftTermElabM `($refId $hdr.paramIdents*)
  let tryApp ← liftTermElabM `($tryId $hdr.paramIdents*)
  let rB : TSyntax ``Parser.Term.bracketedBinder :=
    ← toBracketed <$> `(explicitBinderF| (r : $refApp))
  let worldB ← liftTermElabM mkWorldBindersNoε
  let wB : TSyntax ``Parser.Term.bracketedBinder :=
    ← toBracketed <$> `(explicitBinderF| (_w : Lsc.World S X E))
  elabCommand <| ← `(
    def $tryFn $hdr.paramImplBinders:bracketedBinder* (r : $refApp) : $tryApp :=
      ⟨r.addr⟩)
  let instFields : Array (TSyntax ``Parser.Term.structInstField) ←
    liftTermElabM do
      methods.mapM fun m => do
        let n := mkIdent m.fieldName
        let body ← if m.isView then ofRefViewBody m else ofRefFnBody structName hdr m
        `(Parser.Term.structInstField| $n:ident := $body)
  let ofRefBinds := hdr.paramImplBinders.push worldB |>.push rB
  elabCommand <| ← `(
    def $ofRefId $ofRefBinds:bracketedBinder* :
        $implId $hdr.paramIdents* (Lsc.World S X E) where
      $[$instFields]*
      step := fun _ctx w w' =>
        ∃ sel args rets x',
          w.oracle.call r.addr sel args w.ext = some (rets, x') ∧
          w' = { w with ext := x' })
  let implBinds := hdr.paramImplBinders ++ #[worldB, rB, wB]
  elabCommand <| ← `(
    def $implFn $implBinds:bracketedBinder* :
        $implId $hdr.paramIdents* (Lsc.World S X E) :=
      $ofRefId r)

def deriveInterface (declNames : Array Name) : CommandElabM Bool := do
  for n in declNames do
    deriveOne n
  return true

initialize
  registerDerivingHandler ``Lsc.Interface deriveInterface

end Lsc.InterfaceDeriving
