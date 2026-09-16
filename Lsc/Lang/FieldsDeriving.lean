import Lsc.Lang.Tx
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util

/-!
`deriving Fields` handler: from a storage structure, emit one `Field S α`
lens per field in `S.Fields`, including inherited fields of `extends`, plus
a lens per parent subobject (for `ERC20.Fields.ofParent`). Each lens gets a
`Field.Lawful` instance. Parameterized structures (`ERC20.Storage a`) are
supported. Contract files `open Storage.Fields` so `reserve1` in contract
code *is* the lens (`deriving` cannot persist that `open` itself).
-/

open Lean Elab Command Meta PrettyPrinter
open Lean.Elab.Deriving
open Lean.Parser.Term

namespace Lsc.FieldsDeriving

def rootIdent (parts : Name) : Ident :=
  mkIdent (`_root_ ++ parts)

def toBracketed (stx : Syntax) : TSyntax ``Parser.Term.bracketedBinder := ⟨stx⟩

def identOfFVar (x : Expr) : MetaM Ident := do
  let n := (← x.fvarId!.getUserName).eraseMacroScopes
  return mkIdent n

def emitLens (structName : Name) (fieldName : Name)
    (paramBinders : Array (TSyntax ``Parser.Term.bracketedBinder))
    (structApp : Term) (nparams : Nat) : CommandElabM Unit := do
  let projName := structName ++ fieldName
  let tyStx ← liftTermElabM do
    let projTy ← inferType (mkConst projName)
    forallBoundedTelescope projTy (some (nparams + 1)) fun _ rest => delab rest
  let lensId := rootIdent (structName ++ `Fields ++ fieldName)
  let projId := rootIdent projName
  let fld := mkIdent fieldName
  let σ := mkIdent `σ
  let v := mkIdent `v
  elabCommand <| ← `(
    @[reducible] def $lensId $paramBinders:bracketedBinder* :
        Lsc.Field $structApp $tyStx :=
      ⟨$projId, fun $σ $v => { $σ with $fld:ident := $v }⟩)
  elabCommand <| ← `(
    instance $paramBinders:bracketedBinder* :
        Lsc.Field.Lawful ($lensId : Lsc.Field $structApp $tyStx) where
      get_set := by intros; rfl
      set_get := by intros s; cases s; rfl
      set_set := by intros; rfl)

def deriveOne (structName : Name) : CommandElabM Unit := do
  unless isStructure (← getEnv) structName do
    throwError "`deriving Fields` requires a structure"
  let indVal ← getConstInfoInduct structName
  let env ← getEnv
  let nparams := indVal.numParams
  let (paramBinders, structApp) ← liftTermElabM do
    forallTelescope indVal.type fun xs _ => do
      let params := xs.extract 0 nparams
      let mut binders : Array (TSyntax ``Parser.Term.bracketedBinder) := #[]
      let mut idents : Array Ident := #[]
      for x in params do
        let id ← identOfFVar x
        let ty ← delab (← inferType x)
        binders := binders.push (← toBracketed <$> `(implicitBinderF| {$id:ident : $ty}))
        idents := idents.push id
      let app ← `($(mkCIdent structName) $idents*)
      pure (binders, app)
  let flat := getStructureFieldsFlattened env structName
      (includeSubobjectFields := false)
  let mut seen : NameSet := {}
  for fieldName in flat do
    emitLens structName fieldName paramBinders structApp nparams
    seen := seen.insert fieldName
  for fieldName in getStructureFields env structName do
    if seen.contains fieldName then continue
    unless (isSubobjectField? env structName fieldName).isSome do continue
    emitLens structName fieldName paramBinders structApp nparams
  for f1 in flat do
    for f2 in flat do
      if f1 == f2 then continue
      let l1 := rootIdent (structName ++ `Fields ++ f1)
      let l2 := rootIdent (structName ++ `Fields ++ f2)
      elabCommand <| ← `(
        instance $paramBinders:bracketedBinder* :
            Lsc.Field.Independent ($l1 : Lsc.Field $structApp _)
              ($l2 : Lsc.Field $structApp _) where
          get_set_other := by intros s v; cases s; rfl)
  elabCommand <| ← `(instance $paramBinders:bracketedBinder* :
      Lsc.Fields $structApp := ⟨⟩)

def deriveFields (declNames : Array Name) : CommandElabM Bool := do
  for n in declNames do
    deriveOne n
  return true

initialize
  registerDerivingHandler ``Lsc.Fields deriveFields

end Lsc.FieldsDeriving
