import Lsc.Lang.Tx
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util

/-!
`deriving Fields` handler: from a storage structure, emit one `Field S α`
lens per field in `S.Fields`. Contract files then `open Storage.Fields` so
`reserve1` in contract code *is* the lens (`deriving` runs inside the
`structure` command, so an `open` emitted here would not persist).
`read` / `write` of a bare ident resolve to `S.Fields.f` (binders may
reuse the field name).
-/

open Lean Elab Command Meta PrettyPrinter
open Lean.Elab.Deriving

namespace Lsc.FieldsDeriving

def rootIdent (parts : Name) : Ident :=
  mkIdent (`_root_ ++ parts)

def deriveOne (structName : Name) : CommandElabM Unit := do
  unless isStructure (← getEnv) structName do
    throwError "`deriving Fields` requires a structure"
  let indVal ← getConstInfoInduct structName
  unless indVal.numParams == 0 do
    throwError "`deriving Fields` does not support parameterized structures"
  let env ← getEnv
  let structIdent := mkCIdent structName
  for fieldName in getStructureFields env structName do
    let projName := structName ++ fieldName
    let tyStx ← liftTermElabM do
      let projTy ← inferType (mkConst projName)
      forallBoundedTelescope projTy (some 1) fun _ rest => delab rest
    let lensId := rootIdent (structName ++ `Fields ++ fieldName)
    let projId := rootIdent projName
    let fld := mkIdent fieldName
    let σ := mkIdent `σ
    let v := mkIdent `v
    elabCommand <| ← `(
      @[reducible] def $lensId : Lsc.Field $structIdent $tyStx :=
        ⟨$projId, fun $σ $v => { $σ with $fld:ident := $v }⟩)
  elabCommand <| ← `(instance : Lsc.Fields $structIdent := ⟨⟩)
  -- `open` here does not persist: `deriving` runs inside the `structure`
  -- command's scope. Contract files `open Storage.Fields` after the
  -- structure so unqualified `reserve1` is the lens.

def deriveFields (declNames : Array Name) : CommandElabM Bool := do
  for n in declNames do
    deriveOne n
  return true

initialize
  registerDerivingHandler ``Lsc.Fields deriveFields

end Lsc.FieldsDeriving
