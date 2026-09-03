import Lsc.Lang.Syntax
import Lsc.Lib.Math.Stmt

/-!
# Math library — `library_view` for contract integration (no `lscExpr` syntax)

Use `library_view` instead of `view ... => Math.sqrtDown(...)` when a read-only function needs
sqrt/min. The return expression is a Lean `Fixed.Expr` term (typically built with
`Lsc.Math.Stmt` helpers); bodies are flushed at `derive_contract` like ordinary `view`s. -/

namespace Lsc.Math

open Lean Lean.Elab Lean.Elab.Command Lsc.Deriving Lsc.Syntax

/-- `library_view name(params) : RetTy => fixedExpr;` — like `view`, but the body is a Lean
`Fixed.Expr` term instead of `lscExpr` surface syntax. -/
syntax (name := lscLibraryView) "library_view " ident
  (optional("(" lscTxParam,* ")")) " : " ident " => " term ";" : command

elab "library_view " name:ident params:(optional("(" lscTxParam,* ")")) " : " retTy:ident
    " => " expr:term ";" : command => do
  let ns ← getCurrNamespace
  let fnName := ns ++ name.getId
  let paramsStx : Array (TSyntax `lscTxParam) :=
    if params.raw.getNumArgs > 0 then
      params.raw[1]!.getSepArgs.map fun s => (⟨s⟩ : TSyntax `lscTxParam)
    else #[]
  let paramsResolved ← liftTermElabM <| paramsStx.toList.mapM elabTxParam
  let retKind ← liftTermElabM <| elabLscTyIdent retTy
  stashParamTys fnName paramsStx
  modifyEnv fun env =>
    Lsc.Deriving.contractLibraryViewSyntaxExt.modifyState env fun m =>
      m.insert ns ((m.find? ns |>.getD []) ++
        [(fnName, name.raw, paramsResolved, retKind, expr.raw)])

end Lsc.Math
