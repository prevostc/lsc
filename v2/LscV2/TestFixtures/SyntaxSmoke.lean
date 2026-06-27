import LscV2.Lang.AST

/-!
  Minimal Stmt shapes for macro, lowering, and validation smoke tests.
  Field names (`number`, `paused`, `owner`) mirror a typical storage layout but
  are not tied to any particular example contract.
-/

namespace LscV2.TestFixtures

def incrementLet : Stmt :=
  Stmt.letBind "n" ⟨Ty.wei, Wei.addCheckedNatStorage "number" 1⟩

def incrementSet : Stmt :=
  Stmt.storageSet "number" ⟨Ty.wei, Wei.Expr.var "n"⟩

def incrementEmit : Stmt :=
  Stmt.emit "Incremented" [⟨Ty.wei, Wei.Expr.var "n"⟩]

def incrementRequire : Stmt :=
  Stmt.require (CoreExpr.not (CoreExpr.storageGet Ty.bool "paused")) "Paused"

def incrementTail : Stmt := Stmt.seq incrementSet incrementEmit

def pauseRequireOwner : Stmt :=
  Stmt.require
    (CoreExpr.eq Ty.address (CoreExpr.txField .caller)
      (CoreExpr.storageGet Ty.address "owner")) "NotOwner"

def pauseEmit : Stmt := Stmt.emit "Paused" []

def pauseSet : Stmt :=
  Stmt.storageSet "paused" ⟨Ty.bool, CoreExpr.lit Ty.bool (.bool true)⟩

def pauseTail : Stmt := Stmt.seq pauseSet pauseEmit

def pauseBody : Stmt := Stmt.seq incrementRequire pauseTail

def pauseAst : Stmt := Stmt.seq pauseRequireOwner pauseBody

def unpauseRequirePaused : Stmt :=
  Stmt.require (CoreExpr.storageGet Ty.bool "paused") "Paused"

def unpauseSet : Stmt :=
  Stmt.storageSet "paused" ⟨Ty.bool, CoreExpr.lit Ty.bool (.bool false)⟩

def unpauseEmit : Stmt := Stmt.emit "Unpaused" []

def unpauseTail : Stmt := Stmt.seq unpauseSet unpauseEmit

def unpauseBody : Stmt := Stmt.seq unpauseRequirePaused unpauseTail

def unpauseAst : Stmt := Stmt.seq pauseRequireOwner unpauseBody

def incrementBody : Stmt := Stmt.seq incrementLet incrementTail

def incrementAst : Stmt := Stmt.seq incrementRequire incrementBody

end LscV2.TestFixtures
