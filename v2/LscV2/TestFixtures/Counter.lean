import LscV2.AST

namespace LscV2.TestFixtures

def incrementLet : Stmt :=
  Stmt.letBind "n" ⟨Ty.wei, Wei.addCheckedNatStorage "number" 1⟩

@[simp] theorem incrementLet_eq :
    incrementLet =
      Stmt.letBind "n" ⟨Ty.wei, Wei.addCheckedNatStorage "number" 1⟩ := rfl

def incrementSet : Stmt :=
  Stmt.storageSet "number" ⟨Ty.wei, Wei.Expr.var "n"⟩

@[simp] theorem incrementSet_eq :
    incrementSet =
      Stmt.storageSet "number" ⟨Ty.wei, Wei.Expr.var "n"⟩ := rfl

def incrementEmit : Stmt :=
  Stmt.emit "Incremented" [⟨Ty.wei, Wei.Expr.var "n"⟩]

@[simp] theorem incrementEmit_eq :
    incrementEmit =
      Stmt.emit "Incremented" [⟨Ty.wei, Wei.Expr.var "n"⟩] := rfl

def incrementRequire : Stmt :=
  Stmt.require (CoreExpr.not (CoreExpr.storageGet Ty.bool "paused")) "Paused"

@[simp] theorem incrementRequire_eq :
    incrementRequire =
      Stmt.require (CoreExpr.not (CoreExpr.storageGet Ty.bool "paused")) "Paused" := rfl

def incrementAst : Stmt :=
  Stmt.seq incrementRequire
    (Stmt.seq incrementLet (Stmt.seq incrementSet incrementEmit))

@[simp] theorem incrementAst_eq :
    incrementAst =
      Stmt.seq incrementRequire
        (Stmt.seq incrementLet (Stmt.seq incrementSet incrementEmit)) := rfl

def pauseRequireOwner : Stmt :=
  Stmt.require
    (CoreExpr.eq Ty.address (CoreExpr.txField .caller)
      (CoreExpr.storageGet Ty.address "owner")) "NotOwner"

@[simp] theorem pauseRequireOwner_eq :
    pauseRequireOwner =
      Stmt.require
        (CoreExpr.eq Ty.address (CoreExpr.txField .caller)
          (CoreExpr.storageGet Ty.address "owner")) "NotOwner" := rfl

def pauseEmit : Stmt := Stmt.emit "Paused" []

@[simp] theorem pauseEmit_eq : pauseEmit = Stmt.emit "Paused" [] := rfl

def pauseAst : Stmt :=
  Stmt.seq pauseRequireOwner
    (Stmt.seq incrementRequire (Stmt.seq
      (Stmt.storageSet "paused" ⟨Ty.bool, CoreExpr.lit Ty.bool (.bool true)⟩)
      pauseEmit))

@[simp] theorem pauseAst_eq :
    pauseAst =
      Stmt.seq pauseRequireOwner
        (Stmt.seq incrementRequire (Stmt.seq
          (Stmt.storageSet "paused" ⟨Ty.bool, CoreExpr.lit Ty.bool (.bool true)⟩)
          pauseEmit)) := rfl

def unpauseAst : Stmt :=
  Stmt.seq pauseRequireOwner
    (Stmt.seq
      (Stmt.require (CoreExpr.storageGet Ty.bool "paused") "Paused")
      (Stmt.seq
        (Stmt.storageSet "paused" ⟨Ty.bool, CoreExpr.lit Ty.bool (.bool false)⟩)
        (Stmt.emit "Unpaused" [])))

@[simp] theorem unpauseAst_eq :
    unpauseAst =
      Stmt.seq pauseRequireOwner
        (Stmt.seq
          (Stmt.require (CoreExpr.storageGet Ty.bool "paused") "Paused")
          (Stmt.seq
            (Stmt.storageSet "paused" ⟨Ty.bool, CoreExpr.lit Ty.bool (.bool false)⟩)
            (Stmt.emit "Unpaused" []))) := rfl

end LscV2.TestFixtures
