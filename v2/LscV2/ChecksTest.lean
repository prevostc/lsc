import LscV2.Checks
import LscV2.AST

open LscV2

namespace LscV2.ChecksTest

def counterIncrementAst : Stmt :=
  Stmt.seq
    (Stmt.require (Expr.not (Expr.storageGet (t := .bool) "paused")) "Paused")
    (Stmt.seq
      (Stmt.letBind "n" ⟨Ty.wei,
        Expr.weiAddCheckedNat (Expr.storageGet (t := .wei) "number") 1⟩)
      (Stmt.seq
        (Stmt.storageSet "number" ⟨Ty.wei, Expr.var (t := .wei) "n"⟩)
        (Stmt.emit "Incremented" [⟨Ty.wei, Expr.var (t := .wei) "n"⟩])))

def counterDef : ContractDef where
  name := "Counter"
  storage :=
    [("number", .wei, none), ("paused", .bool, some ⟨.bool, Expr.litBool false⟩),
     ("owner", .address, none)]
  errors := ["Paused", "NotOwner", "Overflow"]
  events := [("Incremented", [("n", .wei)]), ("Paused", []), ("Unpaused", [])]
  functions :=
    [{ name := "increment", kind := .external, params := [], retTy := .unit,
       body := counterIncrementAst, permits := [] },
     { name := "pause", kind := .external, params := [], retTy := .unit, body := .skip, permits := [] },
     { name := "unpause", kind := .external, params := [], retTy := .unit, body := .skip, permits := [] }]
  interfaces := []

example : Checks.validateAll counterDef = .ok counterDef := rfl

def cyclicBody : Stmt := Stmt.call "f" []
def cyclicDef : ContractDef where
  name := "Cyclic"
  storage := []
  errors := []
  events := []
  functions :=
    [{ name := "f", kind := .internal, params := [], retTy := .unit, body := cyclicBody, permits := [] }]
  interfaces := []

example : (Checks.validateAll cyclicDef).isError := by
  native_decide

def badUInt256Body : Stmt :=
  Stmt.letBind "n" ⟨Ty.wei,
    Expr.weiAddCheckedNat (Expr.litU256 1) 1⟩

def badUInt256Def : ContractDef where
  name := "Bad"
  storage := []
  errors := []
  events := []
  functions :=
    [{ name := "f", kind := .external, params := [], retTy := .unit, body := badUInt256Body, permits := [] }]
  interfaces := []

example : Checks.checkNoUInt256Arithmetic badUInt256Def |>.isSome := rfl

def collisionDef : ContractDef where
  name := "Collide"
  storage := []
  errors := []
  events := []
  functions :=
    [{ name := "f", kind := .external, params := [], retTy := .unit, body := .skip, permits := [] },
     { name := "g", kind := .external, params := [], retTy := .unit, body := .skip, permits := [] }]
  interfaces := []

example : Checks.checkSelectorCollisions collisionDef = none := rfl

end LscV2.ChecksTest
