import LscV2.Lang.Checks
import LscV2.TestFixtures.SyntaxSmoke

open LscV2 LscV2.TestFixtures

namespace LscV2.ChecksTest

def counterDef : ContractDef where
  name := "Counter"
  storage :=
    [("number", .wei, none), ("paused", .bool, some ⟨.bool, CoreExpr.lit Ty.bool (.bool false)⟩),
     ("owner", .address, none)]
  errors := ["Paused", "NotOwner", "Overflow"]
  events := [("Incremented", [("n", .wei)]), ("Paused", []), ("Unpaused", [])]
  functions :=
    [{ name := "increment", kind := .external, params := [], retTy := .unit, body := incrementAst },
     { name := "pause", kind := .external, params := [], retTy := .unit, body := .skip },
     { name := "unpause", kind := .external, params := [], retTy := .unit, body := .skip }]
  interfaces := []

example : (Checks.validateAll counterDef).isOk := by native_decide

def badUInt256Body : Stmt :=
  Stmt.letBind "n" ⟨Ty.uint256, CoreExpr.lit Ty.uint256 (.u256 1)⟩

def badUInt256Def : ContractDef where
  name := "Bad"
  storage := []
  errors := []
  events := []
  functions :=
    [{ name := "f", kind := .external, params := [], retTy := .unit, body := badUInt256Body }]
  interfaces := []

example : Checks.checkNoUInt256Arithmetic badUInt256Def |>.isSome := by native_decide

def collisionDef : ContractDef where
  name := "Collide"
  storage := []
  errors := []
  events := []
  functions :=
    [{ name := "f", kind := .external, params := [], retTy := .unit, body := .skip },
     { name := "g", kind := .external, params := [], retTy := .unit, body := .skip }]
  interfaces := []

example : Checks.checkSelectorCollisions collisionDef = none := by native_decide

end LscV2.ChecksTest
