import Lsc.Lang.Checks
import Lsc.TestFixtures.SyntaxSmoke

open Lsc Lsc.TestFixtures

namespace Lsc.ChecksTest

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

-- arith-error-coverage: `+?` reachable, matching `Overflow` constructor declared ⇒ passes.
def overflowOkDef : ContractDef where
  name := "OverflowOk"
  storage := [("n", .wei, none)]
  errors := ["Overflow"]
  events := []
  functions :=
    [{ name := "bump", kind := .external, params := [], retTy := .unit,
       body := Stmt.letBind "m" ⟨Ty.wei, Wei.addCheckedNatStorage "n" 1⟩ }]
  interfaces := []

example : Checks.checkArithErrorCoverage overflowOkDef = none := by native_decide

-- arith-error-coverage: `+?` reachable, NO `Overflow` constructor declared ⇒ fails with a
-- clear, actionable message naming the function/operator/missing constructor.
def overflowMissingDef : ContractDef where
  name := "OverflowMissing"
  storage := [("n", .wei, none)]
  errors := []
  events := []
  functions :=
    [{ name := "bump", kind := .external, params := [], retTy := .unit,
       body := Stmt.letBind "m" ⟨Ty.wei, Wei.addCheckedNatStorage "n" 1⟩ }]
  interfaces := []

example : Checks.checkArithErrorCoverage overflowMissingDef |>.isSome := by native_decide

example :
    Checks.checkArithErrorCoverage overflowMissingDef =
      some "`bump` uses `+?`, which can raise `ArithError.Overflow`, but \
OverflowMissing's error type has no `Overflow` constructor — add one or write \
`ContractErrors` by hand" := by
  native_decide

-- The same contract is also rejected end-to-end via the compile pipeline.
example : ¬ (Checks.validateAll overflowMissingDef).isOk := by native_decide

end Lsc.ChecksTest
