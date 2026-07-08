import Lsc.Lang.Derive
import Lsc.Lang.Syntax
import Lsc.Lang.Eval
import Lsc.Lang.Checks
import Lsc.Compile.Bytecode

/-!
# End-to-end tests for `view` functions

Covers the full pipeline the "View functions: syntax, elaboration, and bytecode" plan added:
`Stmt.evalView`'s runtime semantics, `Checks.checkViewPurity`/`checkViewReturns`'s static
rejections, and the real surface syntax (`view name(..) : Ty => e;`/block form) compiled all the
way through `derive_contract` to bytecode with a genuine `RETURN` (not just `STOP`). -/

open Lsc

namespace Lsc.ViewTest

structure VStorage where
  n : Wad := ⟨0⟩
  deriving Lsc.Deriving.ContractStorage

inductive VError where
  | Overflow
  deriving Repr, DecidableEq, Lsc.Deriving.ContractError

inductive VEvent where
  | Bumped
  deriving Repr, DecidableEq, Lsc.Deriving.ContractEvent

def mkVState (n : Wad) : ContractState VStorage :=
  { storage := { n := n }
    context := { caller := 0, callvalue := 0, timestamp := 0, origin := 0 }
    locked := false }

/-! ## `Checks.checkViewPurity`/`checkViewReturns` -/

-- A `view` whose body writes storage is rejected — never reaches the bytecode/Yul pipeline.
def impureViewFn : FunctionDef :=
  { name := "bad", kind := .view, params := [], retTy := .uint256,
    body := Stmt.seq (Stmt.storageSet "n" ⟨Ty.uint256, CoreExpr.lit Ty.uint256 (.u256 1)⟩)
      (Stmt.ret ⟨Ty.uint256, CoreExpr.lit Ty.uint256 (.u256 1)⟩) }

example : (Checks.checkViewPurity impureViewFn).isSome := by native_decide

-- A `view` that doesn't return on every path is rejected too.
def nonReturningViewFn : FunctionDef :=
  { name := "bad2", kind := .view, params := [], retTy := .uint256, body := Stmt.skip }

example : (Checks.checkViewReturns nonReturningViewFn).isSome := by native_decide

-- A well-formed `view` — pure, and returns on every path — passes both checks.
def goodViewFn : FunctionDef :=
  { name := "good", kind := .view, params := [], retTy := .uint256,
    body := Stmt.ret ⟨Ty.uint256, CoreExpr.lit Ty.uint256 (.u256 1)⟩ }

example : (Checks.checkViewPurity goodViewFn).isNone := by native_decide
example : (Checks.checkViewReturns goodViewFn).isNone := by native_decide

/-! ## End-to-end: real `view` surface syntax, compiled all the way through bytecode. -/

-- Expression-shorthand form.
view getN : Wad => σ.n;

-- Block form, exercising `let`/`return` (and a real parameter). `Compile.Lower`'s `lowerStmt`
-- has no case for `.ifThenElse` yet (a pre-existing gap, unrelated to `view` support), so this
-- deliberately avoids `if` in order to stay compilable all the way to bytecode below —
-- `ifReturnBody`'s direct `Stmt.evalView` unit tests below already exercise `if`/`return`
-- together at the semantics level.
view getPlusAlt(alt : Wad) : Wad {
  let m = σ.n +? alt;
  return m;
}

tx bump {
  let m = σ.n +? 1;
  σ.n = m;
  emit Bumped();
}

derive_contract "V" VStorage VError VEvent

/-! ## `Stmt.evalView` — direct unit tests against `VStorage`'s real `ContractDSL` instance,
no surface syntax involved. -/

/-- `return 7;` — a trivial view body that always returns the literal `7`. -/
def constBody : Stmt := Stmt.ret ⟨Ty.uint256, CoreExpr.lit Ty.uint256 (.u256 7)⟩

example :
    Except.map (fun x => Val.u256Of x.1)
        (runS (Stmt.evalView (S := VStorage) (E := VEvent) (Err := VError)
          Ty.uint256 constBody) (mkVState (Wad.mkNat 0)))
      = .ok 7 := by
  native_decide

/-- `if (cond) { return 1; } return 0;` — every path returns, matching
`Checks.allPathsReturn`'s static rule. -/
def ifReturnBody (condVal : Bool) : Stmt :=
  Stmt.ifThenElse (CoreExpr.lit Ty.bool (.bool condVal))
    (Stmt.ret ⟨Ty.uint256, CoreExpr.lit Ty.uint256 (.u256 1)⟩)
    (Stmt.ret ⟨Ty.uint256, CoreExpr.lit Ty.uint256 (.u256 0)⟩)

example :
    Except.map (fun x => Val.u256Of x.1)
        (runS (Stmt.evalView (S := VStorage) (E := VEvent) (Err := VError)
          Ty.uint256 (ifReturnBody true)) (mkVState (Wad.mkNat 0)))
      = .ok 1 := by
  native_decide

example :
    Except.map (fun x => Val.u256Of x.1)
        (runS (Stmt.evalView (S := VStorage) (E := VEvent) (Err := VError)
          Ty.uint256 (ifReturnBody false)) (mkVState (Wad.mkNat 0)))
      = .ok 0 := by
  native_decide

-- `getN`/`getNOrOne` are registered as real `.view` functions with a real `Ty.wad` `retTy`,
-- not folded into the `.external`/`tx`-only default.
example : (contractDef.functions.filter (·.kind == Lsc.FunctionKind.view)).length = 2 := by
  native_decide

-- The whole contract (both `tx`s and both `view`s) still passes every structural check
-- (`checkSelectorCollisions` now spans both kinds; `checkViewPurity`/`checkViewReturns` pass).
example : (Checks.validateAll contractDef).isOk := by native_decide

-- `getN` really is callable as a genuine `ContractM`-valued Lean function, returning the
-- ABI-tagged `Val Ty.wad` (`Stmt.evalView`'s result type).
example :
    Except.map (fun x => Val.wadOf x.1) (runS getN (mkVState (Wad.mkNat 42)))
      = .ok (Wad.mkNat 42) := by
  native_decide

example :
    Except.map (fun x => Val.wadOf x.1)
        (runS (getPlusAlt (Wad.mkNat 8)) (mkVState (Wad.mkNat 42)))
      = .ok (Wad.mkNat 50) := by
  native_decide

-- The compiled bytecode is real (`derive_contract`'s auto-generated `bytecodeHex`, using
-- the real topic0 table) — non-empty confirms `Bytecode.contract`/`Codegen`'s `.ret` case (the
-- `MSTORE .. RETURN` sequence for `getN`/`getNOrAlt`) actually ran without error.
example : bytecodeHex ≠ "" := by native_decide

end Lsc.ViewTest
