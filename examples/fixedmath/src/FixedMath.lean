import Lsc.Prelude
import Lsc.Compile.Bytecode
import Lsc.Lang.Checks
import Lsc.Lib.Math.Inline

open Lsc Lsc.Compile Lsc.Deriving

namespace FixedMath

structure FixedMathStorage where
  dummy : Wad := ⟨0⟩
  deriving Repr, ContractStorage

inductive FixedMathError where
  | Overflow
  deriving Repr, DecidableEq, ContractError

inductive FixedMathEvent where
  | Dummy
  deriving Repr, DecidableEq, ContractEvent

library_view sqrtProduct(a : Wad, b : Wad) : Wad =>
  Lsc.Math.Stmt.sqrtProductExpr (Fixed.Expr.var "a") (Fixed.Expr.var "b");

library_view minOf(a : Wad, b : Wad) : Wad =>
  Lsc.Math.Stmt.minOfExpr (Fixed.Expr.var "a") (Fixed.Expr.var "b");

derive_contract "FixedMath" FixedMathStorage FixedMathError FixedMathEvent

def mkState : ContractState FixedMathStorage :=
  { storage := { dummy := ⟨0⟩ }
    context := { caller := 0, callvalue := 0, timestamp := 0, origin := 0 }
    locked := false }

example : (Checks.validateAll contractDef).isOk := by native_decide

example : bytecodeHex.startsWith "0x" ∧ bytecodeHex.length > 10 := by native_decide

#check (sqrtProduct : Wad → Wad → FixedMathM (Val Ty.wad))
#check (minOf : Wad → Wad → FixedMathM (Val Ty.wad))

end FixedMath
