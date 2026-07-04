import Lsc.Compile.Lower
import Lsc.Compile.IR
import Lsc.TestFixtures.SyntaxSmoke
import Lsc.Lib.Wei.Optimize
import Lsc.Compile.IR.Eval

namespace Lsc.Compile.Correctness

open Lsc.TestFixtures
open Lsc.Compile.IR (IRState evalExpr evalStmt)

abbrev IRExpr := Lsc.Compile.IR.Expr
abbrev IRStmt := Lsc.Compile.IR.Stmt

def counterConfig : Config :=
  { storage := StorageLayout.fromList [("number", 0), ("paused", 1), ("owner", 2)]
  , events := { topic0 := fun _ => none } }

theorem Wei_lower_addCheckedNatStorage_shape :
    Wei.lowerLetBind (fun f => counterConfig.storage.fieldSlot f) "n"
        (Wei.addCheckedNatStorage "number" 1) =
      .ok Wei.incrementLetIR := rfl

theorem incrementLet_lowers_ok :
    (Lower.stmt counterConfig incrementLet).isOk := by native_decide

theorem incrementLet_ir_binds_incremented_local :
    let st := evalStmt { slots := [(0, 5)] } Wei.incrementLetIR
    st.lookupLocal "n" = 6 ∧ st.lookupLocal "lsc_n_old" = 5 ∧ ¬ st.reverted := by native_decide

def incrementBody : Stmt :=
  Stmt.seq incrementLet (Stmt.seq incrementSet incrementEmit)

def incrementEventConfig : Config :=
  { storage := counterConfig.storage
  , events := { topic0 := fun
      | "Incremented" => some 0x20d8a6f5a693f9d1d627a598e8820f7a55ee74c183aa8f1a30e8d4e8dd9a8d84
      | _ => none } }

theorem increment_body_lowers_ok :
    Lower.stmt incrementEventConfig incrementBody |>.isOk := by native_decide

end Lsc.Compile.Correctness
