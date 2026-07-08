import Lsc.Compile.Yul

/-!
Codegen-level tests for `IR.Stmt.staticCall` — `STATICCALL` with mandatory success check and
no transient-storage lock (`tload`/`tstore`). -/

open Lsc Lsc.Compile Lsc.Compile.IR

namespace Lsc.StaticCallTest

def sampleStaticCall : IR.Stmt :=
  .staticCall (.local "target") 0 [] 0

def sampleReadTxBody : IR.Stmt :=
  .seq (.staticCall (.sload 1) 0 [] 0) .skip

def yulStaticCall : String := irStmtToYulString sampleStaticCall
def yulReadTxBody : String := irStmtToYulString sampleReadTxBody

theorem static_call_emits_opcode :
    yulStaticCall.contains "staticcall(gas()" = true := by native_decide

theorem static_call_checks_success :
    yulStaticCall.contains "iszero(lsc_static_success)" = true := by native_decide

theorem static_call_has_no_transient_lock :
    yulStaticCall.contains "tload(" = false ∧ yulStaticCall.contains "tstore(" = false := by
  native_decide

theorem read_tx_body_has_staticcall_no_lock :
    yulReadTxBody.contains "staticcall(gas()" = true ∧
      yulReadTxBody.contains "tload(" = false ∧ yulReadTxBody.contains "tstore(" = false := by
  native_decide

#eval IO.println yulStaticCall
#eval IO.println yulReadTxBody

end Lsc.StaticCallTest
