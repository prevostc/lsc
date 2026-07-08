import Lsc.Compile.Yul

/-!
Codegen-level tests for `IR.Stmt.externalCall` (`Lsc/Compile/IR.lean`) — the real EVM `CALL`
IR node: every rendering includes the mandatory success check, and (when requested) the
mandatory `bool`-return check — asserted via `native_decide` on the rendered Yul string. -/

open Lsc Lsc.Compile Lsc.Compile.IR

namespace Lsc.SafeExternalCallTest

def sampleCallNoBoolCheck : IR.Stmt :=
  .externalCall (.local "target") 0 [] false

def sampleCallWithBoolCheck : IR.Stmt :=
  .externalCall (.local "target") 0 [] true

def sampleGuardedCall : IR.Stmt :=
  .seq .checkReentrancyLock
    (.seq (.setReentrancyLock true)
      (.seq (.externalCall (.local "target") 0 [] false)
        (.setReentrancyLock false)))

def yulNoBoolCheck : String := irStmtToYulString sampleCallNoBoolCheck
def yulWithBoolCheck : String := irStmtToYulString sampleCallWithBoolCheck
def yulGuardedCall : String := irStmtToYulString sampleGuardedCall

theorem no_bool_check_still_reverts_on_call_failure :
    yulNoBoolCheck.contains "iszero(lsc_call_success)" = true := by native_decide

theorem with_bool_check_still_reverts_on_call_failure :
    yulWithBoolCheck.contains "iszero(lsc_call_success)" = true := by native_decide

theorem no_bool_check_emits_the_real_call_opcode :
    yulNoBoolCheck.contains "call(gas()" = true := by native_decide

theorem with_bool_check_decodes_return_value :
    yulWithBoolCheck.contains "mload(0x" = true := by native_decide

theorem with_bool_check_guards_on_returndatasize :
    yulWithBoolCheck.contains "returndatasize()" = true := by native_decide

theorem no_bool_check_omits_return_decoding :
    yulNoBoolCheck.contains "returndatasize()" = false := by native_decide

theorem no_bool_check_reverts_with_no_data :
    yulNoBoolCheck.contains "revert(0x0000000000000000000000000000000000000000000000000000000000000000, 0x0000000000000000000000000000000000000000000000000000000000000000)"
      = true := by native_decide

theorem guarded_call_emits_transient_lock_ops :
    yulGuardedCall.contains "tload(" = true ∧ yulGuardedCall.contains "tstore(" = true := by
  native_decide

#eval IO.println yulNoBoolCheck
#eval IO.println yulWithBoolCheck
#eval IO.println yulGuardedCall

end Lsc.SafeExternalCallTest
