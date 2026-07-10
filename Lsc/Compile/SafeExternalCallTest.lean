import Lsc.Compile.Yul
import Lsc.Compile.Bytecode
import Lsc.Compile.Bytecode.Codegen
import Lsc.Compile.IR.Opt.Pipeline

/-!
Codegen-level tests for `IR.Stmt.externalCall` (`Lsc/Compile/IR.lean`) — the real EVM `CALL`
IR node: every rendering includes the mandatory success check, and (when requested) the
mandatory `bool`-return check — asserted via `native_decide` on the rendered Yul string.

Bytecode tests below guard stack-depth tracking in `Bytecode/Codegen.lean`'s ABI pack +
`emitCall` path (Escrow `release` → inlined IERC20 `transfer`). -/

open Lsc Lsc.Compile Lsc.Compile.IR

namespace Lsc.SafeExternalCallTest

def sampleCallNoBoolCheck : IR.Stmt :=
  .externalCall (.local "target") 0 [] false

def sampleCallWithBoolCheck : IR.Stmt :=
  .externalCall (.local "target") 0 [] true

def sampleCallBind : IR.Stmt :=
  .externalCallBind (.local "token") 0x00000000 [] "ok"

def sampleGuardedCall : IR.Stmt :=
  .seq .checkReentrancyLock
    (.seq (.setReentrancyLock true)
      (.seq (.externalCall (.local "target") 0 [] false)
        (.setReentrancyLock false)))

def yulNoBoolCheck : String := irStmtToYulString sampleCallNoBoolCheck
def yulWithBoolCheck : String := irStmtToYulString sampleCallWithBoolCheck
def yulCallBind : String := irStmtToYulString sampleCallBind
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

theorem call_bind_emits_call_and_mload_binding :
    yulCallBind.contains "call(gas()" = true ∧
      yulCallBind.contains "let ok := mload(0x" = true := by native_decide

theorem call_bind_omits_legacy_checkBoolReturn_path :
    yulCallBind.contains "returndatasize()" = false := by native_decide

theorem no_bool_check_omits_return_decoding :
    yulNoBoolCheck.contains "returndatasize()" = false := by native_decide

theorem no_bool_check_reverts_with_no_data :
    yulNoBoolCheck.contains "revert(0x0000000000000000000000000000000000000000000000000000000000000000, 0x0000000000000000000000000000000000000000000000000000000000000000)"
      = true := by native_decide

theorem guarded_call_emits_transient_lock_ops :
    yulGuardedCall.contains "tload(" = true ∧ yulGuardedCall.contains "tstore(" = true := by
  native_decide

/-! ## Bytecode backend: `CALL` target must reference the token address, not a calldata arg -/

private def stmtToHex (s : IR.Stmt) : String :=
  match Bytecode.Codegen.stmtFresh (IR.Opt.optimizeStmt s) with
  | .ok instrs =>
    match Bytecode.encode instrs with
    | .ok bytes => Bytecode.toHex bytes
    | .error e => panic! e
  | .error e => panic! e

/-- Minimal Escrow-shaped repro: `recipient`/`amount` locals + `token = sload(2)` + `transfer`. -/
def transferBindStmt : IR.Stmt :=
  .seq (.letBind "recipient" (.lit 0xaaa))
    (.seq (.letBind "amount" (.lit 100))
      (.seq (.letBind "token" (.sload 2))
        (.externalCallBind (.local "token") 0xa9059cbb
          [.local "recipient", .local "amount"] "ok")))

def transferBindHex : String := stmtToHex transferBindStmt

theorem transfer_bind_loads_token_from_slot2 :
    transferBindHex.contains "600254" = true := by native_decide

theorem transfer_bind_call_avoids_gas_dup4 :
    transferBindHex.contains "5a83" = false := by native_decide

theorem transfer_bind_call_uses_gas_dup_token :
    transferBindHex.contains "5a81" = true := by native_decide

#eval IO.println yulNoBoolCheck
#eval IO.println yulWithBoolCheck
#eval IO.println yulCallBind
#eval IO.println yulGuardedCall

end Lsc.SafeExternalCallTest
