import Lsc.Compile.Yul

/-!
Codegen-level tests for `IR.Stmt.safeExternalCall` (`Lsc/Compile/IR.lean`) — the real EVM `CALL`
IR node introduced so a black-box cross-contract call is **safe by construction, no opt-out**:
there is no lower-level "raw call" primitive in this pipeline a contract author could reach
instead, so every one of this node's Yul renderings below always includes the mandatory success
check, and (when requested) the mandatory `bool`-return check — asserted here exactly the same
way `Lsc/Compile/YulTest.lean` asserts other codegen invariants (`.contains` on the rendered Yul
string, checked via `native_decide`), so a future change to `safeExternalCallToYul` that
accidentally dropped either check would fail to compile this file, not just silently ship. -/

open Lsc Lsc.Compile Lsc.Compile.IR

namespace Lsc.SafeExternalCallTest

/-- A representative `safeExternalCall`, addressing a `local "target"` callee with calldata
already sitting at memory `[0, 4)` — the exact shape `exec Token.transfer(recipient, amount);`
would eventually lower to once real ABI-encoded-calldata generation lands (`docs/todo/backlog.md`'s N-contract
dispatch registry item). -/
def sampleCallNoBoolCheck : IR.Stmt :=
  .safeExternalCall (.local "target") (.lit 0) (.lit 4) false

def sampleCallWithBoolCheck : IR.Stmt :=
  .safeExternalCall (.local "target") (.lit 0) (.lit 4) true

def yulNoBoolCheck : String := irStmtToYulString sampleCallNoBoolCheck
def yulWithBoolCheck : String := irStmtToYulString sampleCallWithBoolCheck

/-! ## The success check is always present — no opt-out, regardless of `checkBoolReturn` -/

theorem no_bool_check_still_reverts_on_call_failure :
    yulNoBoolCheck.contains "iszero(lsc_call_success)" = true := by native_decide

theorem with_bool_check_still_reverts_on_call_failure :
    yulWithBoolCheck.contains "iszero(lsc_call_success)" = true := by native_decide

theorem no_bool_check_emits_the_real_call_opcode :
    yulNoBoolCheck.contains "call(gas()" = true := by native_decide

/-! ## `checkBoolReturn = true` additionally decodes and checks the returned `bool` -/

theorem with_bool_check_decodes_return_value :
    yulWithBoolCheck.contains "mload(0x" = true := by native_decide

theorem with_bool_check_guards_on_returndatasize :
    yulWithBoolCheck.contains "returndatasize()" = true := by native_decide

/-- `checkBoolReturn = false` (a callee with no meaningful return value, e.g. one that always
reverts on any failure and returns nothing on success) must **not** synthesize the bool-decode
check at all — there is genuinely no return data to decode in that case. -/
theorem no_bool_check_omits_return_decoding :
    yulNoBoolCheck.contains "returndatasize()" = false := by native_decide

/-- Every rendering unconditionally reverts with empty returndata (`revert(0, 0)`) on failure —
never a "soft-fail"/swallowed-error shape, mirroring `Lsc.ContractM.PairM.exec`'s Lean-level
`exec_never_silently_swallows_failure` (`Core/ContractM.lean`) one layer down, at the actual
bytecode this is meant to become. -/
theorem no_bool_check_reverts_with_no_data :
    yulNoBoolCheck.contains "revert(0x0000000000000000000000000000000000000000000000000000000000000000, 0x0000000000000000000000000000000000000000000000000000000000000000)"
      = true := by native_decide

#eval IO.println yulNoBoolCheck
#eval IO.println yulWithBoolCheck

end Lsc.SafeExternalCallTest
