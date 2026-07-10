import Lsc.Compile.Yul
import Lsc.Compile.Bytecode
import Lsc.Compile.Bytecode.Codegen
import Lsc.Compile.Bytecode.CodegenInvariant
import Lsc.Compile.ExternalCallSpec
import Lsc.Compile.IR.Opt.Pipeline

/-!
High-level properties for `IR.externalCall` / `IR.externalCallBind` lowering.

Each theorem states a plain-English guarantee first, then encodes it via `ExternalCallSpec` or
`CodegenInvariant` predicates — never raw opcode hex substrings. -/

open Lsc Lsc.Compile Lsc.Compile.IR Lsc.Compile.Bytecode

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

/-- Minimal Escrow-shaped repro: locals + `token = sload(2)` + IERC20 `transfer`. -/
def transferBindStmt : IR.Stmt :=
  .seq (.letBind "recipient" (.lit 0xaaa))
    (.seq (.letBind "amount" (.lit 100))
      (.seq (.letBind "token" (.sload 2))
        (.externalCallBind (.local "token") 0xa9059cbb
          [.local "recipient", .local "amount"] "ok")))

private def yulStmts (s : IR.Stmt) : List EvmYul.Yul.Ast.Stmt :=
  irStmtToYul s

private def bytecodeInstrs (s : IR.Stmt) : List Instr :=
  match Bytecode.Codegen.stmtFresh (IR.Opt.optimizeStmt s) with
  | .ok instrs => instrs
  | .error e => panic! e

/-! ### External `call` -/

/-- **Property:** An `externalCall` reverts when the underlying EVM call returns failure. -/
theorem externalCall_reverts_on_call_failure :
    YulSpec.revertsOnCallFailure (yulStmts sampleCallNoBoolCheck) = true := by native_decide

/-- **Property:** An `externalCall` issues a real EVM `call` opcode in generated Yul. -/
theorem externalCall_emits_call_opcode :
    YulSpec.emitsCall (yulStmts sampleCallNoBoolCheck) = true := by native_decide

/-- **Property:** An `externalCall` without bool-check does not decode returndata. -/
theorem externalCall_omits_returndata_decode :
    YulSpec.hasReturndataBoolGuard (yulStmts sampleCallNoBoolCheck) = false := by native_decide

/-- **Property:** An `externalCall` with `checkBoolReturn` decodes returndata and guards on false. -/
theorem externalCall_with_bool_check_decodes_returndata :
    YulSpec.hasReturndataBoolGuard (yulStmts sampleCallWithBoolCheck) = true := by native_decide

/-- **Property:** An `externalCall` with `checkBoolReturn` still reverts on call failure. -/
theorem externalCall_with_bool_check_reverts_on_failure :
    YulSpec.revertsOnCallFailure (yulStmts sampleCallWithBoolCheck) = true := by native_decide

/-! ### External `call` + return binding -/

/-- **Property:** An `externalCallBind` binds the first return word to the named local. -/
theorem externalCallBind_binds_return_word :
    YulSpec.bindsReturnWord (yulStmts sampleCallBind) "ok" = true := by native_decide

/-- **Property:** An `externalCallBind` issues a real EVM `call` opcode in generated Yul. -/
theorem externalCallBind_emits_call_opcode :
    YulSpec.emitsCall (yulStmts sampleCallBind) = true := by native_decide

/-- **Property:** An `externalCallBind` does not use the legacy ERC20 returndata bool-check path. -/
theorem externalCallBind_omits_returndata_bool_check :
    YulSpec.hasReturndataBoolGuard (yulStmts sampleCallBind) = false := by native_decide

/-! ### Reentrancy guard -/

/-- **Property:** A reentrancy-guarded external call uses transient storage lock/unlock. -/
theorem guarded_externalCall_uses_transient_lock :
    YulSpec.usesTransientLock (yulStmts sampleGuardedCall) = true := by native_decide

/-! ### IR optimization + bytecode callee address -/

/-- **Property:** IR optimization does not change external-call sites on the transfer repro. -/
theorem optimize_preserves_transfer_call_site :
    externalCallSites (IR.Opt.optimizeStmt transferBindStmt) =
      externalCallSites transferBindStmt := by native_decide

/-- **Property:** Bytecode codegen loads the IERC20 callee with `DUP2` after `GAS` (token, not amount). -/
theorem externalCallBind_bytecode_uses_dup2_callee_after_gas :
    gasDupDepthBeforeCall (bytecodeInstrs transferBindStmt) = some 2 := by native_decide

/-- **Property:** Bytecode codegen does not load the CALL callee with `DUP4` (the pre-fix amount bug). -/
theorem externalCallBind_bytecode_not_dup4_callee_after_gas :
    gasDupDepthBeforeCall (bytecodeInstrs transferBindStmt) ≠ some 4 := by native_decide

/-- **Property:** The transfer repro lowers to one `externalCallBind` on the `token` local. -/
theorem transfer_bind_lowers_to_token_call :
    externalCallSites transferBindStmt =
      [ExternalCallSite.callBind (.local "token") 0xa9059cbb
        [.local "recipient", .local "amount"] "ok"] := by native_decide

end Lsc.SafeExternalCallTest
