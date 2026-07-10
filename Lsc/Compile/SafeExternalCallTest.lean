import Lsc.Compile.Yul
import Lsc.Compile.Abi
import Lsc.Compile.Bytecode
import Lsc.Compile.Bytecode.Codegen
import Lsc.Compile.Bytecode.CodegenInvariant
import Lsc.Compile.ExternalCallSpec
import Lsc.Compile.IR.Opt.Pipeline

/-!
High-level properties for `IR.externalCall` / `IR.externalCallBind` lowering.

Each theorem states a plain-English guarantee first, then encodes it via `ExternalCallSpec` or
`CodegenInvariant` predicates — never raw opcode hex substrings. -/

open Lsc Lsc.Compile Lsc.Compile.IR Lsc.Compile.Bytecode Lsc.Compile.Abi
open EvmYul.Operation

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

/-- Same repro wrapped in reentrancy lock (Escrow `release` shape without SafeERC20 re-binds). -/
def guardedTransferBindStmt : IR.Stmt :=
  .seq (.letBind "recipient" (.lit 0xaaa))
    (.seq (.letBind "amount" (.lit 100))
      (.seq (.letBind "token" (.sload 2))
        (.seq (.seq .checkReentrancyLock (.setReentrancyLock true))
          (.seq (.externalCallBind (.local "token") 0xa9059cbb
              [.local "recipient", .local "amount"] "ok")
            (.setReentrancyLock false)))))

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

/-- **Property:** Bytecode codegen reloads token from storage slot 2 after `GAS` before `CALL`. -/
theorem externalCallBind_bytecode_reloads_token_sload_after_gas :
    gasSloadSlotBeforeCall (bytecodeInstrs transferBindStmt) 2 = true := by native_decide

/-- **Property:** The transfer repro `CALL` targets the `token` local (resolves to `sload 2`). -/
theorem externalCallBind_bytecode_call_targets_token :
    codegenCallUsesAddrInStmt (IR.Opt.optimizeStmt transferBindStmt)
      (bytecodeInstrs transferBindStmt) (.local "token") = true := by native_decide

/-- **Property:** Guarded transfer repro `CALL` targets token after reentrancy lock (Escrow bug shape). -/
theorem guarded_transfer_bind_call_targets_token :
    codegenCallUsesAddrInStmt (IR.Opt.optimizeStmt guardedTransferBindStmt)
      (bytecodeInstrs guardedTransferBindStmt) (.local "token") = true := by native_decide

/-- **Property:** Guarded transfer repro reloads token from slot 2 after `GAS`. -/
theorem guarded_transfer_bind_reloads_token_sload_after_gas :
    gasSloadSlotBeforeCall (bytecodeInstrs guardedTransferBindStmt) 2 = true := by native_decide

/-- **Property:** Bytecode codegen does not load the CALL callee with `DUP4` (the pre-fix amount bug). -/
theorem externalCallBind_bytecode_not_dup4_callee_after_gas :
    gasDupDepthBeforeCall (bytecodeInstrs transferBindStmt) ≠ some 4 := by native_decide

/-- **Property:** The transfer repro lowers to one `externalCallBind` on the `token` local. -/
theorem transfer_bind_lowers_to_token_call :
    externalCallSites transferBindStmt =
      [ExternalCallSite.callBind (.local "token") 0xa9059cbb
        [.local "recipient", .local "amount"] "ok"] := by native_decide

/-! ### ABI selector constant folding -/

/-- **Property:** Transfer calldata packing does not emit runtime `SHL` in bytecode. -/
theorem transfer_bind_bytecode_omits_shl :
    Bytecode.usesOp (bytecodeInstrs transferBindStmt) SHL = false := by native_decide

/-- **Property:** Transfer calldata packing stores the compile-time padded selector at offset 0. -/
theorem transfer_bind_bytecode_mstores_padded_selector :
    Bytecode.mstoresAt (bytecodeInstrs transferBindStmt) 0 (paddedSelector 0xa9059cbb) = true :=
  by native_decide

/-- **Property:** Transfer calldata packing does not emit runtime `shl` in Yul. -/
theorem transfer_bind_yul_omits_shl :
    YulSpec.usesBuiltin (yulStmts transferBindStmt) "shl" = false := by native_decide

/-- **Property:** Transfer calldata packing stores the compile-time padded selector at offset 0 in Yul. -/
theorem transfer_bind_yul_mstores_padded_selector :
    YulSpec.mstoresLitAt (yulStmts transferBindStmt) 0 (paddedSelector 0xa9059cbb) = true :=
  by native_decide

end Lsc.SafeExternalCallTest
