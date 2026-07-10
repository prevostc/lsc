import Escrow
import Lsc.Compile.Lower
import Lsc.Compile.Bytecode
import Lsc.Compile.Bytecode.CodegenInvariant
import Lsc.Compile.ExternalCallSpec
import Lsc.Compile.IR.Opt.Pipeline
import Lsc.Selectors
import Lsc.Tools.AbiJson

open Lsc Lsc.Compile Escrow EvmYul Yul Lsc.Tools
open Lsc.Compile.Bytecode

namespace EscrowCompileTest

example : Escrow.contractDef.functions.length = 1 := by native_decide

private def releaseFn : FunctionDef :=
  match Escrow.contractDef.functions[0]? with
  | some fn => fn
  | none =>
    { name := "release", kind := .external, params := [], retTy := .unit, body := .skip }

private def releaseIr : IR.Stmt :=
  match Lower.function Escrow.config releaseFn with
  | .ok ir => IR.Opt.optimizeStmt ir
  | .error _ => .skip

private def releaseYulStmts : List Ast.Stmt :=
  irStmtToYul releaseIr

private def releaseInstrs : List Instr :=
  match Bytecode.Contract.functionInstrs Escrow.config releaseFn with
  | .ok instrs => instrs
  | .error _ => []

/-- **Property:** `release` lowers to exactly one IERC20 `transfer` on the escrow token address. -/
theorem release_lowers_to_token_transfer :
    externalCallSites releaseIr =
      [ExternalCallSite.callBind (.local "token") 0xa9059cbb
        [.local "recipient", .local "amount"] "ok"] := by native_decide

/-- **Property:** `release` binds the IERC20 transfer return word and checks it in generated Yul. -/
theorem release_yul_binds_and_checks_ok :
    YulSpec.bindsReturnWord releaseYulStmts "ok" = true := by native_decide

/-- **Property:** `release` inlines SafeERC20 — exactly one external call site. -/
theorem release_inlines_single_transfer_call :
    (externalCallSites releaseIr).length = 1 := by native_decide

/-- **Property:** `release` generated Yul issues a real EVM `call` opcode. -/
theorem release_yul_emits_call :
    YulSpec.emitsCall releaseYulStmts = true := by native_decide

/-- **Property:** `release` uses transient storage reentrancy lock. -/
theorem release_yul_uses_transient_lock :
    YulSpec.usesTransientLock releaseYulStmts = true := by native_decide

/-- **Property:** `release` bytecode `CALL` targets the escrow token (`σ.token` → slot 2). -/
theorem release_call_targets_token :
    codegenCallUsesAddrInStmt releaseIr releaseInstrs (.local "token") = true := by native_decide

/-- **Property:** `release` bytecode reloads token from storage slot 2 after `GAS` before `CALL`. -/
example : gasSloadSlotBeforeCall releaseInstrs 2 = true := by native_decide

/-- **Property:** `release` bytecode loads the CALL callee after `GAS` (via `SLOAD` or `DUP`). -/
example : gasLoadsCalleeBeforeCall releaseInstrs 2 = true := by native_decide

/-- **Property:** `release` generated Yul uses custom-error reverts (`revert(0, 4)`). -/
theorem release_yul_uses_custom_error_reverts :
    YulSpec.usesCustomErrorRevert releaseYulStmts = true := by native_decide

/-- **Property:** Escrow ABI JSON includes declared custom errors. -/
example : contractAbiJson Escrow.contractDef |>.contains "\"type\":\"error\"" := by native_decide

example :
    contractAbiJson Escrow.contractDef |>.contains
      ("\"name\":\"" ++ "NotOwner" ++ "\"") := by native_decide

example :
    (computeErrorSelector "ExternalCallFailed" []).toNat =
      (Escrow.config.errors.errorSelector "ExternalCallFailed").getD 0 := by native_decide

end EscrowCompileTest
