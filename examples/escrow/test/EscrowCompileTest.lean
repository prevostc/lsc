import Escrow
import Lsc.Compile.Lower
import Lsc.Compile.Bytecode
import Lsc.Compile.Bytecode.CodegenInvariant
import Lsc.Compile.ExternalCallSpec
import Lsc.Compile.IR.Opt.Pipeline

open Lsc Lsc.Compile Escrow EvmYul Yul
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

/-- **Property:** `release` bytecode loads the CALL callee with `DUP2` after `GAS` (token, not amount). -/
example : gasDupDepthBeforeCall releaseInstrs = some 2 := by native_decide

end EscrowCompileTest
