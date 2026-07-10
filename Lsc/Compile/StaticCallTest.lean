import Lsc.Compile.Yul
import Lsc.Compile.ExternalCallSpec

/-!
High-level properties for `IR.staticCall` lowering — read-only cross-contract calls. -/

open Lsc Lsc.Compile Lsc.Compile.IR

namespace Lsc.StaticCallTest

def sampleStaticCall : IR.Stmt :=
  .staticCall (.local "target") 0 [] 0 0

def sampleReadTxBody : IR.Stmt :=
  .seq (.staticCall (.sload 1) 0 [] 0 0) .skip

private def yulStmts (s : IR.Stmt) : List EvmYul.Yul.Ast.Stmt :=
  irStmtToYul s

/-- **Property:** A `staticCall` issues a real EVM `staticcall` opcode in generated Yul. -/
theorem staticCall_emits_opcode :
    YulSpec.emitsStaticCall (yulStmts sampleStaticCall) = true := by native_decide

/-- **Property:** A `staticCall` reverts when the underlying EVM staticcall returns failure. -/
theorem staticCall_reverts_on_failure :
    YulSpec.revertsOnStaticCallFailure (yulStmts sampleStaticCall) = true := by native_decide

/-- **Property:** A read-only `staticCall` does not touch the transient reentrancy lock. -/
theorem staticCall_has_no_transient_lock :
    YulSpec.usesTransientLock (yulStmts sampleStaticCall) = false := by native_decide

/-- **Property:** A tx body using only `staticCall` for reads does not acquire a reentrancy lock. -/
theorem read_tx_body_has_staticcall_without_lock :
    YulSpec.emitsStaticCall (yulStmts sampleReadTxBody) = true ∧
      YulSpec.usesTransientLock (yulStmts sampleReadTxBody) = false := by native_decide

end Lsc.StaticCallTest
