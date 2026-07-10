import Lsc.Compile.Yul
import Lsc.Compile.ExternalCallSpec
import Lsc.TestFixtures.SyntaxSmoke

open Lsc Lsc.Compile Lsc.TestFixtures
open EvmYul Yul

def incrementedTopic : Nat := 0x20d8a6f5a693f9d1d627a598e8820f7a55ee74c183aa8f1a30e8d4e8dd9a8d84

def counterConfig : Config where
  storage := StorageLayout.fromList [("number", 0), ("paused", 1), ("owner", 2)]
  events := { topic0 := fun
    | "Incremented" => some incrementedTopic
    | _ => none }
  errors := { errorSelector := fun
    | "Overflow" => some 0
    | _ => none }

namespace Lsc.YulTest

/-- Lower increment body only (Yul slice test). -/
def incrementBodyAst : Stmt :=
  Stmt.seq incrementLet (Stmt.seq incrementSet incrementEmit)

private def incrementYulStmts : List Ast.Stmt :=
  match Compile.stmtToYulAst counterConfig incrementBodyAst with
  | .ok fn => fn.body
  | .error e => panic! e

/-- **Property:** Increment body reads the `number` storage field (slot 0). -/
theorem increment_body_reads_number :
    YulSpec.readsStorageSlot incrementYulStmts 0 = true := by native_decide

/-- **Property:** Increment body writes the `number` storage field (slot 0). -/
theorem increment_body_writes_number :
    YulSpec.writesStorageSlot incrementYulStmts 0 = true := by native_decide

/-- **Property:** Increment body emits an event log. -/
theorem increment_body_emits_event :
    YulSpec.emitsLog1 incrementYulStmts = true := by native_decide

/-- **Property:** Increment body contains a revert path (failed require). -/
theorem increment_body_has_revert_path :
    YulSpec.hasRevertPath incrementYulStmts = true := by native_decide

/-- **Property:** Increment body lowers to non-empty Yul. -/
theorem increment_body_nonempty :
    incrementYulStmts.length > 0 := by native_decide

end Lsc.YulTest
