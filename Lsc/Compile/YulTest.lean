import Lsc.Compile.Yul
import Lsc.TestFixtures.SyntaxSmoke
import EvmYul.Yul.Ast

open Lsc Lsc.Compile Lsc.TestFixtures
open EvmYul Yul

def incrementedTopic : Nat := 0x20d8a6f5a693f9d1d627a598e8820f7a55ee74c183aa8f1a30e8d4e8dd9a8d84

def counterConfig : Config where
  storage := StorageLayout.fromList [("number", 0), ("paused", 1), ("owner", 2)]
  events := { topic0 := fun
    | "Incremented" => some incrementedTopic
    | _ => none }

namespace Lsc.YulTest

private def stmtToYul! (cfg : Config) (s : Stmt) : String :=
  match Compile.stmtToYul cfg s with
  | .ok yul => yul
  | .error e => panic! e

private def stmtToYulAst! (cfg : Config) (s : Stmt) : Ast.FunctionDefinition :=
  match Compile.stmtToYulAst cfg s with
  | .ok fn => fn
  | .error e => panic! e

/-- Lower increment body only (Yul slice test). -/
def incrementBodyAst : Stmt :=
  Stmt.seq incrementLet (Stmt.seq incrementSet incrementEmit)

def incrementYul : String :=
  stmtToYul! counterConfig incrementBodyAst

def incrementFn : Ast.FunctionDefinition :=
  stmtToYulAst! counterConfig incrementBodyAst

theorem increment_yul_contains_sload : incrementYul.contains "sload(0x" = true := by native_decide

theorem increment_yul_contains_sstore : incrementYul.contains "sstore(0x" = true := by native_decide

theorem increment_yul_contains_log1 : incrementYul.contains "log1(" = true := by native_decide

theorem increment_yul_contains_revert : incrementYul.contains "revert(0x" = true := by native_decide

theorem increment_fn_body_nonempty : incrementFn.body.length > 0 := by native_decide

#eval IO.println incrementYul

end Lsc.YulTest
