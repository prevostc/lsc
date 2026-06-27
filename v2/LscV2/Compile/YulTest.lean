import LscV2.Compile.Yul
import EvmYul.Yul.Ast

open LscV2 LscV2.Compile
open EvmYul Yul

/-- Same shape as `Counter.incrementAst`. -/
def incrementAst : LscV2.Stmt :=
  Stmt.seq
    (Stmt.letBind "n" ⟨Ty.wei,
      Expr.weiAddCheckedNat (Expr.storageGet (t := .wei) "number") 1⟩)
    (Stmt.seq
      (Stmt.storageSet "number" ⟨Ty.wei, Expr.var (t := .wei) "n"⟩)
      (Stmt.emit "Incremented" [⟨Ty.wei, Expr.var (t := .wei) "n"⟩]))

/-- keccak256("Incremented(uint256)") -/
def incrementedTopic : Nat := 0x20d8a6f5a693f9d1d627a598e8820f7a55ee74c183aa8f1a30e8d4e8dd9a8d84

def counterConfig : Config where
  storage := StorageLayout.fromList [("number", 0)]
  events := { topic0 := fun
    | "Incremented" => some incrementedTopic
    | _ => none }

def incrementYul : String :=
  incrementAst.toYul! counterConfig

def incrementFn : Ast.FunctionDefinition :=
  incrementAst.toYulAst! counterConfig

#guard incrementYul.contains "sload(0x"
#guard incrementYul.contains "sstore(0x"
#guard incrementYul.contains "log1("
#guard incrementYul.contains "revert(0x"

#guard incrementFn.body.length > 0
#guard match incrementFn.body[1]! with
  | Ast.Stmt.Let ["n"] (some _) => true
  | _ => false

#guard (incrementAst.toYulContract counterConfig "increment").isOk

#eval IO.println incrementYul
