import LscV2.Compile.Yul

open LscV2 LscV2.Compile

/-- Same shape as `Counter.incrementAst`. -/
def incrementAst : Stmt :=
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

#guard incrementYul.contains "sload(0)"
#guard incrementYul.contains "sstore(0"
#guard incrementYul.contains "log1("
#guard incrementYul.contains "revert(0, 0)"

#eval IO.println incrementYul
