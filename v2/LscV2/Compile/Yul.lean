import LscV2.AST
import LscV2.Compile.IR
import LscV2.Compile.Lower

namespace LscV2.Compile

private def hex256 (n : Nat) : String :=
  "0x" ++ (BitVec.ofNat 256 n).toHex

private def renderExpr (e : IR.Expr) : String :=
  match e with
  | .lit n => hex256 n
  | .local name => name
  | .sload slot => s!"sload({slot})"
  | .add a b => s!"add({renderExpr a}, {renderExpr b})"
  | .lt a b => s!"lt({renderExpr a}, {renderExpr b})"

private partial def renderStmtInner (s : IR.Stmt) (indent : Nat) : String :=
  let pad := String.ofList (List.replicate indent ' ')
  match s with
  | .skip => ""
  | .seq s1 s2 =>
    let a := renderStmtInner s1 indent
    let b := renderStmtInner s2 indent
    if a.isEmpty then b
    else if b.isEmpty then a
    else a ++ "\n" ++ b
  | .letBind name e => s!"{pad}let {name} := {renderExpr e}"
  | .sstore slot e => s!"{pad}sstore({slot}, {renderExpr e})"
  | .ifRevert cond => s!"{pad}if {renderExpr cond} " ++ "{ revert(0, 0) }"
  | .log1 topic data => s!"{pad}log1({hex256 topic}, {renderExpr data})"
  | .revert0 => s!"{pad}revert(0, 0)"

def renderStmt (s : IR.Stmt) : String :=
  renderStmtInner s 4

def renderFunction (name : Ident) (body : IR.Stmt) : String :=
  "function " ++ name ++ "() {\n" ++ renderStmt body ++ "\n}"

def stmtToYul (cfg : Config) (s : LscV2.Stmt) : Except String String :=
  match Lower.stmt cfg s with
  | .ok ir => .ok (renderFunction "lsc_body" ir)
  | .error e => .error e

def stmtToYul! (cfg : Config) (s : LscV2.Stmt) : String :=
  match stmtToYul cfg s with
  | .ok yul => yul
  | .error e => s!"// lowering error: {e}"

end LscV2.Compile

namespace LscV2

namespace Stmt

def toYul (s : Stmt) (cfg : Compile.Config) : Except String String :=
  Compile.stmtToYul cfg s

def toYul! (s : Stmt) (cfg : Compile.Config) : String :=
  Compile.stmtToYul! cfg s

end Stmt

end LscV2
