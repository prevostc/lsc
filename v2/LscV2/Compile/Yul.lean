import LscV2.Lang.AST
import LscV2.Compile.IR
import LscV2.Compile.Lower
import EvmYul.Yul.Ast
import EvmYul.Operations
import EvmYul.UInt256

namespace LscV2.Compile

open EvmYul Yul

private def hex256 (n : Nat) : String :=
  "0x" ++ (BitVec.ofNat 256 n).toHex

private def yulLit (n : Nat) : Ast.Expr := .Lit (UInt256.ofNat n)

private def yulCall (name : String) (args : List Ast.Expr) : Ast.Expr :=
  .Call (.inr name) args

private def irExprToYul (e : IR.Expr) : Ast.Expr :=
  match e with
  | .lit n => yulLit n
  | .local "caller" => .Call (.inl (Operation.CALLER (τ := .Yul))) []
  | .local name => .Var name
  | .sload slot => yulCall "sload" [yulLit slot]
  | .add a b => yulCall "add" [irExprToYul a, irExprToYul b]
  | .sub a b => yulCall "sub" [irExprToYul a, irExprToYul b]
  | .lt a b => yulCall "lt" [irExprToYul a, irExprToYul b]
  | .eq a b => yulCall "eq" [irExprToYul a, irExprToYul b]
  | .isZero a => yulCall "iszero" [irExprToYul a]

private partial def irStmtToYul (s : IR.Stmt) : List Ast.Stmt :=
  match s with
  | .skip => []
  | .seq s1 s2 => irStmtToYul s1 ++ irStmtToYul s2
  | .letBind name e => [Ast.Stmt.Let [name] (some (irExprToYul e))]
  | .sstore slot e => [Ast.Stmt.ExprStmtCall (yulCall "sstore" [yulLit slot, irExprToYul e])]
  | .ifRevert cond =>
    [Ast.Stmt.If (irExprToYul cond) [Ast.Stmt.ExprStmtCall (yulCall "revert" [yulLit 0, yulLit 0])]]
  | .log0 topic =>
    [Ast.Stmt.ExprStmtCall (yulCall "log1" [yulLit 0, yulLit 0, yulLit topic])]
  | .log1 topic data =>
    [Ast.Stmt.ExprStmtCall (yulCall "log1" [yulLit topic, irExprToYul data])]
  | .revert0 => [Ast.Stmt.ExprStmtCall (yulCall "revert" [yulLit 0, yulLit 0])]

private def renderExpr (e : Ast.Expr) : String :=
  match e with
  | .Lit u => hex256 u.toNat
  | .Var name => name
  | .Call (.inl op) args =>
    s!"{Ast.stringOfPrimOp op}({String.intercalate ", " (args.map renderExpr)})"
  | .Call (.inr name) args =>
    s!"{name}({String.intercalate ", " (args.map renderExpr)})"

private partial def renderStmt (s : Ast.Stmt) (indent : Nat) : String :=
  let pad := String.ofList (List.replicate indent ' ')
  match s with
  | .Let [name] (some expr) => s!"{pad}let {name} := {renderExpr expr}"
  | .ExprStmtCall expr => s!"{pad}{renderExpr expr}"
  | .If cond body =>
    let inner := String.intercalate "\n" (body.map fun b => renderStmt b (indent + 4))
    s!"{pad}if {renderExpr cond} " ++ "{\n" ++ inner ++ "\n" ++ pad ++ "}"
  | .Block stmts => String.intercalate "\n" (stmts.map fun b => renderStmt b indent)
  | _ => s!"{pad}// unsupported stmt"

def renderFunction (name : Ident) (body : List Ast.Stmt) : String :=
  let inner := String.intercalate "\n" (body.map fun s => renderStmt s 4)
  "function " ++ name ++ "() {\n" ++ inner ++ "\n}"

def irToYulContract (name : Ident) (body : IR.Stmt) : Ast.YulContract :=
  { dispatcher := Ast.Stmt.Block []
  , functions := (∅ : Finmap (fun (_ : Ast.YulFunctionName) ↦ Ast.FunctionDefinition)).insert name
      (Ast.FunctionDefinition.Def [] [] (irStmtToYul body)) }

def stmtToYulAst (cfg : Config) (s : LscV2.Stmt) : Except String Ast.FunctionDefinition :=
  match Lower.stmt cfg s with
  | .ok ir => .ok (Ast.FunctionDefinition.Def [] [] (irStmtToYul ir))
  | .error e => .error e

def stmtToYul (cfg : Config) (s : LscV2.Stmt) : Except String String :=
  match stmtToYulAst cfg s with
  | .ok fn => .ok (renderFunction "lsc_body" fn.body)
  | .error e => .error e

end LscV2.Compile
