import Lsc.Lang.AST
import Lsc.Compile.IR
import Lsc.Compile.Lower
import EvmYul.Yul.Ast
import EvmYul.Operations
import EvmYul.UInt256

namespace Lsc.Compile

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
  | .mul a b => yulCall "mul" [irExprToYul a, irExprToYul b]
  | .div a b => yulCall "div" [irExprToYul a, irExprToYul b]
  | .lt a b => yulCall "lt" [irExprToYul a, irExprToYul b]
  | .eq a b => yulCall "eq" [irExprToYul a, irExprToYul b]
  | .isZero a => yulCall "iszero" [irExprToYul a]

/-- Lowering for `IR.Stmt.safeExternalCall` (see that constructor's docstring for the full
rationale) — the one and only Yul shape this node can ever produce, with **no parameter to skip
either check**:

```
let success := call(gas(), addr, 0, inOffset, inSize, 0, 32)
if iszero(success) { revert(0, 0) }
-- only emitted when checkBoolReturn is true:
if gt(returndatasize(), 0) {
  if iszero(mload(0)) { revert(0, 0) }
}
```

`call`'s own `retOffset`/`retSize` (`0`/`32`) already ask the EVM to copy up to the first 32
bytes of return data into memory at offset `0` as part of the `CALL` itself — no separate
`returndatacopy` is needed for the single-word `bool` this checks. A callee returning zero-length
return data (`returndatasize() == 0` — real-world tokens that omit `transfer`'s `bool` return
entirely) skips the `mload`-based check altogether and is treated as success, matching
`SafeERC20.safeTransfer`'s own handling of that case. -/
private def safeExternalCallToYul (addr inOffset inSize : IR.Expr) (checkBoolReturn : Bool) :
    List Ast.Stmt :=
  let callExpr := yulCall "call"
    [yulCall "gas" [], irExprToYul addr, yulLit 0, irExprToYul inOffset, irExprToYul inSize,
     yulLit 0, yulLit 32]
  let successCheck : Ast.Stmt :=
    Ast.Stmt.If (yulCall "iszero" [.Var "lsc_call_success"])
      [Ast.Stmt.ExprStmtCall (yulCall "revert" [yulLit 0, yulLit 0])]
  let boolReturnCheck : List Ast.Stmt :=
    if checkBoolReturn then
      [Ast.Stmt.If (yulCall "gt" [yulCall "returndatasize" [], yulLit 0])
        [Ast.Stmt.If (yulCall "iszero" [yulCall "mload" [yulLit 0]])
          [Ast.Stmt.ExprStmtCall (yulCall "revert" [yulLit 0, yulLit 0])]]]
    else []
  [Ast.Stmt.Let ["lsc_call_success"] (some callExpr), successCheck] ++ boolReturnCheck

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
  | .ret e =>
    [Ast.Stmt.ExprStmtCall (yulCall "mstore" [yulLit 0, irExprToYul e]),
     Ast.Stmt.ExprStmtCall (yulCall "return" [yulLit 0, yulLit 32])]
  | .safeExternalCall addr inOffset inSize checkBoolReturn => safeExternalCallToYul addr inOffset inSize checkBoolReturn

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

def stmtToYulAst (cfg : Config) (s : Lsc.Stmt) : Except String Ast.FunctionDefinition :=
  match Lower.stmt cfg s with
  | .ok ir => .ok (Ast.FunctionDefinition.Def [] [] (irStmtToYul ir))
  | .error e => .error e

def stmtToYul (cfg : Config) (s : Lsc.Stmt) : Except String String :=
  match stmtToYulAst cfg s with
  | .ok fn => .ok (renderFunction "lsc_body" fn.body)
  | .error e => .error e

/-- Render a raw `IR.Stmt` directly to a Yul function body string, bypassing `Lower.lean`
entirely — needed for `IR.Stmt.safeExternalCall` specifically, since nothing lowers an
`Lsc.Stmt` to it yet (see that constructor's docstring, `IR.lean`); this is the one way to
exercise/test its Yul codegen (`safeExternalCallToYul`) today. -/
def irStmtToYulString (s : IR.Stmt) : String :=
  renderFunction "lsc_body" (irStmtToYul s)

end Lsc.Compile
