import Lsc.Lang.AST
import Lsc.Compile.IR
import Lsc.Compile.Abi
import Lsc.Compile.Lower
import EvmYul.Yul.Ast
import EvmYul.Operations
import EvmYul.UInt256

namespace Lsc.Compile

open EvmYul Yul
open Lsc.Compile.Abi

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
  | .calldataWord offset => yulCall "calldataload" [yulLit offset]
  | .mapSlot _ _ => yulLit 0
  | .dynSload slot => yulCall "sload" [irExprToYul slot]
  | .add a b => yulCall "add" [irExprToYul a, irExprToYul b]
  | .sub a b => yulCall "sub" [irExprToYul a, irExprToYul b]
  | .mul a b => yulCall "mul" [irExprToYul a, irExprToYul b]
  | .div a b => yulCall "div" [irExprToYul a, irExprToYul b]
  | .lt a b => yulCall "lt" [irExprToYul a, irExprToYul b]
  | .eq a b => yulCall "eq" [irExprToYul a, irExprToYul b]
  | .isZero a => yulCall "iszero" [irExprToYul a]

private def mapSlotToYul (base : Nat) (key : IR.Expr) : List Ast.Stmt × Ast.Expr :=
  let keyExpr := irExprToYul key
  ( [Ast.Stmt.ExprStmtCall (yulCall "mstore" [yulLit 0, keyExpr]),
     Ast.Stmt.ExprStmtCall (yulCall "mstore" [yulLit 32, yulLit base])],
    yulCall "keccak256" [yulLit 64, yulLit 0] )

private def revertEmpty : Ast.Stmt :=
  Ast.Stmt.ExprStmtCall (yulCall "revert" [yulLit 0, yulLit 0])

/-- ABI-pack `selector` and `args` into memory starting at offset 0. -/
private def packCalldataToYul (selector : Nat) (args : List IR.Expr) : List Ast.Stmt :=
  let selectorStore :=
    [Ast.Stmt.ExprStmtCall (yulCall "mstore" [yulLit 0, yulLit (paddedSelector selector)])]
  let rec go (i : Nat) (rest : List IR.Expr) : List Ast.Stmt :=
    match rest with
    | [] => []
    | arg :: tail =>
      Ast.Stmt.ExprStmtCall (yulCall "mstore" [yulLit (4 + 32 * i), irExprToYul arg]) :: go (i + 1) tail
  selectorStore ++ go 0 args

private def calldataSize (args : List IR.Expr) : Nat :=
  4 + 32 * args.length

private def checkReentrancyLockToYul : List Ast.Stmt :=
  let held := yulCall "tload" [yulLit IR.reentrancyLockSlot]
  [Ast.Stmt.Let ["lsc_lock_held"] (some held),
   Ast.Stmt.If (yulCall "iszero" [yulCall "iszero" [.Var "lsc_lock_held"]]) [revertEmpty]]

private def setReentrancyLockToYul (held : Bool) : List Ast.Stmt :=
  [Ast.Stmt.ExprStmtCall (yulCall "tstore" [yulLit IR.reentrancyLockSlot, yulLit (if held then 1 else 0)])]

/-- `IR.externalCall` — `CALL` with mandatory success check (optional ERC20 bool decode). -/
private def externalCallToYul (addr : IR.Expr) (selector : Nat) (args : List IR.Expr)
    (checkBoolReturn : Bool) : List Ast.Stmt :=
  let inSize := calldataSize args
  let callExpr := yulCall "call"
    [yulCall "gas" [], irExprToYul addr, yulLit 0, yulLit 0, yulLit inSize, yulLit 0, yulLit 32]
  let successCheck : Ast.Stmt :=
    Ast.Stmt.If (yulCall "iszero" [.Var "lsc_call_success"]) [revertEmpty]
  let boolReturnCheck : List Ast.Stmt :=
    if checkBoolReturn then
      [Ast.Stmt.If (yulCall "gt" [yulCall "returndatasize" [], yulLit 0])
        [Ast.Stmt.If (yulCall "iszero" [yulCall "mload" [yulLit 0]]) [revertEmpty]]]
    else []
  packCalldataToYul selector args ++
    [Ast.Stmt.Let ["lsc_call_success"] (some callExpr), successCheck] ++ boolReturnCheck

/-- `IR.externalCallBind` — `CALL` + bind first return word to `bindName`. -/
private def externalCallBindToYul (addr : IR.Expr) (selector : Nat) (args : List IR.Expr)
    (bindName : Ident) : List Ast.Stmt :=
  let inSize := calldataSize args
  let callExpr := yulCall "call"
    [yulCall "gas" [], irExprToYul addr, yulLit 0, yulLit 0, yulLit inSize, yulLit 0, yulLit 32]
  let successCheck : Ast.Stmt :=
    Ast.Stmt.If (yulCall "iszero" [.Var "lsc_call_success"]) [revertEmpty]
  packCalldataToYul selector args ++
    [Ast.Stmt.Let ["lsc_call_success"] (some callExpr), successCheck,
     Ast.Stmt.Let [bindName] (some (yulCall "mload" [yulLit 0]))]

/-- `IR.staticCall` — `STATICCALL` with mandatory success check; no reentrancy lock. -/
private def staticCallToYul (addr : IR.Expr) (selector : Nat) (args : List IR.Expr)
    (retWords : Nat) : List Ast.Stmt :=
  let inSize := calldataSize args
  let retSize := 32 * retWords
  let callExpr := yulCall "staticcall"
    [yulCall "gas" [], irExprToYul addr, yulLit 0, yulLit inSize, yulLit 0, yulLit retSize]
  let successCheck : Ast.Stmt :=
    Ast.Stmt.If (yulCall "iszero" [.Var "lsc_static_success"]) [revertEmpty]
  packCalldataToYul selector args ++
    [Ast.Stmt.Let ["lsc_static_success"] (some callExpr), successCheck]

/-- `IR.staticCallBind` — `STATICCALL` + bind first return word. -/
private def staticCallBindToYul (addr : IR.Expr) (selector : Nat) (args : List IR.Expr)
    (bindName : Ident) : List Ast.Stmt :=
  let inSize := calldataSize args
  let callExpr := yulCall "staticcall"
    [yulCall "gas" [], irExprToYul addr, yulLit 0, yulLit inSize, yulLit 0, yulLit 32]
  let successCheck : Ast.Stmt :=
    Ast.Stmt.If (yulCall "iszero" [.Var "lsc_static_success"]) [revertEmpty]
  packCalldataToYul selector args ++
    [Ast.Stmt.Let ["lsc_static_success"] (some callExpr), successCheck,
     Ast.Stmt.Let [bindName] (some (yulCall "mload" [yulLit 0]))]

partial def irStmtToYul (s : IR.Stmt) : List Ast.Stmt :=
  match s with
  | .skip => []
  | .seq s1 s2 => irStmtToYul s1 ++ irStmtToYul s2
  | .letBind name (.dynSload (.mapSlot base key)) =>
    let (setup, slotExpr) := mapSlotToYul base key
    setup ++ [Ast.Stmt.Let [name] (some (yulCall "sload" [slotExpr]))]
  | .letBind name e => [Ast.Stmt.Let [name] (some (irExprToYul e))]
  | .sstore slot e => [Ast.Stmt.ExprStmtCall (yulCall "sstore" [yulLit slot, irExprToYul e])]
  | .sstoreDyn (.mapSlot base key) val =>
    let (setup, slotExpr) := mapSlotToYul base key
    setup ++ [Ast.Stmt.ExprStmtCall (yulCall "sstore" [slotExpr, irExprToYul val])]
  | .sstoreDyn slot val =>
    [Ast.Stmt.ExprStmtCall (yulCall "sstore" [irExprToYul slot, irExprToYul val])]
  | .ifRevert cond =>
    [Ast.Stmt.If (irExprToYul cond) [revertEmpty]]
  | .log0 topic =>
    [Ast.Stmt.ExprStmtCall (yulCall "log1" [yulLit 0, yulLit 0, yulLit topic])]
  | .log1 topic data =>
    [Ast.Stmt.ExprStmtCall (yulCall "log1" [yulLit topic, irExprToYul data])]
  | .revert0 => [revertEmpty]
  | .ret (.dynSload (.mapSlot base key)) =>
    let (setup, slotExpr) := mapSlotToYul base key
    setup ++
      [Ast.Stmt.ExprStmtCall (yulCall "mstore" [yulLit 0, yulCall "sload" [slotExpr]]),
       Ast.Stmt.ExprStmtCall (yulCall "return" [yulLit 0, yulLit 32])]
  | .ret e =>
    [Ast.Stmt.ExprStmtCall (yulCall "mstore" [yulLit 0, irExprToYul e]),
     Ast.Stmt.ExprStmtCall (yulCall "return" [yulLit 0, yulLit 32])]
  | .checkReentrancyLock => checkReentrancyLockToYul
  | .setReentrancyLock held => setReentrancyLockToYul held
  | .externalCall addr selector args checkBoolReturn =>
    externalCallToYul addr selector args checkBoolReturn
  | .externalCallBind addr selector args bindName =>
    externalCallBindToYul addr selector args bindName
  | .staticCall addr selector args retWords =>
    staticCallToYul addr selector args retWords
  | .staticCallBind addr selector args bindName =>
    staticCallBindToYul addr selector args bindName

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
  | .Block stmts => String.intercalate "\n" (stmts.map fun s => renderStmt s indent)
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

def irStmtToYulString (s : IR.Stmt) : String :=
  renderFunction "lsc_body" (irStmtToYul s)

end Lsc.Compile
