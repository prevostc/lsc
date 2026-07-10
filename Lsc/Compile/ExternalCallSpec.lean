import Lsc.Compile.IR
import Lsc.Compile.Yul
import EvmYul.Yul.Ast

namespace Lsc.Compile

open EvmYul Yul
open Lsc.Compile.IR

/-! IR/Yul spec helpers for high-level compile tests.
Each `def` encodes one plain-English property from the test-suite plan. -/

inductive ExternalCallKind where
  | call
  | callBind
  | staticCall
  | staticBind
  deriving DecidableEq, Repr

structure ExternalCallSite where
  kind : ExternalCallKind
  addr : IR.Expr
  selector : Nat
  args : List IR.Expr
  bindName : Option Ident := none
  checkBoolReturn : Bool := false
  deriving DecidableEq, Repr

namespace ExternalCallSite

def call (addr : IR.Expr) (selector : Nat) (args : List IR.Expr) (checkBoolReturn : Bool) :
    ExternalCallSite :=
  { kind := .call, addr, selector, args, checkBoolReturn := checkBoolReturn }

def callBind (addr : IR.Expr) (selector : Nat) (args : List IR.Expr) (bindName : Ident) :
    ExternalCallSite :=
  { kind := .callBind, addr, selector, args, bindName := some bindName }

def staticCall (addr : IR.Expr) (selector : Nat) (args : List IR.Expr) : ExternalCallSite :=
  { kind := .staticCall, addr, selector, args }

end ExternalCallSite

partial def externalCallSites : IR.Stmt → List ExternalCallSite
  | .skip => []
  | .seq s1 s2 => externalCallSites s1 ++ externalCallSites s2
  | .letBind _ _ => []
  | .sstore _ _ => []
  | .sstoreDyn _ _ => []
  | .ifRevert _ => []
  | .log0 _ => []
  | .log1 _ _ => []
  | .revert0 => []
  | .ret _ => []
  | .checkReentrancyLock => []
  | .setReentrancyLock _ => []
  | .externalCall addr selector args checkBoolReturn =>
    [ExternalCallSite.call addr selector args checkBoolReturn]
  | .externalCallBind addr selector args bindName =>
    [ExternalCallSite.callBind addr selector args bindName]
  | .staticCall addr selector args _ =>
    [ExternalCallSite.staticCall addr selector args]
  | .staticCallBind addr selector args bindName =>
    [{ kind := .staticBind, addr, selector, args, bindName := some bindName }]

namespace YulSpec

private partial def exprCalls (e : Ast.Expr) : List String :=
  match e with
  | .Call (.inr name) args => name :: args.flatMap exprCalls
  | .Call (.inl _) args => args.flatMap exprCalls
  | _ => []

mutual
  private partial def stmtCalls (s : Ast.Stmt) : List String :=
    match s with
    | .Let _ (some e) => exprCalls e
    | .ExprStmtCall e => exprCalls e
    | .If cond body => exprCalls cond ++ stmtsCalls body
    | .Block body => stmtsCalls body
    | _ => []

  private partial def stmtsCalls (stmts : List Ast.Stmt) : List String :=
    stmts.flatMap stmtCalls
end

private def hasCallNamed (stmts : List Ast.Stmt) (name : String) : Bool :=
  (stmtsCalls stmts).any (· == name)

private partial def stmtsAny (stmts : List Ast.Stmt) (p : Ast.Stmt → Bool) : Bool :=
  stmts.any fun s =>
    p s || match s with
    | .If _ body => stmtsAny body p
    | .Block body => stmtsAny body p
    | _ => false

private def isRevertStmt (s : Ast.Stmt) : Bool :=
  match s with
  | .ExprStmtCall (.Call (.inr "revert") _) => true
  | _ => false

private partial def exprHas (e : Ast.Expr) (p : Ast.Expr → Bool) : Bool :=
  p e || match e with
  | .Call _ args => args.any (exprHas · p)
  | _ => false

private partial def exprReadsSloadSlot (e : Ast.Expr) (slot : Nat) : Bool :=
  match e with
  | .Call (.inr "sload") [.Lit u] => u.toNat == slot
  | .Call _ args => args.any (exprReadsSloadSlot · slot)
  | _ => false

private partial def stmtReadsSloadSlot (s : Ast.Stmt) (slot : Nat) : Bool :=
  match s with
  | .Let _ (some e) => exprReadsSloadSlot e slot
  | .ExprStmtCall e => exprReadsSloadSlot e slot
  | .If _ body => body.any (stmtReadsSloadSlot · slot)
  | .Block body => body.any (stmtReadsSloadSlot · slot)
  | _ => false

private partial def exprWritesSstoreSlot (e : Ast.Expr) (slot : Nat) : Bool :=
  match e with
  | .Call (.inr "sstore") [.Lit u, _] => u.toNat == slot
  | .Call _ args => args.any (exprWritesSstoreSlot · slot)
  | _ => false

private partial def stmtWritesSstoreSlot (s : Ast.Stmt) (slot : Nat) : Bool :=
  match s with
  | .ExprStmtCall e => exprWritesSstoreSlot e slot
  | .If _ body => body.any (stmtWritesSstoreSlot · slot)
  | .Block body => body.any (stmtWritesSstoreSlot · slot)
  | _ => false

/-- **Property:** generated Yul reverts when the EVM `call` opcode reports failure. -/
def revertsOnCallFailure (stmts : List Ast.Stmt) : Bool :=
  stmtsAny stmts fun s =>
    match s with
    | .If (Ast.Expr.Call (.inr "iszero") [.Var "lsc_call_success"]) body =>
        body.any isRevertStmt
    | _ => false

/-- **Property:** generated Yul reverts when the EVM `staticcall` opcode reports failure. -/
def revertsOnStaticCallFailure (stmts : List Ast.Stmt) : Bool :=
  stmtsAny stmts fun s =>
    match s with
    | .If (Ast.Expr.Call (.inr "iszero") [.Var "lsc_static_success"]) body =>
        body.any isRevertStmt
    | _ => false

/-- **Property:** generated Yul includes the legacy ERC20 returndata bool-decode guard. -/
def hasReturndataBoolGuard (stmts : List Ast.Stmt) : Bool :=
  hasCallNamed stmts "returndatasize"

/-- **Property:** generated Yul uses EIP-1153 transient storage for reentrancy locking. -/
def usesTransientLock (stmts : List Ast.Stmt) : Bool :=
  hasCallNamed stmts "tload" && hasCallNamed stmts "tstore"

/-- **Property:** generated Yul binds `bindName` from `mload(0)` after a call. -/
def bindsReturnWord (stmts : List Ast.Stmt) (bindName : String) : Bool :=
  stmtsAny stmts fun s =>
    match s with
    | .Let [name] (some (Ast.Expr.Call (.inr "mload") _)) => name == bindName
    | _ => false

/-- **Property:** generated Yul issues a real `call` opcode. -/
def emitsCall (stmts : List Ast.Stmt) : Bool :=
  hasCallNamed stmts "call"

/-- **Property:** generated Yul issues a real `staticcall` opcode. -/
def emitsStaticCall (stmts : List Ast.Stmt) : Bool :=
  hasCallNamed stmts "staticcall"

/-- **Property:** generated Yul reads a storage slot via `sload`. -/
def readsStorageSlot (stmts : List Ast.Stmt) (slot : Nat) : Bool :=
  stmts.any (stmtReadsSloadSlot · slot)

/-- **Property:** generated Yul writes a storage slot via `sstore`. -/
def writesStorageSlot (stmts : List Ast.Stmt) (slot : Nat) : Bool :=
  stmts.any (stmtWritesSstoreSlot · slot)

/-- **Property:** generated Yul emits an event log via `log1`. -/
def emitsLog1 (stmts : List Ast.Stmt) : Bool :=
  hasCallNamed stmts "log1"

/-- **Property:** generated Yul contains a revert path. -/
def hasRevertPath (stmts : List Ast.Stmt) : Bool :=
  hasCallNamed stmts "revert"

/-- **Property:** generated Yul calls builtin `name` (e.g. `shl`). -/
def usesBuiltin (stmts : List Ast.Stmt) (name : String) : Bool :=
  hasCallNamed stmts name

private partial def exprMstoresLitAt (e : Ast.Expr) (offset val : Nat) : Bool :=
  match e with
  | .Call (.inr "mstore") [.Lit off, .Lit v] => off.toNat == offset && v.toNat == val
  | .Call _ args => args.any (exprMstoresLitAt · offset val)
  | _ => false

private partial def stmtMstoresLitAt (s : Ast.Stmt) (offset val : Nat) : Bool :=
  match s with
  | .ExprStmtCall e => exprMstoresLitAt e offset val
  | .If _ body => body.any (stmtMstoresLitAt · offset val)
  | .Block body => body.any (stmtMstoresLitAt · offset val)
  | _ => false

/-- **Property:** generated Yul stores literal `val` at memory offset `offset`. -/
def mstoresLitAt (stmts : List Ast.Stmt) (offset val : Nat) : Bool :=
  stmts.any (stmtMstoresLitAt · offset val)

/-- **Property:** generated Yul `call` targets a named local callee address. -/
def callTargetsLocal (stmts : List Ast.Stmt) (name : String) : Bool :=
  stmtsAny stmts fun s =>
    match s with
    | .Let ["lsc_call_success"] (some (Ast.Expr.Call (.inr "call")
        [.Call (.inr "gas") _, .Var v, _, _, _, _, _])) => v == name
    | _ => false

end YulSpec

end Lsc.Compile
