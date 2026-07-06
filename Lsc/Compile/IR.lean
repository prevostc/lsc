import Lsc.Types

namespace Lsc.Compile.IR

/-- Flat IR: storage slots resolved, linear types erased. -/
inductive Expr where
  | lit : Nat → Expr
  | local : Ident → Expr
  | sload : Nat → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | div : Expr → Expr → Expr
  | lt : Expr → Expr → Expr
  | eq : Expr → Expr → Expr
  | isZero : Expr → Expr
  deriving Repr

inductive Stmt where
  | skip : Stmt
  | seq : Stmt → Stmt → Stmt
  | letBind : Ident → Expr → Stmt
  | sstore : Nat → Expr → Stmt
  | ifRevert : Expr → Stmt
  | log0 : Nat → Stmt
  | log1 : Nat → Expr → Stmt
  | revert0 : Stmt
  deriving Repr

end Lsc.Compile.IR
