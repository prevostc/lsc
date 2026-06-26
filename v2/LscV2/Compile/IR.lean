import LscV2.Types

namespace LscV2.Compile.IR

/-- Flat IR: storage slots resolved, linear types erased. -/
inductive Expr where
  | lit : Nat → Expr
  | local : Ident → Expr
  | sload : Nat → Expr
  | add : Expr → Expr → Expr
  | lt : Expr → Expr → Expr
  deriving Repr

inductive Stmt where
  | skip : Stmt
  | seq : Stmt → Stmt → Stmt
  | letBind : Ident → Expr → Stmt
  | sstore : Nat → Expr → Stmt
  | ifRevert : Expr → Stmt
  | log1 : Nat → Expr → Stmt
  | revert0 : Stmt
  deriving Repr

end LscV2.Compile.IR
