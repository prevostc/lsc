import LscV2.Compile.IR

namespace LscV2.Compile.IR

open LscV2 (Ident)

def freeVarsExpr : Expr → List Ident
  | .lit _ => []
  | .local name => [name]
  | .sload _ => []
  | .add a b => freeVarsExpr a ++ freeVarsExpr b
  | .sub a b => freeVarsExpr a ++ freeVarsExpr b
  | .lt a b => freeVarsExpr a ++ freeVarsExpr b
  | .eq a b => freeVarsExpr a ++ freeVarsExpr b
  | .isZero a => freeVarsExpr a

def freeVarsExprs : List Expr → List Ident :=
  List.foldl (init := []) fun acc e => acc ++ freeVarsExpr e

def freeVarsStmt : Stmt → List Ident
  | .skip => []
  | .seq s1 s2 => freeVarsStmt s1 ++ freeVarsStmt s2
  | .letBind name e => name :: freeVarsExpr e
  | .sstore _ e => freeVarsExpr e
  | .ifRevert cond => freeVarsExpr cond
  | .log0 _ => []
  | .log1 _ data => freeVarsExpr data
  | .revert0 => []

/-- Variables whose incoming `lookupLocal` value can affect evaluation. -/
def readVarsStmt : Stmt → List Ident
  | .skip => []
  | .seq s1 s2 => readVarsStmt s1 ++ readVarsStmt s2
  | .letBind _name e => freeVarsExpr e
  | .sstore _ e => freeVarsExpr e
  | .ifRevert cond => freeVarsExpr cond
  | .log0 _ => []
  | .log1 _ data => freeVarsExpr data
  | .revert0 => []

end LscV2.Compile.IR
