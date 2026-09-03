import Lsc.Compile.IR

namespace Lsc.Compile.IR

open Lsc (Ident)

def freeVarsExpr : Expr → List Ident
  | .lit _ => []
  | .local name => [name]
  | .sload _ => []
  | .mapSlot _ key => freeVarsExpr key
  | .mapSlot2 _ key1 key2 => freeVarsExpr key1 ++ freeVarsExpr key2
  | .dynSload slot => freeVarsExpr slot
  | .calldataWord _ => []
  | .add a b => freeVarsExpr a ++ freeVarsExpr b
  | .sub a b => freeVarsExpr a ++ freeVarsExpr b
  | .mul a b => freeVarsExpr a ++ freeVarsExpr b
  | .div a b => freeVarsExpr a ++ freeVarsExpr b
  | .lt a b => freeVarsExpr a ++ freeVarsExpr b
  | .eq a b => freeVarsExpr a ++ freeVarsExpr b
  | .isZero a => freeVarsExpr a
  | .gt a b => freeVarsExpr a ++ freeVarsExpr b
  | .shr amount val => freeVarsExpr amount ++ freeVarsExpr val
  | .xor a b => freeVarsExpr a ++ freeVarsExpr b

def freeVarsExprs : List Expr → List Ident :=
  List.foldl (init := []) fun acc e => acc ++ freeVarsExpr e

def freeVarsStmt : Stmt → List Ident
  | .skip => []
  | .seq s1 s2 => freeVarsStmt s1 ++ freeVarsStmt s2
  | .letBind name e => name :: freeVarsExpr e
  | .sstore _ e => freeVarsExpr e
  | .sstoreDyn slot val => freeVarsExpr slot ++ freeVarsExpr val
  | .ifRevertSelector cond _ => freeVarsExpr cond
  | .log _ datas => freeVarsExprs datas
  | .revertSelector _ => []
  | .ret e => freeVarsExpr e
  | .checkReentrancyLock _ => []
  | .setReentrancyLock _ => []
  | .externalCall addr _ args _ _ => freeVarsExpr addr ++ freeVarsExprs args
  | .externalCallBind addr _ args bindName _ => freeVarsExpr addr ++ freeVarsExprs args ++ [bindName]
  | .staticCall addr _ args _ _ => freeVarsExpr addr ++ freeVarsExprs args
  | .staticCallBind addr _ args bindName _ => freeVarsExpr addr ++ freeVarsExprs args ++ [bindName]

/-- Variables whose incoming `lookupLocal` value can affect evaluation. -/
def readVarsStmt : Stmt → List Ident
  | .skip => []
  | .seq s1 s2 => readVarsStmt s1 ++ readVarsStmt s2
  | .letBind _name e => freeVarsExpr e
  | .sstore _ e => freeVarsExpr e
  | .sstoreDyn slot val => freeVarsExpr slot ++ freeVarsExpr val
  | .ifRevertSelector cond _ => freeVarsExpr cond
  | .log _ datas => freeVarsExprs datas
  | .revertSelector _ => []
  | .ret e => freeVarsExpr e
  | .checkReentrancyLock _ => []
  | .setReentrancyLock _ => []
  | .externalCall addr _ args _ _ => freeVarsExpr addr ++ freeVarsExprs args
  | .externalCallBind addr _ args bindName _ => freeVarsExpr addr ++ freeVarsExprs args ++ [bindName]
  | .staticCall addr _ args _ _ => freeVarsExpr addr ++ freeVarsExprs args
  | .staticCallBind addr _ args bindName _ => freeVarsExpr addr ++ freeVarsExprs args ++ [bindName]

end Lsc.Compile.IR
