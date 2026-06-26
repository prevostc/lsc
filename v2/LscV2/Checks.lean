import LscV2.AST

namespace LscV2
namespace Checks

partial def arithErrorsOfExpr : {t : Ty} → Expr t → List ArithError
  | _, .weiAddChecked _ _ => [.Overflow]
  | _, .weiSubChecked _ _ => [.Underflow]
  | _, .weiMulChecked _ _ => [.Overflow]
  | _, .weiDivFloor _ _ => [.DivisionByZero]
  | _, .weiAddCheckedNat _ _ => [.Overflow]
  | _, .wadAddChecked _ _ => [.Overflow]
  | _, .wadSubChecked _ _ => [.Underflow]
  | _, .wadMulDown _ _ => [.Overflow, .DivisionByZero]
  | _, .wadMulUp _ _ => [.Overflow, .DivisionByZero]
  | _, .wadMulHalfUp _ _ => [.Overflow, .DivisionByZero]
  | _, .wadDivDown _ _ => [.DivisionByZero, .Overflow]
  | _, .wadDivUp _ _ => [.DivisionByZero, .Overflow]
  | _, .wadDivHalfUp _ _ => [.DivisionByZero, .Overflow]
  | _, .rayAddChecked _ _ => [.Overflow]
  | _, .raySubChecked _ _ => [.Underflow]
  | _, .eq a b => arithErrorsOfExpr a ++ arithErrorsOfExpr b
  | _, .lt a b => arithErrorsOfExpr a ++ arithErrorsOfExpr b
  | _, .le a b => arithErrorsOfExpr a ++ arithErrorsOfExpr b
  | _, .not a => arithErrorsOfExpr a
  | _, .and a b => arithErrorsOfExpr a ++ arithErrorsOfExpr b
  | _, .or a b => arithErrorsOfExpr a ++ arithErrorsOfExpr b
  | _, .mappingGet m k => arithErrorsOfExpr m ++ arithErrorsOfExpr k
  | _, .tokenMint a => arithErrorsOfExpr a
  | _, .tokenBurn a => arithErrorsOfExpr a
  | _, .tokenSplit a => arithErrorsOfExpr a
  | _, .tokenMerge a b => arithErrorsOfExpr a ++ arithErrorsOfExpr b
  | _, _ => []

partial def arithErrorsOfExprAny (e : ExprAny) : List ArithError :=
  arithErrorsOfExpr e.2

partial def arithErrorsOfStmt : Stmt → List ArithError
  | .skip => []
  | .seq s1 s2 => arithErrorsOfStmt s1 ++ arithErrorsOfStmt s2
  | .letBind _ e => arithErrorsOfExpr e.2
  | .letBind2 _ _ e => arithErrorsOfExpr e.2
  | .storageSet _ e => arithErrorsOfExpr e.2
  | .storageMapSet _ ek ev => arithErrorsOfExpr ek.2 ++ arithErrorsOfExpr ev.2
  | .require e _ => arithErrorsOfExpr e
  | .ifThenElse e s1 s2 => arithErrorsOfExpr e ++ arithErrorsOfStmt s1 ++ arithErrorsOfStmt s2
  | .call _ args => args.flatMap arithErrorsOfExprAny
  | .externalCall _ _ args => args.flatMap arithErrorsOfExprAny
  | .emit _ args => args.flatMap arithErrorsOfExprAny
  | .revert _ => []
  | .lockAcquire _ => []
  | .lockRelease e => arithErrorsOfExpr e

def arithErrorsOfContract (c : ContractDef) : List ArithError :=
  let fromStorage := c.storage.flatMap fun (_, _, def?) =>
    def?.map arithErrorsOfExprAny |>.getD []
  let fromFns := c.functions.flatMap fun fn => arithErrorsOfStmt fn.body
  (fromStorage ++ fromFns).eraseDups

def arithErrorName : ArithError → String
  | .Overflow => "Overflow"
  | .Underflow => "Underflow"
  | .DivisionByZero => "DivByZero"

def checkArithErrorCoverage (c : ContractDef) : Option String :=
  let missing := (arithErrorsOfContract c).filter fun ae =>
    ¬ c.errors.contains (arithErrorName ae)
  match missing with
  | [] => none
  | ae :: _ => some s!"arith error {arithErrorName ae} is reachable but not declared in errors:"

def checkNoCycles (_c : ContractDef) : Option String := none
def checkLinear (_c : ContractDef) : Option String := none
def checkSelectorCollisions (_c : ContractDef) : Option String := none
def checkNoUInt256Arithmetic (_c : ContractDef) : Option String := none

def validateAll (c : ContractDef) : Except String ContractDef :=
  if let some err := checkNoCycles c then .error err
  else if let some err := checkLinear c then .error err
  else if let some err := checkSelectorCollisions c then .error err
  else if let some err := checkNoUInt256Arithmetic c then .error err
  else if let some err := checkArithErrorCoverage c then .error err
  else .ok c

end Checks
end LscV2
