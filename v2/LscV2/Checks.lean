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

partial def callsOfStmt : Stmt → List Ident
  | .skip => []
  | .seq s1 s2 => callsOfStmt s1 ++ callsOfStmt s2
  | .letBind _ _ => []
  | .letBind2 _ _ _ => []
  | .storageSet _ _ => []
  | .storageMapSet _ _ _ => []
  | .require _ _ => []
  | .ifThenElse _ s1 s2 => callsOfStmt s1 ++ callsOfStmt s2
  | .call name _ => [name]
  | .externalCall _ _ _ => []
  | .emit _ _ => []
  | .revert _ => []
  | .lockAcquire _ => []
  | .lockRelease _ => []

def buildCallGraph (fns : List FunctionDef) : List (Ident × List Ident) :=
  fns.map fun fn => (fn.name, callsOfStmt fn.body)

partial def dfsCycle (graph : List (Ident × List Ident)) (stack : List Ident) (visited : List Ident)
    (node : Ident) : Option (List Ident) :=
  if stack.contains node then
    some (stack.reverse ++ [node])
  else if visited.contains node then
    none
  else
    let visited' := node :: visited
    let stack' := node :: stack
    match graph.find? (·.1 == node) with
    | none => none
    | some (_, callees) =>
      callees.foldl (init := none) fun acc callee =>
        match acc with
        | some cycle => some cycle
        | none => dfsCycle graph stack' visited' callee

def checkNoCycles (c : ContractDef) : Option String :=
  let graph := buildCallGraph c.functions
  let starts := c.functions.map (·.name)
  match starts.find? fun name => (dfsCycle graph [] [] name).isSome with
  | some _ => some "Recursive call cycle detected"
  | none => none

partial def exprUsesUInt256CheckedArith : {t : Ty} → Expr t → Bool
  | _, .weiAddChecked a b => hasUInt256Operand a || hasUInt256Operand b
  | _, .weiSubChecked a b => hasUInt256Operand a || hasUInt256Operand b
  | _, .weiMulChecked a b => hasUInt256Operand a || hasUInt256Operand b
  | _, .weiDivFloor a b => hasUInt256Operand a || hasUInt256Operand b
  | _, .weiAddCheckedNat a _ => hasUInt256Operand a
  | _, .wadAddChecked a b => hasUInt256Operand a || hasUInt256Operand b
  | _, .wadSubChecked a b => hasUInt256Operand a || hasUInt256Operand b
  | _, .wadMulDown a b => hasUInt256Operand a || hasUInt256Operand b
  | _, .wadMulUp a b => hasUInt256Operand a || hasUInt256Operand b
  | _, .wadMulHalfUp a b => hasUInt256Operand a || hasUInt256Operand b
  | _, .wadDivDown a b => hasUInt256Operand a || hasUInt256Operand b
  | _, .wadDivUp a b => hasUInt256Operand a || hasUInt256Operand b
  | _, .wadDivHalfUp a b => hasUInt256Operand a || hasUInt256Operand b
  | _, .rayAddChecked a b => hasUInt256Operand a || hasUInt256Operand b
  | _, .raySubChecked a b => hasUInt256Operand a || hasUInt256Operand b
  | _, .eq a b => exprUsesUInt256CheckedArith a || exprUsesUInt256CheckedArith b
  | _, .lt a b => exprUsesUInt256CheckedArith a || exprUsesUInt256CheckedArith b
  | _, .le a b => exprUsesUInt256CheckedArith a || exprUsesUInt256CheckedArith b
  | _, .not a => exprUsesUInt256CheckedArith a
  | _, .and a b => exprUsesUInt256CheckedArith a || exprUsesUInt256CheckedArith b
  | _, .or a b => exprUsesUInt256CheckedArith a || exprUsesUInt256CheckedArith b
  | _, .mappingGet m k => exprUsesUInt256CheckedArith m || exprUsesUInt256CheckedArith k
  | _, .tokenMint a => exprUsesUInt256CheckedArith a
  | _, .tokenBurn a => exprUsesUInt256CheckedArith a
  | _, .tokenSplit a => exprUsesUInt256CheckedArith a
  | _, .tokenMerge a b => exprUsesUInt256CheckedArith a || exprUsesUInt256CheckedArith b
  | _, _ => false
  where
    hasUInt256Operand : {t : Ty} → Expr t → Bool
      | _, .var _ => false
      | _, .litU256 _ => true
      | _, .storageGet _ => false
      | _, e => exprUsesUInt256CheckedArith e

partial def stmtUsesUInt256CheckedArith : Stmt → Bool
  | .skip => false
  | .seq s1 s2 => stmtUsesUInt256CheckedArith s1 || stmtUsesUInt256CheckedArith s2
  | .letBind _ e => exprUsesUInt256CheckedArith e.2
  | .letBind2 _ _ e => exprUsesUInt256CheckedArith e.2
  | .storageSet _ e => exprUsesUInt256CheckedArith e.2
  | .storageMapSet _ ek ev => exprUsesUInt256CheckedArith ek.2 || exprUsesUInt256CheckedArith ev.2
  | .require e _ => exprUsesUInt256CheckedArith e
  | .ifThenElse e s1 s2 =>
    exprUsesUInt256CheckedArith e || stmtUsesUInt256CheckedArith s1 || stmtUsesUInt256CheckedArith s2
  | .call _ args => args.any fun e => exprUsesUInt256CheckedArith e.2
  | .externalCall _ _ args => args.any fun e => exprUsesUInt256CheckedArith e.2
  | .emit _ args => args.any fun e => exprUsesUInt256CheckedArith e.2
  | .revert _ => false
  | .lockAcquire _ => false
  | .lockRelease e => exprUsesUInt256CheckedArith e

def checkNoUInt256Arithmetic (c : ContractDef) : Option String :=
  let badStorage := c.storage.any fun (_, _, def?) =>
    def?.map (fun e => exprUsesUInt256CheckedArith e.2) |>.getD false
  let badFns := c.functions.any fun fn => stmtUsesUInt256CheckedArith fn.body
  if badStorage || badFns then
    some "bare UInt256 arithmetic is not allowed in contract bodies"
  else
    none

def fnSignature (fn : FunctionDef) : String :=
  let params := String.intercalate "," (fn.params.map fun (n, t) => s!"{n}:{repr t}")
  s!"{fn.name}({params})"

/-- Stub selector: deterministic hash of external function signature (Keccak deferred). -/
def computeSelector (fn : FunctionDef) : UInt32 :=
  fnSignature fn |>.hash.toUInt32

def checkSelectorCollisions (c : ContractDef) : Option String :=
  let externals := c.functions.filter (·.kind == .external)
  let selectors := externals.map computeSelector
  if selectors.length ≠ selectors.eraseDups.length then
    some "Selector collision detected between external functions"
  else
    none

def checkLinear (_c : ContractDef) : Option String := none

def validateAll (c : ContractDef) : Except String ContractDef :=
  if let some err := checkNoCycles c then .error err
  else if let some err := checkLinear c then .error err
  else if let some err := checkSelectorCollisions c then .error err
  else if let some err := checkNoUInt256Arithmetic c then .error err
  else if let some err := checkArithErrorCoverage c then .error err
  else .ok c

end Checks
end LscV2
