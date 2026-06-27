import LscV2.Lang.AST
import LscV2.Lib.Wei.Syntax
import LscV2.Selectors

namespace LscV2
namespace Checks

open LscV2 (computeSelector)

structure VisitResult where
  arithErrors : List ArithError := []
  internalCalls : List Ident := []
  usesUInt256Arith : Bool := false
  deriving Repr, Inhabited

namespace VisitResult

def empty : VisitResult := {}

def merge (a b : VisitResult) : VisitResult :=
  { arithErrors := a.arithErrors ++ b.arithErrors
  , internalCalls := a.internalCalls ++ b.internalCalls
  , usesUInt256Arith := a.usesUInt256Arith || b.usesUInt256Arith }

end VisitResult

partial def visitWeiExpr (e : Wei.Expr) : VisitResult :=
  { arithErrors := Wei.arithErrors e
  , usesUInt256Arith := false }

partial def visitCoreExpr : {t : Ty} → CoreExpr t → VisitResult
  | _, .lit _ l =>
    match l with
    | .u256 _ => { usesUInt256Arith := true }
    | _ => {}
  | _, .eq _ a b => visitCoreExpr a |>.merge (visitCoreExpr b)
  | _, .lt a b => visitCoreExpr a |>.merge (visitCoreExpr b)
  | _, .le a b => visitCoreExpr a |>.merge (visitCoreExpr b)
  | _, .not a => visitCoreExpr a
  | _, .and a b => visitCoreExpr a |>.merge (visitCoreExpr b)
  | _, .or a b => visitCoreExpr a |>.merge (visitCoreExpr b)
  | _, _ => {}

partial def visitExpr : {t : Ty} → Expr t → VisitResult
  | .wei, e => visitWeiExpr e
  | .uint256, e => visitCoreExpr e
  | .bool, e => visitCoreExpr e
  | .address, e => visitCoreExpr e
  | .unit, e => visitCoreExpr e

partial def visitExprAny (e : ExprAny) : VisitResult :=
  visitExpr e.2

partial def visitStmt : Stmt → VisitResult
  | .skip => {}
  | .seq s1 s2 => visitStmt s1 |>.merge (visitStmt s2)
  | .letBind _ e => visitExpr e.2
  | .storageSet _ e => visitExpr e.2
  | .require e _ => visitExpr e
  | .ifThenElse e s1 s2 => visitExpr e |>.merge (visitStmt s1) |>.merge (visitStmt s2)
  | .emit _ args => args.foldl (init := {}) fun acc e => acc.merge (visitExpr e.2)
  | .revert _ => {}

def arithErrorsOfContract (c : ContractDef) : List ArithError :=
  let fromStorage := c.storage.flatMap fun (_, _, def?) =>
    def?.map visitExprAny |>.getD {} |>.arithErrors
  let fromFns := c.functions.flatMap fun fn => visitStmt fn.body |>.arithErrors
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

def buildCallGraph (fns : List FunctionDef) : List (Ident × List Ident) :=
  fns.map fun fn => (fn.name, visitStmt fn.body |>.internalCalls)

def checkNoCycles (c : ContractDef) : Option String :=
  let graph := buildCallGraph c.functions
  let starts := c.functions.map (·.name)
  match starts.find? fun name => (dfsCycle graph [] [] name).isSome with
  | some _ => some "Recursive call cycle detected"
  | none => none

def checkNoUInt256Arithmetic (c : ContractDef) : Option String :=
  let badStorage := c.storage.any fun (_, _, def?) =>
    def?.map (fun e => visitExpr e.2 |>.usesUInt256Arith) |>.getD false
  let badFns := c.functions.any fun fn => visitStmt fn.body |>.usesUInt256Arith
  if badStorage || badFns then
    some "bare UInt256 arithmetic is not allowed in contract bodies"
  else
    none

def checkSelectorCollisions (c : ContractDef) : Option String :=
  let externals := c.functions.filter (·.kind == .external)
  let selectors := externals.map computeSelector
  if selectors.length ≠ selectors.eraseDups.length then
    some "Selector collision detected between external functions"
  else
    none

/-- Linearity pass stub — see `docs/spec_idea_2/extensions/linear-types/`. -/
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
