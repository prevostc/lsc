import Lsc.Lang.AST
import Lsc.Lib.Wei.Syntax
import Lsc.Lib.Wad.Syntax
import Lsc.Selectors

namespace Lsc
namespace Checks

open Lsc (computeSelector)

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

/-- Mirrors `visitWeiExpr`, for `Wad.Expr`'s checked mul/div coverage. -/
partial def visitWadExpr (e : Wad.Expr) : VisitResult :=
  { arithErrors := Wad.arithErrors e
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
  | .wad, e => visitWadExpr e
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
  | .mapSet _ _ e => visitWadExpr e
  | .require e _ => visitExpr e
  | .ifThenElse e s1 s2 => visitExpr e |>.merge (visitStmt s1) |>.merge (visitStmt s2)
  | .emit _ args => args.foldl (init := {}) fun acc e => acc.merge (visitExpr e.2)
  | .revert _ => {}
  | .ret e => visitExprAny e
  | .externalExec _ _ args => args.foldl (init := {}) fun acc e => acc.merge (visitExpr e.2)
  | .letExecBind _ _ _ _ args => args.foldl (init := {}) fun acc e => acc.merge (visitExpr e.2)
  | .externalRead _ _ _ args => args.foldl (init := {}) fun acc e => acc.merge (visitExpr e.2)
  | .letReadBind _ _ _ _ _ args => args.foldl (init := {}) fun acc e => acc.merge (visitExpr e.2)
  | .reentrancyGuard body => visitStmt body

def arithErrorsOfContract (c : ContractDef) : List ArithError :=
  let fromStorage := c.storage.flatMap fun (_, _, def?) =>
    def?.map visitExprAny |>.getD {} |>.arithErrors
  let fromFns := c.functions.flatMap fun fn => visitStmt fn.body |>.arithErrors
  let fromCtor := match c.deployFn with
    | none => []
    | some fn => visitStmt fn.body |>.arithErrors
  (fromStorage ++ fromFns ++ fromCtor).eraseDups

/-- Name a reachable `ArithError` the way `deriving ContractError` expects a matching
    same-named user error constructor to be spelled (see `Lang/Derive.lean`). -/
def arithErrorName : ArithError → String
  | .Overflow => "Overflow"
  | .Underflow => "Underflow"
  | .DivisionByZero => "DivisionByZero"

/-- The checked-arithmetic operator notation that can raise this error, for actionable
    error messages (e.g. "`+?`" for `+? : Wei → Nat/Wei → Wei`). -/
def arithErrorOp : ArithError → String
  | .Overflow => "+?"
  | .Underflow => "-?"
  | .DivisionByZero => "/?"

/-- Reachable `ArithError`s per function, for per-function diagnostics. Storage
    field initializers are attributed to a synthetic `"<storage>"` pseudo-function. -/
def arithErrorsByFunction (c : ContractDef) : List (Ident × List ArithError) :=
  let fromStorage :=
    let errs := c.storage.flatMap fun (_, _, def?) =>
      def?.map visitExprAny |>.getD {} |>.arithErrors
    if errs.isEmpty then [] else [("<storage>", errs.eraseDups)]
  let fromFns := c.functions.filterMap fun fn =>
    let errs := (visitStmt fn.body).arithErrors.eraseDups
    if errs.isEmpty then none else some (fn.name, errs)
  fromStorage ++ fromFns

/-- Walk all function bodies (and storage initializers) of `c`, find every `ArithError`
    actually reachable via a checked-arithmetic op (`+?`/`-?`/`/?`), and ensure `c.errors`
    declares a same-named constructor for each one — matching the naming convention
    `deriving ContractError` (`Lang/Derive.lean`) uses to map `ArithError` variants to
    user error constructors. This is what turns a silent `ContractErrors.unreachableArith`
    fallback (chosen at `deriving` time, before bodies exist) into a loud compile-time
    failure once the full picture (declared constructors *and* actual usage) is known.

    `FrameworkError` (`Reentrant`/`Unauthorized`/`InvalidSelector`) is intentionally NOT
    checked for reachability here: unlike checked-arithmetic ops, there is no AST node
    that "raises" a `FrameworkError` the way `Wei.Expr.addChecked` raises `Overflow` —
    those errors come from framework-level guards (e.g. reentrancy locks) outside the
    `Stmt`/`Expr` data the contract author writes, so there's no decidable reachability
    signal to walk yet. Revisit if/when framework guards become explicit `Stmt` nodes. -/
def checkArithErrorCoverage (c : ContractDef) : Option String :=
  let missing := (arithErrorsByFunction c).flatMap fun (fnName, errs) =>
    errs.filter (fun ae => ¬ c.errors.contains (arithErrorName ae))
      |>.map fun ae => (fnName, ae)
  match missing with
  | [] => none
  | (fnName, ae) :: _ =>
    some s!"`{fnName}` uses `{arithErrorOp ae}`, which can raise `ArithError.{arithErrorName ae}`, \
but {c.name}'s error type has no `{arithErrorName ae}` constructor — add one or write \
`ContractErrors` by hand"

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
  -- `view` functions share the same 4-byte ABI selector dispatch table as `external` ones
  -- (`Bytecode/Contract.lean`'s `selectorDispatch` jumps into both kinds off one shared
  -- calldata-selector check), so collisions must be checked across both kinds together.
  let dispatched := c.functions.filter fun fn => fn.kind == .external || fn.kind == .view
  let selectors := dispatched.map computeSelector
  if selectors.length ≠ selectors.eraseDups.length then
    some "Selector collision detected between external/view functions"
  else
    none

/-- A `view` function's body must never mutate storage or emit an event — it is meant to be a
pure, `STATICCALL`-style read (see `Core/ContractM.lean`'s `PairM.read` docstring). `require`/
`revert` are still allowed (a lookup can validly reject bad input), and cross-contract `exec`/
`read` statements never reach `Stmt` at all (`Lang/Syntax.lean`'s cross-call elaborator bypasses
`Stmt` entirely), so neither needs special-casing here. -/
partial def hasViewMutation : Stmt → Bool
  | .storageSet _ _ => true
  | .mapSet _ _ _ => true
  | .emit _ _ => true
  | .seq s1 s2 => hasViewMutation s1 || hasViewMutation s2
  | .ifThenElse _ s1 s2 => hasViewMutation s1 || hasViewMutation s2
  | _ => false

def checkViewPurity (fn : FunctionDef) : Option String :=
  if hasViewMutation fn.body then
    some s!"`{fn.name}` is a `view` function but its body mutates storage or emits an event"
  else
    none

/-- Every control-flow path through a `view` body must end in a `return` of the declared
`retTy` — mirrors the early-return semantics `Eval.lean`'s `Stmt.evalWith` implements at
runtime (`.seq`'s second branch is skipped once the first branch already returned), so a body
this check accepts is guaranteed to make `Stmt.evalView` succeed rather than fall through to its
`Unauthorized` fallback. -/
partial def allPathsReturn (t : Ty) : Stmt → Bool
  | .ret ⟨t', _⟩ => t == t'
  | .seq s1 s2 => allPathsReturn t s1 || allPathsReturn t s2
  | .ifThenElse _ s1 s2 => allPathsReturn t s1 && allPathsReturn t s2
  | _ => false

def checkViewReturns (fn : FunctionDef) : Option String :=
  if allPathsReturn fn.retTy fn.body then
    none
  else
    some s!"`{fn.name}` is a `view` function whose body does not return a `{repr fn.retTy}` on \
every path"

def checkViews (c : ContractDef) : Option String :=
  let views := c.functions.filter (·.kind == .view)
  views.foldl (init := none) fun acc fn =>
    match acc with
    | some e => some e
    | none =>
      match checkViewPurity fn with
      | some e => some e
      | none => checkViewReturns fn

/-- Linearity pass stub — see `docs/extensions/linear-types/`. -/
def checkLinear (_c : ContractDef) : Option String := none

/-- Whether `s` contains an `externalExec` node. -/
partial def usesExternalExec : Stmt → Bool
  | .skip => false
  | .seq s1 s2 => usesExternalExec s1 || usesExternalExec s2
  | .externalExec .. => true
  | .letExecBind .. => true
  | .reentrancyGuard body => usesExternalExec body
  | .ifThenElse _ s1 s2 => usesExternalExec s1 || usesExternalExec s2
  | _ => false

/-- Whether `s` is wrapped in `reentrancyGuard` at its outermost layer. -/
def hasReentrancyGuard : Stmt → Bool
  | .reentrancyGuard _ => true
  | _ => false

/-- Any function using `externalExec` must be `@nonreentrant` with a `reentrancyGuard` body. -/
def checkNonReentrant (c : ContractDef) : Option String :=
  c.functions.findSome? fun fn =>
    if usesExternalExec fn.body then
      if !fn.nonReentrant then
        some s!"`{fn.name}` uses `exec` but is not marked `@nonreentrant`"
      else if !hasReentrancyGuard fn.body then
        some s!"`{fn.name}` uses `exec` but its body is not wrapped in `reentrancyGuard`"
      else none
    else none

/-- Collect field names written by `σ.field = ...` (`Stmt.storageSet`) in a `Stmt` tree. -/
partial def collectStorageSets : Stmt → List Ident
  | .storageSet field _ => [field]
  | .seq s1 s2 => collectStorageSets s1 ++ collectStorageSets s2
  | .ifThenElse _ s1 s2 => collectStorageSets s1 ++ collectStorageSets s2
  | .reentrancyGuard body => collectStorageSets body
  | _ => []

/-- Every scalar storage field must be initialized either via a struct default
(`ContractDef.storage`'s third component is `some`) or an explicit `σ.field = ...` in the
constructor body. -/
def checkStorageInitialization (c : ContractDef) : Option String :=
  let requiredFields := c.storage.filterMap fun (name, _, def?) =>
    if def?.isNone then some name else none
  if requiredFields.isEmpty then none
  else
    let ctorWrites := match c.deployFn with
      | some fn => collectStorageSets fn.body
      | none => []
    let missing := requiredFields.filter fun f => !ctorWrites.contains f
    if missing.isEmpty then none
    else if c.deployFn.isNone then
      some s!"storage field `{missing.head!}` has no struct default and no constructor is \
declared — add `:= ...` or a `constructor` block that sets it"
    else
      some s!"constructor does not initialize `{missing.head!}` — add `σ.{missing.head!} = ...` \
or a struct default"

-- `checkNonReentrant` replaces the old deferred check that lived here when cross-call txs
-- bypassed `ContractDef`. Cross-contract calls are now `Stmt.externalExec`/`externalRead`.

def validateAll (c : ContractDef) : Except String ContractDef :=
  if let some err := checkNoCycles c then .error err
  else if let some err := checkLinear c then .error err
  else if let some err := checkSelectorCollisions c then .error err
  else if let some err := checkNoUInt256Arithmetic c then .error err
  else if let some err := checkStorageInitialization c then .error err
  else if let some err := checkArithErrorCoverage c then .error err
  else if let some err := checkNonReentrant c then .error err
  else if let some err := checkViews c then .error err
  else .ok c

end Checks
end Lsc
