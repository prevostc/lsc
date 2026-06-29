import LscV2.Lang.AST
import LscV2.Core.ContractM
import LscV2.Lib.Wei.Eval

namespace LscV2

namespace CoreExpr

variable {S E Err : Type} [ContractErrors Err] [dsl : ContractDSL S E Err]

def eval
    {t : Ty} (e : CoreExpr t) (env : LocalEnv) : ContractM S E Err (Val t) :=
  match e with
  | .lit _ l =>
    match l with
    | .u256 n => pure (.u256 n)
    | .bool b => pure (.bool b)
    | .addr a => pure (.addr a)
  | .var _ name =>
    match env.lookup name with
    | some ⟨t', v⟩ =>
      if ht : t = t' then
        pure (cast (by simp [ht]) v)
      else
        ContractM.revert .Unauthorized
    | none => ContractM.revert .Unauthorized
  | .storageGet _ name => do
    let st ← ContractM.get
    match dsl.getField t name st.storage with
    | some v => pure v
    | none => ContractM.revert .Unauthorized
  | .txField f =>
    match f with
    | .caller => do
      let a ← ContractM.caller
      pure (.addr a)
    | .callvalue => pure (.u256 0)
    | .timestamp => pure (.u256 0)
  | .eq _ a b => do
    let va ← eval a env
    let vb ← eval b env
    pure (.bool (Val.eq va vb))
  | .not a => do
    let va ← eval a env
    pure (.bool (!Val.boolOf va))
  | .and a b => do
    let va ← eval a env
    let vb ← eval b env
    pure (.bool (Val.boolOf va && Val.boolOf vb))
  | .or a b => do
    let va ← eval a env
    let vb ← eval b env
    pure (.bool (Val.boolOf va || Val.boolOf vb))
  | .lt a b => do
    let va ← eval a env
    let vb ← eval b env
    pure (.bool (Val.u256Of va < Val.u256Of vb))
  | .le a b => do
    let va ← eval a env
    let vb ← eval b env
    pure (.bool (Val.u256Of va ≤ Val.u256Of vb))
  | .unit => pure (.unit)

attribute [simp] eval

end CoreExpr

namespace Expr

variable {S E Err : Type} [ContractErrors Err] [dsl : ContractDSL S E Err]

def eval
    {t : Ty} (e : Expr t) (env : LocalEnv) : ContractM S E Err (Val t) :=
  match t with
  | .wei => do
    let w ← Wei.eval e env
    pure (.wei w)
  | .uint256 | .bool | .address | .unit =>
    CoreExpr.eval e env

attribute [reducible] eval

end Expr

namespace Stmt

variable {S E Err : Type} [ContractErrors Err] [dsl : ContractDSL S E Err]

/-- Internal evaluator: threads `LocalEnv` through sequential statements for variable scoping. -/
def evalWith
    (stmt : Stmt) (env : LocalEnv) : ContractM S E Err LocalEnv :=
  match stmt with
  | .skip => pure env
  | .seq s1 s2 => do
    let env' ← evalWith s1 env
    evalWith s2 env'
  | .letBind name ⟨t, expr⟩ => do
    let v ← Expr.eval expr env
    pure (LocalEnv.bind name ⟨t, v⟩ env)
  | .storageSet field ⟨t, expr⟩ => do
    let v ← Expr.eval expr env
    ContractM.modifyStorage (dsl.setField t field v)
    pure env
  | .require condExpr errName => do
    let v ← Expr.eval condExpr env
    if Val.boolOf v then
      pure env
    else
      match dsl.resolveErr errName with
      | some err => ContractM.revertUser err
      | none => ContractM.revert .Unauthorized
  | .ifThenElse cond thn els => do
    let v ← Expr.eval cond env
    if Val.boolOf v then
      evalWith thn env
    else
      evalWith els env
  | .emit eventName args => do
    let vals ← args.mapM fun ⟨t, e⟩ => do
      let v ← Expr.eval e env
      pure ⟨t, v⟩
    match dsl.buildEvent eventName vals with
    | some ev => do
      ContractM.emit ev
      pure env
    | none => ContractM.revert .Unauthorized
  | .revert errName =>
    match dsl.resolveErr errName with
    | some err => ContractM.revertUser err
    | none => ContractM.revert .Unauthorized

attribute [reducible] evalWith

/-- Public evaluator: discards the internal `LocalEnv`; return type is `ContractM Unit`. -/
def eval
    (s : Stmt) : ContractM S E Err Unit := do
  let _ ← evalWith s LocalEnv.empty
  pure ()

end Stmt

end LscV2
