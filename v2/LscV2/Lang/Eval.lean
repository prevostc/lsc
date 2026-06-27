import LscV2.Lang.AST
import LscV2.Core.ContractM
import LscV2.Lib.Wei.Eval

namespace LscV2

namespace CoreExpr

variable {S E Err : Type} [ContractErrors Err]

def eval
    (getField : (t : Ty) → Ident → S → Option (Val t))
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
    match getField t name st.storage with
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
    let va ← eval getField a env
    let vb ← eval getField b env
    pure (.bool (Val.eq va vb))
  | .not a => do
    let va ← eval getField a env
    pure (.bool (!Val.boolOf va))
  | .and a b => do
    let va ← eval getField a env
    let vb ← eval getField b env
    pure (.bool (Val.boolOf va && Val.boolOf vb))
  | .or a b => do
    let va ← eval getField a env
    let vb ← eval getField b env
    pure (.bool (Val.boolOf va || Val.boolOf vb))
  | .lt a b => do
    let va ← eval getField a env
    let vb ← eval getField b env
    pure (.bool (Val.u256Of va < Val.u256Of vb))
  | .le a b => do
    let va ← eval getField a env
    let vb ← eval getField b env
    pure (.bool (Val.u256Of va ≤ Val.u256Of vb))
  | .unit => pure (.unit)

attribute [simp] eval

end CoreExpr

namespace Expr

variable {S E Err : Type} [ContractErrors Err]

def eval
    (getField : (t : Ty) → Ident → S → Option (Val t))
    {t : Ty} (e : Expr t) (env : LocalEnv) : ContractM S E Err (Val t) :=
  match t with
  | .wei => do
    let w ← Wei.eval getField e env
    pure (.wei w)
  | .uint256 | .bool | .address | .unit =>
    CoreExpr.eval getField e env

attribute [reducible] eval

end Expr

namespace Stmt

variable {S E Err : Type} [ContractErrors Err]

def eval
    (getField : (t : Ty) → Ident → S → Option (Val t))
    (resolveErr : Ident → Option Err)
    (buildEvent : Ident → List (Sigma Val) → Option E)
    (setField : (t : Ty) → Ident → Val t → S → S)
    (stmt : Stmt) (env : LocalEnv) : ContractM S E Err LocalEnv :=
  match stmt with
  | .skip => pure env
  | .seq s1 s2 => do
    let env' ← eval getField resolveErr buildEvent setField s1 env
    eval getField resolveErr buildEvent setField s2 env'
  | .letBind name ⟨t, expr⟩ => do
    let v ← Expr.eval getField expr env
    pure (LocalEnv.bind name ⟨t, v⟩ env)
  | .storageSet field ⟨t, expr⟩ => do
    let v ← Expr.eval getField expr env
    ContractM.modifyStorage (setField t field v)
    pure env
  | .require condExpr errName => do
    let v ← Expr.eval getField condExpr env
    if Val.boolOf v then
      pure env
    else
      match resolveErr errName with
      | some err => ContractM.revertUser err
      | none => ContractM.revert .Unauthorized
  | .ifThenElse cond thn els => do
    let v ← Expr.eval getField cond env
    if Val.boolOf v then
      eval getField resolveErr buildEvent setField thn env
    else
      eval getField resolveErr buildEvent setField els env
  | .emit eventName args => do
    let vals ← args.mapM fun ⟨t, e⟩ => do
      let v ← Expr.eval getField e env
      pure ⟨t, v⟩
    match buildEvent eventName vals with
    | some ev => do
      ContractM.emit ev
      pure env
    | none => ContractM.revert .Unauthorized
  | .revert errName =>
    match resolveErr errName with
    | some err => ContractM.revertUser err
    | none => ContractM.revert .Unauthorized

attribute [reducible] eval

end Stmt

end LscV2
