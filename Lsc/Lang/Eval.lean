import Lsc.Lang.AST
import Lsc.Core.ContractM
import Lsc.Lib.Wei.Eval
import Lsc.Lib.Wad.Eval

namespace Lsc

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
  | .wadLt a b => do
    let va ← Wad.eval a env
    let vb ← Wad.eval b env
    pure (.bool (va.n < vb.n))
  | .wadLe a b => do
    let va ← Wad.eval a env
    let vb ← Wad.eval b env
    pure (.bool (va.n ≤ vb.n))
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
  | .wad => do
    let w ← Wad.eval e env
    pure (.wad w)
  | .uint256 | .bool | .address | .unit =>
    CoreExpr.eval e env

attribute [reducible] eval

@[simp] theorem eval_wei (e : Expr .wei) (env : LocalEnv) :
    eval (S := S) (E := E) (Err := Err) e env =
      (Wei.eval e env >>= fun w => pure (.wei w)) := rfl

@[simp] theorem eval_wad (e : Expr .wad) (env : LocalEnv) :
    eval (S := S) (E := E) (Err := Err) e env =
      (Wad.eval e env >>= fun w => pure (.wad w)) := rfl

@[simp] theorem eval_uint256 (e : Expr .uint256) (env : LocalEnv) :
    eval (S := S) (E := E) (Err := Err) e env = CoreExpr.eval e env := rfl

@[simp] theorem eval_bool (e : Expr .bool) (env : LocalEnv) :
    eval (S := S) (E := E) (Err := Err) e env = CoreExpr.eval e env := rfl

@[simp] theorem eval_address (e : Expr .address) (env : LocalEnv) :
    eval (S := S) (E := E) (Err := Err) e env = CoreExpr.eval e env := rfl

@[simp] theorem eval_unit (e : Expr .unit) (env : LocalEnv) :
    eval (S := S) (E := E) (Err := Err) e env = CoreExpr.eval e env := rfl

end Expr

namespace Stmt

variable {S E Err : Type} [ContractErrors Err] [dsl : ContractDSL S E Err]

/-- Internal evaluator: threads `LocalEnv` through sequential statements for variable scoping,
alongside an optional "returned value" (`Sigma Val`, only ever produced by `.ret` — see that
constructor's docstring in `Lang/AST.lean`). Once a `.ret` fires, `.seq`'s second branch is
skipped entirely — this is what gives `return e;` real early-return semantics inside `view`
function bodies, matching how `Checks.checkViewReturns` statically reasons about "every path
returns". `tx`/`.external` bodies never contain `.ret` (enforced by `checkViewPurity`'s
counterpart on the `tx` side — `.ret` is only ever emitted by the `view` elaborator, see
`Lang/Syntax.lean`), so for them the returned-value component is always `none` and `Stmt.eval`
below simply discards it. -/
def evalWith
    (stmt : Stmt) (env : LocalEnv) : ContractM S E Err (LocalEnv × Option (Sigma Val)) :=
  match stmt with
  | .skip => pure (env, none)
  | .seq s1 s2 => do
    let (env', ret?) ← evalWith s1 env
    match ret? with
    | some _ => pure (env', ret?)
    | none => evalWith s2 env'
  | .letBind name ⟨t, expr⟩ => do
    let v ← Expr.eval expr env
    pure (LocalEnv.bind name ⟨t, v⟩ env, none)
  | .storageSet field ⟨t, expr⟩ => do
    let v ← Expr.eval expr env
    ContractM.modifyStorage (dsl.setField t field v)
    pure (env, none)
  | .mapSet field key expr => do
    let addr ← match key with
      | .caller => ContractM.caller
      | .var name =>
        match env.lookup name with
        | some ⟨Ty.address, .addr a⟩ => pure a
        | _ => ContractM.revert .Unauthorized
    let w ← Wad.eval expr env
    ContractM.modifyStorage (dsl.setMapField field addr w)
    pure (env, none)
  | .mapSet2 field key1 key2 expr => do
    let addr1 ← Wad.resolveMapKey key1 env
    let addr2 ← Wad.resolveMapKey key2 env
    let w ← Wad.eval expr env
    ContractM.modifyStorage (dsl.setMapField2 field addr1 addr2 w)
    pure (env, none)
  | .require condExpr errName => do
    let v ← Expr.eval condExpr env
    if Val.boolOf v then
      pure (env, none)
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
      pure (env, none)
    | none => ContractM.revert .Unauthorized
  | .revert errName =>
    match dsl.resolveErr errName with
    | some err => ContractM.revertUser err
    | none => ContractM.revert .Unauthorized
  | .ret ⟨t, expr⟩ => do
    let v ← Expr.eval expr env
    pure (env, some ⟨t, v⟩)
  | .reentrancyGuard body => do
    let st ← ContractM.get
    if st.locked then
      ContractM.revert .Reentrant
    else do
      ContractM.setLocked true
      let r ← evalWith body env
      ContractM.setLocked false
      pure r
  | .externalExec .. => pure (env, none)
  | .letExecBind .. => pure (env, none)
  | .externalRead .. => pure (env, none)
  | .letReadBind .. => pure (env, none)

attribute [reducible] evalWith

@[simp] theorem evalWith_skip (env : LocalEnv) :
    evalWith (S := S) (E := E) (Err := Err) .skip env = pure (env, none) := rfl

@[simp] theorem evalWith_seq (s1 s2 : Stmt) (env : LocalEnv) :
    evalWith (S := S) (E := E) (Err := Err) (.seq s1 s2) env =
      (evalWith s1 env >>= fun (env', ret?) =>
        match ret? with
        | some _ => pure (env', ret?)
        | none => evalWith s2 env') := rfl

@[simp] theorem evalWith_letBind (name : Ident) (t : Ty) (expr : Expr t) (env : LocalEnv) :
    evalWith (S := S) (E := E) (Err := Err) (.letBind name ⟨t, expr⟩) env =
      (Expr.eval expr env >>= fun v => pure (LocalEnv.bind name ⟨t, v⟩ env, none)) := rfl

@[simp] theorem evalWith_storageSet (field : Ident) (t : Ty) (expr : Expr t) (env : LocalEnv) :
    evalWith (S := S) (E := E) (Err := Err) (.storageSet field ⟨t, expr⟩) env =
      (Expr.eval expr env >>= fun v =>
        ContractM.modifyStorage (dsl.setField t field v) >>= fun _ => pure (env, none)) := rfl

@[simp] theorem evalWith_mapSet (field : Ident) (key : MapKey) (expr : Wad.Expr) (env : LocalEnv) :
    evalWith (S := S) (E := E) (Err := Err) (.mapSet field key expr) env =
      (do
        let addr ← match key with
          | .caller => ContractM.caller
          | .var name =>
            match env.lookup name with
            | some ⟨Ty.address, .addr a⟩ => pure a
            | _ => ContractM.revert .Unauthorized
        let w ← Wad.eval expr env
        ContractM.modifyStorage (dsl.setMapField field addr w)
        pure (env, none)) := rfl

@[simp] theorem evalWith_mapSet2 (field : Ident) (key1 key2 : MapKey) (expr : Wad.Expr) (env : LocalEnv) :
    evalWith (S := S) (E := E) (Err := Err) (.mapSet2 field key1 key2 expr) env =
      (do
        let addr1 ← Wad.resolveMapKey key1 env
        let addr2 ← Wad.resolveMapKey key2 env
        let w ← Wad.eval expr env
        ContractM.modifyStorage (dsl.setMapField2 field addr1 addr2 w)
        pure (env, none)) := rfl

@[simp] theorem evalWith_require (condExpr : Expr .bool) (errName : Ident) (env : LocalEnv) :
    evalWith (S := S) (E := E) (Err := Err) (.require condExpr errName) env =
      (Expr.eval condExpr env >>= fun v =>
        if Val.boolOf v then pure (env, none)
        else match dsl.resolveErr errName with
          | some err => ContractM.revertUser err
          | none => ContractM.revert .Unauthorized) := rfl

@[simp] theorem evalWith_ifThenElse (cond : Expr .bool) (thn els : Stmt) (env : LocalEnv) :
    evalWith (S := S) (E := E) (Err := Err) (.ifThenElse cond thn els) env =
      (Expr.eval cond env >>= fun v =>
        if Val.boolOf v then evalWith thn env else evalWith els env) := rfl

@[simp] theorem evalWith_emit (eventName : Ident) (args : List ExprAny) (env : LocalEnv) :
    evalWith (S := S) (E := E) (Err := Err) (.emit eventName args) env =
      ((args.mapM fun ⟨t, e⟩ => Expr.eval e env >>= fun v => pure ⟨t, v⟩) >>= fun vals =>
        match dsl.buildEvent eventName vals with
        | some ev => ContractM.emit ev >>= fun _ => pure (env, none)
        | none => ContractM.revert .Unauthorized) := rfl

@[simp] theorem evalWith_revert (errName : Ident) (env : LocalEnv) :
    evalWith (S := S) (E := E) (Err := Err) (.revert errName) env =
      (match dsl.resolveErr errName with
        | some err => ContractM.revertUser err
        | none => ContractM.revert .Unauthorized) := rfl

@[simp] theorem evalWith_ret (t : Ty) (expr : Expr t) (env : LocalEnv) :
    evalWith (S := S) (E := E) (Err := Err) (.ret ⟨t, expr⟩) env =
      (Expr.eval expr env >>= fun v => pure (env, some ⟨t, v⟩)) := rfl

/-- Public evaluator: discards the internal `LocalEnv`/returned value; return type is
`ContractM Unit`. Used for `.external`/`tx` bodies, which never contain a `.ret` (see
`evalWith`'s docstring). -/
def eval
    (s : Stmt) : ContractM S E Err Unit := do
  let _ ← evalWith s LocalEnv.empty
  pure ()

@[simp] theorem eval_def (s : Stmt) :
    eval (S := S) (E := E) (Err := Err) s =
      (evalWith s LocalEnv.empty >>= fun _ => pure ()) := rfl

/-- Public evaluator for `view` function bodies: runs `s`, requires that it hit a `.ret` of
exactly the expected `Ty` `t` (a `checkViewReturns`-passing body always does — this is the
runtime counterpart of that static check), and returns the unwrapped value. Reverts with
`.Unauthorized` if the body somehow returns no value or a mismatched `Ty` (should be
unreachable for any body accepted by `Checks.validateAll`). -/
def evalView (t : Ty) (s : Stmt) : ContractM S E Err (Val t) := do
  let (_, ret?) ← evalWith s LocalEnv.empty
  match ret? with
  | some ⟨t', v⟩ =>
    if ht : t = t' then
      pure (cast (by simp [ht]) v)
    else
      ContractM.revert .Unauthorized
  | none => ContractM.revert .Unauthorized

end Stmt

end Lsc
