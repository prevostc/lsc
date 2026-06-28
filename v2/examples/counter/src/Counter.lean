import LscV2.Lang.Eval
import LscV2.Compile.Yul
import LscV2.Compile.Bytecode

/-!
Counter example — target DSL shape is in docs/spec_idea_2/reference/COUNTER.md.
Hand-written until contract elaboration (IMPLEMENTATION.md Step 7).
-/

open LscV2 LscV2.Compile

namespace Counter

set_option linter.unusedSimpArgs false

structure CounterStorage where
  number : Wei := Wei.mkNat 0
  paused : Bool := false
  owner : Address := 0
  deriving Repr

instance : Inhabited CounterStorage where
  default := {}

inductive CounterError where
  | Paused
  | NotOwner
  | Overflow
  deriving Repr, DecidableEq

instance : Inhabited CounterError where
  default := .Paused

inductive CounterEvent where
  | Incremented (n : Wei)
  | Paused
  | Unpaused
  deriving Repr, DecidableEq

instance : ContractErrors CounterError where
  arith := fun
    | .Overflow => .Overflow
    | ae => ContractErrors.unreachableArith ae
  fromFramework := fun _ => .Overflow

def getField (t : Ty) (field : String) (s : CounterStorage) : Option (Val t) :=
  match t, field with
  | .wei, "number" => some (.wei s.number)
  | .bool, "paused" => some (.bool s.paused)
  | .address, "owner" => some (.addr s.owner)
  | _, _ => none

def setField (t : Ty) (field : String) (v : Val t) (s : CounterStorage) : CounterStorage :=
  match t, field, v with
  | .wei, "number", .wei w => { s with number := w }
  | .bool, "paused", .bool b => { s with paused := b }
  | .address, "owner", .addr a => { s with owner := a }
  | _, _, _ => s

@[simp] theorem getField_number (s : CounterStorage) :
    getField Ty.wei "number" s = some (.wei s.number) := rfl

@[simp] theorem getField_paused (s : CounterStorage) :
    getField Ty.bool "paused" s = some (.bool s.paused) := rfl

@[simp] theorem getField_owner (s : CounterStorage) :
    getField Ty.address "owner" s = some (.addr s.owner) := rfl

@[simp] theorem setField_number (v : Wei) (s : CounterStorage) :
    setField Ty.wei "number" (.wei v) s = { s with number := v } := rfl

@[simp] theorem setField_paused (v : Bool) (s : CounterStorage) :
    setField Ty.bool "paused" (.bool v) s = { s with paused := v } := rfl

@[simp] theorem setField_owner (v : Address) (s : CounterStorage) :
    setField Ty.address "owner" (.addr v) s = { s with owner := v } := rfl

def incrementRequire : Stmt :=
  Stmt.require (CoreExpr.not (CoreExpr.storageGet Ty.bool "paused")) "Paused"

def incrementLet : Stmt :=
  Stmt.letBind "n" ⟨Ty.wei,
    Wei.addCheckedNatStorage "number" 1⟩

def incrementSet : Stmt :=
  Stmt.storageSet "number" ⟨Ty.wei, Wei.Expr.var "n"⟩

def incrementEmit : Stmt :=
  Stmt.emit "Incremented" [⟨Ty.wei, Wei.Expr.var "n"⟩]

def incrementTail : Stmt := Stmt.seq incrementSet incrementEmit

def incrementBody : Stmt := Stmt.seq incrementLet incrementTail

def incrementAst : Stmt := Stmt.seq incrementRequire incrementBody

def resolveError (name : String) : Option CounterError :=
  match name with
  | "Paused" => some .Paused
  | "NotOwner" => some .NotOwner
  | "Overflow" => some .Overflow
  | _ => none

def buildEvent (name : String) (vals : List (Sigma Val)) : Option CounterEvent :=
  match name, vals with
  | "Incremented", [⟨.wei, (.wei n)⟩] => some (.Incremented n)
  | "Paused", [] => some .Paused
  | "Unpaused", [] => some (.Unpaused)
  | _, _ => none

@[simp] theorem resolveError_paused :
    resolveError "Paused" = some .Paused := rfl

@[simp] theorem resolveError_notOwner :
    resolveError "NotOwner" = some .NotOwner := rfl

@[simp] theorem resolveError_overflow :
    resolveError "Overflow" = some .Overflow := rfl

@[simp] theorem buildEvent_incremented (n : Wei) :
    buildEvent "Incremented" [⟨Ty.wei, (.wei n)⟩] =
      some (.Incremented n) := rfl

@[simp] theorem buildEvent_paused :
    buildEvent "Paused" [] = some .Paused := rfl

@[simp] theorem buildEvent_unpaused :
    buildEvent "Unpaused" [] = some .Unpaused := rfl

abbrev CounterM := ContractM CounterStorage CounterEvent CounterError

def incrementViaAst : CounterM LocalEnv :=
  Stmt.eval getField resolveError buildEvent setField incrementAst LocalEnv.empty

def increment : CounterM Unit := do
  let _ ← incrementViaAst
  pure ()

@[simp]
theorem runS_discard_env (m : CounterM LocalEnv) (s : ContractState CounterStorage) :
    runS (do let _ ← m; pure (() : Unit)) s =
      match m s with
      | .error e => .error e
      | .ok (_, s', log) => .ok ((), s', log) := by
  simp only [runS, ContractM.bind_apply, ContractM.pure_apply, List.append_nil]
  cases hm : m s with
  | error e => simp [hm]
  | ok p =>
    rcases p with ⟨_, s', log⟩
    simp [hm]

@[simp]
theorem runS_increment (s : ContractState CounterStorage) :
    runS increment s =
      match incrementViaAst s with
      | .error e => .error e
      | .ok (_, s', log) => .ok ((), s', log) :=
  runS_discard_env incrementViaAst s

private def incrementOkResult (s : ContractState CounterStorage) (w' : Wei) :
    LocalEnv × ContractState CounterStorage × List CounterEvent :=
  (LocalEnv.bind "n" ⟨Ty.wei, (.wei w')⟩ LocalEnv.empty,
    { s with storage := { s.storage with number := w' }},
    [CounterEvent.Incremented w'])

private def runIncrementEval (s : ContractState CounterStorage) :
    Except CounterError (LocalEnv × ContractState CounterStorage × List CounterEvent) :=
  if s.storage.paused then
    .error CounterError.Paused
  else if s.storage.number.raw.toNat + 1 < 2 ^ 256 then
    let w' : Wei := ⟨BitVec.ofNat 256 (s.storage.number.raw.toNat + 1)⟩
    .ok (incrementOkResult s w')
  else
    .error CounterError.Overflow

section bridgeEval

private theorem eval_var_n (s : ContractState CounterStorage) (env : LocalEnv) (w' : Wei)
    (h : env.lookup "n" = some ⟨Ty.wei, Val.wei w'⟩) :
    (Expr.eval getField (show Expr Ty.wei from Wei.Expr.var "n") env : CounterM (Val .wei)) s =
      .ok (Val.wei w', s, []) := by
  simp only [Expr.eval, Wei.eval, h, decide_eq_true_eq, ContractM.pure_apply]
  rfl

private theorem eval_incrementRequire_ok (s : ContractState CounterStorage)
    (hpaused : s.storage.paused = false) :
    Stmt.eval getField resolveError buildEvent setField incrementRequire LocalEnv.empty s = .ok (LocalEnv.empty, s, []) := by
  simp only [incrementRequire, Stmt.eval, Expr.eval, CoreExpr.eval, getField_paused, ContractM.bind_apply,
             ContractM.get, ContractM.pure_apply, resolveError_paused, List.append_nil,
             Val.boolOf_bool, hpaused, Bool.not_false]
  simp [ContractM.pure_apply, List.append_nil]

private theorem eval_incrementRequire_err (s : ContractState CounterStorage)
    (hp : s.storage.paused = true) :
    Stmt.eval getField resolveError buildEvent setField incrementRequire LocalEnv.empty s = .error CounterError.Paused := by
  simp only [incrementRequire, Stmt.eval, Expr.eval, CoreExpr.eval, getField_paused, ContractM.bind_apply,
             ContractM.get, resolveError_paused, ContractM.revertUser, ContractM.revertUser_apply,
             List.append_nil, Val.boolOf_bool, hp, Bool.not_true, if_false]
  simp [ContractM.revertUser_apply]

private theorem eval_incrementLet_ok (s : ContractState CounterStorage) (w' : Wei)
    (hw : w' = ⟨BitVec.ofNat 256 (s.storage.number.raw.toNat + 1)⟩)
    (hno : s.storage.number.raw.toNat + 1 < 2 ^ 256) :
    Stmt.eval getField resolveError buildEvent setField incrementLet LocalEnv.empty s =
      Except.ok (LocalEnv.bind "n" ⟨Ty.wei, (.wei w')⟩ LocalEnv.empty, s, []) := by
  simp only [incrementLet, Stmt.eval, Expr.eval, Wei.eval, Wei.addCheckedNatStorage_eq, getField_number, LocalEnv.empty, LocalEnv.bind,
             ContractM.bind_apply, ContractM.get, ContractM.pure_apply, hw,
             Wei.addCheckedNat_ok s.storage.number 1 hno, Val.weiOf_wei, List.append_nil]

private theorem eval_incrementLet_err (s : ContractState CounterStorage)
    (hov : ¬ s.storage.number.raw.toNat + 1 < 2 ^ 256) :
    Stmt.eval getField resolveError buildEvent setField incrementLet LocalEnv.empty s = .error CounterError.Overflow := by
  simp only [incrementLet, Stmt.eval, Expr.eval, Wei.eval, Wei.addCheckedNatStorage_eq, getField_number, LocalEnv.empty,
             ContractM.bind_apply, ContractM.get, Wei.addCheckedNat_error s.storage.number 1 hov,
             Val.weiOf_wei, ContractM.revertArith, ContractErrors.arith, List.append_nil]

private theorem eval_incrementSet_ok (s : ContractState CounterStorage) (w' : Wei) (env : LocalEnv)
    (henv : env.lookup "n" = some ⟨Ty.wei, Val.wei w'⟩) :
    Stmt.eval getField resolveError buildEvent setField incrementSet env s =
      Except.ok (env, { s with storage := { s.storage with number := w' }}, []) := by
  simp only [incrementSet, Stmt.eval, Expr.eval, eval_var_n s env w' henv, setField_number,
             ContractM.bind_apply, ContractM.modifyStorage, ContractM.pure_apply, List.append_nil]

private theorem eval_incrementEmit_ok (env : LocalEnv) (s' : ContractState CounterStorage) (w' : Wei)
    (h : env.lookup "n" = some ⟨Ty.wei, Val.wei w'⟩) :
    Stmt.eval getField resolveError buildEvent setField incrementEmit env s' =
      Except.ok (env, s', [CounterEvent.Incremented w']) := by
  simp only [incrementEmit, Stmt.eval, List.mapM, List.mapM.loop, List.nil_append,
             List.reverseAux_nil, List.reverse, eval_var_n s' env w' h, buildEvent_incremented,
             ContractM.emit, ContractM.bind_apply, List.reverseAux_cons, List.append_nil]

private theorem eval_incrementTail_ok (s : ContractState CounterStorage) (w' : Wei) (env : LocalEnv)
    (henv : env.lookup "n" = some ⟨Ty.wei, Val.wei w'⟩) :
    Stmt.eval getField resolveError buildEvent setField incrementTail env s =
      Except.ok (env, { s with storage := { s.storage with number := w' }},
        [CounterEvent.Incremented w']) := by
  simp only [incrementTail, Stmt.eval]
  rw [ContractM.bind_apply_ok _ _ _ _ _ _ (eval_incrementSet_ok s w' env henv)]
  simp [eval_incrementEmit_ok env ({ s with storage := { s.storage with number := w' }}) w' henv,
        List.append_nil]

private theorem eval_incrementBody_ok (s : ContractState CounterStorage) (w' : Wei)
    (hno : s.storage.number.raw.toNat + 1 < 2 ^ 256)
    (hw : w' = ⟨BitVec.ofNat 256 (s.storage.number.raw.toNat + 1)⟩) :
    Stmt.eval getField resolveError buildEvent setField incrementBody LocalEnv.empty s = .ok (incrementOkResult s w') := by
  let env' := LocalEnv.bind "n" ⟨Ty.wei, (.wei w')⟩ LocalEnv.empty
  have henv : env'.lookup "n" = some ⟨Ty.wei, Val.wei w'⟩ := by
    simp [env', LocalEnv.bind, decide_eq_true_eq]
  simp only [incrementBody, Stmt.eval]
  rw [ContractM.bind_apply_ok _ _ _ _ _ _ (eval_incrementLet_ok s w' hw hno),
      eval_incrementTail_ok s w' env' henv]
  simp [incrementOkResult, env']

private theorem eval_incrementBody_err (s : ContractState CounterStorage)
    (hov : ¬ s.storage.number.raw.toNat + 1 < 2 ^ 256) :
    Stmt.eval getField resolveError buildEvent setField incrementBody LocalEnv.empty s = .error CounterError.Overflow := by
  simp only [incrementBody, Stmt.eval]
  rw [ContractM.bind_apply_err _ _ _ _ (eval_incrementLet_err s hov)]

private theorem eval_incrementAst_ok (s : ContractState CounterStorage) (w' : Wei)
    (hpaused : s.storage.paused = false) (hno : s.storage.number.raw.toNat + 1 < 2 ^ 256)
    (hw : w' = ⟨BitVec.ofNat 256 (s.storage.number.raw.toNat + 1)⟩) :
    Stmt.eval getField resolveError buildEvent setField incrementAst LocalEnv.empty s = .ok (incrementOkResult s w') := by
  simp only [incrementAst, Stmt.eval]
  rw [ContractM.bind_apply_ok _ _ _ _ _ _ (eval_incrementRequire_ok s hpaused)]
  rw [eval_incrementBody_ok s w' hno hw]
  simp [List.append_nil]

private theorem eval_incrementAst_err_paused (s : ContractState CounterStorage)
    (hp : s.storage.paused = true) :
    Stmt.eval getField resolveError buildEvent setField incrementAst LocalEnv.empty s = .error CounterError.Paused := by
  simp only [incrementAst, Stmt.eval]
  rw [ContractM.bind_apply_err _ _ _ _ (eval_incrementRequire_err s hp)]

private theorem eval_incrementAst_err_overflow (s : ContractState CounterStorage)
    (hpaused : s.storage.paused = false) (hov : ¬ s.storage.number.raw.toNat + 1 < 2 ^ 256) :
    Stmt.eval getField resolveError buildEvent setField incrementAst LocalEnv.empty s = .error CounterError.Overflow := by
  simp only [incrementAst, Stmt.eval]
  rw [ContractM.bind_apply_ok _ _ _ _ _ _ (eval_incrementRequire_ok s hpaused)]
  rw [eval_incrementBody_err s hov]

private theorem incrementViaAst_eq_run (s : ContractState CounterStorage) :
    incrementViaAst s = runIncrementEval s := by
  rw [incrementViaAst]
  cases hp : s.storage.paused with
  | true =>
    have hl := eval_incrementAst_err_paused s hp
    have hr : runIncrementEval s = .error CounterError.Paused := by
      unfold runIncrementEval; simp [hp]
    exact hl.trans hr.symm
  | false =>
    by_cases hno : s.storage.number.raw.toNat + 1 < 2 ^ 256
    · let w' : Wei := ⟨BitVec.ofNat 256 (s.storage.number.raw.toNat + 1)⟩
      have hl := eval_incrementAst_ok s w' hp hno rfl
      have hr : runIncrementEval s = .ok (incrementOkResult s w') := by
        unfold runIncrementEval
        simp only [hp, Bool.false_eq_true, if_false, if_pos hno, w', incrementOkResult]
      exact hl.trans hr.symm
    · have hl := eval_incrementAst_err_overflow s hp hno
      have hr : runIncrementEval s = .error CounterError.Overflow := by
        unfold runIncrementEval
        simp only [hp, Bool.false_eq_true, if_false, if_neg hno]
      exact hl.trans hr.symm

def pauseRequireOwner : Stmt :=
  Stmt.require (CoreExpr.eq Ty.address (CoreExpr.txField .caller) (CoreExpr.storageGet Ty.address "owner")) "NotOwner"

def pauseRequireNotPaused : Stmt := incrementRequire

@[simp] theorem pauseRequireNotPaused_def : pauseRequireNotPaused = incrementRequire := rfl

def pauseSet : Stmt :=
  Stmt.storageSet "paused" ⟨Ty.bool, CoreExpr.lit Ty.bool (.bool true)⟩

def pauseEmit : Stmt := Stmt.emit "Paused" []

def pauseTail : Stmt := Stmt.seq pauseSet pauseEmit

def pauseBody : Stmt := Stmt.seq pauseRequireNotPaused pauseTail

def pauseAst : Stmt := Stmt.seq pauseRequireOwner pauseBody

def unpauseRequireOwner : Stmt := pauseRequireOwner

@[simp] theorem unpauseRequireOwner_def : unpauseRequireOwner = pauseRequireOwner := rfl

def unpauseRequirePaused : Stmt :=
  Stmt.require (CoreExpr.storageGet Ty.bool "paused") "Paused"

def unpauseSet : Stmt :=
  Stmt.storageSet "paused" ⟨Ty.bool, CoreExpr.lit Ty.bool (.bool false)⟩

def unpauseEmit : Stmt := Stmt.emit "Unpaused" []

def unpauseTail : Stmt := Stmt.seq unpauseSet unpauseEmit

def unpauseBody : Stmt := Stmt.seq unpauseRequirePaused unpauseTail

def unpauseAst : Stmt := Stmt.seq unpauseRequireOwner unpauseBody

def pauseViaAst : CounterM LocalEnv :=
  Stmt.eval getField resolveError buildEvent setField pauseAst LocalEnv.empty

def pause : CounterM Unit := do
  let _ ← pauseViaAst
  pure ()

def unpauseViaAst : CounterM LocalEnv :=
  Stmt.eval getField resolveError buildEvent setField unpauseAst LocalEnv.empty

def unpause : CounterM Unit := do
  let _ ← unpauseViaAst
  pure ()

@[simp]
theorem runS_pause (s : ContractState CounterStorage) :
    runS pause s =
      match pauseViaAst s with
      | .error e => .error e
      | .ok (_, s', log) => .ok ((), s', log) :=
  runS_discard_env pauseViaAst s

@[simp]
theorem runS_unpause (s : ContractState CounterStorage) :
    runS unpause s =
      match unpauseViaAst s with
      | .error e => .error e
      | .ok (_, s', log) => .ok ((), s', log) :=
  runS_discard_env unpauseViaAst s

private def pauseOkResult (s : ContractState CounterStorage) :
    LocalEnv × ContractState CounterStorage × List CounterEvent :=
  (LocalEnv.empty, { s with storage := { s.storage with paused := true }}, [.Paused])

private def unpauseOkResult (s : ContractState CounterStorage) :
    LocalEnv × ContractState CounterStorage × List CounterEvent :=
  (LocalEnv.empty, { s with storage := { s.storage with paused := false }}, [.Unpaused])

private def runPauseEval (s : ContractState CounterStorage) :
    Except CounterError (LocalEnv × ContractState CounterStorage × List CounterEvent) :=
  if s.context.caller == s.storage.owner then
    if s.storage.paused then
      .error CounterError.Paused
    else
      .ok (pauseOkResult s)
  else
    .error CounterError.NotOwner

private def runUnpauseEval (s : ContractState CounterStorage) :
    Except CounterError (LocalEnv × ContractState CounterStorage × List CounterEvent) :=
  if s.context.caller == s.storage.owner then
    if s.storage.paused then
      .ok (unpauseOkResult s)
    else
      .error CounterError.Paused
  else
    .error CounterError.NotOwner

private theorem eval_pauseRequireOwner_ok (s : ContractState CounterStorage)
    (h : (s.context.caller == s.storage.owner) = true) :
    Stmt.eval getField resolveError buildEvent setField pauseRequireOwner LocalEnv.empty s = .ok (LocalEnv.empty, s, []) := by
  have hcond : Val.boolOf (Val.bool (s.context.caller == s.storage.owner)) = true := by
    simp [Val.boolOf_bool, h]
  simp only [pauseRequireOwner, Stmt.eval, Expr.eval, CoreExpr.eval, getField_owner, ContractM.caller,
             ContractM.bind_apply, ContractM.get, ContractM.pure_apply, Val.eq_addr,
             resolveError_notOwner, List.append_nil, hcond]
  simp [ContractM.pure_apply, List.append_nil]

private theorem eval_pauseRequireOwner_err (s : ContractState CounterStorage)
    (h : (s.context.caller == s.storage.owner) = false) :
    Stmt.eval getField resolveError buildEvent setField pauseRequireOwner LocalEnv.empty s = .error CounterError.NotOwner := by
  have hcond : Val.boolOf (Val.bool (s.context.caller == s.storage.owner)) = false := by
    simp [Val.boolOf_bool, h]
  simp only [pauseRequireOwner, Stmt.eval, Expr.eval, CoreExpr.eval, getField_owner, ContractM.caller,
             ContractM.bind_apply, ContractM.get, Val.eq_addr, resolveError_notOwner,
             ContractM.revertUser, ContractM.revertUser_apply, List.append_nil, hcond, if_false]
  simp [ContractM.revertUser_apply]

private theorem eval_pauseSet_ok (s : ContractState CounterStorage) (env : LocalEnv) :
    Stmt.eval getField resolveError buildEvent setField pauseSet env s =
      .ok (env, { s with storage := { s.storage with paused := true }}, []) := by
  simp [pauseSet, Stmt.eval, Expr.eval, CoreExpr.eval, setField_paused, ContractM.bind_apply,
        ContractM.modifyStorage, ContractM.pure_apply, List.append_nil]

private theorem eval_pauseEmit_ok (env : LocalEnv) (s' : ContractState CounterStorage) :
    Stmt.eval getField resolveError buildEvent setField pauseEmit env s' =
      .ok (env, s', [.Paused]) := by
  simp only [pauseEmit, Stmt.eval, List.mapM, List.mapM.loop, List.nil_append,
             List.reverseAux_nil, List.reverse, buildEvent_paused, ContractM.emit,
             ContractM.bind_apply, List.reverseAux_cons, List.append_nil]

private theorem eval_pauseTail_ok (s : ContractState CounterStorage) (env : LocalEnv) :
    Stmt.eval getField resolveError buildEvent setField pauseTail env s =
      .ok (env, { s with storage := { s.storage with paused := true }}, [.Paused]) := by
  simp only [pauseTail, Stmt.eval]
  rw [ContractM.bind_apply_ok _ _ _ _ _ _ (eval_pauseSet_ok s env)]
  rw [eval_pauseEmit_ok env ({ s with storage := { s.storage with paused := true }})]
  simp [List.append_nil]

private theorem eval_pauseBody_ok (s : ContractState CounterStorage)
    (hpaused : s.storage.paused = false) :
    Stmt.eval getField resolveError buildEvent setField pauseBody LocalEnv.empty s = .ok (pauseOkResult s) := by
  simp only [pauseBody, pauseRequireNotPaused, Stmt.eval, pauseRequireNotPaused_def]
  rw [ContractM.bind_apply_ok _ _ _ _ _ _ (eval_incrementRequire_ok s hpaused),
      eval_pauseTail_ok s LocalEnv.empty]
  simp [pauseOkResult]

private theorem eval_pauseBody_err (s : ContractState CounterStorage) (hp : s.storage.paused = true) :
    Stmt.eval getField resolveError buildEvent setField pauseBody LocalEnv.empty s = .error CounterError.Paused := by
  simp only [pauseBody, pauseRequireNotPaused, Stmt.eval, pauseRequireNotPaused_def]
  rw [ContractM.bind_apply_err _ _ _ _ (eval_incrementRequire_err s hp)]

private theorem eval_pauseAst_ok (s : ContractState CounterStorage)
    (howner : (s.context.caller == s.storage.owner) = true) (hpaused : s.storage.paused = false) :
    Stmt.eval getField resolveError buildEvent setField pauseAst LocalEnv.empty s = .ok (pauseOkResult s) := by
  simp only [pauseAst, Stmt.eval]
  rw [ContractM.bind_apply_ok _ _ _ _ _ _ (eval_pauseRequireOwner_ok s howner)]
  rw [eval_pauseBody_ok s hpaused]
  simp [List.append_nil]

private theorem eval_pauseAst_err_notOwner (s : ContractState CounterStorage)
    (h : (s.context.caller == s.storage.owner) = false) :
    Stmt.eval getField resolveError buildEvent setField pauseAst LocalEnv.empty s = .error CounterError.NotOwner := by
  simp only [pauseAst, Stmt.eval]
  rw [ContractM.bind_apply_err _ _ _ _ (eval_pauseRequireOwner_err s h)]

private theorem eval_pauseAst_err_paused (s : ContractState CounterStorage)
    (howner : (s.context.caller == s.storage.owner) = true) (hp : s.storage.paused = true) :
    Stmt.eval getField resolveError buildEvent setField pauseAst LocalEnv.empty s = .error CounterError.Paused := by
  simp only [pauseAst, Stmt.eval]
  rw [ContractM.bind_apply_ok _ _ _ _ _ _ (eval_pauseRequireOwner_ok s howner)]
  rw [eval_pauseBody_err s hp]

private theorem pauseViaAst_eq_run (s : ContractState CounterStorage) :
    pauseViaAst s = runPauseEval s := by
  rw [pauseViaAst]
  cases hb : (s.context.caller == s.storage.owner) with
  | true =>
    cases hp : s.storage.paused with
    | true =>
      have hl := eval_pauseAst_err_paused s hb hp
      have hr : runPauseEval s = .error CounterError.Paused := by
        unfold runPauseEval; simp [hb, hp]
      exact hl.trans hr.symm
    | false =>
      have hl := eval_pauseAst_ok s hb hp
      have hr : runPauseEval s = .ok (pauseOkResult s) := by
        unfold runPauseEval; simp [hb, hp]
      exact hl.trans hr.symm
  | false =>
    have hl := eval_pauseAst_err_notOwner s hb
    have hr : runPauseEval s = .error CounterError.NotOwner := by
      unfold runPauseEval; simp [hb]
    exact hl.trans hr.symm

private theorem eval_unpauseSet_ok (s : ContractState CounterStorage) (env : LocalEnv) :
    Stmt.eval getField resolveError buildEvent setField unpauseSet env s =
      .ok (env, { s with storage := { s.storage with paused := false }}, []) := by
  simp [unpauseSet, Stmt.eval, Expr.eval, CoreExpr.eval, setField_paused, ContractM.bind_apply,
        ContractM.modifyStorage, ContractM.pure_apply, List.append_nil]

private theorem eval_unpauseEmit_ok (env : LocalEnv) (s' : ContractState CounterStorage) :
    Stmt.eval getField resolveError buildEvent setField unpauseEmit env s' =
      .ok (env, s', [.Unpaused]) := by
  simp only [unpauseEmit, Stmt.eval, List.mapM, List.mapM.loop, List.nil_append,
             List.reverseAux_nil, List.reverse, buildEvent_unpaused, ContractM.emit,
             ContractM.bind_apply, List.reverseAux_cons, List.append_nil]

private theorem eval_unpauseTail_ok (s : ContractState CounterStorage) (env : LocalEnv) :
    Stmt.eval getField resolveError buildEvent setField unpauseTail env s =
      .ok (env, { s with storage := { s.storage with paused := false }}, [.Unpaused]) := by
  simp only [unpauseTail, Stmt.eval]
  rw [ContractM.bind_apply_ok _ _ _ _ _ _ (eval_unpauseSet_ok s env)]
  rw [eval_unpauseEmit_ok env ({ s with storage := { s.storage with paused := false }})]
  simp [List.append_nil]

private theorem eval_unpauseRequirePaused_ok (s : ContractState CounterStorage)
    (hp : s.storage.paused = true) :
    Stmt.eval getField resolveError buildEvent setField unpauseRequirePaused LocalEnv.empty s = .ok (LocalEnv.empty, s, []) := by
  simp only [unpauseRequirePaused, Stmt.eval, Expr.eval, CoreExpr.eval, getField_paused, ContractM.bind_apply,
             ContractM.get, ContractM.pure_apply, resolveError_paused, List.append_nil,
             Val.boolOf_bool, hp]
  simp [ContractM.pure_apply, List.append_nil]

private theorem eval_unpauseRequirePaused_err (s : ContractState CounterStorage)
    (hp : s.storage.paused = false) :
    Stmt.eval getField resolveError buildEvent setField unpauseRequirePaused LocalEnv.empty s = .error CounterError.Paused := by
  simp only [unpauseRequirePaused, Stmt.eval, Expr.eval, CoreExpr.eval, getField_paused, ContractM.bind_apply,
             ContractM.get, resolveError_paused, ContractM.revertUser, ContractM.revertUser_apply,
             List.append_nil, Val.boolOf_bool, hp, if_false]
  simp [ContractM.revertUser_apply]

private theorem eval_unpauseBody_ok (s : ContractState CounterStorage) (hp : s.storage.paused = true) :
    Stmt.eval getField resolveError buildEvent setField unpauseBody LocalEnv.empty s = .ok (unpauseOkResult s) := by
  simp only [unpauseBody, Stmt.eval]
  rw [ContractM.bind_apply_ok _ _ _ _ _ _ (eval_unpauseRequirePaused_ok s hp),
      eval_unpauseTail_ok s LocalEnv.empty]
  simp [unpauseOkResult]

private theorem eval_unpauseBody_err (s : ContractState CounterStorage)
    (hp : s.storage.paused = false) :
    Stmt.eval getField resolveError buildEvent setField unpauseBody LocalEnv.empty s = .error CounterError.Paused := by
  simp only [unpauseBody, Stmt.eval]
  rw [ContractM.bind_apply_err _ _ _ _ (eval_unpauseRequirePaused_err s hp)]

private theorem eval_unpauseAst_ok (s : ContractState CounterStorage)
    (howner : (s.context.caller == s.storage.owner) = true) (hp : s.storage.paused = true) :
    Stmt.eval getField resolveError buildEvent setField unpauseAst LocalEnv.empty s = .ok (unpauseOkResult s) := by
  simp only [unpauseAst, unpauseRequireOwner_def, Stmt.eval]
  rw [ContractM.bind_apply_ok _ _ _ _ _ _ (eval_pauseRequireOwner_ok s howner)]
  rw [eval_unpauseBody_ok s hp]
  simp [List.append_nil]

private theorem eval_unpauseAst_err_notOwner (s : ContractState CounterStorage)
    (h : (s.context.caller == s.storage.owner) = false) :
    Stmt.eval getField resolveError buildEvent setField unpauseAst LocalEnv.empty s = .error CounterError.NotOwner := by
  simp only [unpauseAst, unpauseRequireOwner_def, Stmt.eval]
  rw [ContractM.bind_apply_err _ _ _ _ (eval_pauseRequireOwner_err s h)]

private theorem eval_unpauseAst_err_notPaused (s : ContractState CounterStorage)
    (howner : (s.context.caller == s.storage.owner) = true) (hp : s.storage.paused = false) :
    Stmt.eval getField resolveError buildEvent setField unpauseAst LocalEnv.empty s = .error CounterError.Paused := by
  simp only [unpauseAst, unpauseRequireOwner_def, Stmt.eval]
  rw [ContractM.bind_apply_ok _ _ _ _ _ _ (eval_pauseRequireOwner_ok s howner)]
  rw [eval_unpauseBody_err s hp]

private theorem unpauseViaAst_eq_run (s : ContractState CounterStorage) :
    unpauseViaAst s = runUnpauseEval s := by
  rw [unpauseViaAst]
  cases hb : (s.context.caller == s.storage.owner) with
  | true =>
    cases hp : s.storage.paused with
    | true =>
      have hl := eval_unpauseAst_ok s hb hp
      have hr : runUnpauseEval s = .ok (unpauseOkResult s) := by
        unfold runUnpauseEval; simp [hb, hp]
      exact hl.trans hr.symm
    | false =>
      have hl := eval_unpauseAst_err_notPaused s hb hp
      have hr : runUnpauseEval s = .error CounterError.Paused := by
        unfold runUnpauseEval; simp [hb, hp]
      exact hl.trans hr.symm
  | false =>
    have hl := eval_unpauseAst_err_notOwner s hb
    have hr : runUnpauseEval s = .error CounterError.NotOwner := by
      unfold runUnpauseEval; simp [hb]
    exact hl.trans hr.symm

end bridgeEval

def counterFn (name : Ident) (body : Stmt) : FunctionDef where
  name := name
  kind := .external
  params := []
  retTy := .unit
  body := body

def counterDef : ContractDef where
  name := "Counter"
  storage :=
    [("number", .wei, none), ("paused", .bool, some ⟨.bool, CoreExpr.lit Ty.bool (.bool false)⟩),
     ("owner", .address, none)]
  errors := ["Paused", "NotOwner", "Overflow"]
  events := [("Incremented", [("n", .wei)]), ("Paused", []), ("Unpaused", [])]
  functions :=
    [counterFn "increment" incrementAst, counterFn "pause" pauseAst,
     counterFn "unpause" unpauseAst]
  interfaces := []

/-- Compile layout for Yul / bytecode emission. -/
def stubEventTopic0 : Ident → Option Nat
  | "Incremented" => some 0x20d8a6f5a693f9d1d627a598e8820f7a55ee74c183aa8f1a30e8d4e8dd9a8d84
  | name => some name.hash.toNat

def compileConfig : Config :=
  Compile.configFromContract counterDef stubEventTopic0

def incrementYul : String :=
  match Compile.stmtToYul compileConfig incrementAst with
  | .ok yul => yul
  | .error _ => ""

def counterBytecodeHex : String :=
  match Compile.contractToBytecodeHex counterDef stubEventTopic0 with
  | .ok hex => hex
  | .error _ => ""

theorem increment_increases_number_when_not_paused
    (s s' : ContractState CounterStorage)
    (log : List CounterEvent)
    (hpaused : ¬ s.storage.paused)
    (hno : s.storage.number.raw.toNat + 1 < 2 ^ 256)
    (h : runS increment s = .ok ((), s', log)) :
    s'.storage.number.raw.toNat = s.storage.number.raw.toNat + 1 := by
  rw [runS_increment] at h
  rw [incrementViaAst_eq_run s] at h
  simp only [runIncrementEval, hpaused, hno] at h
  cases h
  change (BitVec.ofNat 256 (BitVec.toNat s.storage.number.raw + 1)).toNat =
    BitVec.toNat s.storage.number.raw + 1
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hno

theorem increment_errors_when_paused
    (s : ContractState CounterStorage)
    (hp : s.storage.paused) :
    runS increment s = .error CounterError.Paused := by
  rw [runS_increment, incrementViaAst_eq_run s, runIncrementEval, if_pos hp]

theorem increment_does_not_change_paused
    (s s' : ContractState CounterStorage)
    (log : List CounterEvent)
    (hpaused : ¬ s.storage.paused)
    (hno : s.storage.number.raw.toNat + 1 < 2 ^ 256)
    (h : runS increment s = .ok ((), s', log)) :
    s'.storage.paused = s.storage.paused := by
  rw [runS_increment] at h
  rw [incrementViaAst_eq_run s] at h
  simp only [runIncrementEval, hpaused, hno] at h
  cases h
  rfl

theorem increment_does_not_change_owner
    (s s' : ContractState CounterStorage)
    (log : List CounterEvent)
    (hpaused : ¬ s.storage.paused)
    (hno : s.storage.number.raw.toNat + 1 < 2 ^ 256)
    (h : runS increment s = .ok ((), s', log)) :
    s'.storage.owner = s.storage.owner := by
  rw [runS_increment] at h
  rw [incrementViaAst_eq_run s] at h
  simp only [runIncrementEval, hpaused, hno] at h
  cases h
  rfl

theorem increment_emits_incremented
    (s s' : ContractState CounterStorage)
    (log : List CounterEvent)
    (hpaused : ¬ s.storage.paused)
    (hno : s.storage.number.raw.toNat + 1 < 2 ^ 256)
    (h : runS increment s = .ok ((), s', log)) :
    log = [CounterEvent.Incremented s'.storage.number] := by
  rw [runS_increment] at h
  rw [incrementViaAst_eq_run s] at h
  simp only [runIncrementEval, hpaused, hno] at h
  cases h
  rfl

theorem increment_reverts_on_overflow
    (s : ContractState CounterStorage)
    (hpaused : ¬ s.storage.paused)
    (hov : ¬ s.storage.number.raw.toNat + 1 < 2 ^ 256) :
    runS increment s = .error CounterError.Overflow := by
  rw [runS_increment, incrementViaAst_eq_run s, runIncrementEval, if_neg hpaused, if_neg hov]

theorem pause_sets_paused_when_owner
    (s s' : ContractState CounterStorage) (log : List CounterEvent)
    (howner : s.context.caller == s.storage.owner)
    (hpaused : ¬ s.storage.paused)
    (h : runS pause s = .ok ((), s', log)) :
    s'.storage.paused = true := by
  rw [runS_pause] at h
  rw [pauseViaAst_eq_run s] at h
  simp only [runPauseEval, howner, hpaused] at h
  cases h
  rfl

theorem pause_errors_when_not_owner
    (s : ContractState CounterStorage)
    (h : ¬ s.context.caller == s.storage.owner) :
    runS pause s = .error CounterError.NotOwner := by
  rw [runS_pause, pauseViaAst_eq_run s, runPauseEval, if_neg h]

theorem pause_errors_when_already_paused
    (s : ContractState CounterStorage)
    (howner : s.context.caller == s.storage.owner)
    (hp : s.storage.paused) :
    runS pause s = .error CounterError.Paused := by
  rw [runS_pause, pauseViaAst_eq_run s, runPauseEval, if_pos howner, if_pos hp]

theorem unpause_clears_paused_when_owner
    (s s' : ContractState CounterStorage) (log : List CounterEvent)
    (howner : s.context.caller == s.storage.owner)
    (hp : s.storage.paused)
    (h : runS unpause s = .ok ((), s', log)) :
    s'.storage.paused = false := by
  rw [runS_unpause] at h
  rw [unpauseViaAst_eq_run s] at h
  simp only [runUnpauseEval, howner, hp] at h
  cases h
  rfl

end Counter
