import Lsc.Compiler.Proof.CoreExt
import Lsc.Lang.CoreProof

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

/-!
`α.ofState` preservation along local `stepOp` / `noExt` `Step`.
Non-halting `stepOp` is proved once (`stepOp_ok_ofState`); `step_ofState` is
structural induction on `Step`.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc hiding Op Stmt

theorem ofState_of_CallWorld {G} (α : Abs G) {st st' : EvmState} {a : Address}
    (h : CallWorld.ofState st' = CallWorld.ofState st) :
    α.ofState st' a = α.ofState st a :=
  (α.ofState_proj st' a).trans ((congrArg (α.ofWorld · a) h).trans (α.ofState_proj st a).symm)

theorem ofState_halt {G} (α : Abs G) (st : EvmState) (h : Option (HaltKind × List UInt8))
    (a : Address) :
    α.ofState { st with halted := h } a = α.ofState st a := by
  apply ofState_of_CallWorld
  simp [CallWorld.ofState]

/-- Local `sstore` does not change a **foreign** ghost (`Abs.ignoresLocal`
allows `storageOf` at the executing address to move). -/
theorem ofState_of_sstore {G} {α : Abs G} (hign : α.ignoresLocal)
    (st : EvmState) (slot val : U256) (a : Address)
    (hne : accountKey (BitVec.ofNat 256 (a : Nat)) ≠ accountKey st.env.address) :
    α.ofState
      { st with
        storage := upd st.storage slot val
        env := { st.env with
          storageOf := updAccount st.env.storageOf st.env.address slot val } } a =
      α.ofState st a := by
  refine hign st (upd st.storage slot val) st.transient
    (updAccount st.env.storageOf st.env.address slot val) st.env.transientOf a hne ?_ ?_
  · intro addr k hne'
    simp [updAccount, hne']
  · intros; rfl

theorem ofState_appendLog {G} (α : Abs G) (st : EvmState)
    (topics : List U256) (p n : U256) (a : Address) :
    α.ofState (appendLog st topics p n) a = α.ofState st a := by
  apply ofState_of_CallWorld
  simp [CallWorld.ofState, appendLog, touchMemory]

theorem ofState_of_tstore {G} {α : Abs G} (hign : α.ignoresLocal)
    (st : EvmState) (slot val : U256) (a : Address)
    (hne : accountKey (BitVec.ofNat 256 (a : Nat)) ≠ accountKey st.env.address) :
    α.ofState
      { st with
        transient := upd st.transient slot val
        env := { st.env with
          transientOf := updAccount st.env.transientOf st.env.address slot val } } a =
      α.ofState st a := by
  refine hign st st.storage (upd st.transient slot val)
    st.env.storageOf (updAccount st.env.transientOf st.env.address slot val) a hne ?_ ?_
  · intros; rfl
  · intro addr k hne'
    simp [updAccount, hne']

theorem hfr_of_addr {a : Address} {st st' : EvmState}
    (hfr : accountKey (BitVec.ofNat 256 (a : Nat)) ≠ accountKey st.env.address)
    (h : st'.env.address = st.env.address) :
    accountKey (BitVec.ofNat 256 (a : Nat)) ≠ accountKey st'.env.address := by
  rwa [h]

/-- Result machine state of a `Res`. -/
def resState {D : Dialect} : Res D → D.State
  | .eres (.vals _ st) => st
  | .eres (.halt st) => st
  | .sres _ st _ => st

theorem ofState_touchMemory {G} (α : Abs G) (st : EvmState) (p n : Nat) (a : Address) :
    α.ofState (touchMemory st p n) a = α.ofState st a := by
  apply ofState_of_CallWorld
  simp [CallWorld.ofState, touchMemory]

theorem some_ok_state {xs ys : List U256} {s s' : EvmState}
    (h : some (BuiltinResult.ok xs s) = some (BuiltinResult.ok ys s')) :
    s' = s := by
  injection h with h'
  injection h' with _ hs
  exact hs.symm

theorem not_none_some {β} {x : β}
    (h : (none : Option β) = some x) : False := by
  cases h

theorem not_halt_ok {rets : List U256} {stH st' : EvmState}
    (h : BuiltinResult.halt stH = BuiltinResult.ok rets st') : False := by
  cases h

/-- Non-halting `stepOp` leaves a **foreign** `α.ofState` unchanged (`ignoresLocal`
for `sstore`/`tstore`) and does not retarget `env.address`. -/
theorem stepOp_ok_ofState {G} {α : Abs G} (hign : α.ignoresLocal)
    {op : EVM.Op} {args : List U256} {st : EvmState} {rets : List U256} {st' : EvmState}
    (h : stepOp op args st = some (.ok rets st')) (a : Address)
    (hne : accountKey (BitVec.ofNat 256 (a : Nat)) ≠ accountKey st.env.address) :
    α.ofState st' a = α.ofState st a ∧ st'.env.address = st.env.address := by
  cases op
  -- `all_goals (try t)` not `try all_goals t`: one failing goal must not roll back the rest.
  all_goals (try simp [stepOp, un, bin, ter, rd0, rd1, guardStatic] at h)
  all_goals (try split at h)
  all_goals (try split at h)
  all_goals (try exact (not_none_some h).elim)
  all_goals (try exact (not_halt_ok (Option.some.inj h)).elim)
  all_goals (try (have hst := some_ok_state h; subst hst))
  all_goals (try exact ⟨rfl, rfl⟩)
  all_goals (try exact ⟨ofState_of_sstore hign st _ _ a hne, rfl⟩)
  all_goals (try exact ⟨ofState_of_tstore hign st _ _ a hne, rfl⟩)
  all_goals (try exact ⟨ofState_appendLog α st _ _ _ a, by simp [appendLog, touchMemory]⟩)
  all_goals (try exact ⟨ofState_touchMemory α st _ _ a, by simp [touchMemory]⟩)
  all_goals (try exact ⟨ofState_of_CallWorld α (by
      simp [CallWorld.ofState, touchMemory, touchMemory2, appendLog]), by
      simp [touchMemory, touchMemory2, appendLog]⟩)

theorem some_halt_state {s s' : EvmState}
    (h : (some (BuiltinResult.halt s) : Option (BuiltinResult U256 EvmState)) =
          some (BuiltinResult.halt s')) :
    s' = s := by
  injection h with h'
  injection h' with hs
  exact hs.symm

theorem noExt_all_loop {c post body}
    (hc : noExtExpr c = true) (hp : noExtBlock post = true) (hb : noExtBlock body = true) :
    NoExternalOps (.loop c post body) := by
  simp [NoExternalOps, noExtCode, hc, hp, hb]

/-- Halting `stepOp` other than `selfdestruct` leaves `α.ofState` unchanged
and does not retarget `env.address`. -/
theorem stepOp_halt_ofState {G} {α : Abs G} (hign : α.ignoresLocal)
    {op : EVM.Op} {args : List U256} {st st' : EvmState}
    (h : stepOp op args st = some (.halt st')) (a : Address)
    (hnsd : op ≠ .selfdestruct) :
    α.ofState st' a = α.ofState st a ∧ st'.env.address = st.env.address := by
  cases op
  all_goals (try exact (hnsd rfl).elim)
  all_goals (try simp [stepOp, un, bin, ter, rd0, rd1, guardStatic] at h)
  all_goals (try split at h)
  all_goals (try split at h)
  all_goals (try exact (not_none_some h).elim)
  all_goals (try exact (not_halt_ok (Option.some.inj h).symm).elim)
  all_goals (try (have hst := some_halt_state h; subst hst))
  all_goals (try exact ⟨ofState_halt α st _ a, rfl⟩)
  all_goals (try exact ⟨(ofState_halt α (touchMemory st _ _) _ a).trans
      (ofState_touchMemory α st _ _ a), by simp [touchMemory]⟩)

theorem step_ok_ofState {G} {α : Abs G} (hign : α.ignoresLocal)
    {funs : FunEnv evm} {V : VEnv evm} {st : EvmState} {code : Code evm.Op}
    {res : Res evm} (h : Step evm funs V st code res) (a : Address)
    (hfr : accountKey (BitVec.ofNat 256 (a : Nat)) ≠ accountKey st.env.address) :
    (∀ vs st', res = Res.eres (EResult.vals vs st') →
      α.ofState st' a = α.ofState st a ∧ st'.env.address = st.env.address) ∧
    (∀ V' st' o, res = Res.sres V' st' o → o ≠ Outcome.halt →
      α.ofState st' a = α.ofState st a ∧ st'.env.address = st.env.address) := by
  revert hfr
  induction h generalizing a with
  | lit | var | argsNil =>
    intro _hfr
    constructor
    · intro vs st' heq; cases heq; exact ⟨rfl, rfl⟩
    · intro V' st' o heq; cases heq
  | funDef | letZero | seqNil | «break» | «continue» | «leave» =>
    intro _hfr
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq _; cases heq; exact ⟨rfl, rfl⟩
  | builtinOk hargs hbu ih =>
    intro hfr
    constructor
    · intro vs st' heq
      injection heq with hr; injection hr with _ hst; subst hst
      have ⟨hαArgs, haddrArgs⟩ := (ih a hfr).1 _ _ rfl
      have ⟨hαOp, haddrOp⟩ :=
        stepOp_ok_ofState hign hbu a (hfr_of_addr hfr (by simpa [resState] using haddrArgs))
      exact ⟨hαOp.trans hαArgs, haddrOp.trans haddrArgs⟩
    · intro _ _ _ heq; cases heq
  | builtinHalt | builtinArgsHalt | callHalt | callArgsHalt
  | argsRestHalt | argsHeadHalt =>
    intro _hfr
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq; cases heq
  | callOk hargs hlk hlen hbody ho ihArgs ihBody =>
    intro hfr
    constructor
    · intro vs st' heq
      injection heq with hr; injection hr with _ hst; subst hst
      have ⟨hαArgs, haddrArgs⟩ := (ihArgs a hfr).1 _ _ rfl
      rcases ho with hn | hl
      · subst hn
        have ⟨hαB, haddrB⟩ :=
          (ihBody a (hfr_of_addr hfr (by simpa [resState] using haddrArgs))).2 _ _ _ rfl (by intro hh; cases hh)
        exact ⟨hαB.trans hαArgs, haddrB.trans haddrArgs⟩
      · subst hl
        have ⟨hαB, haddrB⟩ :=
          (ihBody a (hfr_of_addr hfr (by simpa [resState] using haddrArgs))).2 _ _ _ rfl (by intro hh; cases hh)
        exact ⟨hαB.trans hαArgs, haddrB.trans haddrArgs⟩
    · intro _ _ _ heq; cases heq
  | argsCons hrest hhead ihRest ihHead =>
    intro hfr
    constructor
    · intro vs st' heq
      injection heq with hr; injection hr with _ hst; subst hst
      have ⟨hαR, haddrR⟩ := (ihRest a hfr).1 _ _ rfl
      have ⟨hαH, haddrH⟩ := (ihHead a (hfr_of_addr hfr (by simpa [resState] using haddrR))).1 _ _ rfl
      exact ⟨hαH.trans hαR, haddrH.trans haddrR⟩
    · intro _ _ _ heq; cases heq
  | block hbody ih =>
    intro hfr
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq ho; cases heq; exact (ih a hfr).2 _ _ _ rfl ho
  | letVal he _ ih | assignVal he _ ih | exprStmt he ih =>
    intro hfr
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq _; cases heq; exact (ih a hfr).1 _ _ rfl
  | letHalt | assignHalt | exprStmtHalt | ifHalt | switchHalt
  | forInitHalt | loopCondHalt | loopPostHalt | loopBodyHalt =>
    intro _hfr
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq ho; cases heq; exact (ho rfl).elim
  | ifTrue he _ hbody ihE ihB | switchExec he hbody ihE ihB =>
    intro hfr
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq ho; cases heq
      have ⟨hαE, haddrE⟩ := (ihE a hfr).1 _ _ rfl
      have ⟨hαB, haddrB⟩ := (ihB a (hfr_of_addr hfr (by simpa [resState] using haddrE))).2 _ _ _ rfl ho
      exact ⟨hαB.trans hαE, haddrB.trans haddrE⟩
  | ifFalse he _ ih | loopDone he _ ih =>
    intro hfr
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq _; cases heq; exact (ih a hfr).1 _ _ rfl
  | forLoop hi hl ihI ihL =>
    intro hfr
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq ho; cases heq
      have ⟨hαI, haddrI⟩ := (ihI a hfr).2 _ _ _ rfl (by intro hh; cases hh)
      have ⟨hαL, haddrL⟩ := (ihL a (hfr_of_addr hfr (by simpa [resState] using haddrI))).2 _ _ _ rfl ho
      exact ⟨hαL.trans hαI, haddrL.trans haddrI⟩
  | seqCons hs hr ihs ihr =>
    intro hfr
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq ho; cases heq
      have ⟨hαS, haddrS⟩ := (ihs a hfr).2 _ _ _ rfl (by intro hh; cases hh)
      have ⟨hαR, haddrR⟩ := (ihr a (hfr_of_addr hfr (by simpa [resState] using haddrS))).2 _ _ _ rfl ho
      exact ⟨hαR.trans hαS, haddrR.trans haddrS⟩
  | seqStop hs _ ih =>
    intro hfr
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq ho; cases heq; exact (ih a hfr).2 _ _ _ rfl ho
  | loopStep he hne hbody hob hp hrest ihE ihB ihP ihR =>
    intro hfr
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq ho; cases heq
      have ⟨hαE, haddrE⟩ := (ihE a hfr).1 _ _ rfl
      rcases hob with hn | hc
      · subst hn
        have ⟨hαB, haddrB⟩ :=
          (ihB a (hfr_of_addr hfr (by simpa [resState] using haddrE))).2 _ _ _ rfl (by intro hh; cases hh)
        have ⟨hαP, haddrP⟩ :=
          (ihP a (hfr_of_addr hfr (by simpa [resState] using haddrB.trans haddrE))).2 _ _ _ rfl (by intro hh; cases hh)
        have ⟨hαR, haddrR⟩ :=
          (ihR a (hfr_of_addr hfr (by simpa [resState] using haddrP.trans (haddrB.trans haddrE)))).2 _ _ _ rfl ho
        exact ⟨hαR.trans (hαP.trans (hαB.trans hαE)),
          haddrR.trans (haddrP.trans (haddrB.trans haddrE))⟩
      · subst hc
        have ⟨hαB, haddrB⟩ :=
          (ihB a (hfr_of_addr hfr (by simpa [resState] using haddrE))).2 _ _ _ rfl (by intro hh; cases hh)
        have ⟨hαP, haddrP⟩ :=
          (ihP a (hfr_of_addr hfr (by simpa [resState] using haddrB.trans haddrE))).2 _ _ _ rfl (by intro hh; cases hh)
        have ⟨hαR, haddrR⟩ :=
          (ihR a (hfr_of_addr hfr (by simpa [resState] using haddrP.trans (haddrB.trans haddrE)))).2 _ _ _ rfl ho
        exact ⟨hαR.trans (hαP.trans (hαB.trans hαE)),
          haddrR.trans (haddrP.trans (haddrB.trans haddrE))⟩
  | loopBreak he _ hbody ihE ihB | loopLeave he _ hbody ihE ihB =>
    intro hfr
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq _; cases heq
      have ⟨hαE, haddrE⟩ := (ihE a hfr).1 _ _ rfl
      have ⟨hαB, haddrB⟩ :=
        (ihB a (hfr_of_addr hfr (by simpa [resState] using haddrE))).2 _ _ _ rfl (by intro hh; cases hh)
      exact ⟨hαB.trans hαE, haddrB.trans haddrE⟩

theorem execStmts_normal_ofState {G} {α : Abs G} (hign : α.ignoresLocal)
    {funs : FunEnv evm} {V : VEnv evm} {st : EvmState} {ss : YBlock}
    {V' : VEnv evm} {st' : EvmState}
    (h : ExecStmts evm funs V st ss V' st' .normal) (a : Address)
    (hfr : accountKey (BitVec.ofNat 256 (a : Nat)) ≠ accountKey st.env.address) :
    α.ofState st' a = α.ofState st a :=
  ((step_ok_ofState hign h a hfr).2 V' st' .normal rfl (by intro hh; cases hh)).1

/-- `α.ofState` along any `noExt` `Step` (`selfdestruct` excluded by `noExtOp`).
Non-halting `stepOp` preserves the `ignoresLocal` projection once
(`stepOp_ok_ofState`); the rest is structural induction on `Step`. -/
theorem step_ofState {calls : ExternalCalls} {G} {α : Abs G} (hign : α.ignoresLocal)
    {funs : FunEnv (yulD calls)} {V : VEnv (yulD calls)} {st : EvmState}
    {code : Code YOp} {res : Res (yulD calls)}
    (h : Step (yulD calls) funs V st code res) (a : Address)
    (hfuns : noExtFuns funs = true) (hcode : NoExternalOps code)
    (hfr : accountKey (BitVec.ofNat 256 (a : Nat)) ≠ accountKey st.env.address) :
    α.ofState (resState res) a = α.ofState st a ∧
      (resState res).env.address = st.env.address := by
  revert hfuns hcode hfr
  induction h generalizing a with
  | lit | var | argsNil | funDef | letZero | seqNil | «break» | «continue» | «leave» =>
    intro _ _ _; exact ⟨rfl, rfl⟩
  | builtinOk _hargs hbu ih =>
    intro hfuns hcode hfr
    have ⟨hop', hargs'⟩ := noExt_expr_builtin (noExt_code_expr hcode)
    have ⟨hαArgs, haddrArgs⟩ := ih a hfuns (noExt_all_args hargs') hfr
    have ⟨hαOp, haddrOp⟩ :=
      stepOp_ok_ofState hign (builtin_descend hop' hbu) a (hfr_of_addr hfr (by simpa [resState] using haddrArgs))
    exact ⟨hαOp.trans hαArgs, haddrOp.trans haddrArgs⟩
  | builtinHalt _hargs hbu ih =>
    intro hfuns hcode hfr
    have ⟨hop', hargs'⟩ := noExt_expr_builtin (noExt_code_expr hcode)
    have ⟨hαArgs, haddrArgs⟩ := ih a hfuns (noExt_all_args hargs') hfr
    have ⟨hαOp, haddrOp⟩ :=
      stepOp_halt_ofState hign (builtin_descend hop' hbu) a (by
        intro hopEq; subst hopEq; simp [noExtOp] at hop')
    exact ⟨hαOp.trans hαArgs, haddrOp.trans haddrArgs⟩
  | builtinArgsHalt _hargs ih =>
    intro hfuns hcode hfr
    have ⟨_, hargs'⟩ := noExt_expr_builtin (noExt_code_expr hcode)
    exact ih a hfuns (noExt_all_args hargs') hfr
  | callOk _hargs hlu _hln _hbody _ho ihArgs ihBody =>
    intro hfuns hcode hfr
    have hargs' := noExt_expr_call (noExt_code_expr hcode)
    obtain ⟨hbod, hcenv⟩ := lookupFun_noExt hfuns hlu
    have ⟨hαA, haddrA⟩ := ihArgs a hfuns (noExt_all_args hargs') hfr
    have ⟨hαB, haddrB⟩ :=
      ihBody a hcenv (noExt_all_block_stmt hbod) (hfr_of_addr hfr (by simpa [resState] using haddrA))
    exact ⟨hαB.trans hαA, haddrB.trans haddrA⟩
  | callHalt _hargs hlu _hln _hbody ihArgs ihBody =>
    intro hfuns hcode hfr
    have hargs' := noExt_expr_call (noExt_code_expr hcode)
    obtain ⟨hbod, hcenv⟩ := lookupFun_noExt hfuns hlu
    have ⟨hαA, haddrA⟩ := ihArgs a hfuns (noExt_all_args hargs') hfr
    have ⟨hαB, haddrB⟩ :=
      ihBody a hcenv (noExt_all_block_stmt hbod) (hfr_of_addr hfr (by simpa [resState] using haddrA))
    exact ⟨hαB.trans hαA, haddrB.trans haddrA⟩
  | callArgsHalt _hargs ih =>
    intro hfuns hcode hfr
    exact ih a hfuns (noExt_all_args (noExt_expr_call (noExt_code_expr hcode))) hfr
  | argsCons _hrest _hhead ihRest ihHead =>
    intro hfuns hcode hfr
    have ⟨he', hrest'⟩ := noExt_args_cons (noExt_code_args hcode)
    have ⟨hαR, haddrR⟩ := ihRest a hfuns (noExt_all_args hrest') hfr
    have ⟨hαH, haddrH⟩ := ihHead a hfuns (noExt_all_expr he') (hfr_of_addr hfr (by simpa [resState] using haddrR))
    exact ⟨hαH.trans hαR, haddrH.trans haddrR⟩
  | argsRestHalt _hrest ih =>
    intro hfuns hcode hfr
    have ⟨_, hrest'⟩ := noExt_args_cons (noExt_code_args hcode)
    exact ih a hfuns (noExt_all_args hrest') hfr
  | argsHeadHalt _hrest _he ihRest ihHead =>
    intro hfuns hcode hfr
    have ⟨he', hrest'⟩ := noExt_args_cons (noExt_code_args hcode)
    have ⟨hαR, haddrR⟩ := ihRest a hfuns (noExt_all_args hrest') hfr
    have ⟨hαH, haddrH⟩ := ihHead a hfuns (noExt_all_expr he') (hfr_of_addr hfr (by simpa [resState] using haddrR))
    exact ⟨hαH.trans hαR, haddrH.trans haddrR⟩
  | block _hbody ih =>
    intro hfuns hcode hfr
    have hb := noExt_stmt_block (noExt_code_stmt hcode)
    exact ih a (noExtFuns_hoist_cons hb hfuns) (noExt_all_stmts hb) hfr
  | letVal _he _hlen ih | letHalt _he ih =>
    intro hfuns hcode hfr
    exact ih a hfuns (noExt_all_expr (noExt_stmt_let (noExt_code_stmt hcode))) hfr
  | assignVal _he _hlen ih | assignHalt _he ih =>
    intro hfuns hcode hfr
    exact ih a hfuns (noExt_all_expr (noExt_stmt_assign (noExt_code_stmt hcode))) hfr
  | exprStmt _he ih | exprStmtHalt _he ih =>
    intro hfuns hcode hfr
    exact ih a hfuns (noExt_all_expr (noExt_stmt_expr (noExt_code_stmt hcode))) hfr
  | ifHalt _he ih =>
    intro hfuns hcode hfr
    exact ih a hfuns (noExt_all_expr (noExt_stmt_cond (noExt_code_stmt hcode)).1) hfr
  | switchHalt _he ih =>
    intro hfuns hcode hfr
    exact ih a hfuns (noExt_all_expr (noExt_stmt_switch (noExt_code_stmt hcode)).1) hfr
  | loopCondHalt _he ih =>
    intro hfuns hcode hfr
    exact ih a hfuns (noExt_all_expr (noExt_code_loop hcode).1) hfr
  | ifTrue _he _hne _hbody ihE ihB =>
    intro hfuns hcode hfr
    have ⟨hc, hb⟩ := noExt_stmt_cond (noExt_code_stmt hcode)
    have ⟨hαE, haddrE⟩ := ihE a hfuns (noExt_all_expr hc) hfr
    have ⟨hαB, haddrB⟩ := ihB a hfuns (noExt_all_block_stmt hb) (hfr_of_addr hfr (by simpa [resState] using haddrE))
    exact ⟨hαB.trans hαE, haddrB.trans haddrE⟩
  | switchExec _he _hbody ihE ihB =>
    intro hfuns hcode hfr
    rename_i _funs _V _st _cnd cases dflt cv _st1 _V2 _st2 _o
    have ⟨hc, hcases, hd⟩ := noExt_stmt_switch (noExt_code_stmt hcode)
    have hsel := noExt_selectSwitch (calls := calls) (cv := cv) cases dflt hcases hd
    have ⟨hαE, haddrE⟩ := ihE a hfuns (noExt_all_expr hc) hfr
    have ⟨hαB, haddrB⟩ :=
      ihB a hfuns (noExt_all_block_stmt hsel) (hfr_of_addr hfr (by simpa [resState] using haddrE))
    exact ⟨hαB.trans hαE, haddrB.trans haddrE⟩
  | ifFalse _he _hz ih =>
    intro hfuns hcode hfr
    exact ih a hfuns (noExt_all_expr (noExt_stmt_cond (noExt_code_stmt hcode)).1) hfr
  | loopDone _he _hz ih =>
    intro hfuns hcode hfr
    exact ih a hfuns (noExt_all_expr (noExt_code_loop hcode).1) hfr
  | forLoop _hi _hl ihI ihL =>
    intro hfuns hcode hfr
    have ⟨hi', hc, hp, hb⟩ := noExt_stmt_for (noExt_code_stmt hcode)
    have hf' := noExtFuns_hoist_cons hi' hfuns
    have ⟨hαI, haddrI⟩ := ihI a hf' (noExt_all_stmts hi') hfr
    have ⟨hαL, haddrL⟩ :=
      ihL a hf' (noExt_all_loop hc hp hb) (hfr_of_addr hfr (by simpa [resState] using haddrI))
    exact ⟨hαL.trans hαI, haddrL.trans haddrI⟩
  | forInitHalt _hi ih =>
    intro hfuns hcode hfr
    have ⟨hi', _, _, _⟩ := noExt_stmt_for (noExt_code_stmt hcode)
    exact ih a (noExtFuns_hoist_cons hi' hfuns) (noExt_all_stmts hi') hfr
  | seqCons _hs _hr ihs ihr =>
    intro hfuns hcode hfr
    have ⟨hs', hr'⟩ := noExt_block_cons (noExt_code_stmts hcode)
    have ⟨hαS, haddrS⟩ := ihs a hfuns (noExt_all_stmt hs') hfr
    have ⟨hαR, haddrR⟩ := ihr a hfuns (noExt_all_stmts hr') (hfr_of_addr hfr (by simpa [resState] using haddrS))
    exact ⟨hαR.trans hαS, haddrR.trans haddrS⟩
  | seqStop _hs _hne ih =>
    intro hfuns hcode hfr
    have ⟨hs', _⟩ := noExt_block_cons (noExt_code_stmts hcode)
    exact ih a hfuns (noExt_all_stmt hs') hfr
  | loopStep _he _hne _hbody _ho _hp _hrest ihE ihB ihP ihR =>
    intro hfuns hcode hfr
    have ⟨hc, hp', hb'⟩ := noExt_code_loop hcode
    have ⟨hαE, haddrE⟩ := ihE a hfuns (noExt_all_expr hc) hfr
    have ⟨hαB, haddrB⟩ :=
      ihB a hfuns (noExt_all_block_stmt hb') (hfr_of_addr hfr (by simpa [resState] using haddrE))
    have ⟨hαP, haddrP⟩ :=
      ihP a hfuns (noExt_all_block_stmt hp') (hfr_of_addr hfr (by simpa [resState] using haddrB.trans haddrE))
    have ⟨hαR, haddrR⟩ := ihR a hfuns hcode (hfr_of_addr hfr (by simpa [resState] using haddrP.trans (haddrB.trans haddrE)))
    exact ⟨hαR.trans (hαP.trans (hαB.trans hαE)),
      haddrR.trans (haddrP.trans (haddrB.trans haddrE))⟩
  | loopPostHalt _he _hne _hbody _ho _hp ihE ihB ihP =>
    intro hfuns hcode hfr
    have ⟨hc, hp', hb'⟩ := noExt_code_loop hcode
    have ⟨hαE, haddrE⟩ := ihE a hfuns (noExt_all_expr hc) hfr
    have ⟨hαB, haddrB⟩ :=
      ihB a hfuns (noExt_all_block_stmt hb') (hfr_of_addr hfr (by simpa [resState] using haddrE))
    have ⟨hαP, haddrP⟩ :=
      ihP a hfuns (noExt_all_block_stmt hp') (hfr_of_addr hfr (by simpa [resState] using haddrB.trans haddrE))
    exact ⟨hαP.trans (hαB.trans hαE), haddrP.trans (haddrB.trans haddrE)⟩
  | loopBreak _he _hne _hbody ihE ihB | loopLeave _he _hne _hbody ihE ihB
  | loopBodyHalt _he _hne _hbody ihE ihB =>
    intro hfuns hcode hfr
    have ⟨hc, _, hb'⟩ := noExt_code_loop hcode
    have ⟨hαE, haddrE⟩ := ihE a hfuns (noExt_all_expr hc) hfr
    have ⟨hαB, haddrB⟩ :=
      ihB a hfuns (noExt_all_block_stmt hb') (hfr_of_addr hfr (by simpa [resState] using haddrE))
    exact ⟨hαB.trans hαE, haddrB.trans haddrE⟩

theorem ofState_noExt_halt {calls : ExternalCalls} {G} {α : Abs G}
    (hign : α.ignoresLocal)
    {funs : FunEnv (yulD calls)} {V : VEnv (yulD calls)} {st : EvmState} {ss : YBlock}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hfuns : noExtFuns funs = true) (hno : noExtBlock ss = true)
    (h : ExecStmts (yulD calls) funs V st ss V' st' o) (a : Address)
    (hfr : accountKey (BitVec.ofNat 256 (a : Nat)) ≠ accountKey st.env.address) :
    α.ofState st' a = α.ofState st a :=
  (step_ofState (calls := calls) hign h a hfuns (noExt_all_stmts hno) hfr).1

theorem foreign_of_ctx {a : Address} {ctx : Ctx} {st : EvmState}
    (hctx : ctxRel ctx st)
    (hne : accountKey (BitVec.ofNat 256 (a : Nat)) ≠ accountKey (BitVec.ofNat 256 ctx.self)) :
    accountKey (BitVec.ofNat 256 (a : Nat)) ≠ accountKey st.env.address := by
  simpa [ctxRel_address hctx] using hne

end Lsc.Compiler
