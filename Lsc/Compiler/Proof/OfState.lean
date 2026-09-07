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

/-- Local `sstore` does not change a foreign ghost (`Abs.ignoresLocal` allows
`storageOf` at the executing address to move). -/
theorem ofState_of_sstore {G} {α : Abs G} (hign : α.ignoresLocal)
    (st : EvmState) (slot val : U256) (a : Address) :
    α.ofState
      { st with
        storage := upd st.storage slot val
        env := { st.env with
          storageOf := updAccount st.env.storageOf st.env.address slot val } } a =
      α.ofState st a := by
  refine hign st (upd st.storage slot val) st.transient
    (updAccount st.env.storageOf st.env.address slot val) st.env.transientOf a ?_ ?_
  · intro addr k hne
    simp [updAccount, hne]
  · intros; rfl

theorem ofState_appendLog {G} (α : Abs G) (st : EvmState)
    (topics : List U256) (p n : U256) (a : Address) :
    α.ofState (appendLog st topics p n) a = α.ofState st a := by
  apply ofState_of_CallWorld
  simp [CallWorld.ofState, appendLog, touchMemory]

theorem ofState_of_tstore {G} {α : Abs G} (hign : α.ignoresLocal)
    (st : EvmState) (slot val : U256) (a : Address) :
    α.ofState
      { st with
        transient := upd st.transient slot val
        env := { st.env with
          transientOf := updAccount st.env.transientOf st.env.address slot val } } a =
      α.ofState st a := by
  refine hign st st.storage (upd st.transient slot val)
    st.env.storageOf (updAccount st.env.transientOf st.env.address slot val) a ?_ ?_
  · intros; rfl
  · intro addr k hne
    simp [updAccount, hne]

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

/-- Non-halting `stepOp` leaves `α.ofState` unchanged (`ignoresLocal` for `sstore`/`tstore`). -/
theorem stepOp_ok_ofState {G} {α : Abs G} (hign : α.ignoresLocal)
    {op : EVM.Op} {args : List U256} {st : EvmState} {rets : List U256} {st' : EvmState}
    (h : stepOp op args st = some (.ok rets st')) (a : Address) :
    α.ofState st' a = α.ofState st a := by
  cases op
  -- `all_goals (try t)` not `try all_goals t`: one failing goal must not roll back the rest.
  all_goals (try simp [stepOp, un, bin, ter, rd0, rd1, guardStatic] at h)
  all_goals (try split at h)
  all_goals (try split at h)
  all_goals (try exact (not_none_some h).elim)
  all_goals (try exact (not_halt_ok (Option.some.inj h)).elim)
  all_goals (try (have hst := some_ok_state h; subst hst))
  all_goals (try rfl)
  all_goals (try exact ofState_of_sstore hign st _ _ a)
  all_goals (try exact ofState_of_tstore hign st _ _ a)
  all_goals (try exact ofState_appendLog α st _ _ _ a)
  all_goals (try exact ofState_touchMemory α st _ _ a)
  all_goals (try apply ofState_of_CallWorld α)
  all_goals (try simp [CallWorld.ofState, touchMemory, touchMemory2, appendLog])

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

/-- Halting `stepOp` other than `selfdestruct` leaves `α.ofState` unchanged. -/
theorem stepOp_halt_ofState {G} {α : Abs G} (hign : α.ignoresLocal)
    {op : EVM.Op} {args : List U256} {st st' : EvmState}
    (h : stepOp op args st = some (.halt st')) (a : Address)
    (hnsd : op ≠ .selfdestruct) :
    α.ofState st' a = α.ofState st a := by
  cases op
  all_goals (try exact (hnsd rfl).elim)
  all_goals (try simp [stepOp, un, bin, ter, rd0, rd1, guardStatic] at h)
  all_goals (try split at h)
  all_goals (try split at h)
  all_goals (try exact (not_none_some h).elim)
  all_goals (try exact (not_halt_ok (Option.some.inj h).symm).elim)
  all_goals (try (have hst := some_halt_state h; subst hst))
  all_goals (try exact ofState_halt α st _ a)
  all_goals (try exact (ofState_halt α (touchMemory st _ _) _ a).trans (ofState_touchMemory α st _ _ a))

theorem step_ok_ofState {G} {α : Abs G} (hign : α.ignoresLocal)
    {funs : FunEnv evm} {V : VEnv evm} {st : EvmState} {code : Code evm.Op}
    {res : Res evm} (h : Step evm funs V st code res) (a : Address) :
    (∀ vs st', res = Res.eres (EResult.vals vs st') →
      α.ofState st' a = α.ofState st a) ∧
    (∀ V' st' o, res = Res.sres V' st' o → o ≠ Outcome.halt →
      α.ofState st' a = α.ofState st a) := by
  induction h generalizing a with
  | lit | var | argsNil =>
    constructor
    · intro vs st' heq; cases heq; rfl
    · intro V' st' o heq; cases heq
  | funDef | letZero | seqNil | «break» | «continue» | «leave» =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq _; cases heq; rfl
  | builtinOk hargs hbu ih =>
    constructor
    · intro vs st' heq
      injection heq with hr; injection hr with _ hst; subst hst
      exact (stepOp_ok_ofState hign hbu a).trans ((ih a).1 _ _ rfl)
    · intro _ _ _ heq; cases heq
  | builtinHalt | builtinArgsHalt | callHalt | callArgsHalt
  | argsRestHalt | argsHeadHalt =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq; cases heq
  | callOk hargs hlk hlen hbody ho ihArgs ihBody =>
    constructor
    · intro vs st' heq
      injection heq with hr; injection hr with _ hst; subst hst
      rcases ho with hn | hl
      · subst hn
        exact ((ihBody a).2 _ _ _ rfl (by intro hh; cases hh)).trans ((ihArgs a).1 _ _ rfl)
      · subst hl
        exact ((ihBody a).2 _ _ _ rfl (by intro hh; cases hh)).trans ((ihArgs a).1 _ _ rfl)
    · intro _ _ _ heq; cases heq
  | argsCons hrest hhead ihRest ihHead =>
    constructor
    · intro vs st' heq
      injection heq with hr; injection hr with _ hst; subst hst
      exact ((ihHead a).1 _ _ rfl).trans ((ihRest a).1 _ _ rfl)
    · intro _ _ _ heq; cases heq
  | block hbody ih =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq ho; cases heq; exact (ih a).2 _ _ _ rfl ho
  | letVal he _ ih | assignVal he _ ih | exprStmt he ih =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq _; cases heq; exact (ih a).1 _ _ rfl
  | letHalt | assignHalt | exprStmtHalt | ifHalt | switchHalt
  | forInitHalt | loopCondHalt | loopPostHalt | loopBodyHalt =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq ho; cases heq; exact (ho rfl).elim
  | ifTrue he _ hbody ihE ihB | switchExec he hbody ihE ihB =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq ho; cases heq
      exact ((ihB a).2 _ _ _ rfl ho).trans ((ihE a).1 _ _ rfl)
  | ifFalse he _ ih | loopDone he _ ih =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq _; cases heq; exact (ih a).1 _ _ rfl
  | forLoop hi hl ihI ihL =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq ho; cases heq
      exact ((ihL a).2 _ _ _ rfl ho).trans ((ihI a).2 _ _ _ rfl (by intro hh; cases hh))
  | seqCons hs hr ihs ihr =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq ho; cases heq
      exact ((ihr a).2 _ _ _ rfl ho).trans ((ihs a).2 _ _ _ rfl (by intro hh; cases hh))
  | seqStop hs _ ih =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq ho; cases heq; exact (ih a).2 _ _ _ rfl ho
  | loopStep he hne hbody hob hp hrest ihE ihB ihP ihR =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq ho; cases heq
      rcases hob with hn | hc
      · subst hn
        exact ((ihR a).2 _ _ _ rfl ho).trans
          (((ihP a).2 _ _ _ rfl (by intro hh; cases hh)).trans
            (((ihB a).2 _ _ _ rfl (by intro hh; cases hh)).trans ((ihE a).1 _ _ rfl)))
      · subst hc
        exact ((ihR a).2 _ _ _ rfl ho).trans
          (((ihP a).2 _ _ _ rfl (by intro hh; cases hh)).trans
            (((ihB a).2 _ _ _ rfl (by intro hh; cases hh)).trans ((ihE a).1 _ _ rfl)))
  | loopBreak he _ hbody ihE ihB | loopLeave he _ hbody ihE ihB =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq _; cases heq
      exact ((ihB a).2 _ _ _ rfl (by intro hh; cases hh)).trans ((ihE a).1 _ _ rfl)

theorem execStmts_normal_ofState {G} {α : Abs G} (hign : α.ignoresLocal)
    {funs : FunEnv evm} {V : VEnv evm} {st : EvmState} {ss : YBlock}
    {V' : VEnv evm} {st' : EvmState}
    (h : ExecStmts evm funs V st ss V' st' .normal) (a : Address) :
    α.ofState st' a = α.ofState st a :=
  (step_ok_ofState hign h a).2 V' st' .normal rfl (by intro hh; cases hh)

/-- Result machine state of a `Res`. -/
def resState {D : Dialect} : Res D → D.State
  | .eres (.vals _ st) => st
  | .eres (.halt st) => st
  | .sres _ st _ => st

/-- `α.ofState` along any `noExt` `Step` (`selfdestruct` excluded by `noExtOp`).
Non-halting `stepOp` preserves the `ignoresLocal` projection once
(`stepOp_ok_ofState`); the rest is structural induction on `Step`. -/
theorem step_ofState {calls : ExternalCalls} {G} {α : Abs G} (hign : α.ignoresLocal)
    {funs : FunEnv (yulD calls)} {V : VEnv (yulD calls)} {st : EvmState}
    {code : Code YOp} {res : Res (yulD calls)}
    (h : Step (yulD calls) funs V st code res) (a : Address)
    (hfuns : noExtFuns funs = true) (hcode : NoExternalOps code) :
    α.ofState (resState res) a = α.ofState st a := by
  revert hfuns hcode
  induction h generalizing a with
  | lit | var | argsNil | funDef | letZero | seqNil | «break» | «continue» | «leave» =>
    intro _ _; rfl
  | builtinOk _hargs hbu ih =>
    intro hfuns hcode
    have ⟨hop', hargs'⟩ := noExt_expr_builtin (noExt_code_expr hcode)
    exact (stepOp_ok_ofState hign (builtin_descend hop' hbu) a).trans
      (ih a hfuns (noExt_all_args hargs'))
  | builtinHalt _hargs hbu ih =>
    intro hfuns hcode
    have ⟨hop', hargs'⟩ := noExt_expr_builtin (noExt_code_expr hcode)
    exact (stepOp_halt_ofState hign (builtin_descend hop' hbu) a (by
        intro hopEq; subst hopEq; simp [noExtOp] at hop')).trans
      (ih a hfuns (noExt_all_args hargs'))
  | builtinArgsHalt _hargs ih =>
    intro hfuns hcode
    have ⟨_, hargs'⟩ := noExt_expr_builtin (noExt_code_expr hcode)
    exact ih a hfuns (noExt_all_args hargs')
  | callOk _hargs hlu _hln _hbody _ho ihArgs ihBody =>
    intro hfuns hcode
    have hargs' := noExt_expr_call (noExt_code_expr hcode)
    obtain ⟨hbod, hcenv⟩ := lookupFun_noExt hfuns hlu
    exact (ihBody a hcenv (noExt_all_block_stmt hbod)).trans
      (ihArgs a hfuns (noExt_all_args hargs'))
  | callHalt _hargs hlu _hln _hbody ihArgs ihBody =>
    intro hfuns hcode
    have hargs' := noExt_expr_call (noExt_code_expr hcode)
    obtain ⟨hbod, hcenv⟩ := lookupFun_noExt hfuns hlu
    exact (ihBody a hcenv (noExt_all_block_stmt hbod)).trans
      (ihArgs a hfuns (noExt_all_args hargs'))
  | callArgsHalt _hargs ih =>
    intro hfuns hcode
    exact ih a hfuns (noExt_all_args (noExt_expr_call (noExt_code_expr hcode)))
  | argsCons _hrest _hhead ihRest ihHead =>
    intro hfuns hcode
    have ⟨he', hrest'⟩ := noExt_args_cons (noExt_code_args hcode)
    exact (ihHead a hfuns (noExt_all_expr he')).trans
      (ihRest a hfuns (noExt_all_args hrest'))
  | argsRestHalt _hrest ih =>
    intro hfuns hcode
    have ⟨_, hrest'⟩ := noExt_args_cons (noExt_code_args hcode)
    exact ih a hfuns (noExt_all_args hrest')
  | argsHeadHalt _hrest _he ihRest ihHead =>
    intro hfuns hcode
    have ⟨he', hrest'⟩ := noExt_args_cons (noExt_code_args hcode)
    exact (ihHead a hfuns (noExt_all_expr he')).trans
      (ihRest a hfuns (noExt_all_args hrest'))
  | block _hbody ih =>
    intro hfuns hcode
    have hb := noExt_stmt_block (noExt_code_stmt hcode)
    exact ih a (noExtFuns_hoist_cons hb hfuns) (noExt_all_stmts hb)
  | letVal _he _hlen ih | letHalt _he ih =>
    intro hfuns hcode
    exact ih a hfuns (noExt_all_expr (noExt_stmt_let (noExt_code_stmt hcode)))
  | assignVal _he _hlen ih | assignHalt _he ih =>
    intro hfuns hcode
    exact ih a hfuns (noExt_all_expr (noExt_stmt_assign (noExt_code_stmt hcode)))
  | exprStmt _he ih | exprStmtHalt _he ih =>
    intro hfuns hcode
    exact ih a hfuns (noExt_all_expr (noExt_stmt_expr (noExt_code_stmt hcode)))
  | ifHalt _he ih =>
    intro hfuns hcode
    exact ih a hfuns (noExt_all_expr (noExt_stmt_cond (noExt_code_stmt hcode)).1)
  | switchHalt _he ih =>
    intro hfuns hcode
    exact ih a hfuns (noExt_all_expr (noExt_stmt_switch (noExt_code_stmt hcode)).1)
  | loopCondHalt _he ih =>
    intro hfuns hcode
    exact ih a hfuns (noExt_all_expr (noExt_code_loop hcode).1)
  | ifTrue _he _hne _hbody ihE ihB =>
    intro hfuns hcode
    have ⟨hc, hb⟩ := noExt_stmt_cond (noExt_code_stmt hcode)
    exact (ihB a hfuns (noExt_all_block_stmt hb)).trans
      (ihE a hfuns (noExt_all_expr hc))
  | switchExec _he _hbody ihE ihB =>
    intro hfuns hcode
    rename_i _funs _V _st _cnd cases dflt cv _st1 _V2 _st2 _o
    have ⟨hc, hcases, hd⟩ := noExt_stmt_switch (noExt_code_stmt hcode)
    have hsel := noExt_selectSwitch (calls := calls) (cv := cv) cases dflt hcases hd
    exact (ihB a hfuns (noExt_all_block_stmt hsel)).trans
      (ihE a hfuns (noExt_all_expr hc))
  | ifFalse _he _hz ih =>
    intro hfuns hcode
    exact ih a hfuns (noExt_all_expr (noExt_stmt_cond (noExt_code_stmt hcode)).1)
  | loopDone _he _hz ih =>
    intro hfuns hcode
    exact ih a hfuns (noExt_all_expr (noExt_code_loop hcode).1)
  | forLoop _hi _hl ihI ihL =>
    intro hfuns hcode
    have ⟨hi', hc, hp, hb⟩ := noExt_stmt_for (noExt_code_stmt hcode)
    have hf' := noExtFuns_hoist_cons hi' hfuns
    exact (ihL a hf' (noExt_all_loop hc hp hb)).trans
      (ihI a hf' (noExt_all_stmts hi'))
  | forInitHalt _hi ih =>
    intro hfuns hcode
    have ⟨hi', _, _, _⟩ := noExt_stmt_for (noExt_code_stmt hcode)
    exact ih a (noExtFuns_hoist_cons hi' hfuns) (noExt_all_stmts hi')
  | seqCons _hs _hr ihs ihr =>
    intro hfuns hcode
    have ⟨hs', hr'⟩ := noExt_block_cons (noExt_code_stmts hcode)
    exact (ihr a hfuns (noExt_all_stmts hr')).trans
      (ihs a hfuns (noExt_all_stmt hs'))
  | seqStop _hs _hne ih =>
    intro hfuns hcode
    have ⟨hs', _⟩ := noExt_block_cons (noExt_code_stmts hcode)
    exact ih a hfuns (noExt_all_stmt hs')
  | loopStep _he _hne _hbody _ho _hp _hrest ihE ihB ihP ihR =>
    intro hfuns hcode
    have ⟨hc, hp', hb'⟩ := noExt_code_loop hcode
    exact (ihR a hfuns hcode).trans
      ((ihP a hfuns (noExt_all_block_stmt hp')).trans
        ((ihB a hfuns (noExt_all_block_stmt hb')).trans
          (ihE a hfuns (noExt_all_expr hc))))
  | loopPostHalt _he _hne _hbody _ho _hp ihE ihB ihP =>
    intro hfuns hcode
    have ⟨hc, hp', hb'⟩ := noExt_code_loop hcode
    exact (ihP a hfuns (noExt_all_block_stmt hp')).trans
      ((ihB a hfuns (noExt_all_block_stmt hb')).trans
        (ihE a hfuns (noExt_all_expr hc)))
  | loopBreak _he _hne _hbody ihE ihB | loopLeave _he _hne _hbody ihE ihB
  | loopBodyHalt _he _hne _hbody ihE ihB =>
    intro hfuns hcode
    have ⟨hc, _, hb'⟩ := noExt_code_loop hcode
    exact (ihB a hfuns (noExt_all_block_stmt hb')).trans
      (ihE a hfuns (noExt_all_expr hc))

theorem ofState_noExt_halt {calls : ExternalCalls} {G} {α : Abs G}
    (hign : α.ignoresLocal)
    {funs : FunEnv (yulD calls)} {V : VEnv (yulD calls)} {st : EvmState} {ss : YBlock}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hfuns : noExtFuns funs = true) (hno : noExtBlock ss = true)
    (h : ExecStmts (yulD calls) funs V st ss V' st' o) (a : Address) :
    α.ofState st' a = α.ofState st a := by
  simpa [resState] using
    step_ofState (calls := calls) hign h a hfuns (noExt_all_stmts hno)

end Lsc.Compiler
