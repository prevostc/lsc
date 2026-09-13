import Lsc.Compiler.Proof.CoreExt
import Lsc.Compiler.Proof.Descend

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 800000

/-!
`ExtAgree` along `noExt` `Step`: local `sstore`/`tstore`/logs/memory/halt are
dropped by `scrubSelf`, so a call-free run keeps the callee-visible view.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc hiding Op Stmt

def resState {D : Dialect} : Res D → D.State
  | .eres (.vals _ st) => st
  | .eres (.halt st) => st
  | .sres _ st _ => st

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

theorem some_halt_state {s s' : EvmState}
    (h : (some (BuiltinResult.halt s) : Option (BuiltinResult U256 EvmState)) =
          some (BuiltinResult.halt s')) :
    s' = s := by
  injection h with h'
  injection h' with hs
  exact hs.symm

theorem haddr_of_addr {self : Address} {st st' : EvmState}
    (haddr : st.env.address = BitVec.ofNat 256 self)
    (h : st'.env.address = st.env.address) :
    st'.env.address = BitVec.ofNat 256 self :=
  h.trans haddr

theorem scrubSelf_sstore (self : Address) (st : EvmState) (slot val : U256)
    (haddr : st.env.address = BitVec.ofNat 256 self) :
    scrubSelf self (ExtView.ofState
      { st with
        storage := upd st.storage slot val
        env := { st.env with
          storageOf := updAccount st.env.storageOf st.env.address slot val } }) =
      scrubSelf self (ExtView.ofState st) := by
  unfold scrubSelf ExtView.ofState ExtState.ofState
  simp only [haddr]
  congr
  ext a k
  by_cases hkey : accountKey a = accountKey (BitVec.ofNat 256 self) <;> simp [hkey, updAccount]

theorem scrubSelf_tstore (self : Address) (st : EvmState) (slot val : U256)
    (haddr : st.env.address = BitVec.ofNat 256 self) :
    scrubSelf self (ExtView.ofState
      { st with
        transient := upd st.transient slot val
        env := { st.env with
          transientOf := updAccount st.env.transientOf st.env.address slot val } }) =
      scrubSelf self (ExtView.ofState st) := by
  unfold scrubSelf ExtView.ofState ExtState.ofState
  simp only [haddr]
  congr
  ext a k
  by_cases hkey : accountKey a = accountKey (BitVec.ofNat 256 self) <;> simp [hkey, updAccount]

theorem scrubSelf_touch (self : Address) (st : EvmState) (p n : Nat) :
    scrubSelf self (ExtView.ofState (touchMemory st p n)) =
      scrubSelf self (ExtView.ofState st) := by
  simp [scrubSelf, ExtView.ofState, ExtState.ofState, touchMemory]

theorem scrubSelf_halt (self : Address) (st : EvmState)
    (h : Option (HaltKind × List UInt8)) :
    scrubSelf self (ExtView.ofState { st with halted := h }) =
      scrubSelf self (ExtView.ofState st) := by
  simp [scrubSelf, ExtView.ofState, ExtState.ofState]

theorem noExt_all_loop {c post body}
    (hc : noExtExpr c = true) (hp : noExtBlock post = true)
    (hb : noExtBlock body = true) :
    NoExternalOps (.loop c post body) := by
  simp [NoExternalOps, noExtCode, hc, hp, hb]

/-- Non-halting `stepOp` (no `call`/`create`/`gas`/`selfdestruct`) keeps the
scrubbed callee view and does not retarget `env.address`. -/
theorem stepOp_ok_scrub {self : Address} {op : EVM.Op} {args : List U256}
    {st : EvmState} {rets : List U256} {st' : EvmState}
    (haddr : st.env.address = BitVec.ofNat 256 self)
    (h : stepOp op args st = some (.ok rets st')) :
    scrubSelf self (ExtView.ofState st') = scrubSelf self (ExtView.ofState st) ∧
      st'.env.address = st.env.address := by
  cases op
  all_goals (try simp [stepOp, un, bin, ter, rd0, rd1, guardStatic] at h)
  all_goals (try split at h)
  all_goals (try split at h)
  all_goals (try exact (not_none_some h).elim)
  all_goals (try exact (not_halt_ok (Option.some.inj h)).elim)
  all_goals (try (have hst := some_ok_state h; subst hst))
  all_goals (try exact ⟨rfl, rfl⟩)
  all_goals (try exact ⟨scrubSelf_sstore self st _ _ haddr, rfl⟩)
  all_goals (try exact ⟨scrubSelf_tstore self st _ _ haddr, rfl⟩)
  all_goals (try exact ⟨by
      simp [scrubSelf, ExtView.ofState, ExtState.ofState, appendLog, touchMemory],
    by simp [appendLog, touchMemory]⟩)
  all_goals (try exact ⟨scrubSelf_touch self st _ _, by simp [touchMemory]⟩)
  all_goals (try exact ⟨by
      simp [scrubSelf, ExtView.ofState, ExtState.ofState, touchMemory, touchMemory2,
        appendLog],
    by simp [touchMemory, touchMemory2, appendLog]⟩)

theorem stepOp_halt_scrub {self : Address} {op : EVM.Op} {args : List U256}
    {st st' : EvmState}
    (h : stepOp op args st = some (.halt st'))
    (hnsd : op ≠ .selfdestruct) :
    scrubSelf self (ExtView.ofState st') = scrubSelf self (ExtView.ofState st) ∧
      st'.env.address = st.env.address := by
  cases op
  all_goals (try exact (hnsd rfl).elim)
  all_goals (try simp [stepOp, un, bin, ter, rd0, rd1, guardStatic] at h)
  all_goals (try split at h)
  all_goals (try split at h)
  all_goals (try exact (not_none_some h).elim)
  all_goals (try exact (not_halt_ok (Option.some.inj h).symm).elim)
  all_goals (try (have hst := some_halt_state h; subst hst))
  all_goals (try exact ⟨scrubSelf_halt self st _, rfl⟩)
  all_goals (try exact ⟨(scrubSelf_halt self (touchMemory st _ _) _).trans
      (scrubSelf_touch self st _ _), by simp [touchMemory]⟩)

/-- `noExt` `Step` keeps the scrubbed callee view. -/
theorem step_scrub {calls : ExternalCalls} {self : Address}
    {funs : FunEnv (yulD calls)} {V : VEnv (yulD calls)} {st : EvmState}
    {code : Code YOp} {res : Res (yulD calls)}
    (h : Step (yulD calls) funs V st code res)
    (haddr : st.env.address = BitVec.ofNat 256 self)
    (hfuns : noExtFuns funs = true) (hcode : NoExternalOps code) :
    scrubSelf self (ExtView.ofState (resState res)) =
        scrubSelf self (ExtView.ofState st) ∧
      (resState res).env.address = st.env.address := by
  revert hfuns hcode haddr
  induction h with
  | lit | var | argsNil | funDef | letZero | seqNil | «break» | «continue» | «leave» =>
    intro _ _ _; exact ⟨rfl, rfl⟩
  | builtinOk _hargs hbu ih =>
    intro haddr hfuns hcode
    have ⟨hop', hargs'⟩ := noExt_expr_builtin (noExt_code_expr hcode)
    have ⟨hαArgs, haddrArgs⟩ := ih haddr hfuns (noExt_all_args hargs')
    have ⟨hαOp, haddrOp⟩ :=
      stepOp_ok_scrub (self := self)
        (haddr_of_addr haddr (by simpa [resState] using haddrArgs))
        (builtin_descend hop' hbu)
    exact ⟨hαOp.trans hαArgs, haddrOp.trans haddrArgs⟩
  | builtinHalt _hargs hbu ih =>
    intro haddr hfuns hcode
    have ⟨hop', hargs'⟩ := noExt_expr_builtin (noExt_code_expr hcode)
    have ⟨hαArgs, haddrArgs⟩ := ih haddr hfuns (noExt_all_args hargs')
    have ⟨hαOp, haddrOp⟩ :=
      stepOp_halt_scrub (self := self) (builtin_descend hop' hbu) (by
        intro hopEq; subst hopEq; simp [noExtOp] at hop')
    exact ⟨hαOp.trans hαArgs, haddrOp.trans haddrArgs⟩
  | builtinArgsHalt _hargs ih =>
    intro haddr hfuns hcode
    have ⟨_, hargs'⟩ := noExt_expr_builtin (noExt_code_expr hcode)
    exact ih haddr hfuns (noExt_all_args hargs')
  | callOk _hargs hlu _hln _hbody _ho ihArgs ihBody =>
    intro haddr hfuns hcode
    have hargs' := noExt_expr_call (noExt_code_expr hcode)
    obtain ⟨hbod, hcenv⟩ := lookupFun_noExt hfuns hlu
    have ⟨hαA, haddrA⟩ := ihArgs haddr hfuns (noExt_all_args hargs')
    have ⟨hαB, haddrB⟩ :=
      ihBody (haddr_of_addr haddr (by simpa [resState] using haddrA))
        hcenv (noExt_all_block_stmt hbod)
    exact ⟨hαB.trans hαA, haddrB.trans haddrA⟩
  | callHalt _hargs hlu _hln _hbody ihArgs ihBody =>
    intro haddr hfuns hcode
    have hargs' := noExt_expr_call (noExt_code_expr hcode)
    obtain ⟨hbod, hcenv⟩ := lookupFun_noExt hfuns hlu
    have ⟨hαA, haddrA⟩ := ihArgs haddr hfuns (noExt_all_args hargs')
    have ⟨hαB, haddrB⟩ :=
      ihBody (haddr_of_addr haddr (by simpa [resState] using haddrA))
        hcenv (noExt_all_block_stmt hbod)
    exact ⟨hαB.trans hαA, haddrB.trans haddrA⟩
  | callArgsHalt _hargs ih =>
    intro haddr hfuns hcode
    exact ih haddr hfuns (noExt_all_args (noExt_expr_call (noExt_code_expr hcode)))
  | argsCons _hrest _hhead ihRest ihHead =>
    intro haddr hfuns hcode
    have ⟨he', hrest'⟩ := noExt_args_cons (noExt_code_args hcode)
    have ⟨hαR, haddrR⟩ := ihRest haddr hfuns (noExt_all_args hrest')
    have ⟨hαH, haddrH⟩ :=
      ihHead (haddr_of_addr haddr (by simpa [resState] using haddrR))
        hfuns (noExt_all_expr he')
    exact ⟨hαH.trans hαR, haddrH.trans haddrR⟩
  | argsRestHalt _hrest ih =>
    intro haddr hfuns hcode
    have ⟨_, hrest'⟩ := noExt_args_cons (noExt_code_args hcode)
    exact ih haddr hfuns (noExt_all_args hrest')
  | argsHeadHalt _hrest _he ihRest ihHead =>
    intro haddr hfuns hcode
    have ⟨he', hrest'⟩ := noExt_args_cons (noExt_code_args hcode)
    have ⟨hαR, haddrR⟩ := ihRest haddr hfuns (noExt_all_args hrest')
    have ⟨hαH, haddrH⟩ :=
      ihHead (haddr_of_addr haddr (by simpa [resState] using haddrR))
        hfuns (noExt_all_expr he')
    exact ⟨hαH.trans hαR, haddrH.trans haddrR⟩
  | block _hbody ih =>
    intro haddr hfuns hcode
    have hb := noExt_stmt_block (noExt_code_stmt hcode)
    exact ih haddr (noExtFuns_hoist_cons hb hfuns) (noExt_all_stmts hb)
  | letVal _he _hlen ih | letHalt _he ih =>
    intro haddr hfuns hcode
    exact ih haddr hfuns (noExt_all_expr (noExt_stmt_let (noExt_code_stmt hcode)))
  | assignVal _he _hlen ih | assignHalt _he ih =>
    intro haddr hfuns hcode
    exact ih haddr hfuns (noExt_all_expr (noExt_stmt_assign (noExt_code_stmt hcode)))
  | exprStmt _he ih | exprStmtHalt _he ih =>
    intro haddr hfuns hcode
    exact ih haddr hfuns (noExt_all_expr (noExt_stmt_expr (noExt_code_stmt hcode)))
  | ifHalt _he ih =>
    intro haddr hfuns hcode
    exact ih haddr hfuns (noExt_all_expr (noExt_stmt_cond (noExt_code_stmt hcode)).1)
  | switchHalt _he ih =>
    intro haddr hfuns hcode
    exact ih haddr hfuns (noExt_all_expr (noExt_stmt_switch (noExt_code_stmt hcode)).1)
  | loopCondHalt _he ih =>
    intro haddr hfuns hcode
    exact ih haddr hfuns (noExt_all_expr (noExt_code_loop hcode).1)
  | ifTrue _he _hne _hbody ihE ihB =>
    intro haddr hfuns hcode
    have ⟨hc, hb⟩ := noExt_stmt_cond (noExt_code_stmt hcode)
    have ⟨hαE, haddrE⟩ := ihE haddr hfuns (noExt_all_expr hc)
    have ⟨hαB, haddrB⟩ :=
      ihB (haddr_of_addr haddr (by simpa [resState] using haddrE))
        hfuns (noExt_all_block_stmt hb)
    exact ⟨hαB.trans hαE, haddrB.trans haddrE⟩
  | switchExec _he _hbody ihE ihB =>
    intro haddr hfuns hcode
    rename_i _funs _V _st _cnd cases dflt cv _st1 _V2 _st2 _o
    have ⟨hc, hcases, hd⟩ := noExt_stmt_switch (noExt_code_stmt hcode)
    have hsel := noExt_selectSwitch (calls := calls) (cv := cv) cases dflt hcases hd
    have ⟨hαE, haddrE⟩ := ihE haddr hfuns (noExt_all_expr hc)
    have ⟨hαB, haddrB⟩ :=
      ihB (haddr_of_addr haddr (by simpa [resState] using haddrE))
        hfuns (noExt_all_block_stmt hsel)
    exact ⟨hαB.trans hαE, haddrB.trans haddrE⟩
  | ifFalse _he _hz ih =>
    intro haddr hfuns hcode
    exact ih haddr hfuns (noExt_all_expr (noExt_stmt_cond (noExt_code_stmt hcode)).1)
  | loopDone _he _hz ih =>
    intro haddr hfuns hcode
    exact ih haddr hfuns (noExt_all_expr (noExt_code_loop hcode).1)
  | forLoop _hi _hl ihI ihL =>
    intro haddr hfuns hcode
    have ⟨hi', hc, hp, hb⟩ := noExt_stmt_for (noExt_code_stmt hcode)
    have hf' := noExtFuns_hoist_cons hi' hfuns
    have ⟨hαI, haddrI⟩ := ihI haddr hf' (noExt_all_stmts hi')
    have ⟨hαL, haddrL⟩ :=
      ihL (haddr_of_addr haddr (by simpa [resState] using haddrI))
        hf' (noExt_all_loop hc hp hb)
    exact ⟨hαL.trans hαI, haddrL.trans haddrI⟩
  | forInitHalt _hi ih =>
    intro haddr hfuns hcode
    have ⟨hi', _, _, _⟩ := noExt_stmt_for (noExt_code_stmt hcode)
    exact ih haddr (noExtFuns_hoist_cons hi' hfuns) (noExt_all_stmts hi')
  | seqCons _hs _hr ihs ihr =>
    intro haddr hfuns hcode
    have ⟨hs', hr'⟩ := noExt_block_cons (noExt_code_stmts hcode)
    have ⟨hαS, haddrS⟩ := ihs haddr hfuns (noExt_all_stmt hs')
    have ⟨hαR, haddrR⟩ :=
      ihr (haddr_of_addr haddr (by simpa [resState] using haddrS))
        hfuns (noExt_all_stmts hr')
    exact ⟨hαR.trans hαS, haddrR.trans haddrS⟩
  | seqStop _hs _hne ih =>
    intro haddr hfuns hcode
    have ⟨hs', _⟩ := noExt_block_cons (noExt_code_stmts hcode)
    exact ih haddr hfuns (noExt_all_stmt hs')
  | loopStep _he _hne _hbody _ho _hp _hrest ihE ihB ihP ihR =>
    intro haddr hfuns hcode
    have ⟨hc, hp', hb'⟩ := noExt_code_loop hcode
    have ⟨hαE, haddrE⟩ := ihE haddr hfuns (noExt_all_expr hc)
    have ⟨hαB, haddrB⟩ :=
      ihB (haddr_of_addr haddr (by simpa [resState] using haddrE))
        hfuns (noExt_all_block_stmt hb')
    have ⟨hαP, haddrP⟩ :=
      ihP (haddr_of_addr haddr (by simpa [resState] using haddrB.trans haddrE))
        hfuns (noExt_all_block_stmt hp')
    have ⟨hαR, haddrR⟩ :=
      ihR (haddr_of_addr haddr (by simpa [resState] using haddrP.trans (haddrB.trans haddrE)))
        hfuns hcode
    exact ⟨hαR.trans (hαP.trans (hαB.trans hαE)),
      haddrR.trans (haddrP.trans (haddrB.trans haddrE))⟩
  | loopPostHalt _he _hne _hbody _ho _hp ihE ihB ihP =>
    intro haddr hfuns hcode
    have ⟨hc, hp', hb'⟩ := noExt_code_loop hcode
    have ⟨hαE, haddrE⟩ := ihE haddr hfuns (noExt_all_expr hc)
    have ⟨hαB, haddrB⟩ :=
      ihB (haddr_of_addr haddr (by simpa [resState] using haddrE))
        hfuns (noExt_all_block_stmt hb')
    have ⟨hαP, haddrP⟩ :=
      ihP (haddr_of_addr haddr (by simpa [resState] using haddrB.trans haddrE))
        hfuns (noExt_all_block_stmt hp')
    exact ⟨hαP.trans (hαB.trans hαE), haddrP.trans (haddrB.trans haddrE)⟩
  | loopBreak _he _hne _hbody ihE ihB | loopLeave _he _hne _hbody ihE ihB
  | loopBodyHalt _he _hne _hbody ihE ihB =>
    intro haddr hfuns hcode
    have ⟨hc, _, hb'⟩ := noExt_code_loop hcode
    have ⟨hαE, haddrE⟩ := ihE haddr hfuns (noExt_all_expr hc)
    have ⟨hαB, haddrB⟩ :=
      ihB (haddr_of_addr haddr (by simpa [resState] using haddrE))
        hfuns (noExt_all_block_stmt hb')
    exact ⟨hαB.trans hαE, haddrB.trans haddrE⟩

/-- Call-free `ExecStmts` preserve `ExtAgree`. -/
theorem ExtAgree_noExt {calls : ExternalCalls} {self : Address} {x : Lsc.ExtState}
    {funs : FunEnv (yulD calls)} {V : VEnv (yulD calls)} {st : EvmState} {ss : YBlock}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hAgr : ExtAgree self x st)
    (haddr : st.env.address = BitVec.ofNat 256 self)
    (hfuns : noExtFuns funs = true) (hno : noExtBlock ss = true)
    (h : ExecStmts (yulD calls) funs V st ss V' st' o) :
    ExtAgree self x st' :=
  ExtAgree_of_scrub hAgr
    (step_scrub (calls := calls) h haddr hfuns (noExt_all_stmts hno)).1

end Lsc.Compiler
