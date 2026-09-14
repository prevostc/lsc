import Lsc.Compiler.Proof.Progress
import Lsc.Compiler.Proof.CoreExtSimProof
import YulEvmCompiler.Optimizer.Implementation.MemorySpill

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1200000

/-!
S2 `core_progress` / `yul_progress`: a halted `Run` of compiled S2Frag code exists
under `toCalls o`. `NoReentry` is the only callee hypothesis.
-/

namespace Lsc.Compiler

variable (tag : String)

open YulSemantics
open YulSemantics.EVM
open Lsc hiding Op Stmt
open Lsc.Compiler.Proof

theorem exec_switch_halt_open {calls : ExternalCalls}
    {funs : FunEnv (yulD calls)} {V : VEnv (yulD calls)} {st : EvmState}
    {V' : VEnv (yulD calls)} {st' : EvmState}
    {cnd : YExpr} {eA eB body : YBlock} {cv : U256}
    (he : EvalExpr (yulD calls) funs V st cnd (.vals [cv] st))
    (hsel : selectSwitch (yulD calls) cv
      [(YulSemantics.Literal.number 0, eB)] (some eA) = body)
    (hhoist : hoist (yulD calls) body = [])
    (hexec : ExecStmts (yulD calls) ([] :: funs) V st body V' st' .halt) :
    ExecStmts (yulD calls) funs V st
      [.switch cnd [(YulSemantics.Literal.number 0, eB)] (some eA)]
      (restore V V') st' .halt := by
  refine Step.seqStop ?_ halt_ne_normal
  refine Step.switchExec he ?_
  exact Step.block (by rwa [hsel, hhoist])

theorem exec_head_halt_open {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {s : YulSemantics.Stmt YOp}
    {rest : YBlock} {st' : EvmState}
    (h : ExecStmt (yulD calls) funs V st s V st' .halt) :
    ExecStmts (yulD calls) funs V st (s :: rest) V st' .halt :=
  Step.seqStop (rest := rest) h halt_ne_normal

theorem exec_pair_halt_open {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {s1 s2 : YulSemantics.Stmt YOp}
    {st' : EvmState}
    (h1 : ExecStmt (yulD calls) funs V st s1 V st .normal)
    (h2 : ExecStmt (yulD calls) funs V st s2 V st' .halt) :
    ExecStmts (yulD calls) funs V st [s1, s2] V st' .halt :=
  Step.seqCons h1 (Step.seqStop (rest := []) h2 halt_ne_normal)

theorem switch_halt_nil_open {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {st : EvmState} {cnd : YExpr} {cv : U256}
    {cases : List (YulSemantics.Literal × YBlock)} {dflt : Option YBlock}
    {body : YBlock} {st' : EvmState}
    (he : EvalExpr (yulD calls) funs [] st cnd (.vals [cv] st))
    (hsel : selectSwitch (yulD calls) cv cases dflt = body)
    (hh : hoist (yulD calls) body = [])
    (hexec : ExecStmts (yulD calls) ([] :: funs) [] st body [] st' .halt) :
    ExecStmt (yulD calls) funs [] st (.switch cnd cases dflt) [] st' .halt := by
  refine Step.switchExec he ?_
  rw [hsel]
  have hb := Step.block (D := yulD calls) (by rwa [hh])
  rw [restore_nil_any (D := yulD calls)] at hb
  exact hb

theorem return_var0_progress {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ} {w : World S X E} {st : EvmState} {v : Nat}
    {calls : ExternalCalls} {n : Nat}
    (hv : v < wordBound) (hR : R c Γ κ w st)
    {env : List Nat} {V : VEnv evm}
    (hV : V = toVEnv tag (v :: env))
    (hn : identsNodup tag (v :: env).length = true) :
    ∃ st', ExecStmts (yulD calls) (List.replicate n []) V st
      (emitReturnWords {} [atomE tag (env.length + 1) (.var 0)]).stmts V st' .halt := by
  have he := eval_atom tag (funs := List.replicate n []) (st := st) hV hn (.var 0)
  have : (v :: env).length = env.length + 1 := rfl
  simp only [this] at he
  have ⟨st', hexec, _, _⟩ := return_word_sim (c := c) (Γ := Γ) (κ := κ) (w := w)
    (funs := List.replicate n []) V hv he hR
  exact ⟨st', execStmts_lift_nils hexec⟩

theorem finish_opTail_word {S E ε}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε}
    {κ ctx} {w : World S ExtState E} {env : List Nat}
    {V : VEnv evm} {st : EvmState} {n : Nat} {e1 : Emit}
    {V1 : VEnv evm} {st1 : EvmState} {out : Outcome}
    {calls : ExternalCalls} (clearLock : Bool)
    (hV : V = toVEnv tag env)
    (hexec : ExecStmts (yulD calls) (List.replicate n []) (toVEnv tag env) st
      e1.stmts V1 st1 out)
    (ho : out = .halt ∨ (out = .normal ∧ ∃ v, V1 = toVEnv tag (v :: env) ∧
      Inv tag Γ c κ ctx w (v :: env) V1 st1))
    (hn1 : identsNodup tag (env.length + 1) = true) :
    ∃ V' st', ExecStmts (yulD calls) (List.replicate n []) V st
      (e1.stmts ++ ((if clearLock then [lockClearStmt] else []) ++
        (emitReturnWords {} [atomE tag (env.length + 1) (.var 0)]).stmts))
      V' st' .halt := by
  rcases ho with ho | ⟨ho, v, hVeq, hinv1⟩
  · subst ho
    exact ⟨V1, st1, execStmts_append_halt_open (by simpa [hV] using hexec)⟩
  · subst ho
    have hn1' : identsNodup tag (v :: env).length = true := by simpa using hn1
    have hv : v < wordBound := hinv1.wf v (by simp)
    have hstatic := ctxRel_static hinv1.ctxr
    have hMO := memOnly_stAfterLockClear clearLock st1
    have ⟨stR, hret⟩ :=
      return_var0_progress tag (κ := κ) (w := w)
        (st := stAfterLockClear clearLock st1) (calls := calls) (n := n)
        hv (R_memOnly hinv1.rel hMO) hVeq hn1'
    have hmid := execStmts_maybe_lockClear_nils (calls := calls) (n := n)
      clearLock hstatic hret
    exact ⟨V1, stR, execStmts_append_open (by simpa [hV] using hexec) hmid⟩

theorem finish_stmtTail {S E ε}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε}
    {κ ctx} {w : World S ExtState E} {env : List Nat}
    {V : VEnv evm} {st : EvmState} {n : Nat}
    {V1 : VEnv evm} {st1 : EvmState} {out : Outcome}
    {calls : ExternalCalls} {ss : YBlock} (clearLock : Bool)
    (hV : V = toVEnv tag env)
    (hexec : ExecStmts (yulD calls) (List.replicate n []) (toVEnv tag env) st
      ss V1 st1 out)
    (ho : out = .halt ∨ (out = .normal ∧ V1 = toVEnv tag env ∧
      Inv tag Γ c κ ctx w env V1 st1)) :
    ∃ V' st', ExecStmts (yulD calls) (List.replicate n []) V st
      (ss ++ ((if clearLock then [lockClearStmt] else []) ++ [stopStmt]))
      V' st' .halt := by
  rcases ho with ho | ⟨ho, hVeq, hinv1⟩
  · subst ho
    exact ⟨V1, st1, execStmts_append_halt_open (by simpa [hV] using hexec)⟩
  · subst ho
    have hstatic := ctxRel_static hinv1.ctxr
    have hstop :=
      execStmts_lift_nils (calls := calls) (n := n)
        (stop_sim (List.replicate n []) V1 (stAfterLockClear clearLock st1))
    have hmid := execStmts_maybe_lockClear_nils (calls := calls) (n := n)
      clearLock hstatic hstop
    exact ⟨V1, _, execStmts_append_open (by simpa [hV] using hexec) hmid⟩

/-! ## `core_progress` -/

theorem core_progress {S E ε}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε}
    {κ ctx haltUnit}
    (hhalt : haltUnit = true) (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    (o : ExtOracle)
    {t} (core : Core t) (hS2 : S2Frag core) :
    ∀ {w : World S ExtState E} {env : List Nat} {V : VEnv evm} {st : EvmState} (n : Nat)
      (hwf : coreWF c core = true)
      (hn : identsNodup tag (env.length + coreExtraDepth core) = true)
      (hinv : Inv tag Γ c κ ctx w env V st)
      (hNR : ExtOracle.NoReentry o ctx.self)
      {clearLock : Bool} {e' : Emit}
      (hem : emitCore tag c {} env.length haltUnit core clearLock = some e'),
      ∃ V' st',
        ExecStmts (yulD (toCalls o)) (List.replicate n []) V st e'.stmts V' st' .halt := by
  revert hS2
  induction core with
  | ret r =>
    intro hS2 w env V st n hwf hn hinv hNR clearLock e' hem
    cases r with
    | pair x y =>
      cases x with
      | word _ =>
        cases y with
        | word _ =>
          exact core_progress_callFree tag hhalt hΓ hκ hlen (calls := toCalls o)
            _ (by simp [CallFree, M1Frag]) hwf hn hinv hem
        | _ => cases hS2
      | _ => cases hS2
    | unit | word _ | addr _ | flag _ =>
      exact core_progress_callFree tag hhalt hΓ hκ hlen (calls := toCalls o)
        _ (by simp [CallFree, M1Frag]) hwf hn hinv hem
  | revertTail err args =>
    intro hS2 w env V st n hwf hn hinv hNR clearLock e' hem
    exact core_progress_callFree tag hhalt hΓ hκ hlen (calls := toCalls o) _
      (by simpa [CallFree, M1Frag, S2Frag] using hS2) hwf hn hinv hem
  | opTail op =>
    intro hS2 w env V st n hwf hn hinv hNR clearLock e' hem
    cases s2op_elim (by simpa [S2Frag] using hS2) with
    | inl hcall =>
      obtain ⟨target, sel, args, ret, rfl⟩ := hcall
      simp only [emitCore] at hem
      cases hE : emitLetOp tag c {} env.length (.call target sel args ret) with
      | none => simp [hE] at hem
      | some e1 =>
        simp only [hE] at hem
        cases hem
        rw [emitRet_word_stmts_if tag e1 (env.length + 1) haltUnit (.var 0) clearLock]
        have ⟨hwfCall, hsel⟩ :=
          opWF_call (c := c) (t := target) (sel := sel) (args := args) (ret := ret) (by simpa [coreWF] using hwf)
        have hn0 : identsNodup tag env.length = true :=
          identsNodup_mono tag (by simp [coreExtraDepth]) hn
        have hn1 : identsNodup tag (env.length + 1) = true :=
          identsNodup_mono tag (by simp [coreExtraDepth]) hn
        have hinvT : Inv tag Γ c κ ctx w env (toVEnv tag env) st := by
          rwa [hinv.venv] at hinv
        have hcallP :=
          op_call_progress tag o (n := n) (target := target) (sel := sel) (args := args) (ret := ret) hinvT hNR hwfCall hsel hn0 hn1
        obtain ⟨V1, st1, out, hexec, ho⟩ := hcallP
        rw [hE] at hexec
        exact finish_opTail_word tag clearLock hinv.venv hexec ho hn1
    | inr hrest =>
      cases hrest with
      | inl hview =>
        obtain ⟨target, sel, args, ret, rfl⟩ := hview
        simp only [emitCore] at hem
        cases hE : emitLetOp tag c {} env.length (.view target sel args ret) with
        | none => simp [hE] at hem
        | some e1 =>
          simp only [hE] at hem
          cases hem
          rw [emitRet_word_stmts_if tag e1 (env.length + 1) haltUnit (.var 0) clearLock]
          have ⟨hwfCall, hsel⟩ :=
            opWF_view (c := c) (t := target) (sel := sel) (args := args) (ret := ret) (by simpa [coreWF] using hwf)
          have hn0 : identsNodup tag env.length = true :=
            identsNodup_mono tag (by simp [coreExtraDepth]) hn
          have hn1 : identsNodup tag (env.length + 1) = true :=
            identsNodup_mono tag (by simp [coreExtraDepth]) hn
          have hinvT : Inv tag Γ c κ ctx w env (toVEnv tag env) st := by
            rwa [hinv.venv] at hinv
          have hcallP :=
            op_view_progress tag o (n := n) (target := target) (sel := sel) (args := args) (ret := ret) hinvT hwfCall hsel hn0 hn1
          obtain ⟨V1, st1, out, hexec, ho⟩ := hcallP
          rw [hE] at hexec
          exact finish_opTail_word tag clearLock hinv.venv hexec ho hn1
      | inr hM1 =>
        exact core_progress_callFree tag hhalt hΓ hκ hlen (calls := toCalls o)
          (.opTail op) (by simpa [CallFree, M1Frag] using hM1) hwf hn hinv hem
  | opTailAddr op =>
    intro hS2 w env V st n hwf hn hinv hNR clearLock e' hem
    cases s2op_elim (by simpa [S2Frag] using hS2) with
    | inl hcall =>
      obtain ⟨target, sel, args, ret, rfl⟩ := hcall
      simp only [emitCore] at hem
      cases hE : emitLetOp tag c {} env.length (.call target sel args ret) with
      | none => simp [hE] at hem
      | some e1 =>
        simp only [hE] at hem
        cases hem
        rw [emitRet_addr_stmts_if tag e1 (env.length + 1) haltUnit (.var 0) clearLock]
        have ⟨hwfCall, hsel⟩ :=
          opWF_call (c := c) (t := target) (sel := sel) (args := args) (ret := ret) (by simpa [coreWF] using hwf)
        have hn0 : identsNodup tag env.length = true :=
          identsNodup_mono tag (by simp [coreExtraDepth]) hn
        have hn1 : identsNodup tag (env.length + 1) = true :=
          identsNodup_mono tag (by simp [coreExtraDepth]) hn
        have hinvT : Inv tag Γ c κ ctx w env (toVEnv tag env) st := by
          rwa [hinv.venv] at hinv
        have hcallP :=
          op_call_progress tag o (n := n) (target := target) (sel := sel) (args := args) (ret := ret) hinvT hNR hwfCall hsel hn0 hn1
        obtain ⟨V1, st1, out, hexec, ho⟩ := hcallP
        rw [hE] at hexec
        exact finish_opTail_word tag clearLock hinv.venv hexec ho hn1
    | inr hrest =>
      cases hrest with
      | inl hview =>
        obtain ⟨target, sel, args, ret, rfl⟩ := hview
        simp only [emitCore] at hem
        cases hE : emitLetOp tag c {} env.length (.view target sel args ret) with
        | none => simp [hE] at hem
        | some e1 =>
          simp only [hE] at hem
          cases hem
          rw [emitRet_addr_stmts_if tag e1 (env.length + 1) haltUnit (.var 0) clearLock]
          have ⟨hwfCall, hsel⟩ :=
            opWF_view (c := c) (t := target) (sel := sel) (args := args) (ret := ret) (by simpa [coreWF] using hwf)
          have hn0 : identsNodup tag env.length = true :=
            identsNodup_mono tag (by simp [coreExtraDepth]) hn
          have hn1 : identsNodup tag (env.length + 1) = true :=
            identsNodup_mono tag (by simp [coreExtraDepth]) hn
          have hinvT : Inv tag Γ c κ ctx w env (toVEnv tag env) st := by
            rwa [hinv.venv] at hinv
          have hcallP :=
            op_view_progress tag o (n := n) (target := target) (sel := sel) (args := args) (ret := ret) hinvT hwfCall hsel hn0 hn1
          obtain ⟨V1, st1, out, hexec, ho⟩ := hcallP
          rw [hE] at hexec
          exact finish_opTail_word tag clearLock hinv.venv hexec ho hn1
      | inr hM1 =>
        exact core_progress_callFree tag hhalt hΓ hκ hlen (calls := toCalls o)
          (.opTailAddr op) (by simpa [CallFree, M1Frag] using hM1) hwf hn hinv hem
  | opTailFlag op =>
    intro hS2 w env V st n hwf hn hinv hNR clearLock e' hem
    cases s2op_elim (by simpa [S2Frag] using hS2) with
    | inl hcall =>
      obtain ⟨target, sel, args, ret, rfl⟩ := hcall
      simp only [emitCore] at hem
      cases hE : emitLetOp tag c {} env.length (.call target sel args ret) with
      | none => simp [hE] at hem
      | some e1 =>
        simp only [hE] at hem
        cases hem
        rw [emitRet_flag_stmts_if tag e1 (env.length + 1) haltUnit (.var 0) clearLock]
        have ⟨hwfCall, hsel⟩ :=
          opWF_call (c := c) (t := target) (sel := sel) (args := args) (ret := ret) (by simpa [coreWF] using hwf)
        have hn0 : identsNodup tag env.length = true :=
          identsNodup_mono tag (by simp [coreExtraDepth]) hn
        have hn1 : identsNodup tag (env.length + 1) = true :=
          identsNodup_mono tag (by simp [coreExtraDepth]) hn
        have hinvT : Inv tag Γ c κ ctx w env (toVEnv tag env) st := by
          rwa [hinv.venv] at hinv
        have hcallP :=
          op_call_progress tag o (n := n) (target := target) (sel := sel) (args := args) (ret := ret) hinvT hNR hwfCall hsel hn0 hn1
        obtain ⟨V1, st1, out, hexec, ho⟩ := hcallP
        rw [hE] at hexec
        exact finish_opTail_word tag clearLock hinv.venv hexec ho hn1
    | inr hrest =>
      cases hrest with
      | inl hview =>
        obtain ⟨target, sel, args, ret, rfl⟩ := hview
        simp only [emitCore] at hem
        cases hE : emitLetOp tag c {} env.length (.view target sel args ret) with
        | none => simp [hE] at hem
        | some e1 =>
          simp only [hE] at hem
          cases hem
          rw [emitRet_flag_stmts_if tag e1 (env.length + 1) haltUnit (.var 0) clearLock]
          have ⟨hwfCall, hsel⟩ :=
            opWF_view (c := c) (t := target) (sel := sel) (args := args) (ret := ret) (by simpa [coreWF] using hwf)
          have hn0 : identsNodup tag env.length = true :=
            identsNodup_mono tag (by simp [coreExtraDepth]) hn
          have hn1 : identsNodup tag (env.length + 1) = true :=
            identsNodup_mono tag (by simp [coreExtraDepth]) hn
          have hinvT : Inv tag Γ c κ ctx w env (toVEnv tag env) st := by
            rwa [hinv.venv] at hinv
          have hcallP :=
            op_view_progress tag o (n := n) (target := target) (sel := sel) (args := args) (ret := ret) hinvT hwfCall hsel hn0 hn1
          obtain ⟨V1, st1, out, hexec, ho⟩ := hcallP
          rw [hE] at hexec
          exact finish_opTail_word tag clearLock hinv.venv hexec ho hn1
      | inr hM1 =>
        exact core_progress_callFree tag hhalt hΓ hκ hlen (calls := toCalls o)
          (.opTailFlag op) (by simpa [CallFree, M1Frag] using hM1) hwf hn hinv hem
  | stmtTail s =>
    intro hS2 w env V st n hwf hn hinv hNR clearLock e' hem
    cases s2stmt_elim (by simpa [S2Frag] using hS2) with
    | inl hcall =>
      obtain ⟨target, sel, args, ret, rfl⟩ := hcall
      simp only [emitCore, hhalt] at hem
      cases hem
      rw [emitReturnUnit_lock_if]
      have ⟨hwfCall, hsel⟩ :=
        stmtWF_call (c := c) (t := target) (sel := sel) (args := args) (ret := ret) (by simpa [coreWF] using hwf)
      have hn0 : identsNodup tag env.length = true := by simpa [coreExtraDepth] using hn
      have hinvT : Inv tag Γ c κ ctx w env (toVEnv tag env) st := by
        rwa [hinv.venv] at hinv
      have hcallP :=
        stmt_call_progress tag o (n := n) (target := target) (sel := sel) (args := args) (ret := ret) hinvT hNR hwfCall hsel hn0
      obtain ⟨V1, st1, out, hexec, ho⟩ := hcallP
      exact finish_stmtTail tag clearLock hinv.venv hexec ho
    | inr hrest =>
      cases hrest with
      | inl hview =>
        obtain ⟨target, sel, args, ret, rfl⟩ := hview
        simp only [emitCore, hhalt] at hem
        cases hem
        rw [emitReturnUnit_lock_if]
        have ⟨hwfCall, hsel⟩ :=
          stmtWF_view (c := c) (t := target) (sel := sel) (args := args) (ret := ret) (by simpa [coreWF] using hwf)
        have hn0 : identsNodup tag env.length = true := by simpa [coreExtraDepth] using hn
        have hinvT : Inv tag Γ c κ ctx w env (toVEnv tag env) st := by
          rwa [hinv.venv] at hinv
        have hcallP :=
          stmt_view_progress tag o (n := n) (target := target) (sel := sel) (args := args) (ret := ret) hinvT hwfCall hsel hn0
        obtain ⟨V1, st1, out, hexec, ho⟩ := hcallP
        exact finish_stmtTail tag clearLock hinv.venv hexec ho
      | inr hM1 =>
        exact core_progress_callFree tag hhalt hΓ hκ hlen (calls := toCalls o)
          (.stmtTail s) (by simpa [CallFree, M1Frag] using hM1) hwf hn hinv hem
  | letOp op k ih =>
    intro hS2 w env V st n hwf hn hinv hNR clearLock e' hem
    have ⟨hopS2, hkS2⟩ := s2frag_letOp.mp hS2
    obtain ⟨e1, e0, h1, h0, hst⟩ := emitCore_letOp_split tag hem
    have ⟨hwfOp, hwfK⟩ : opWF c op = true ∧ coreWF c k = true := by
      simpa [coreWF, Bool.and_eq_true] using hwf
    have hn0 : identsNodup tag env.length = true :=
      identsNodup_mono tag (Nat.le_add_right env.length _) hn
    have hn1 : identsNodup tag (env.length + 1) = true :=
      identsNodup_mono tag (Nat.le_add_right (env.length + 1) (coreExtraDepth k))
        (by simpa [coreExtraDepth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn)
    have hnK : identsNodup tag ((env.length + 1) + coreExtraDepth k) = true := by
      simpa [coreExtraDepth, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
    rw [hst]
    cases s2op_elim hopS2 with
    | inl hcall =>
      obtain ⟨target, sel, args, ret, rfl⟩ := hcall
      have ⟨hwfCall, hsel⟩ := opWF_call (c := c) (t := target) (sel := sel) (args := args) (ret := ret) (by simpa [opWF] using hwfOp)
      have hinvT : Inv tag Γ c κ ctx w env (toVEnv tag env) st := by
        rwa [hinv.venv] at hinv
      have hcallP :=
        op_call_progress tag o (n := n) (target := target) (sel := sel) (args := args) (ret := ret) hinvT hNR hwfCall hsel hn0 hn1
      obtain ⟨V1, st1, out, hexec, ho⟩ := hcallP
      simp only [h1] at hexec
      rcases ho with ho | ⟨ho, v, hVeq, hinv1⟩
      · subst ho
        exact ⟨V1, st1, execStmts_append_halt_open (by simpa [hinv.venv] using hexec)⟩
      · subst ho
        have ihk := ih hkS2 (env := v :: env) (n := n) hwfK hnK
          (by simpa [hVeq] using hinv1) hNR h0
        obtain ⟨V2, st2, hk⟩ := ihk
        exact ⟨V2, st2, execStmts_append_open (by simpa [hinv.venv, hVeq] using hexec) hk⟩
    | inr hrest =>
      cases hrest with
      | inl hview =>
        obtain ⟨target, sel, args, ret, rfl⟩ := hview
        have ⟨hwfCall, hsel⟩ := opWF_view (c := c) (t := target) (sel := sel) (args := args) (ret := ret) (by simpa [opWF] using hwfOp)
        have hinvT : Inv tag Γ c κ ctx w env (toVEnv tag env) st := by
          rwa [hinv.venv] at hinv
        have hcallP :=
          op_view_progress tag o (n := n) (target := target) (sel := sel) (args := args) (ret := ret) hinvT hwfCall hsel hn0 hn1
        obtain ⟨V1, st1, out, hexec, ho⟩ := hcallP
        simp only [h1] at hexec
        rcases ho with ho | ⟨ho, v, hVeq, hinv1⟩
        · subst ho
          exact ⟨V1, st1, execStmts_append_halt_open (by simpa [hinv.venv] using hexec)⟩
        · subst ho
          have ihk := ih hkS2 (env := v :: env) (n := n) hwfK hnK
            (by simpa [hVeq] using hinv1) hNR h0
          obtain ⟨V2, st2, hk⟩ := ihk
          exact ⟨V2, st2, execStmts_append_open (by simpa [hinv.venv, hVeq] using hexec) hk⟩
      | inr hM1 =>
        have hsim := op_sim tag (List.replicate n []) hinv hΓ hκ hlen hM1 hwfOp hn1
        cases hrun : Tx.run (Op.denote Γ env op) ctx w with
        | ok p =>
          simp only [hrun, except_ok_prod] at hsim
          obtain ⟨st1, hexec, hinv1⟩ := hsim
          simp only [h1] at hexec
          rcases p with ⟨v, w'⟩
          have hexec' := execStmts_lift_nils (calls := toCalls o) (n := n) hexec
          have ihk := ih hkS2 (env := v :: env) (n := n) hwfK hnK hinv1 hNR h0
          obtain ⟨V2, st2, hk⟩ := ihk
          exact ⟨V2, st2, execStmts_append_open hexec' hk⟩
        | error e =>
          simp only [hrun, except_error_prod] at hsim
          obtain ⟨V1, st1, _, hexec, _, _⟩ := hsim
          simp only [h1] at hexec
          exact ⟨V1, st1, execStmts_append_halt_open (execStmts_lift_nils hexec)⟩
  | seq s k ih =>
    intro hS2 w env V st n hwf hn hinv hNR clearLock e' hem
    have ⟨hsS2, hkS2⟩ := s2frag_seq.mp hS2
    obtain ⟨e0, h0, hst⟩ := emitCore_seq_split tag hem
    have ⟨hwfS, hwfK⟩ : stmtWF c s = true ∧ coreWF c k = true := by
      simpa [coreWF, Bool.and_eq_true] using hwf
    have hn0 : identsNodup tag env.length = true :=
      identsNodup_mono tag (Nat.le_add_right _ _) hn
    have hnK : identsNodup tag (env.length + coreExtraDepth k) = true := by
      simpa [coreExtraDepth] using hn
    rw [hst]
    cases s2stmt_elim hsS2 with
    | inl hcall =>
      obtain ⟨target, sel, args, ret, rfl⟩ := hcall
      have ⟨hwfCall, hsel⟩ := stmtWF_call (c := c) (t := target) (sel := sel) (args := args) (ret := ret) (by simpa [stmtWF] using hwfS)
      have hinvT : Inv tag Γ c κ ctx w env (toVEnv tag env) st := by
        rwa [hinv.venv] at hinv
      have hcallP :=
        stmt_call_progress tag o (n := n) (target := target) (sel := sel) (args := args) (ret := ret) hinvT hNR hwfCall hsel hn0
      obtain ⟨V1, st1, out, hexec, ho⟩ := hcallP
      rcases ho with ho | ⟨ho, hVeq, hinv1⟩
      · subst ho
        exact ⟨V1, st1, execStmts_append_halt_open (by simpa [hinv.venv] using hexec)⟩
      · subst ho
        have ihk := ih hkS2 (n := n) hwfK hnK (by simpa [hVeq] using hinv1) hNR h0
        obtain ⟨V2, st2, hk⟩ := ihk
        exact ⟨V2, st2, execStmts_append_open (by simpa [hinv.venv, hVeq] using hexec) hk⟩
    | inr hrest =>
      cases hrest with
      | inl hview =>
        obtain ⟨target, sel, args, ret, rfl⟩ := hview
        have ⟨hwfCall, hsel⟩ := stmtWF_view (c := c) (t := target) (sel := sel) (args := args) (ret := ret) (by simpa [stmtWF] using hwfS)
        have hinvT : Inv tag Γ c κ ctx w env (toVEnv tag env) st := by
          rwa [hinv.venv] at hinv
        have hcallP :=
          stmt_view_progress tag o (n := n) (target := target) (sel := sel) (args := args) (ret := ret) hinvT hwfCall hsel hn0
        obtain ⟨V1, st1, out, hexec, ho⟩ := hcallP
        rcases ho with ho | ⟨ho, hVeq, hinv1⟩
        · subst ho
          exact ⟨V1, st1, execStmts_append_halt_open (by simpa [hinv.venv] using hexec)⟩
        · subst ho
          have ihk := ih hkS2 (n := n) hwfK hnK (by simpa [hVeq] using hinv1) hNR h0
          obtain ⟨V2, st2, hk⟩ := ihk
          exact ⟨V2, st2, execStmts_append_open (by simpa [hinv.venv, hVeq] using hexec) hk⟩
      | inr hM1 =>
        have hsim := stmt_sim tag (List.replicate n []) hinv hΓ hκ hlen hM1 hwfS hn0
        cases hrun : Tx.run (Stmt.denote Γ env s) ctx w with
        | ok p =>
          simp only [hrun, except_ok_prod] at hsim
          obtain ⟨st1, hexec, hinv1⟩ := hsim
          have hexec' := execStmts_lift_nils (calls := toCalls o) (n := n) hexec
          rcases p with ⟨_, w'⟩
          have ihk := ih hkS2 (n := n) hwfK hnK hinv1 hNR h0
          obtain ⟨V2, st2, hk⟩ := ihk
          exact ⟨V2, st2, execStmts_append_open hexec' hk⟩
        | error e =>
          simp only [hrun, except_error_prod] at hsim
          obtain ⟨V1, st1, _, hexec, _, _⟩ := hsim
          exact ⟨V1, st1, execStmts_append_halt_open (execStmts_lift_nils hexec)⟩
  | letPure p args k ih =>
    intro hS2 w env V st n hwf hn hinv hNR clearLock e' hem
    have ⟨hp, hargs, hkS2⟩ := s2frag_letPure.mp hS2
    subst hp
    have ⟨a, hargs'⟩ := length_eq_one.mp hargs
    subst hargs'
    have ⟨hwfA, hkWF⟩ : atomWF a = true ∧ coreWF c k = true := by
      simpa [coreWF, Bool.and_eq_true] using hwf
    simp only [emitCore, emitPrim] at hem
    obtain ⟨e0, h0, hst⟩ := emitCore_prefix tag hem
    have hn0 : identsNodup tag env.length = true :=
      identsNodup_mono tag (Nat.le_add_right env.length _) hn
    have hnK : identsNodup tag ((env.length + 1) + coreExtraDepth k) = true := by
      simpa [coreExtraDepth, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
    have he := eval_atom tag (List.replicate n []) (st := st) hinv.venv hn0 a
    have hv := atom_eval_lt hinv.wf hwfA
    have hlet :
        ExecStmt (yulD (toCalls o)) (List.replicate n []) V st
          (.letDecl [identV tag env.length] (some (atomE tag env.length a)))
          ((identV tag env.length, BitVec.ofNat 256 (a.eval env)) :: V) st .normal :=
      Step.letVal (evalExpr_lift_nils he) rfl
    have hinv1 : Inv tag Γ c κ ctx w (a.eval env :: env)
        ((identV tag env.length, BitVec.ofNat 256 (a.eval env)) :: V) st :=
      ⟨by rw [hinv.venv, toVEnv_cons], envWF_cons hv hinv.wf, hinv.rel, hinv.ctxr⟩
    have ihk := ih hkS2 (env := a.eval env :: env) (n := n) hkWF
      (by simpa using hnK) hinv1 hNR h0
    obtain ⟨V2, st2, hk⟩ := ihk
    refine ⟨V2, st2, ?_⟩
    rw [hst]
    simp only [emitLet, Emit.stmts_push, Emit.stmts_nil, List.nil_append]
    exact execStmts_append_open (Step.seqCons hlet Step.seqNil) hk
  | ite cond a b iha ihb =>
    intro hS2 w env V st n hwf hn hinv hNR clearLock e' hem
    have ⟨hC, haS2, hbS2⟩ := s2frag_ite.mp hS2
    have hwf' := hwf
    simp [coreWF, Bool.and_eq_true] at hwf'
    obtain ⟨⟨hcWF, haWF⟩, hbWF⟩ := hwf'
    simp only [emitCore] at hem
    obtain ⟨eA, hA⟩ := emitCore_some tag (c := c) (halt := haltUnit) (clearLock := clearLock)
      a ({} : Emit) env.length
    obtain ⟨eB, hB⟩ := emitCore_some tag (c := c) (halt := haltUnit) (clearLock := clearLock)
      b ({} : Emit) env.length
    simp [hA, hB] at hem
    cases hem
    have hn0 : identsNodup tag env.length = true :=
      identsNodup_mono tag (Nat.le_add_right _ _) hn
    have hnA : identsNodup tag (env.length + coreExtraDepth a) = true :=
      identsNodup_mono tag (Nat.add_le_add_left (Nat.le_max_left _ _) _) hn
    have hnB : identsNodup tag (env.length + coreExtraDepth b) = true :=
      identsNodup_mono tag (Nat.add_le_add_left (Nat.le_max_right _ _) _) hn
    have hcond := eval_cond tag (st := st) (List.replicate n []) hinv.venv hinv.wf hn0 hC hcWF
    have hcond' := evalExpr_lift_nils (calls := toCalls o) (n := n) hcond
    have hpush :
        (Emit.push ({} : Emit) (.switch (emitCond tag env.length cond)
          [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts))).stmts =
          [.switch (emitCond tag env.length cond)
            [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts)] := by
      simp [Emit.stmts_push, Emit.stmts_nil]
    rw [hpush]
    by_cases hc : cond.denote env
    · have hne : b2w (decide (cond.denote env)) ≠ 0 :=
        b2w_ne_zero.mpr (decide_eq_true hc)
      have hsel := selectSwitch_nonzero_yulD (calls := toCalls o)
        (eA := eA.stmts) (eB := eB.stmts) hne
      have ihA := iha haS2 (n := n + 1) haWF hnA hinv hNR hA
      obtain ⟨VA, stA, hAexec⟩ := ihA
      have hfuns : List.replicate (n + 1) ([] : FScope (yulD (toCalls o))) =
          [] :: List.replicate n [] := List.replicate_succ ..
      rw [hfuns] at hAexec
      refine ⟨restore V VA, stA, ?_⟩
      exact exec_switch_halt_open hcond' hsel
        (hoist_yulD_of_evm (hoist_emitCore tag hA)) hAexec
    · have hsel := selectSwitch_zero_yulD (calls := toCalls o)
        (eA := eA.stmts) (eB := eB.stmts)
      have : b2w (decide (cond.denote env)) = 0 := by simp [hc, b2w_false]
      have ihB := ihb hbS2 (n := n + 1) hbWF hnB hinv hNR hB
      obtain ⟨VB, stB, hBexec⟩ := ihB
      have hfuns : List.replicate (n + 1) ([] : FScope (yulD (toCalls o))) =
          [] :: List.replicate n [] := List.replicate_succ ..
      rw [hfuns] at hBexec
      refine ⟨restore V VB, stB, ?_⟩
      have hsel' : selectSwitch (yulD (toCalls o)) (b2w (decide (cond.denote env)))
          [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) = eB.stmts := by
        simpa [this] using hsel
      exact exec_switch_halt_open hcond' hsel'
        (hoist_yulD_of_evm (hoist_emitCore tag hB)) hBexec

/-! ## Function and dispatcher progress -/

theorem toYulFn_progress {S E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε}
    {κ ctx} (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    (o : ExtOracle)
    (f : FnDef) (hf : f.kind ≠ .constructor) (hS2 : S2Frag f.core)
    (hbound : 4 + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : toYulFn c f = some yul)
    (w : World S ExtState E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0)
    (hNR : ExtOracle.NoReentry o ctx.self)
    {n : Nat} :
    ∃ V' st', ExecStmts (yulD (toCalls o)) (List.replicate n []) [] st0 yul V' st' .halt := by
  have ⟨hwf, hnod, e, hem, hy⟩ := toYulFn_inv hyul hf
  subst hy
  set args := decodeArgs f st0.env.calldata
  have henv : EnvWF args.reverse := decodeArgs_wf f st0.env.calldata
  have hdec := decodeArgs_runtime (f := f) (cd := st0.env.calldata) hf
  have hpar := params_sim (tag := f.name) (funs := List.replicate n []) st0 4 f.params.length hbound
  have hpar' := execStmts_lift_nils (calls := toCalls o) (n := n) hpar
  have hinv : Inv f.name Γ c κ ctx w args.reverse (toVEnv f.name args.reverse) st0 :=
    ⟨rfl, henv, hR, hctx⟩
  obtain ⟨e0, h0, hst⟩ := emitCore_prefix (tag := f.name) hem
  have hn : identsNodup f.name (f.params.length + coreExtraDepth f.core) = true := by
    simpa [maxDepth] using hnod
  have hn' : identsNodup f.name (args.reverse.length + coreExtraDepth f.core) = true := by
    simpa [args, decodeArgs_length, List.length_reverse] using hn
  have h0' : emitCore f.name c {} args.reverse.length true f.core (locks f) = some e0 := by
    simpa [args, decodeArgs_length, List.length_reverse] using h0
  have ⟨V', st', hexec⟩ :=
    core_progress (tag := f.name) (haltUnit := true) rfl hΓ hκ hlen o f.core hS2
      (n := n) hwf hn' hinv hNR h0'
  refine ⟨V', st', ?_⟩
  rw [hst]
  have hparE : ExecStmts (yulD (toCalls o)) (List.replicate n []) [] st0
      (emitParams f.name {} 4 f.params.length).stmts (toVEnv f.name args.reverse) st0 .normal := by
    convert hpar'
    try simp [args, hdec]
  exact execStmts_append_open hparE hexec

namespace Proof
theorem yul_progress {S E ε : Type}
    (c : ContractDef) (Γ : ContractSchema S ExtState E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (o : ExtOracle)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : runtimeBlock c = some yul)
    (ctx : Ctx) (w : World S ExtState E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0)
    (hNR : ExtOracle.NoReentry o ctx.self) :
    ∃ st' out, Run (yulD (toCalls o))
      (YulEvmCompiler.Optimizer.MemorySpill.eraseMemoryGuardStmts yul) st0 [] st' out := by
  obtain ⟨_, cases, hmap, hy⟩ := runtimeBlock_inv hyul
  obtain ⟨casesE, hmapE, hE⟩ := erase_runtimeBlock hyul
  rw [show casesE = cases from Option.some.inj (hmapE.symm.trans hmap)] at hE
  subst hy
  rw [hE]
  set cd := st0.env.calldata
  have hcd := ctxRel_calldata_lt hctx
  set stA : EvmState := stAfterGuard st0
  have hG : ExecStmt (yulD (toCalls o)) [[]] [] st0 memoryGuardErased [] stA .normal :=
    exec_memoryGuardErased_nils (calls := toCalls o) (n := 1)
  have hMO := memOnly_stAfterGuard st0
  have hctxA := ctxRel_memOnly hctx hMO
  have hRA := R_memOnly hR hMO
  have hcdA : stA.env.calldata = cd := by
    rcases hMO with ⟨_, _, _, _, _, _, _, _, _, hcd', _⟩
    exact hcd'
  have hhoist := hoist_erased_runtime_open (calls := toCalls o) (emitGuardLt {} 4).stmts
    (bop Op.shr [lit 224, bop Op.calldataload [lit 0]]) cases
  set stRev : EvmState :=
    { touchMemory stA 0 0 with halted := some (.revert, []) }
  have hselE := eval_selector_nils (calls := toCalls o) (n := 1) (V := []) (st := stA)
  rw [hcdA] at hselE
  by_cases hLF : LockFree stA
  case neg =>
    have hchk := exec_lockCheck_halt_nils (calls := toCalls o) (n := 1) (V := [])
      (st := stA) hLF
    exact ⟨stRev, .halt,
      run_of_execStmts_open hhoist
        (exec_cons_normal_open hG (exec_head_halt_open hchk))⟩
  case pos =>
  have hLockChk : ExecStmt (yulD (toCalls o)) [[]] [] stA lockCheckStmt [] stA .normal :=
    exec_lockCheck_ok_nils (calls := toCalls o) (n := 1) hLF
  by_cases hshort : cd.length < 4
  · have hguard := guardLt_halt_nils (calls := toCalls o) (m := 2) (V := []) (st := stA)
      (by simpa [hcdA] using hcd) four_lt_wordBound (by simpa [hcdA] using hshort)
    have hblk := exec_block_halt_open (funs := [[]]) (V := [])
      (hoist_yulD_of_evm (hoist_guardLt 4)) hguard
    rw [restore_self_open] at hblk
    exact ⟨stRev, .halt,
      run_of_execStmts_open hhoist
        (exec_cons_normal_open hG (exec_cons_normal_open hLockChk
          (exec_head_halt_open hblk)))⟩
  · have hge4 : 4 ≤ cd.length := Nat.le_of_not_gt hshort
    have hguard := guardLt_ok_nils (calls := toCalls o) (m := 2) (V := []) (st := stA)
      (by simpa [hcdA] using hcd) four_lt_wordBound (by simpa [hcdA] using hge4)
    have hblk4 := exec_block_ok_open (funs := [[]]) (V := [])
      (hoist_yulD_of_evm (hoist_guardLt 4)) hguard
    rw [restore_self_open] at hblk4
    have hswM := selectSwitch_mapM (c := c) (sel := calldataSelector cd)
      (calldataSelector_lt_word cd) hmap
    cases hfind : c.functions.find? (fun f => f.selector = calldataSelector cd) with
    | none =>
      have hswEq : selectSwitch (yulD (toCalls o)) (BitVec.ofNat 256 (calldataSelector cd))
          cases (some [revert00]) = [revert00] := by
        rw [selectSwitch_uncast]
        simpa [hfind] using hswM
      have hswStmt := switch_halt_nil_open (calls := toCalls o) (funs := [[]])
        hselE hswEq (hoist_yulD_of_evm hoist_revert00)
        (revert00_nils (calls := toCalls o) (n := 2) (V := []) (st := stA))
      exact ⟨stRev, .halt,
        run_of_execStmts_open hhoist
          (exec_cons_normal_open hG (exec_cons_normal_open hLockChk
            (exec_pair_halt_open hblk4 hswStmt)))⟩
    | some f =>
      have hfmem : f ∈ c.functions := mem_of_find? hfind
      have hfb := hbound f hfmem
      have ⟨body, hbody, hswEqE⟩ :
          ∃ body, toYulFn c f = some body ∧
            selectSwitch evm (BitVec.ofNat 256 (calldataSelector cd))
              cases (some [revert00]) =
                YulSemantics.Stmt.block
                  (emitGuardLt {} (4 + 32 * f.params.length)).stmts ::
                  lockSetPrefix f ++ [YulSemantics.Stmt.block body] := by
        simpa [hfind] using hswM
      have hswEq : selectSwitch (yulD (toCalls o)) (BitVec.ofNat 256 (calldataSelector cd))
          cases (some [revert00]) =
            YulSemantics.Stmt.block
              (emitGuardLt {} (4 + 32 * f.params.length)).stmts ::
              lockSetPrefix f ++ [YulSemantics.Stmt.block body] := by
        rw [selectSwitch_uncast]; exact hswEqE
      set caseBody : YBlock :=
        YulSemantics.Stmt.block (emitGuardLt {} (4 + 32 * f.params.length)).stmts ::
          lockSetPrefix f ++ [YulSemantics.Stmt.block body]
      have hcaseH : hoist (yulD (toCalls o)) caseBody = [] :=
        hoist_yulD_of_evm (hoist_entryCaseBody f _ _)
      by_cases hshortF : cd.length < 4 + 32 * f.params.length
      · have hgF := guardLt_halt_nils (calls := toCalls o) (m := 3) (V := []) (st := stA)
          (by simpa [hcdA] using hcd) hfb (by simpa [hcdA] using hshortF)
        have hblkF := exec_block_halt_open (funs := [[], []]) (V := [])
          (hoist_yulD_of_evm (hoist_guardLt (4 + 32 * f.params.length))) hgF
        rw [restore_self_open] at hblkF
        have hcase : ExecStmts (yulD (toCalls o)) [[], []] [] stA caseBody [] stRev .halt :=
          exec_head_halt_open hblkF
        have hswStmt := switch_halt_nil_open (calls := toCalls o) (funs := [[]])
          hselE hswEq hcaseH hcase
        exact ⟨stRev, .halt,
          run_of_execStmts_open hhoist
            (exec_cons_normal_open hG (exec_cons_normal_open hLockChk
              (exec_pair_halt_open hblk4 hswStmt)))⟩
      · have hgeF : 4 + 32 * f.params.length ≤ cd.length := Nat.le_of_not_gt hshortF
        have hgF := guardLt_ok_nils (calls := toCalls o) (m := 3) (V := []) (st := stA)
          (by simpa [hcdA] using hcd) hfb (by simpa [hcdA] using hgeF)
        have hblkF := exec_block_ok_open (funs := [[], []]) (V := [])
          (hoist_yulD_of_evm (hoist_guardLt (4 + 32 * f.params.length))) hgF
        rw [restore_self_open] at hblkF
        by_cases hlocks : locks f
        · have hpre : lockSetPrefix f = [lockSetStmt] := by simp [lockSetPrefix, hlocks]
          have hstatic := ctxRel_static hctxA
          have hset := exec_lockSetStmt_nils (calls := toCalls o) (n := 2) (V := [])
            hstatic
          set stL : EvmState :=
            stTstore stA (BitVec.ofNat 256 reentrancyLockSlot) 1
          have hMOL := memOnly_tstore stA
            (BitVec.ofNat 256 reentrancyLockSlot) 1
          have hctxL := ctxRel_memOnly hctxA hMOL
          have hRL := R_memOnly hRA hMOL
          have ⟨V', st', hexecB⟩ :=
            toYulFn_progress hΓ hκ hlen o f
              (hctor f hfmem) (hS2 f hfmem) (hbound f hfmem)
              body hbody w stL hctxL hRL hNR (n := 3)
          have hfH := hoist_yulD_of_evm (calls := toCalls o)
            (toYulFn_hoist hbody (hctor f hfmem))
          have hbodyStmt :
              ExecStmt (yulD (toCalls o)) [[], []] [] stL (.block body) [] st' .halt := by
            have hb := exec_block_halt_open (funs := [[], []]) (V := []) hfH hexecB
            rw [restore_nil_any (D := yulD (toCalls o))] at hb
            exact hb
          have hcase : ExecStmts (yulD (toCalls o)) [[], []] [] stA caseBody [] st' .halt := by
            simp [caseBody, hpre]
            exact exec_cons_normal_open hblkF
              (exec_cons_normal_open hset (exec_head_halt_open hbodyStmt))
          have hswStmt := switch_halt_nil_open (calls := toCalls o) (funs := [[]])
            hselE hswEq hcaseH hcase
          exact ⟨st', .halt,
            run_of_execStmts_open hhoist
              (exec_cons_normal_open hG (exec_cons_normal_open hLockChk
                (exec_pair_halt_open hblk4 hswStmt)))⟩
        · have hpre : lockSetPrefix f = [] := by simp [lockSetPrefix, hlocks]
          have ⟨V', st', hexecB⟩ :=
            toYulFn_progress hΓ hκ hlen o f
              (hctor f hfmem) (hS2 f hfmem) (hbound f hfmem)
              body hbody w stA hctxA hRA hNR (n := 3)
          have hfH := hoist_yulD_of_evm (calls := toCalls o)
            (toYulFn_hoist hbody (hctor f hfmem))
          have hbodyStmt :
              ExecStmt (yulD (toCalls o)) [[], []] [] stA (.block body) [] st' .halt := by
            have hb := exec_block_halt_open (funs := [[], []]) (V := []) hfH hexecB
            rw [restore_nil_any (D := yulD (toCalls o))] at hb
            exact hb
          have hcase : ExecStmts (yulD (toCalls o)) [[], []] [] stA caseBody [] st' .halt := by
            simp [caseBody, hpre]
            exact exec_pair_halt_open hblkF hbodyStmt
          have hswStmt := switch_halt_nil_open (calls := toCalls o) (funs := [[]])
            hselE hswEq hcaseH hcase
          exact ⟨st', .halt,
            run_of_execStmts_open hhoist
              (exec_cons_normal_open hG (exec_cons_normal_open hLockChk
                (exec_pair_halt_open hblk4 hswStmt)))⟩

end Proof

end Lsc.Compiler
