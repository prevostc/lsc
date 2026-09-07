import Lsc.Compiler.Proof.Progress
import Lsc.Compiler.Proof.CoreExtSim

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1200000

/-!
S2 `core_progress` / `yul_progress`: a halted `Run` of compiled S2Frag code exists
under `CallsTotal`.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc hiding Op Stmt

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
    (hV : V = toVEnv (v :: env))
    (hn : identsNodup (v :: env).length = true) :
    ∃ st', ExecStmts (yulD calls) (List.replicate n []) V st
      (emitReturnWords {} [atomE (env.length + 1) (.var 0)]).stmts V st' .halt := by
  have he := eval_atom (funs := List.replicate n []) (st := st) hV hn (.var 0)
  have : (v :: env).length = env.length + 1 := rfl
  simp only [this] at he
  have ⟨st', hexec, _, _⟩ := return_word_sim (c := c) (Γ := Γ) (κ := κ) (w := w)
    (funs := List.replicate n []) V hv he hR
  exact ⟨st', execStmts_lift_nils hexec⟩

/-! ## `core_progress` -/

theorem core_progress {I : Interface} {S X E ε}
    (bs : List (BindEnv I S X)) {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx haltUnit}
    (hhalt : haltUnit = true) (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    {calls : ExternalCalls} (htot : CallsTotal calls)
    {t} (core : Core t) (hS2 : S2Frag core)
    (hslot : BindEnvs.avoids Γ c bs core) :
    ∀ {w : World S X E} {env : List Nat} {V : VEnv evm} {st : EvmState} (n : Nat)
      (hwf : coreWF c core = true)
      (hn : identsNodup (env.length + coreExtraDepth core) = true)
      (hinv : Inv Γ c κ ctx w env V st)
      (hconf : BindEnvs.conforms bs ctx.self w.self calls)
      (hBind : BindEnvs.lookupWF c Γ bs)
      {e' : Emit} (hem : emitCore c {} env.length haltUnit core = some e'),
      ∃ V' st',
        ExecStmts (yulD calls) (List.replicate n []) V st e'.stmts V' st' .halt := by
  revert hS2 hslot
  induction core with
  | ret r =>
    intro hS2 hslot w env V st n hwf hn hinv hconf hBind e' hem
    cases r with
    | pair x y =>
      cases x with
      | word _ =>
        cases y with
        | word _ =>
          exact core_progress_callFree hhalt hΓ hκ hlen _ (by simp [CallFree, M1Frag])
            hwf hn hinv hem
        | _ => cases hS2
      | _ => cases hS2
    | unit | word _ | addr _ | flag _ =>
      exact core_progress_callFree hhalt hΓ hκ hlen _ (by simp [CallFree, M1Frag])
        hwf hn hinv hem
  | revertTail err args =>
    intro hS2 hslot w env V st n hwf hn hinv hconf hBind e' hem
    exact core_progress_callFree hhalt hΓ hκ hlen _ (by simpa [CallFree, M1Frag, S2Frag] using hS2)
      hwf hn hinv hem
  | opTail op =>
    intro hS2 hslot w env V st n hwf hn hinv hconf hBind e' hem
    cases s2op_elim (by simpa [S2Frag] using hS2) with
    | inr hM1 =>
      exact core_progress_callFree hhalt hΓ hκ hlen (.opTail op)
        (by simpa [CallFree, M1Frag] using hM1) hwf hn hinv hem
    | inl hcall =>
      obtain ⟨b, m, args, rfl⟩ := hcall
      simp only [emitCore] at hem
      cases hE : emitLetOp c {} env.length (.call b m args) with
      | none => simp [hE] at hem
      | some e1 =>
        simp only [hE] at hem
        cases hem
        rw [emitRet_word_stmts]
        have hopWF : callWF c b m args = true := by simpa [coreWF, opWF] using hwf
        obtain ⟨eCall, heCall, meth, hbd⟩ := hBind b m args hopWF
        have hn0 : identsNodup env.length = true :=
          identsNodup_mono (by simp [coreExtraDepth]) hn
        have hn1 : identsNodup (env.length + 1) = true :=
          identsNodup_mono (by simp [coreExtraDepth]) hn
        have hinvT : Inv Γ c κ ctx w env (toVEnv env) st := by rwa [hinv.venv] at hinv
        have hcallP :=
          op_call_progress (I := I) eCall.α eCall.bind htot (n := n) hinvT hbd
            (hconf eCall heCall) hopWF hn0 hn1
        obtain ⟨V1, st1, o1, hexec, ho⟩ := hcallP
        rw [hE] at hexec
        rcases ho with ho | ⟨ho, v, hVeq, hinv1⟩
        · subst ho
          exact ⟨V1, st1, execStmts_append_halt_open (by simpa [hinv.venv] using hexec)⟩
        · subst ho
          have hn1' : identsNodup (v :: env).length = true := by simpa using hn1
          have hv : v < wordBound := hinv1.wf v (by simp)
          have ⟨stR, hret⟩ :=
            return_var0_progress (κ := κ) (w := w) (st := st1) (calls := calls) (n := n)
              hv hinv1.rel hVeq hn1'
          exact ⟨V1, stR, execStmts_append_open (by simpa [hinv.venv] using hexec)
            (by simpa [hVeq] using hret)⟩
  | opTailAddr op =>
    intro hS2 hslot w env V st n hwf hn hinv hconf hBind e' hem
    cases s2op_elim (by simpa [S2Frag] using hS2) with
    | inr hM1 =>
      exact core_progress_callFree hhalt hΓ hκ hlen (.opTailAddr op)
        (by simpa [CallFree, M1Frag] using hM1) hwf hn hinv hem
    | inl hcall =>
      obtain ⟨b, m, args, rfl⟩ := hcall
      simp only [emitCore] at hem
      cases hE : emitLetOp c {} env.length (.call b m args) with
      | none => simp [hE] at hem
      | some e1 =>
        simp only [hE] at hem
        cases hem
        rw [emitRet_addr_stmts]
        have hopWF : callWF c b m args = true := by simpa [coreWF, opWF] using hwf
        obtain ⟨eCall, heCall, meth, hbd⟩ := hBind b m args hopWF
        have hn0 : identsNodup env.length = true :=
          identsNodup_mono (by simp [coreExtraDepth]) hn
        have hn1 : identsNodup (env.length + 1) = true :=
          identsNodup_mono (by simp [coreExtraDepth]) hn
        have hinvT : Inv Γ c κ ctx w env (toVEnv env) st := by rwa [hinv.venv] at hinv
        have hcallP :=
          op_call_progress (I := I) eCall.α eCall.bind htot (n := n) hinvT hbd
            (hconf eCall heCall) hopWF hn0 hn1
        obtain ⟨V1, st1, o1, hexec, ho⟩ := hcallP
        rw [hE] at hexec
        rcases ho with ho | ⟨ho, v, hVeq, hinv1⟩
        · subst ho
          exact ⟨V1, st1, execStmts_append_halt_open (by simpa [hinv.venv] using hexec)⟩
        · subst ho
          have hn1' : identsNodup (v :: env).length = true := by simpa using hn1
          have hv : v < wordBound := hinv1.wf v (by simp)
          have ⟨stR, hret⟩ :=
            return_var0_progress (κ := κ) (w := w) (st := st1) (calls := calls) (n := n)
              hv hinv1.rel hVeq hn1'
          exact ⟨V1, stR, execStmts_append_open (by simpa [hinv.venv] using hexec)
            (by simpa [hVeq] using hret)⟩
  | opTailFlag op =>
    intro hS2 hslot w env V st n hwf hn hinv hconf hBind e' hem
    cases s2op_elim (by simpa [S2Frag] using hS2) with
    | inr hM1 =>
      exact core_progress_callFree hhalt hΓ hκ hlen (.opTailFlag op)
        (by simpa [CallFree, M1Frag] using hM1) hwf hn hinv hem
    | inl hcall =>
      obtain ⟨b, m, args, rfl⟩ := hcall
      simp only [emitCore] at hem
      cases hE : emitLetOp c {} env.length (.call b m args) with
      | none => simp [hE] at hem
      | some e1 =>
        simp only [hE] at hem
        cases hem
        rw [emitRet_flag_stmts]
        have hopWF : callWF c b m args = true := by simpa [coreWF, opWF] using hwf
        obtain ⟨eCall, heCall, meth, hbd⟩ := hBind b m args hopWF
        have hn0 : identsNodup env.length = true :=
          identsNodup_mono (by simp [coreExtraDepth]) hn
        have hn1 : identsNodup (env.length + 1) = true :=
          identsNodup_mono (by simp [coreExtraDepth]) hn
        have hinvT : Inv Γ c κ ctx w env (toVEnv env) st := by rwa [hinv.venv] at hinv
        have hcallP :=
          op_call_progress (I := I) eCall.α eCall.bind htot (n := n) hinvT hbd
            (hconf eCall heCall) hopWF hn0 hn1
        obtain ⟨V1, st1, o1, hexec, ho⟩ := hcallP
        rw [hE] at hexec
        rcases ho with ho | ⟨ho, v, hVeq, hinv1⟩
        · subst ho
          exact ⟨V1, st1, execStmts_append_halt_open (by simpa [hinv.venv] using hexec)⟩
        · subst ho
          have hn1' : identsNodup (v :: env).length = true := by simpa using hn1
          have hv : v < wordBound := hinv1.wf v (by simp)
          have ⟨stR, hret⟩ :=
            return_var0_progress (κ := κ) (w := w) (st := st1) (calls := calls) (n := n)
              hv hinv1.rel hVeq hn1'
          exact ⟨V1, stR, execStmts_append_open (by simpa [hinv.venv] using hexec)
            (by simpa [hVeq] using hret)⟩
  | stmtTail s =>
    intro hS2 hslot w env V st n hwf hn hinv hconf hBind e' hem
    cases s2stmt_elim (by simpa [S2Frag] using hS2) with
    | inr hM1 =>
      exact core_progress_callFree hhalt hΓ hκ hlen (.stmtTail s)
        (by simpa [CallFree, M1Frag] using hM1) hwf hn hinv hem
    | inl hcall =>
      obtain ⟨b, m, args, rfl⟩ := hcall
      simp only [emitCore, hhalt] at hem
      cases hem
      rw [emitReturnUnit_true]
      have hopWF : callWF c b m args = true := by simpa [coreWF, stmtWF] using hwf
      obtain ⟨eCall, heCall, meth, hbd⟩ := hBind b m args hopWF
      have hn0 : identsNodup env.length = true := by simpa [coreExtraDepth] using hn
      have hinvT : Inv Γ c κ ctx w env (toVEnv env) st := by rwa [hinv.venv] at hinv
      have hcallP :=
        stmt_call_progress (I := I) eCall.α eCall.bind htot (n := n) hinvT hbd
          (hconf eCall heCall) hopWF hn0
      obtain ⟨V1, st1, o1, hexec, ho⟩ := hcallP
      rcases ho with ho | ⟨ho, hVeq, hinv1⟩
      · subst ho
        exact ⟨V1, st1, execStmts_append_halt_open (by simpa [hinv.venv] using hexec)⟩
      · subst ho
        have hstop :=
          execStmts_lift_nils (calls := calls) (n := n)
            (stop_sim (List.replicate n []) V1 st1)
        exact ⟨V1, _, execStmts_append_open (by simpa [hinv.venv] using hexec)
          (by simpa [hVeq] using hstop)⟩
  | letOp op k ih =>
    intro hS2 hslot w env V st n hwf hn hinv hconf hBind e' hem
    have ⟨hopS2, hkS2⟩ := s2frag_letOp.mp hS2
    obtain ⟨e1, e0, h1, h0, hst⟩ := emitCore_letOp_split hem
    have ⟨hwfOp, hwfK⟩ : opWF c op = true ∧ coreWF c k = true := by
      simpa [coreWF, Bool.and_eq_true] using hwf
    have hn0 : identsNodup env.length = true :=
      identsNodup_mono (Nat.le_add_right env.length _) hn
    have hn1 : identsNodup (env.length + 1) = true :=
      identsNodup_mono (Nat.le_add_right (env.length + 1) (coreExtraDepth k))
        (by simpa [coreExtraDepth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn)
    have hnK : identsNodup ((env.length + 1) + coreExtraDepth k) = true := by
      simpa [coreExtraDepth, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
    rw [hst]
    cases s2op_elim hopS2 with
    | inr hM1 =>
      have hsim := op_sim (List.replicate n []) hinv hΓ hκ hlen hM1 hwfOp hn1
      cases hrun : Tx.run (Op.denote Γ env op) ctx w with
      | ok p =>
        simp only [hrun, except_ok_prod] at hsim
        obtain ⟨st1, hexec, hinv1⟩ := hsim
        simp only [h1] at hexec
        rcases p with ⟨v, w'⟩
        have hexec' := execStmts_lift_nils (calls := calls) (n := n) hexec
        have hw : w' = w := m1op_world (Γ := Γ) hM1 env ctx w (by simpa [Tx.run] using hrun)
        have ihk := ih hkS2 (BindEnvs.avoids_letOp hslot) (env := v :: env) (n := n) hwfK hnK hinv1
          (BindEnvs.conforms_self (congrArg World.self hw) hconf) hBind h0
        obtain ⟨V2, st2, hk⟩ := ihk
        exact ⟨V2, st2, execStmts_append_open hexec' hk⟩
      | error e =>
        simp only [hrun, except_error_prod] at hsim
        obtain ⟨V1, st1, _, hexec, _, _⟩ := hsim
        simp only [h1] at hexec
        exact ⟨V1, st1, execStmts_append_halt_open (execStmts_lift_nils hexec)⟩
    | inl hcall =>
      obtain ⟨b, m, args, rfl⟩ := hcall
      have hopWF : callWF c b m args = true := by simpa [opWF] using hwfOp
      obtain ⟨eCall, heCall, meth, hbd⟩ := hBind b m args hopWF
      have hinvT : Inv Γ c κ ctx w env (toVEnv env) st := by rwa [hinv.venv] at hinv
      have hcallP :=
        op_call_progress (I := I) eCall.α eCall.bind htot (n := n) hinvT hbd
          (hconf eCall heCall) hopWF hn0 hn1
      obtain ⟨V1, st1, o1, hexec, ho⟩ := hcallP
      simp only [h1] at hexec
      rcases ho with ho | ⟨ho, v, hVeq, hinv1⟩
      · subst ho
        exact ⟨V1, st1, execStmts_append_halt_open (by simpa [hinv.venv] using hexec)⟩
      · subst ho
        have ihk := ih hkS2 (BindEnvs.avoids_letOp hslot) (env := v :: env) (n := n) hwfK hnK
          (by simpa [hVeq] using hinv1) hconf hBind h0
        obtain ⟨V2, st2, hk⟩ := ihk
        exact ⟨V2, st2, execStmts_append_open (by simpa [hinv.venv, hVeq] using hexec) hk⟩
  | seq s k ih =>
    intro hS2 hslot w env V st n hwf hn hinv hconf hBind e' hem
    have ⟨hsS2, hkS2⟩ := s2frag_seq.mp hS2
    obtain ⟨e0, h0, hst⟩ := emitCore_seq_split hem
    have ⟨hwfS, hwfK⟩ : stmtWF c s = true ∧ coreWF c k = true := by
      simpa [coreWF, Bool.and_eq_true] using hwf
    have hn0 : identsNodup env.length = true :=
      identsNodup_mono (Nat.le_add_right _ _) hn
    have hnK : identsNodup (env.length + coreExtraDepth k) = true := by
      simpa [coreExtraDepth] using hn
    rw [hst]
    cases s2stmt_elim hsS2 with
    | inr hM1 =>
      have hsim := stmt_sim (List.replicate n []) hinv hΓ hκ hlen hM1 hwfS hn0
      cases hrun : Tx.run (Stmt.denote Γ env s) ctx w with
      | ok p =>
        simp only [hrun, except_ok_prod] at hsim
        obtain ⟨st1, hexec, hinv1⟩ := hsim
        have hexec' := execStmts_lift_nils (calls := calls) (n := n) hexec
        rcases p with ⟨_, w'⟩
        have ha : ∀ e ∈ bs, e.bind.addr w'.self = e.bind.addr w.self := by
          intro e he
          obtain ⟨slot, hs, hkind, hav⟩ := hslot e he
          exact m1stmt_preserves_addr (I := I) (bind := e.bind) hΓ hs hkind hM1 hwfS hav.1
            env ctx w (by simpa [Tx.run] using hrun)
        have hconf' : BindEnvs.conforms bs ctx.self w'.self calls := by
          intro e he
          simpa [ha e he] using hconf e he
        have ihk := ih hkS2 (BindEnvs.avoids_seq hslot) (n := n) hwfK hnK hinv1
          hconf' hBind h0
        obtain ⟨V2, st2, hk⟩ := ihk
        exact ⟨V2, st2, execStmts_append_open hexec' hk⟩
      | error e =>
        simp only [hrun, except_error_prod] at hsim
        obtain ⟨V1, st1, _, hexec, _, _⟩ := hsim
        exact ⟨V1, st1, execStmts_append_halt_open (execStmts_lift_nils hexec)⟩
    | inl hcall =>
      obtain ⟨b, m, args, rfl⟩ := hcall
      have hopWF : callWF c b m args = true := by simpa [stmtWF] using hwfS
      obtain ⟨eCall, heCall, meth, hbd⟩ := hBind b m args hopWF
      have hinvT : Inv Γ c κ ctx w env (toVEnv env) st := by rwa [hinv.venv] at hinv
      have hcallP :=
        stmt_call_progress (I := I) eCall.α eCall.bind htot (n := n) hinvT hbd
          (hconf eCall heCall) hopWF hn0
      obtain ⟨V1, st1, o1, hexec, ho⟩ := hcallP
      rcases ho with ho | ⟨ho, hVeq, hinv1⟩
      · subst ho
        exact ⟨V1, st1, execStmts_append_halt_open (by simpa [hinv.venv] using hexec)⟩
      · subst ho
        have ihk := ih hkS2 (BindEnvs.avoids_seq hslot) (n := n) hwfK hnK
          (by simpa [hVeq] using hinv1) hconf hBind h0
        obtain ⟨V2, st2, hk⟩ := ihk
        exact ⟨V2, st2, execStmts_append_open (by simpa [hinv.venv, hVeq] using hexec) hk⟩
  | letPure p args k ih =>
    intro hS2 hslot w env V st n hwf hn hinv hconf hBind e' hem
    have ⟨hp, hargs, hkS2⟩ := s2frag_letPure.mp hS2
    subst hp
    have ⟨a, hargs'⟩ := length_eq_one.mp hargs
    subst hargs'
    have ⟨hwfA, hkWF⟩ : atomWF a = true ∧ coreWF c k = true := by
      simpa [coreWF, Bool.and_eq_true] using hwf
    simp only [emitCore, emitPrim] at hem
    obtain ⟨e0, h0, hst⟩ := emitCore_prefix hem
    have hn0 : identsNodup env.length = true :=
      identsNodup_mono (Nat.le_add_right env.length _) hn
    have hnK : identsNodup ((env.length + 1) + coreExtraDepth k) = true := by
      simpa [coreExtraDepth, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
    have he := eval_atom (List.replicate n []) (st := st) hinv.venv hn0 a
    have hv := atom_eval_lt hinv.wf hwfA
    have hlet :
        ExecStmt (yulD calls) (List.replicate n []) V st
          (.letDecl [identV env.length] (some (atomE env.length a)))
          ((identV env.length, BitVec.ofNat 256 (a.eval env)) :: V) st .normal :=
      Step.letVal (evalExpr_lift_nils he) rfl
    have hinv1 : Inv Γ c κ ctx w (a.eval env :: env)
        ((identV env.length, BitVec.ofNat 256 (a.eval env)) :: V) st :=
      ⟨by rw [hinv.venv, toVEnv_cons], envWF_cons hv hinv.wf, hinv.rel, hinv.ctxr⟩
    have ihk := ih hkS2 (BindEnvs.avoids_letPure hslot) (env := a.eval env :: env) (n := n) hkWF (by simpa using hnK) hinv1 hconf hBind h0
    obtain ⟨V2, st2, hk⟩ := ihk
    refine ⟨V2, st2, ?_⟩
    rw [hst]
    simp only [emitLet, Emit.stmts_push, Emit.stmts_nil, List.nil_append]
    exact execStmts_append_open (Step.seqCons hlet Step.seqNil) hk
  | ite cond a b iha ihb =>
    intro hS2 hslot w env V st n hwf hn hinv hconf hBind e' hem
    have ⟨hC, haS2, hbS2⟩ := s2frag_ite.mp hS2
    have hwf' := hwf
    simp [coreWF, Bool.and_eq_true] at hwf'
    obtain ⟨⟨hcWF, haWF⟩, hbWF⟩ := hwf'
    simp only [emitCore] at hem
    obtain ⟨eA, hA⟩ := emitCore_some (c := c) (halt := haltUnit) a ({} : Emit) env.length
    obtain ⟨eB, hB⟩ := emitCore_some (c := c) (halt := haltUnit) b ({} : Emit) env.length
    simp [hA, hB] at hem
    cases hem
    have hn0 : identsNodup env.length = true :=
      identsNodup_mono (Nat.le_add_right _ _) hn
    have hnA : identsNodup (env.length + coreExtraDepth a) = true :=
      identsNodup_mono (Nat.add_le_add_left (Nat.le_max_left _ _) _) hn
    have hnB : identsNodup (env.length + coreExtraDepth b) = true :=
      identsNodup_mono (Nat.add_le_add_left (Nat.le_max_right _ _) _) hn
    have hcond := eval_cond (st := st) (List.replicate n []) hinv.venv hinv.wf hn0 hC hcWF
    have hcond' := evalExpr_lift_nils (calls := calls) (n := n) hcond
    have hpush :
        (Emit.push ({} : Emit) (.switch (emitCond env.length cond)
          [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts))).stmts =
          [.switch (emitCond env.length cond)
            [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts)] := by
      simp [Emit.stmts_push, Emit.stmts_nil]
    rw [hpush]
    by_cases hc : cond.denote env
    · have hne : b2w (decide (cond.denote env)) ≠ 0 :=
        b2w_ne_zero.mpr (decide_eq_true hc)
      have hsel := selectSwitch_nonzero_yulD (calls := calls) (eA := eA.stmts) (eB := eB.stmts) hne
      have ihA := iha haS2 (BindEnvs.avoids_ite hslot).1 (n := n + 1) haWF hnA hinv hconf hBind hA
      obtain ⟨VA, stA, hAexec⟩ := ihA
      have hfuns : List.replicate (n + 1) ([] : FScope (yulD calls)) =
          [] :: List.replicate n [] := List.replicate_succ ..
      rw [hfuns] at hAexec
      refine ⟨restore V VA, stA, ?_⟩
      exact exec_switch_halt_open hcond' hsel
        (hoist_yulD_of_evm (hoist_emitCore hA)) hAexec
    · have hsel := selectSwitch_zero_yulD (calls := calls) (eA := eA.stmts) (eB := eB.stmts)
      have : b2w (decide (cond.denote env)) = 0 := by simp [hc, b2w_false]
      have ihB := ihb hbS2 (BindEnvs.avoids_ite hslot).2 (n := n + 1) hbWF hnB hinv hconf hBind hB
      obtain ⟨VB, stB, hBexec⟩ := ihB
      have hfuns : List.replicate (n + 1) ([] : FScope (yulD calls)) =
          [] :: List.replicate n [] := List.replicate_succ ..
      rw [hfuns] at hBexec
      refine ⟨restore V VB, stB, ?_⟩
      have hsel' : selectSwitch (yulD calls) (b2w (decide (cond.denote env)))
          [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) = eB.stmts := by
        simpa [this] using hsel
      exact exec_switch_halt_open hcond' hsel'
        (hoist_yulD_of_evm (hoist_emitCore hB)) hBexec

/-! ## Function and dispatcher progress -/

theorem toYulFn_progress {I : Interface} {S X E ε : Type}
    (bs : List (BindEnv I S X)) {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    {calls : ExternalCalls} (htot : CallsTotal calls)
    (f : FnDef) (hf : f.kind ≠ .constructor) (hS2 : S2Frag f.core)
    (hslot : BindEnvs.avoids Γ c bs f.core)
    (hbound : 4 + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : toYulFn c f = some yul)
    (w : World S X E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0)
    (hconf : BindEnvs.conforms bs ctx.self w.self calls)
    (hBind : BindEnvs.lookupWF c Γ bs)
    {n : Nat} :
    ∃ V' st', ExecStmts (yulD calls) (List.replicate n []) [] st0 yul V' st' .halt := by
  have ⟨hwf, hnod, e, hem, hy⟩ := toYulFn_inv hyul hf
  subst hy
  set args := decodeArgs f st0.env.calldata
  have henv : EnvWF args.reverse := decodeArgs_wf f st0.env.calldata
  have hdec := decodeArgs_runtime (f := f) (cd := st0.env.calldata) hf
  have hpar := params_sim (funs := List.replicate n []) st0 4 f.params.length hbound
  have hpar' := execStmts_lift_nils (calls := calls) (n := n) hpar
  have hinv : Inv Γ c κ ctx w args.reverse (toVEnv args.reverse) st0 :=
    ⟨rfl, henv, hR, hctx⟩
  obtain ⟨e0, h0, hst⟩ := emitCore_prefix hem
  have hn : identsNodup (f.params.length + coreExtraDepth f.core) = true := by
    simpa [maxDepth] using hnod
  have hn' : identsNodup (args.reverse.length + coreExtraDepth f.core) = true := by
    simpa [args, decodeArgs_length, List.length_reverse] using hn
  have h0' : emitCore c {} args.reverse.length true f.core = some e0 := by
    simpa [args, decodeArgs_length, List.length_reverse] using h0
  have ⟨V', st', hexec⟩ :=
    core_progress (I := I) bs (haltUnit := true) rfl hΓ hκ hlen htot f.core hS2 hslot
      (n := n) hwf hn' hinv hconf hBind h0'
  refine ⟨V', st', ?_⟩
  rw [hst]
  have hparE : ExecStmts (yulD calls) (List.replicate n []) [] st0
      (emitParams {} 4 f.params.length).stmts (toVEnv args.reverse) st0 .normal := by
    convert hpar'
    try simp [args, hdec]
  exact execStmts_append_open hparE hexec

theorem yul_progress {I : Interface} {S X E ε : Type}
    (bs : List (BindEnv I S X)) (c : ContractDef) (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (calls : ExternalCalls) (htot : CallsTotal calls)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : runtimeBlock c = some yul)
    (ctx : Ctx) (w : World S X E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0)
    (hconf : BindEnvs.conforms bs ctx.self w.self calls)
    (hBind : BindEnvs.lookupWF c Γ bs)
    (hslot : ∀ f ∈ c.functions, BindEnvs.avoids Γ c bs f.core) :
    ∃ st' o, Run (yulD calls) yul st0 [] st' o := by
  obtain ⟨_, cases, hmap, hy⟩ := runtimeBlock_inv hyul
  subst hy
  set cd := st0.env.calldata
  have hcd := ctxRel_calldata_lt hctx
  have hhoist := hoist_yulD_of_evm (calls := calls)
    (hoist_runtime (emitGuardLt {} 4).stmts
      (bop Op.shr [lit 224, bop Op.calldataload [lit 0]]) cases)
  set stRev : EvmState :=
    { touchMemory st0 0 0 with halted := some (.revert, []) }
  have hselE := eval_selector_nils (calls := calls) (n := 1) (V := []) (st := st0)
  by_cases hshort : cd.length < 4
  · have hguard := guardLt_halt_nils (calls := calls) (m := 2) (V := []) (st := st0)
      hcd four_lt_wordBound hshort
    have hblk := exec_block_halt_open (funs := [[]]) (V := [])
      (hoist_yulD_of_evm (hoist_guardLt 4)) hguard
    rw [restore_self_open] at hblk
    exact ⟨stRev, .halt, run_of_execStmts_open hhoist (exec_head_halt_open hblk)⟩
  · have hge4 : 4 ≤ cd.length := Nat.le_of_not_gt hshort
    have hguard := guardLt_ok_nils (calls := calls) (m := 2) (V := []) (st := st0)
      hcd four_lt_wordBound hge4
    have hblk4 := exec_block_ok_open (funs := [[]]) (V := [])
      (hoist_yulD_of_evm (hoist_guardLt 4)) hguard
    rw [restore_self_open] at hblk4
    have hswM := selectSwitch_mapM (c := c) (sel := calldataSelector cd)
      (calldataSelector_lt_word cd) hmap
    cases hfind : c.functions.find? (fun f => f.selector = calldataSelector cd) with
    | none =>
      have hswEq : selectSwitch (yulD calls) (BitVec.ofNat 256 (calldataSelector cd))
          cases (some [revert00]) = [revert00] := by
        rw [selectSwitch_uncast]
        simpa [hfind] using hswM
      have hswStmt := switch_halt_nil_open (calls := calls) (funs := [[]])
        hselE hswEq (hoist_yulD_of_evm hoist_revert00)
        (revert00_nils (calls := calls) (n := 2) (V := []) (st := st0))
      exact ⟨stRev, .halt, run_of_execStmts_open hhoist (exec_pair_halt_open hblk4 hswStmt)⟩
    | some f =>
      have hfmem : f ∈ c.functions := mem_of_find? hfind
      have hfb := hbound f hfmem
      have ⟨body, hbody, hswEqE⟩ :
          ∃ body, toYulFn c f = some body ∧
            selectSwitch evm (BitVec.ofNat 256 (calldataSelector cd))
              cases (some [revert00]) =
                [YulSemantics.Stmt.block
                  (emitGuardLt {} (4 + 32 * f.params.length)).stmts,
                  YulSemantics.Stmt.block body] := by
        simpa [hfind] using hswM
      have hswEq : selectSwitch (yulD calls) (BitVec.ofNat 256 (calldataSelector cd))
          cases (some [revert00]) =
            [YulSemantics.Stmt.block
              (emitGuardLt {} (4 + 32 * f.params.length)).stmts,
              YulSemantics.Stmt.block body] := by
        rw [selectSwitch_uncast]; exact hswEqE
      set caseBody : YBlock :=
        [YulSemantics.Stmt.block (emitGuardLt {} (4 + 32 * f.params.length)).stmts,
          YulSemantics.Stmt.block body]
      have hcaseH : hoist (yulD calls) caseBody = [] :=
        hoist_yulD_of_evm (hoist_two_blocks _ _)
      by_cases hshortF : cd.length < 4 + 32 * f.params.length
      · have hgF := guardLt_halt_nils (calls := calls) (m := 3) (V := []) (st := st0)
          hcd hfb hshortF
        have hblkF := exec_block_halt_open (funs := [[], []]) (V := [])
          (hoist_yulD_of_evm (hoist_guardLt (4 + 32 * f.params.length))) hgF
        rw [restore_self_open] at hblkF
        have hcase : ExecStmts (yulD calls) [[], []] [] st0 caseBody [] stRev .halt :=
          exec_head_halt_open hblkF
        have hswStmt := switch_halt_nil_open (calls := calls) (funs := [[]])
          hselE hswEq hcaseH hcase
        exact ⟨stRev, .halt, run_of_execStmts_open hhoist (exec_pair_halt_open hblk4 hswStmt)⟩
      · have hgeF : 4 + 32 * f.params.length ≤ cd.length := Nat.le_of_not_gt hshortF
        have hgF := guardLt_ok_nils (calls := calls) (m := 3) (V := []) (st := st0)
          hcd hfb hgeF
        have hblkF := exec_block_ok_open (funs := [[], []]) (V := [])
          (hoist_yulD_of_evm (hoist_guardLt (4 + 32 * f.params.length))) hgF
        rw [restore_self_open] at hblkF
        have ⟨V', st', hexecB⟩ :=
          toYulFn_progress (I := I) bs hΓ hκ hlen htot f
            (hctor f hfmem) (hS2 f hfmem) (hslot f hfmem) (hbound f hfmem)
            body hbody w st0 hctx hR hconf hBind (n := 3)
        have hfH := hoist_yulD_of_evm (calls := calls) (toYulFn_hoist hbody (hctor f hfmem))
        have hbodyStmt :
            ExecStmt (yulD calls) [[], []] [] st0 (.block body) [] st' .halt := by
          have hb := exec_block_halt_open (funs := [[], []]) (V := []) hfH hexecB
          rw [restore_nil_any (D := yulD calls)] at hb
          exact hb
        have hcase : ExecStmts (yulD calls) [[], []] [] st0 caseBody [] st' .halt :=
          exec_pair_halt_open hblkF hbodyStmt
        have hswStmt := switch_halt_nil_open (calls := calls) (funs := [[]])
          hselE hswEq hcaseH hcase
        exact ⟨st', .halt, run_of_execStmts_open hhoist (exec_pair_halt_open hblk4 hswStmt)⟩

end Lsc.Compiler

