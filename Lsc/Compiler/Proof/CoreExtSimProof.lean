import Lsc.Compiler.Proof.CoreExtCall
import Lsc.Lang.CoreTheorems
import Lsc.Compiler.CoreExtSimDefs

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

/-!
Proofs of S2 backward `core_sim_ext` / `toYulFn_correct_ext`.
Statements live in `CoreExtSimTheorems`. Helpers stay in this module under
`Lsc.Compiler.Proof`.
-/

namespace Lsc.Compiler.Proof

open YulSemantics
open YulSemantics.EVM
open Lsc hiding Op Stmt
open Lsc.Compiler

/-- Call-free backward simulation: S1 `core_sim` + descend + fault remapping. -/
theorem core_sim_ext_callFree {I : Interface} {S X E ε}
    (bs : List (BindEnv I S X)) {c Γ κ ctx haltUnit}
    (hhalt : haltUnit = true) (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound) (hign : BindEnvs.ignoresLocal bs)
    {calls : ExternalCalls} {t} (core : Core t) (hM1 : CallFree core)
    (hslot : BindEnvs.avoids Γ c bs core) :
    ∀ {w : World S X E} {env V st} (funs : FunEnv (yulD calls))
      (hfuns : noExtFuns funs = true) (hwf : coreWF c core = true)
      (hn : identsNodup (env.length + coreExtraDepth core) = true)
      (hinv : Inv Γ c κ ctx w env V st) (hRX : RXs bs w st)
      (hBindNe : BindEnvs.neSelf bs ctx.self w.self)
      (hconf : BindEnvs.conforms bs ctx.self w.self calls)
      (hinj : BindEnvs.addrInj bs w.self)
      (hBind : BindEnvs.lookupWF c Γ bs)
      {e'} (hem : emitCore c {} env.length haltUnit core = some e')
      {V' st' o} (hexec : ExecStmts (yulD calls) funs V st e'.stmts V' st' o),
      ∃ fo, ∀ g, oracleAgrees w.ncalls fo g →
        match (Tx.run (Core.denote Γ core env) ctx { w with faults := g } :
            Except (Err ε) (t.denote × World S X E)) with
        | .ok (v, w') =>
            o = Outcome.halt ∧ haltSuccess t v st'.halted ∧
              R c Γ κ w' st' ∧ RXs bs w' st'
        | .error e =>
            ∃ bytes, o = Outcome.halt ∧ st'.halted = some (HaltKind.revert, bytes) ∧
              haltError c Γ e bytes := by
  intro w env V st funs hfuns hwf hn hinv hRX hBindNe _hconf _hinj _hBind e' hem V' st' o hexec
  refine ⟨fun _ => false, ?_⟩
  intro g _hg
  have hno : noExtBlock e'.stmts = true :=
    noExt_core_callFree hM1 {} env.length hem (by simp [Emit.stmts_nil])
  have hdesc := execStmts_descend hfuns hno hexec
  have hS1 :=
    core_sim (c := c) (Γ := Γ) (κ := κ) (ctx := ctx) hhalt hΓ hκ hlen core hM1
      (funEnvUncast calls funs) hwf hn hinv hem
  have hmap := callFree_run_faults (Γ := Γ) hM1 env ctx w g
  cases hTx : Tx.run (Core.denote Γ core env) ctx w with
  | ok p =>
    rcases p with ⟨v, w0⟩
    have hok : Core.denote Γ core env ctx w = .ok (v, w0) := by
      simpa [Tx.run] using hTx
    have haddr := callFree_addrs hΓ hM1 hwf hslot env ctx w hok
    have hg := callFree_preserves_ghost (Γ := Γ) hM1 env ctx w hok
    rw [hTx] at hS1 hmap
    simp only [except_ok_prod, mapWorldFaults] at hS1 hmap ⊢
    rw [hmap]
    simp only [mapWorldFaults]
    obtain ⟨V1, st1, hexecS1, hsucc, hR⟩ := hS1
    obtain ⟨hVeq, hsteq, hoeq⟩ := execStmts_det_evm hdesc hexecS1
    subst hVeq; subst hsteq; subst hoeq
    refine ⟨rfl, hsucc, (R_faults g).mpr hR, ?_⟩
    exact RXs_callFree ((RXs_faults g).mpr hRX)
      (fun e he =>
        ofState_noExt_halt (hign e he) hfuns hno hexec (e.bind.addr w.self)
          (foreign_of_ctx hinv.ctxr (hBindNe e he)))
      hg.1 haddr
  | error err =>
    rw [hTx] at hS1 hmap
    simp only [except_error_prod, mapWorldFaults] at hS1 hmap ⊢
    rw [hmap]
    obtain ⟨V1, st1, bytes, hexecS1, hh, herr⟩ := hS1
    obtain ⟨hVeq, hsteq, hoeq⟩ := execStmts_det_evm hdesc hexecS1
    subst hVeq; subst hsteq; subst hoeq
    exact ⟨bytes, rfl, hh, herr⟩

theorem emitCore_letOp_split {c : ContractDef} {halt : Bool} {t : RetTy}
    {op : Lsc.Op} {k : Core t} {e' : Emit} {d : Nat}
    (hem : emitCore c {} d halt (.letOp op k) = some e') :
    ∃ e1 e0, emitLetOp c {} d op = some e1 ∧
      emitCore c {} (d + 1) halt k = some e0 ∧
      e'.stmts = e1.stmts ++ e0.stmts := by
  simp only [emitCore] at hem
  cases hE : emitLetOp c {} d op with
  | none => simp [hE] at hem
  | some e1 =>
    simp only [hE] at hem
    obtain ⟨e0, h0, hst⟩ := emitCore_prefix hem
    exact ⟨e1, e0, rfl, h0, hst⟩

theorem selectSwitch_zero_yulD {calls : ExternalCalls} {eA eB : YBlock} :
    selectSwitch (yulD calls) (0 : U256)
      [(YulSemantics.Literal.number 0, eB)] (some eA) = eB := by
  simp [selectSwitch, litValue_number]

theorem selectSwitch_nonzero_yulD {calls : ExternalCalls} {eA eB : YBlock} {cv : U256}
    (h : cv ≠ 0) :
    selectSwitch (yulD calls) cv
      [(YulSemantics.Literal.number 0, eB)] (some eA) = eA := by
  have hne : cv ≠ (yulD calls).litValue (.number 0) := by
    rw [show (yulD calls).litValue (.number 0) = (0 : U256) from litValue_number 0]
    exact h
  simp [selectSwitch, List.find?, decide_eq_false hne]

/-- S2 backward `core_sim` for every `S2Frag` core. Call-free constructors
delegate to `core_sim_ext_callFree`. A `.call` head uses `op_sim_call_bwd` /
`stmt_sim_call_bwd`; success composes oracles as
`composeFault w.ncalls false fo'` so the continuation's `∀ g'` at
`{w0 with faults := g}` is `{({w0 with faults := g₀}) with faults := g}`. -/
theorem core_sim_ext {I : Interface} {S X E ε}
    (bs : List (BindEnv I S X)) {c Γ κ ctx haltUnit}
    (hhalt : haltUnit = true) (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound) (hign : BindEnvs.ignoresLocal bs)
    (hsame : BindEnvs.sameAbs bs) (horth : BindEnvs.orthogonal bs)
    {calls : ExternalCalls} {t} (core : Core t) (hS2 : S2Frag core)
    (hslot : BindEnvs.avoids Γ c bs core) :
    ∀ {w : World S X E} {env V st} (funs : FunEnv (yulD calls))
      (hfuns : noExtFuns funs = true) (hwf : coreWF c core = true)
      (hn : identsNodup (env.length + coreExtraDepth core) = true)
      (hinv : Inv Γ c κ ctx w env V st) (hRX : RXs bs w st)
      (hBindNe : BindEnvs.neSelf bs ctx.self w.self)
      (hconf : BindEnvs.conforms bs ctx.self w.self calls)
      (hinj : BindEnvs.addrInj bs w.self)
      (hBind : BindEnvs.lookupWF c Γ bs)
      {e'} (hem : emitCore c {} env.length haltUnit core = some e')
      {V' st' o} (hexec : ExecStmts (yulD calls) funs V st e'.stmts V' st' o),
      ∃ fo, ∀ g, oracleAgrees w.ncalls fo g →
        match (Tx.run (Core.denote Γ core env) ctx { w with faults := g } :
            Except (Err ε) (t.denote × World S X E)) with
        | .ok (v, w') =>
            o = Outcome.halt ∧ haltSuccess t v st'.halted ∧
              R c Γ κ w' st' ∧ RXs bs w' st'
        | .error e =>
            ∃ bytes, o = Outcome.halt ∧ st'.halted = some (HaltKind.revert, bytes) ∧
              haltError c Γ e bytes := by
  revert hS2 hslot
  induction core with
  | ret r =>
    intro hS2 hslot
    cases r with
    | pair x y =>
      cases x with
      | word _ =>
        cases y with
        | word _ =>
          exact core_sim_ext_callFree bs hhalt hΓ hκ hlen hign _
            (by simp [CallFree, M1Frag]) hslot
        | _ => cases hS2
      | _ => cases hS2
    | unit | word _ | addr _ | flag _ =>
      exact core_sim_ext_callFree bs hhalt hΓ hκ hlen hign _
        (by simp [CallFree, M1Frag]) hslot
  | revertTail err args =>
    intro hS2 hslot
    exact core_sim_ext_callFree bs hhalt hΓ hκ hlen hign _
      (by simpa [CallFree, M1Frag, S2Frag] using hS2) hslot
  | opTail op =>
    intro hS2 hslot w env V st funs hfuns hwf hn hinv hRX hBindNe hconf hinj hBind e' hem V' st' o hexec
    cases s2op_elim (by simpa [S2Frag] using hS2) with
    | inr hM1 =>
      exact core_sim_ext_callFree bs hhalt hΓ hκ hlen hign (.opTail op)
        (by simpa [CallFree, M1Frag] using hM1) hslot
        funs hfuns hwf hn hinv hRX hBindNe hconf hinj hBind hem hexec
    | inl hcall =>
      obtain ⟨b, m, args, rfl⟩ := hcall
      simp only [emitCore] at hem
      cases hE : emitLetOp c {} env.length (.call b m args) with
      | none => simp [hE] at hem
      | some e1 =>
        simp only [hE] at hem
        cases hem
        have hretE := emitRet_word_stmts e1 (env.length + 1) haltUnit (.var 0)
        rw [hretE] at hexec
        have hopWF : callWF c b m args = true := by simpa [coreWF, opWF] using hwf
        have hn1 : identsNodup (env.length + 1) = true :=
          identsNodup_mono (by simp [coreExtraDepth]) hn
        exact sim_ext_op_call_return hsame horth hign
          (core := .opTail (.call b m args)) id haltSuccess_word
          (fun h => by simpa [Core.denote, RetTy.denote] using h)
          (fun h => by simpa [Core.denote, RetTy.denote] using h)
          funs hfuns hopWF hn1 hinv hRX hBindNe hconf hinj hBind hE hexec
  | opTailAddr op =>
    intro hS2 hslot w env V st funs hfuns hwf hn hinv hRX hBindNe hconf hinj hBind e' hem V' st' o hexec
    cases s2op_elim (by simpa [S2Frag] using hS2) with
    | inr hM1 =>
      exact core_sim_ext_callFree bs hhalt hΓ hκ hlen hign (.opTailAddr op)
        (by simpa [CallFree, M1Frag] using hM1) hslot
        funs hfuns hwf hn hinv hRX hBindNe hconf hinj hBind hem hexec
    | inl hcall =>
      obtain ⟨b, m, args, rfl⟩ := hcall
      simp only [emitCore] at hem
      cases hE : emitLetOp c {} env.length (.call b m args) with
      | none => simp [hE] at hem
      | some e1 =>
        simp only [hE] at hem
        cases hem
        have hretE := emitRet_addr_stmts e1 (env.length + 1) haltUnit (.var 0)
        rw [hretE] at hexec
        have hopWF : callWF c b m args = true := by simpa [coreWF, opWF] using hwf
        have hn1 : identsNodup (env.length + 1) = true :=
          identsNodup_mono (by simp [coreExtraDepth]) hn
        exact sim_ext_op_call_return hsame horth hign
          (core := .opTailAddr (.call b m args)) (fun n => (n : Address)) haltSuccess_addr
          (fun h => by simpa [Core.denote, RetTy.denote, Address] using h)
          (fun h => by simpa [Core.denote, RetTy.denote, Address] using h)
          funs hfuns hopWF hn1 hinv hRX hBindNe hconf hinj hBind hE hexec
  | opTailFlag op =>
    intro hS2 hslot w env V st funs hfuns hwf hn hinv hRX hBindNe hconf hinj hBind e' hem V' st' o hexec
    cases s2op_elim (by simpa [S2Frag] using hS2) with
    | inr hM1 =>
      exact core_sim_ext_callFree bs hhalt hΓ hκ hlen hign (.opTailFlag op)
        (by simpa [CallFree, M1Frag] using hM1) hslot
        funs hfuns hwf hn hinv hRX hBindNe hconf hinj hBind hem hexec
    | inl hcall =>
      obtain ⟨b, m, args, rfl⟩ := hcall
      simp only [emitCore] at hem
      cases hE : emitLetOp c {} env.length (.call b m args) with
      | none => simp [hE] at hem
      | some e1 =>
        simp only [hE] at hem
        cases hem
        have hretE := emitRet_flag_stmts e1 (env.length + 1) haltUnit (.var 0)
        rw [hretE] at hexec
        have hopWF : callWF c b m args = true := by simpa [coreWF, opWF] using hwf
        have hn1 : identsNodup (env.length + 1) = true :=
          identsNodup_mono (by simp [coreExtraDepth]) hn
        exact sim_ext_op_call_return hsame horth hign
          (core := .opTailFlag (.call b m args)) (fun n => (n : Flag)) haltSuccess_flag
          (fun h => by simpa [Core.denote, RetTy.denote, Flag] using h)
          (fun h => by simpa [Core.denote, RetTy.denote, Flag] using h)
          funs hfuns hopWF hn1 hinv hRX hBindNe hconf hinj hBind hE hexec
  | stmtTail s =>
    intro hS2 hslot w env V st funs hfuns hwf hn hinv hRX hBindNe hconf hinj hBind e' hem V' st' o hexec
    cases s2stmt_elim (by simpa [S2Frag] using hS2) with
    | inr hM1 =>
      exact core_sim_ext_callFree bs hhalt hΓ hκ hlen hign (.stmtTail s)
        (by simpa [CallFree, M1Frag] using hM1) hslot
        funs hfuns hwf hn hinv hRX hBindNe hconf hinj hBind hem hexec
    | inl hcall =>
      obtain ⟨b, m, args, rfl⟩ := hcall
      simp only [emitCore] at hem
      rw [hhalt] at hem
      cases hem
      rw [emitReturnUnit_true] at hexec
      have hopWF : callWF c b m args = true := by simpa [coreWF, stmtWF] using hwf
      obtain ⟨eCall, heCall, meth, hbd⟩ := hBind b m args hopWF
      have hn0 : identsNodup env.length = true :=
        identsNodup_mono (by simp [coreExtraDepth]) hn
      cases execStmts_append_inv hexec with
      | inr hstop =>
        have hexec1 : ExecStmts (yulD calls) funs V st
            (emitStmt c {} env.length (.call b m args)).stmts V' st' o := hstop.2
        obtain ⟨bit, hfail, hok⟩ :=
          stmt_sim_call_bwd (α := eCall.α) heCall hsame horth hinj hinv hbd hRX
            (hconf eCall heCall) hfuns hopWF hn0 hexec1
        cases bit with
        | false =>
          obtain ⟨_, _, _, _, hg⟩ := hok rfl
          obtain ⟨_, ho, _⟩ := hg (fun _ => false) rfl
          exact (hstop.1 ho).elim
        | true =>
          refine ⟨fun _ => true, ?_⟩
          intro g hg
          have gnc : g w.ncalls = true := by
            simpa using hg w.ncalls (Nat.le_refl _)
          have ⟨hrun, ho, hh⟩ := hfail rfl g gnc
          have htx :
              Tx.run (Core.denote Γ (.stmtTail (.call b m args)) env) ctx { w with faults := g } =
                .error .callFailed := by
            simpa [Core.denote, RetTy.denote] using hrun
          rw [htx]
          simp only [except_error_prod]
          exact ⟨[], ho, hh, rfl⟩
      | inl hokPre =>
        obtain ⟨V1, st1, hcallE, hrest⟩ := hokPre
        obtain ⟨bit, hfail, hok⟩ :=
          stmt_sim_call_bwd (α := eCall.α) heCall hsame horth hinj hinv hbd hRX
            (hconf eCall heCall) hfuns hopWF hn0 hcallE
        cases bit with
        | true =>
          have ⟨_, ho, _⟩ := hfail rfl (fun _ => true) rfl
          cases ho
        | false =>
          obtain ⟨w0, hself, _hlog, hncalls, hg⟩ := hok rfl
          let g0 : Nat → Bool := fun _ => false
          obtain ⟨_hrun0, _ho0, hVeq, hInv0, hRX0⟩ := hg g0 rfl
          have hstopE := stop_sim (funEnvUncast calls funs) V1 st1
          have hnoStop : noExtBlock [stopStmt] = true := by
            simp [noExtBlock, noExtStmts, noExt_stop]
          have hdesc := execStmts_descend hfuns hnoStop hrest
          obtain ⟨hVeq', hsteq, hoeq⟩ := execStmts_det_evm hdesc hstopE
          subst hVeq'; subst hsteq; subst hoeq
          refine ⟨composeFault w.ncalls false (fun _ => false), ?_⟩
          intro g hgA
          have ⟨hgfalse, _⟩ := oracleAgrees_compose_false hgA
          obtain ⟨hrun, _ho, _hV, hInvg, hRXg⟩ := hg g hgfalse
          have htx :
              Tx.run (Core.denote Γ (.stmtTail (.call b m args)) env) ctx { w with faults := g } =
                .ok ((), { w0 with faults := g }) := by
            simpa [Core.denote, RetTy.denote] using hrun
          rw [htx]
          simp only [except_ok_prod]
          refine ⟨trivial, haltSuccess_unit_stop rfl, (R_faults g).mpr (R_halted_update hInv0.rel _), ?_⟩
          intro e he
          have hstab := ofState_noExt_halt (hign e he) hfuns hnoStop hrest
            (e.bind.addr w0.self)
            (foreign_of_ctx hInv0.ctxr (by simpa [hself] using hBindNe e he))
          unfold RX
          rw [hstab]
          exact hRXg e he
  | letOp op k ih =>
    intro hS2 hslot w env V st funs hfuns hwf hn hinv hRX hBindNe hconf hinj hBind e' hem V' st' o hexec
    have ⟨hop, hk⟩ := s2frag_letOp.mp hS2
    have ⟨hopWF0, hkWF⟩ := coreWF_letOp.mp hwf
    obtain ⟨e1, e0, hE, h0, hst⟩ := emitCore_letOp_split hem
    rw [hst] at hexec
    have hn1 : identsNodup (env.length + 1) = true :=
      identsNodup_mono (by simp [coreExtraDepth]; try omega) hn
    have hnK : identsNodup ((env.length + 1) + coreExtraDepth k) = true := by
      simpa [coreExtraDepth, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
    have hslotK : BindEnvs.avoids Γ c bs k := BindEnvs.avoids_letOp hslot
    cases s2op_elim hop with
    | inl hcall =>
      obtain ⟨b, m, args, rfl⟩ := hcall
      have hopWF : callWF c b m args = true := by simpa [opWF] using hopWF0
      exact sim_ext_letOp_call hsame horth hk hslotK (ih hk hslotK)
        funs hfuns hkWF hn1 hnK hinv hRX hBindNe hconf hinj hBind hopWF hE h0 hexec
    | inr hM1 =>
      exact sim_ext_letOp_m1 hΓ hκ hlen hign hM1 hk hslotK (ih hk hslotK)
        funs hfuns hopWF0 hkWF hn1 hnK hinv hRX hBindNe hconf hinj hBind hE h0 hexec
  | seq s k ih =>
    intro hS2 hslot w env V st funs hfuns hwf hn hinv hRX hBindNe hconf hinj hBind e' hem V' st' o hexec
    have ⟨hs, hk⟩ := s2frag_seq.mp hS2
    have ⟨hsWF, hkWF⟩ := coreWF_seq.mp hwf
    simp only [emitCore] at hem
    obtain ⟨e0, h0, hst⟩ := emitCore_prefix hem
    rw [hst] at hexec
    have hn0 : identsNodup env.length = true :=
      identsNodup_mono (by simp [coreExtraDepth]) hn
    have hnK : identsNodup (env.length + coreExtraDepth k) = true := by
      simpa [coreExtraDepth] using hn
    have hslotK : BindEnvs.avoids Γ c bs k := BindEnvs.avoids_seq hslot
    cases s2stmt_elim hs with
    | inl hcall =>
      obtain ⟨b, m, args, rfl⟩ := hcall
      have hopWF : callWF c b m args = true := by simpa [stmtWF] using hsWF
      exact sim_ext_seq_call hsame horth hk hslotK (ih hk hslotK)
        funs hfuns hkWF hn0 hnK hinv hRX hBindNe hconf hinj hBind hopWF h0 hexec
    | inr hM1 =>
      exact sim_ext_seq_m1 hΓ hκ hlen hign hM1 hk hslot (ih hk hslotK)
        funs hfuns hsWF hkWF hn0 hnK hinv hRX hBindNe hconf hinj hBind h0 hexec
  | letPure p args k ih =>
    intro hS2 hslot w env V st funs hfuns hwf hn hinv hRX hBindNe hconf hinj hBind e' hem V' st' o hexec
    have ⟨hp, hargs, hk⟩ := s2frag_letPure.mp hS2
    subst hp
    have ⟨a, hargs'⟩ := length_eq_one.mp hargs
    subst hargs'
    have ⟨hwfA, hkWF⟩ : atomWF a = true ∧ coreWF c k = true := by
      simpa [coreWF, Bool.and_eq_true] using hwf
    simp only [emitCore, emitPrim] at hem
    obtain ⟨e0, h0, hst⟩ := emitCore_prefix hem
    rw [hst] at hexec
    have hn0 : identsNodup env.length = true :=
      identsNodup_mono (by simp [coreExtraDepth]; try omega) hn
    have hnK : identsNodup ((env.length + 1) + coreExtraDepth k) = true := by
      simpa [coreExtraDepth, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
    have hslotK : BindEnvs.avoids Γ c bs k := BindEnvs.avoids_letPure hslot
    have he := eval_atom (funEnvUncast calls funs) (st := st) hinv.venv hn0 a
    have hv := atom_eval_lt hinv.wf hwfA
    have hlet :
        ExecStmt evm (funEnvUncast calls funs) V st
          (.letDecl [identV env.length] (some (atomE env.length a)))
          ((identV env.length, BitVec.ofNat 256 (a.eval env)) :: V) st .normal :=
      Step.letVal he rfl
    have hpre : ExecStmts evm (funEnvUncast calls funs) V st
        [.letDecl [identV env.length] (some (atomE env.length a))]
        ((identV env.length, BitVec.ofNat 256 (a.eval env)) :: V) st .normal :=
      Step.seqCons hlet Step.seqNil
    have hnoLet : noExtBlock [.letDecl [identV env.length] (some (atomE env.length a))] = true :=
      noExt_let (e := {}) (by simp [Emit.stmts_nil]) (noExt_atomE _ _)
    simp only [emitLet, Emit.stmts_push, Emit.stmts_nil, List.nil_append] at hexec hnoLet
    have hrest := s1_match_prefix_ok hfuns hnoLet hexec hpre
    have hinv1 : Inv Γ c κ ctx w (a.eval env :: env)
        ((identV env.length, BitVec.ofNat 256 (a.eval env)) :: V) st :=
      ⟨by rw [hinv.venv, toVEnv_cons], envWF_cons hv hinv.wf, hinv.rel, hinv.ctxr⟩
    obtain ⟨fo', hfo'⟩ :=
      ih hk hslotK funs hfuns hkWF (by simpa using hnK) hinv1 hRX hBindNe hconf hinj hBind h0 hrest
    refine ⟨fo', ?_⟩
    intro g hg
    simp only [Core.denote]
    have hpe : Prim.eval .id (List.map (Atom.eval env) [a]) = a.eval env := rfl
    rw [hpe]
    exact hfo' g hg
  | ite cond a b iha ihb =>
    intro hS2 hslot w env V st funs hfuns hwf hn hinv hRX hBindNe hconf hinj hBind e' hem V' st' o hexec
    have ⟨hC, ha, hb⟩ := s2frag_ite.mp hS2
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
    have ⟨hslotA, hslotB⟩ := BindEnvs.avoids_ite hslot
    have hpush :
        (Emit.push ({} : Emit) (.switch (emitCond env.length cond)
          [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts))).stmts =
          [.switch (emitCond env.length cond)
            [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts)] := by
      simp [Emit.stmts_push, Emit.stmts_nil]
    rw [hpush] at hexec
    have hsw := execStmts_one hexec
    have hcond := eval_cond (st := st) (funEnvUncast calls funs) hinv.venv hinv.wf hn0 hC hcWF
    have hfunsN := noExtFuns_cons_nil (calls := calls) hfuns
    cases hsw with
    | switchHalt he =>
      have hdesc := evalExpr_descend hfuns (noExt_emitCond env.length cond) he
      have := evalExpr_det_evm hcond hdesc
      cases this
    | switchExec he hbody =>
      have hdesc := evalExpr_descend hfuns (noExt_emitCond env.length cond) he
      have heq := evalExpr_det_evm hcond hdesc
      simp [eresUncast] at heq
      obtain ⟨rfl, rfl⟩ := heq
      cases hbody with
      | block hss =>
        have hhoistA : hoist (yulD calls) eA.stmts = [] :=
          hoist_yulD_of_evm (hoist_emitCore hA)
        have hhoistB : hoist (yulD calls) eB.stmts = [] :=
          hoist_yulD_of_evm (hoist_emitCore hB)
        simp only [Core.denote]
        split_ifs with hc
        · have hsel :
              selectSwitch (yulD calls) (b2w (decide (cond.denote env)))
                [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) = eA.stmts :=
            selectSwitch_nonzero_yulD (by simp [hc, b2w])
          rw [hsel, hhoistA] at hss
          obtain ⟨fo', hfo'⟩ :=
            iha ha hslotA ([] :: funs) hfunsN haWF hnA hinv hRX hBindNe hconf hinj hBind hA hss
          exact ⟨fo', hfo'⟩
        · have hsel :
              selectSwitch (yulD calls) (b2w (decide (cond.denote env)))
                [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) = eB.stmts := by
            simp [hc, b2w]
            exact selectSwitch_zero_yulD
          rw [hsel, hhoistB] at hss
          obtain ⟨fo', hfo'⟩ :=
            ihb hb hslotB ([] :: funs) hfunsN hbWF hnB hinv hRX hBindNe hconf hinj hBind hB hss
          exact ⟨fo', hfo'⟩

/-- S2 backward `toYulFn` for `S2Frag` cores over a binding family.
The one-binding case is `bs = [⟨α, bind⟩]`. -/
theorem toYulFn_correct_ext {I : Interface} {S X E ε : Type}
    (bs : List (BindEnv I S X))
    (c : ContractDef) (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (calls : ExternalCalls) (f : FnDef) (hf : f.kind ≠ .constructor)
    (hS2 : S2Frag f.core) (hlen : c.fields.length < wordBound)
    (hbound : 4 + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : toYulFn c f = some yul)
    (ctx : Ctx) (w : World S X E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0)
    (hRX : RXs bs w st0) (hign : BindEnvs.ignoresLocal bs)
    (hBindNe : BindEnvs.neSelf bs ctx.self w.self)
    (hconf : BindEnvs.conforms bs ctx.self w.self calls)
    (hsame : BindEnvs.sameAbs bs) (horth : BindEnvs.orthogonal bs)
    (hinj : BindEnvs.addrInj bs w.self)
    (hBind : BindEnvs.lookupWF c Γ bs)
    (hslot : BindEnvs.avoids Γ c bs f.core) :
    ToYulFnCorrectExts bs c Γ κ calls f yul ctx w st0 := by
  intro st' o hrun
  have ⟨hwf, hnod, e, hem, hy⟩ := toYulFn_inv hyul hf
  obtain ⟨e0, h0, hst⟩ := emitCore_prefix hem
  obtain ⟨Vb, hbody, _hV⟩ := run_block_inv hrun
  have hhoist_evm := toYulFn_hoist hyul hf
  have hhoist : hoist (yulD calls) yul = [] := hoist_yulD_of_evm hhoist_evm
  rw [hhoist] at hbody
  have hfuns : noExtFuns ([] :: [] : FunEnv (yulD calls)) = true := noExtFuns_nilScope
  rw [hy, hst] at hbody
  set args := decodeArgs f st0.env.calldata
  have henv : EnvWF args.reverse := decodeArgs_wf f st0.env.calldata
  have hdec := decodeArgs_runtime (f := f) (cd := st0.env.calldata) hf
  have hpar := params_sim (funEnvUncast calls [[]]) st0 4 f.params.length hbound
  have hpar' : ExecStmts evm (funEnvUncast calls [[]]) [] st0
      (emitParams {} 4 f.params.length).stmts (toVEnv args.reverse) st0 .normal := by
    convert hpar
    try simp [args, hdec]
  have hrest :=
    s1_match_prefix_ok (calls := calls) hfuns (noExt_params 4 f.params.length) hbody hpar'
  have hinv : Inv Γ c κ ctx w args.reverse (toVEnv args.reverse) st0 :=
    ⟨rfl, henv, hR, hctx⟩
  have hn : identsNodup (f.params.length + coreExtraDepth f.core) = true := by
    simpa [maxDepth] using hnod
  have hn' : identsNodup (args.reverse.length + coreExtraDepth f.core) = true := by
    simpa [args, decodeArgs_length, List.length_reverse] using hn
  have h0' : emitCore c {} args.reverse.length true f.core = some e0 := by
    simpa [args, decodeArgs_length, List.length_reverse] using h0
  have hsim :=
    core_sim_ext bs (haltUnit := true) rfl hΓ hκ hlen hign hsame horth f.core hS2 hslot
      (funs := [[]]) hfuns hwf hn' hinv hRX hBindNe hconf hinj hBind h0' hrest
  obtain ⟨fo, hfo⟩ := hsim
  refine ⟨fo, ?_⟩
  have hmatch := hfo fo (fun _ _ => rfl)
  cases hTx : Tx.run (Core.denote Γ f.core args.reverse) ctx { w with faults := fo } with
  | ok p =>
    rcases p with ⟨v, w'⟩
    simp only [hTx, except_ok_prod] at hmatch ⊢
    obtain ⟨ho, hsucc, hR', hRX'⟩ := hmatch
    obtain ⟨k, bts, hh, hk⟩ := haltSuccess_commits hsucc
    rw [committedState_commit hh hk]
    exact ⟨ho, hsucc, hR', hRX'⟩
  | error err =>
    simp only [hTx, except_error_prod] at hmatch ⊢
    obtain ⟨bytes, ho, hh, herr⟩ := hmatch
    refine ⟨bytes, ho, ?_, herr, R_rollback_obs hR hh HaltKind.revert_commits⟩
    simp [committedState_rollback hh HaltKind.revert_commits, hh]

/-- Singleton family recovers `ToYulFnCorrectExt`. -/
theorem toYulFn_correct_ext_one {I : Interface} {S X E ε : Type}
    (α : Abs I.Ghost) (bind : Binding I S X)
    (c : ContractDef) (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (calls : ExternalCalls) (f : FnDef) (hf : f.kind ≠ .constructor)
    (hS2 : S2Frag f.core) (hlen : c.fields.length < wordBound)
    (hbound : 4 + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : toYulFn c f = some yul)
    (ctx : Ctx) (w : World S X E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0)
    (hRX : RX α bind w st0) (hign : α.ignoresLocal)
    (hBindNe : accountKey (BitVec.ofNat 256 (bind.addr w.self)) ≠
      accountKey (BitVec.ofNat 256 ctx.self))
    (hconf : Conforms I ctx.self (bind.addr w.self) calls α)
    (hBind : ∀ b m args, callWF c b m args = true → ∃ meth, BindWF c Γ bind b m meth)
    (hslot : ∃ slot : Nat,
        (∀ σ, Γ.st.scalar slot σ = bind.addr σ) ∧
        (c.fields[slot]?).map (·.kind) = some FieldKind.scalar ∧
        coreAvoids slot f.core) :
    ToYulFnCorrectExt α bind c Γ κ calls f yul ctx w st0 := by
  let e : BindEnv I S X := ⟨α, bind⟩
  have hfam :=
    toYulFn_correct_ext [e] c Γ hΓ κ hκ calls f hf hS2 hlen hbound yul hyul
      ctx w st0 hctx hR (RXs_singleton e w st0 |>.mpr hRX)
      (BindEnvs.ignoresLocal_singleton e hign)
      (BindEnvs.neSelf_singleton e ctx.self w.self hBindNe)
      (BindEnvs.conforms_singleton e ctx.self w.self calls hconf)
      (BindEnvs.sameAbs_singleton e) (BindEnvs.orthogonal_singleton e)
      (BindEnvs.addrInj_singleton e w.self)
      (BindEnvs.lookupWF_singleton hBind)
      (BindEnvs.avoids_singleton hslot)
  intro st' o hrun
  obtain ⟨fo, hconcl⟩ := hfam st' o hrun
  refine ⟨fo, ?_⟩
  cases hTx : Tx.run (Core.denote Γ f.core (decodeArgs f st0.env.calldata).reverse)
      ctx { w with faults := fo } with
  | ok p =>
    rcases p with ⟨v, w'⟩
    simp only [hTx] at hconcl ⊢
    obtain ⟨ho, hsucc, hR', hRX'⟩ := hconcl
    exact ⟨ho, hsucc, hR', (RXs_singleton e w' _).mp hRX'⟩
  | error err =>
    simp only [hTx] at hconcl ⊢
    exact hconcl

end Lsc.Compiler.Proof
