import Lsc.Compiler.Proof.BindEnvs
import Lsc.Compiler.Proof.Oracle
import Lsc.Compiler.Proof.OfState
import Lsc.Compiler.Proof.CallBwd
import Lsc.Compiler.Proof.CoreProof
import Lsc.Lang.CoreTheorems

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

/-!
Call-head helpers for `core_sim_ext`: fail-bit, oracle composition, and
`op_sim_call_bwd` / `stmt_sim_call_bwd` composed with a continuation.
-/

namespace Lsc.Compiler

variable (tag : String)

open YulSemantics
open YulSemantics.EVM
open Lsc hiding Op Stmt

theorem s1_match_prefix_ok {calls : ExternalCalls}
    {funs : FunEnv (yulD calls)} {V : VEnv (yulD calls)} {st : EvmState}
    {pre rest : YBlock} {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    {V1 : VEnv evm} {st1 : EvmState}
    (hfuns : noExtFuns funs = true) (hno : noExtBlock pre = true)
    (h : ExecStmts (yulD calls) funs V st (pre ++ rest) V' st' o)
    (hfwd : ExecStmts evm (funEnvUncast calls funs) V st pre V1 st1 .normal) :
    ExecStmts (yulD calls) funs V1 st1 rest V' st' o := by
  cases execStmts_append_inv h with
  | inr hstop =>
    have hdesc := execStmts_descend hfuns hno hstop.2
    have ⟨_, _, ho⟩ := execStmts_det_evm hfwd hdesc
    exact (hstop.1 ho.symm).elim
  | inl hok =>
    obtain ⟨Vmid, stMid, hpre, hrest⟩ := hok
    have hdesc := execStmts_descend hfuns hno hpre
    have ⟨hVeq, hsteq, _⟩ := execStmts_det_evm hfwd hdesc
    rw [← hVeq, ← hsteq] at hrest
    exact hrest

theorem s1_match_prefix_halt {calls : ExternalCalls}
    {funs : FunEnv (yulD calls)} {V : VEnv (yulD calls)} {st : EvmState}
    {pre rest : YBlock} {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    {V1 : VEnv evm} {st1 : EvmState}
    (hfuns : noExtFuns funs = true) (hno : noExtBlock pre = true)
    (h : ExecStmts (yulD calls) funs V st (pre ++ rest) V' st' o)
    (hfwd : ExecStmts evm (funEnvUncast calls funs) V st pre V1 st1 .halt) :
    o = .halt ∧ V' = V1 ∧ st' = st1 := by
  cases execStmts_append_inv h with
  | inl hok =>
    obtain ⟨Vmid, stMid, hpre, _⟩ := hok
    have hdesc := execStmts_descend hfuns hno hpre
    have ⟨_, _, ho⟩ := execStmts_det_evm hfwd hdesc
    cases ho
  | inr hstop =>
    have hdesc := execStmts_descend hfuns hno hstop.2
    have ⟨hV, hst, ho⟩ := execStmts_det_evm hfwd hdesc
    exact ⟨ho.symm, hV.symm, hst.symm⟩

/-- Inner `∀` of `core_sim_ext` (after `hS2` / `hslot`). -/
abbrev SimExt {I : Interface} {S X E ε : Type}
    (bs : List (BindEnv I S X)) (c : ContractDef) (Γ : ContractSchema S X E ε)
    (κ : List UInt8 → U256) (ctx : Ctx) (haltUnit : Bool)
    {calls : ExternalCalls} {t} (core : Core t) : Prop :=
  ∀ {w : World S X E} {env : List Nat} {V : VEnv (yulD calls)} {st : EvmState}
    (funs : FunEnv (yulD calls))
    (hfuns : noExtFuns funs = true) (hwf : coreWF c core = true)
    (hn : identsNodup tag (env.length + coreExtraDepth core) = true)
    (hinv : Inv tag Γ c κ ctx w env V st) (hRX : RXs bs w st)
    (hBindNe : BindEnvs.neSelf bs ctx.self w.self)
    (hconf : BindEnvs.conforms bs ctx.self w.self calls)
    (hinj : BindEnvs.addrInj bs w.self)
    (hBind : BindEnvs.lookupWF c Γ bs)
    {e' : Emit} (hem : emitCore tag c {} env.length haltUnit core = some e')
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hexec : ExecStmts (yulD calls) funs V st e'.stmts V' st' o),
    ∃ fo, ∀ g, oracleAgrees w.ncalls fo g →
      match (Tx.run (Core.denote Γ core env) ctx { w with faults := g } :
          Except (Err ε) (t.denote × World S X E)) with
      | .ok (v, w') =>
          o = Outcome.halt ∧ haltSuccess t v st'.halted ∧
            R c Γ κ w' st' ∧ RXs bs w' st'
      | .error e =>
          ∃ bytes, o = Outcome.halt ∧ st'.halted = some (HaltKind.revert, bytes) ∧
            haltError c Γ e bytes

theorem sim_ext_error_callFailed {I : Interface} {S X E ε : Type} {t : RetTy}
    {c : ContractDef} {Γ : ContractSchema S X E ε} {κ : List UInt8 → U256}
    {ctx : Ctx} {bs : List (BindEnv I S X)} {core : Core t}
    {env : List Nat} {w : World S X E} {st' : EvmState} {o : Outcome}
    (hrun : ∀ g, g w.ncalls = true →
      Tx.run (Core.denote Γ core env) ctx { w with faults := g } = .error .callFailed)
    (ho : o = .halt)
    (hh : st'.halted = some (HaltKind.revert, [])) :
    ∃ fo, ∀ g, oracleAgrees w.ncalls fo g →
      match (Tx.run (Core.denote Γ core env) ctx { w with faults := g } :
          Except (Err ε) (t.denote × World S X E)) with
      | .ok (v, w') =>
          o = Outcome.halt ∧ haltSuccess t v st'.halted ∧
            R c Γ κ w' st' ∧ RXs bs w' st'
      | .error e =>
          ∃ bytes, o = Outcome.halt ∧ st'.halted = some (HaltKind.revert, bytes) ∧
            haltError c Γ e bytes := by
  refine ⟨fun _ => true, ?_⟩
  intro g hg
  have gnc : g w.ncalls = true := by simpa using hg w.ncalls (Nat.le_refl _)
  rw [hrun g gnc]
  simp only [except_error_prod]
  exact ⟨[], ho, hh, rfl⟩

theorem sim_ext_compose {I : Interface} {S X E ε : Type} {t : RetTy}
    {c : ContractDef} {Γ : ContractSchema S X E ε} {κ : List UInt8 → U256}
    {ctx : Ctx} {bs : List (BindEnv I S X)}
    (core k : Core t) (env env' : List Nat) (w w0 : World S X E)
    {st' : EvmState} {o : Outcome}
    (hhead : ∀ g, g w.ncalls = false →
      Tx.run (Core.denote Γ core env) ctx { w with faults := g } =
        Tx.run (Core.denote Γ k env') ctx { w0 with faults := g })
    (hncalls : w0.ncalls = w.ncalls + 1)
    (hcont : ∃ fo', ∀ g, oracleAgrees w0.ncalls fo' g →
      match (Tx.run (Core.denote Γ k env') ctx { w0 with faults := g } :
          Except (Err ε) (t.denote × World S X E)) with
      | .ok (v, w') =>
          o = Outcome.halt ∧ haltSuccess t v st'.halted ∧
            R c Γ κ w' st' ∧ RXs bs w' st'
      | .error e =>
          ∃ bytes, o = Outcome.halt ∧ st'.halted = some (HaltKind.revert, bytes) ∧
            haltError c Γ e bytes) :
    ∃ fo, ∀ g, oracleAgrees w.ncalls fo g →
      match (Tx.run (Core.denote Γ core env) ctx { w with faults := g } :
          Except (Err ε) (t.denote × World S X E)) with
      | .ok (v, w') =>
          o = Outcome.halt ∧ haltSuccess t v st'.halted ∧
            R c Γ κ w' st' ∧ RXs bs w' st'
      | .error e =>
          ∃ bytes, o = Outcome.halt ∧ st'.halted = some (HaltKind.revert, bytes) ∧
            haltError c Γ e bytes := by
  obtain ⟨fo', hfo'⟩ := hcont
  refine ⟨composeFault w.ncalls false fo', ?_⟩
  intro g hgA
  have ⟨hgfalse, hgtail⟩ := oracleAgrees_compose_false hgA
  rw [hhead g hgfalse]
  have hagree : oracleAgrees w0.ncalls fo' g := by simpa [hncalls] using hgtail
  simpa using hfo' g hagree

private theorem noExt_returnVar (d : Nat) :
    noExtBlock (emitReturnWords {} [atomE tag d (.var 0)]).stmts = true :=
  noExt_returnWords _ _ (by simp [Emit.stmts_nil]) (by
    intro x hx; simp at hx; subst hx; exact noExt_atomE tag _ _)

/-- Call op as a tail: `op_sim_call_bwd` then `return_word_sim`. -/
theorem sim_ext_op_call_return {I : Interface} {S X E ε : Type} {t : RetTy}
    {c : ContractDef} {Γ : ContractSchema S X E ε} {κ : List UInt8 → U256}
    {ctx : Ctx} {bs : List (BindEnv I S X)} {calls : ExternalCalls}
    (hsame : BindEnvs.sameAbs bs) (horth : BindEnvs.orthogonal bs)
    (hign : BindEnvs.ignoresLocal bs)
    {core : Core t} {b m : Nat} {args : List Atom}
    (toVal : Nat → t.denote)
    (hsucc : ∀ {v : Nat} {h}, h = some (.ret, wordBytes v) → haltSuccess t (toVal v) h)
    (hokCore : ∀ {v : Nat} {w0 : World S X E} {g : Nat → Bool} {w : World S X E}
        {env : List Nat},
      Tx.run (Op.denote Γ env (.call b m args)) ctx { w with faults := g } =
          .ok (v, { w0 with faults := g }) →
      Tx.run (Core.denote Γ core env) ctx { w with faults := g } =
          .ok (toVal v, { w0 with faults := g }))
    (herrCore : ∀ {g : Nat → Bool} {w : World S X E} {env : List Nat},
      Tx.run (Op.denote Γ env (.call b m args)) ctx { w with faults := g } =
          .error .callFailed →
      Tx.run (Core.denote Γ core env) ctx { w with faults := g } =
          .error .callFailed)
    {w : World S X E} {env : List Nat} {V : VEnv (yulD calls)} {st : EvmState}
    (funs : FunEnv (yulD calls))
    (hfuns : noExtFuns funs = true)
    (hopWF : callWF c b m args = true)
    (hn1 : identsNodup tag (env.length + 1) = true)
    (hinv : Inv tag Γ c κ ctx w env V st) (hRX : RXs bs w st)
    (hBindNe : BindEnvs.neSelf bs ctx.self w.self)
    (hconf : BindEnvs.conforms bs ctx.self w.self calls)
    (hinj : BindEnvs.addrInj bs w.self)
    (hBind : BindEnvs.lookupWF c Γ bs)
    {e1 : Emit} (hE : emitLetOp tag c {} env.length (.call b m args) = some e1)
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hexec : ExecStmts (yulD calls) funs V st
      (e1.stmts ++ (emitReturnWords {} [atomE tag (env.length + 1) (.var 0)]).stmts) V' st' o) :
    ∃ fo, ∀ g, oracleAgrees w.ncalls fo g →
      match (Tx.run (Core.denote Γ core env) ctx { w with faults := g } :
          Except (Err ε) (t.denote × World S X E)) with
      | .ok (v, w') =>
          o = Outcome.halt ∧ haltSuccess t v st'.halted ∧
            R c Γ κ w' st' ∧ RXs bs w' st'
      | .error e =>
          ∃ bytes, o = Outcome.halt ∧ st'.halted = some (HaltKind.revert, bytes) ∧
            haltError c Γ e bytes := by
  obtain ⟨eCall, heCall, meth, hbd⟩ := hBind b m args hopWF
  cases execStmts_append_inv hexec with
  | inr hstop =>
    have hexec1 : ExecStmts (yulD calls) funs V st
        ((emitLetOp tag c {} env.length (.call b m args)).getD {}).stmts V' st' o := by
      simpa [hE] using hstop.2
    obtain ⟨bit, hfail, hok⟩ :=
      op_sim_call_bwd tag (α := eCall.α) heCall hsame horth hinj hinv hbd hRX
        (hconf eCall heCall) hfuns hopWF hn1 hexec1
    cases bit with
    | false =>
      obtain ⟨_, _, _, _, _, hg⟩ := hok rfl
      obtain ⟨_, ho, _⟩ := hg (fun _ => false) rfl
      exact (hstop.1 ho).elim
    | true =>
      have ⟨_, ho, hh⟩ := hfail rfl (fun _ => true) rfl
      exact sim_ext_error_callFailed
        (fun g gnc => herrCore (hfail rfl g gnc).1) ho hh
  | inl hokPre =>
    obtain ⟨V1, st1, hcallE, hrest⟩ := hokPre
    have hexec1 : ExecStmts (yulD calls) funs V st
        ((emitLetOp tag c {} env.length (.call b m args)).getD {}).stmts V1 st1 .normal := by
      simpa [hE] using hcallE
    obtain ⟨bit, hfail, hok⟩ :=
      op_sim_call_bwd tag (α := eCall.α) heCall hsame horth hinj hinv hbd hRX
        (hconf eCall heCall) hfuns hopWF hn1 hexec1
    cases bit with
    | true =>
      have ⟨_, ho, _⟩ := hfail rfl (fun _ => true) rfl
      cases ho
    | false =>
      obtain ⟨v, w0, hself, _hlog, hncalls, hg⟩ := hok rfl
      let g0 : Nat → Bool := fun _ => false
      obtain ⟨_hrun0, _ho0, hVeq, hInv0, _hRX0⟩ := hg g0 rfl
      have hn0 : identsNodup tag (v :: env).length = true := by simpa using hn1
      have he := eval_atom tag (funEnvUncast calls funs) (st := st1) hVeq hn0 (.var 0)
      have hv : v < wordBound := hInv0.wf v (by simp)
      obtain ⟨_stR, hret, hh, hR'⟩ :=
        return_word_sim (funEnvUncast calls funs) V1 hv he hInv0.rel
      have hnoRet := noExt_returnVar tag (env.length + 1)
      have hdesc := execStmts_descend hfuns hnoRet hrest
      obtain ⟨hVeq', hsteq, hoeq⟩ := execStmts_det_evm hdesc hret
      subst hVeq'; subst hsteq; subst hoeq
      refine ⟨composeFault w.ncalls false (fun _ => false), ?_⟩
      intro g hgA
      have ⟨hgfalse, _⟩ := oracleAgrees_compose_false hgA
      obtain ⟨hrun, _ho, _hV, _hInvg, hRXg⟩ := hg g hgfalse
      rw [hokCore hrun]
      simp only [except_ok_prod]
      refine ⟨trivial, hsucc hh, (R_faults g).mpr hR',
        RXs_noExt_halt (w := { w0 with faults := g }) hign hfuns hnoRet hrest
          hInv0.ctxr (BindEnvs.neSelf_self hself hBindNe) hRXg⟩

/-- `stmt_sim_call_bwd` composed with the continuation `ih`. -/
theorem sim_ext_seq_call {I : Interface} {S X E ε : Type} {t : RetTy}
    {c : ContractDef} {Γ : ContractSchema S X E ε} {κ : List UInt8 → U256}
    {ctx : Ctx} {haltUnit : Bool} {bs : List (BindEnv I S X)} {calls : ExternalCalls}
    (hsame : BindEnvs.sameAbs bs) (horth : BindEnvs.orthogonal bs)
    {k : Core t} {b m : Nat} {args : List Atom}
    (hk : S2Frag k) (hslotK : BindEnvs.avoids Γ c bs k)
    (ih : SimExt tag bs c Γ κ ctx haltUnit (calls := calls) k)
    {w : World S X E} {env : List Nat} {V : VEnv (yulD calls)} {st : EvmState}
    (funs : FunEnv (yulD calls))
    (hfuns : noExtFuns funs = true)
    (hkWF : coreWF c k = true)
    (hn0 : identsNodup tag env.length = true)
    (hnK : identsNodup tag (env.length + coreExtraDepth k) = true)
    (hinv : Inv tag Γ c κ ctx w env V st) (hRX : RXs bs w st)
    (hBindNe : BindEnvs.neSelf bs ctx.self w.self)
    (hconf : BindEnvs.conforms bs ctx.self w.self calls)
    (hinj : BindEnvs.addrInj bs w.self)
    (hBind : BindEnvs.lookupWF c Γ bs)
    (hopWF : callWF c b m args = true)
    {e0 : Emit} (h0 : emitCore tag c {} env.length haltUnit k = some e0)
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hexec : ExecStmts (yulD calls) funs V st
      ((emitStmt tag c {} env.length (.call b m args)).stmts ++ e0.stmts) V' st' o) :
    ∃ fo, ∀ g, oracleAgrees w.ncalls fo g →
      match (Tx.run (Core.denote Γ (.seq (.call b m args) k) env) ctx { w with faults := g } :
          Except (Err ε) (t.denote × World S X E)) with
      | .ok (v, w') =>
          o = Outcome.halt ∧ haltSuccess t v st'.halted ∧
            R c Γ κ w' st' ∧ RXs bs w' st'
      | .error e =>
          ∃ bytes, o = Outcome.halt ∧ st'.halted = some (HaltKind.revert, bytes) ∧
            haltError c Γ e bytes := by
  obtain ⟨eCall, heCall, meth, hbd⟩ := hBind b m args hopWF
  cases execStmts_append_inv hexec with
  | inr hstop =>
    obtain ⟨bit, hfail, hok⟩ :=
      stmt_sim_call_bwd tag (α := eCall.α) heCall hsame horth hinj hinv hbd hRX
        (hconf eCall heCall) hfuns hopWF hn0 hstop.2
    cases bit with
    | false =>
      obtain ⟨_, _, _, _, hg⟩ := hok rfl
      obtain ⟨_, ho, _⟩ := hg (fun _ => false) rfl
      exact (hstop.1 ho).elim
    | true =>
      have ⟨_, ho, hh⟩ := hfail rfl (fun _ => true) rfl
      exact sim_ext_error_callFailed
        (fun g gnc => by
          have ⟨hrun, _, _⟩ := hfail rfl g gnc
          simp only [Core.denote, Tx.run_bind, hrun]) ho hh
  | inl hokPre =>
    obtain ⟨V1, st1, hcallE, hrest⟩ := hokPre
    obtain ⟨bit, hfail, hok⟩ :=
      stmt_sim_call_bwd tag (α := eCall.α) heCall hsame horth hinj hinv hbd hRX
        (hconf eCall heCall) hfuns hopWF hn0 hcallE
    cases bit with
    | true =>
      have ⟨_, ho, _⟩ := hfail rfl (fun _ => true) rfl
      cases ho
    | false =>
      obtain ⟨w0, hself, _hlog, hncalls, hg⟩ := hok rfl
      let g0 : Nat → Bool := fun _ => false
      obtain ⟨_hrun0, _ho0, _hVeq, hInv0, hRX0⟩ := hg g0 rfl
      have hconf0 : BindEnvs.conforms bs ctx.self w0.self calls :=
        BindEnvs.conforms_self hself hconf
      have hinj0 : BindEnvs.addrInj bs w0.self :=
        BindEnvs.addrInj_self hself hinj
      obtain ⟨fo', hfo'⟩ :=
        ih (w := { w0 with faults := g0 }) (env := env) (V := V1)
          (st := st1) funs hfuns hkWF hnK hInv0 hRX0
          (BindEnvs.neSelf_self hself hBindNe) hconf0 hinj0 hBind h0 hrest
      exact sim_ext_compose (.seq (.call b m args) k) k env env w w0
        (fun g hgfalse => by
          have ⟨hrun, _, _, _, _⟩ := hg g hgfalse
          simp only [Core.denote, Tx.run_bind, hrun])
        hncalls ⟨fo', fun g hagree => by simpa using hfo' g hagree⟩

/-- `op_sim_call_bwd` composed with the continuation `ih`. -/
theorem sim_ext_letOp_call {I : Interface} {S X E ε : Type} {t : RetTy}
    {c : ContractDef} {Γ : ContractSchema S X E ε} {κ : List UInt8 → U256}
    {ctx : Ctx} {haltUnit : Bool} {bs : List (BindEnv I S X)} {calls : ExternalCalls}
    (hsame : BindEnvs.sameAbs bs) (horth : BindEnvs.orthogonal bs)
    {k : Core t} {b m : Nat} {args : List Atom}
    (hk : S2Frag k) (hslotK : BindEnvs.avoids Γ c bs k)
    (ih : SimExt tag bs c Γ κ ctx haltUnit (calls := calls) k)
    {w : World S X E} {env : List Nat} {V : VEnv (yulD calls)} {st : EvmState}
    (funs : FunEnv (yulD calls))
    (hfuns : noExtFuns funs = true)
    (hkWF : coreWF c k = true)
    (hn1 : identsNodup tag (env.length + 1) = true)
    (hnK : identsNodup tag ((env.length + 1) + coreExtraDepth k) = true)
    (hinv : Inv tag Γ c κ ctx w env V st) (hRX : RXs bs w st)
    (hBindNe : BindEnvs.neSelf bs ctx.self w.self)
    (hconf : BindEnvs.conforms bs ctx.self w.self calls)
    (hinj : BindEnvs.addrInj bs w.self)
    (hBind : BindEnvs.lookupWF c Γ bs)
    (hopWF : callWF c b m args = true)
    {e1 e0 : Emit}
    (hE : emitLetOp tag c {} env.length (.call b m args) = some e1)
    (h0 : emitCore tag c {} (env.length + 1) haltUnit k = some e0)
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hexec : ExecStmts (yulD calls) funs V st (e1.stmts ++ e0.stmts) V' st' o) :
    ∃ fo, ∀ g, oracleAgrees w.ncalls fo g →
      match (Tx.run (Core.denote Γ (.letOp (.call b m args) k) env) ctx { w with faults := g } :
          Except (Err ε) (t.denote × World S X E)) with
      | .ok (v, w') =>
          o = Outcome.halt ∧ haltSuccess t v st'.halted ∧
            R c Γ κ w' st' ∧ RXs bs w' st'
      | .error e =>
          ∃ bytes, o = Outcome.halt ∧ st'.halted = some (HaltKind.revert, bytes) ∧
            haltError c Γ e bytes := by
  obtain ⟨eCall, heCall, meth, hbd⟩ := hBind b m args hopWF
  cases execStmts_append_inv hexec with
  | inr hstop =>
    have hexec1 : ExecStmts (yulD calls) funs V st
        ((emitLetOp tag c {} env.length (.call b m args)).getD {}).stmts V' st' o := by
      simpa [hE] using hstop.2
    obtain ⟨bit, hfail, hok⟩ :=
      op_sim_call_bwd tag (α := eCall.α) heCall hsame horth hinj hinv hbd hRX
        (hconf eCall heCall) hfuns hopWF hn1 hexec1
    cases bit with
    | false =>
      obtain ⟨_, _, _, _, _, hg⟩ := hok rfl
      obtain ⟨_, ho, _⟩ := hg (fun _ => false) rfl
      exact (hstop.1 ho).elim
    | true =>
      have ⟨_, ho, hh⟩ := hfail rfl (fun _ => true) rfl
      exact sim_ext_error_callFailed
        (fun g gnc => by
          have ⟨hrun, _, _⟩ := hfail rfl g gnc
          simp only [Core.denote, Tx.run_bind, hrun]) ho hh
  | inl hokPre =>
    obtain ⟨V1, st1, hcallE, hrest⟩ := hokPre
    have hexec1 : ExecStmts (yulD calls) funs V st
        ((emitLetOp tag c {} env.length (.call b m args)).getD {}).stmts V1 st1 .normal := by
      simpa [hE] using hcallE
    obtain ⟨bit, hfail, hok⟩ :=
      op_sim_call_bwd tag (α := eCall.α) heCall hsame horth hinj hinv hbd hRX
        (hconf eCall heCall) hfuns hopWF hn1 hexec1
    cases bit with
    | true =>
      have ⟨_, ho, _⟩ := hfail rfl (fun _ => true) rfl
      cases ho
    | false =>
      obtain ⟨v, w0, hself, _hlog, hncalls, hg⟩ := hok rfl
      let g0 : Nat → Bool := fun _ => false
      obtain ⟨_hrun0, _ho0, _hVeq, hInv0, hRX0⟩ := hg g0 rfl
      have hconf0 : BindEnvs.conforms bs ctx.self w0.self calls :=
        BindEnvs.conforms_self hself hconf
      have hinj0 : BindEnvs.addrInj bs w0.self :=
        BindEnvs.addrInj_self hself hinj
      obtain ⟨fo', hfo'⟩ :=
        ih (w := { w0 with faults := g0 }) (env := v :: env) (V := V1)
          (st := st1) funs hfuns hkWF (by simpa using hnK) hInv0 hRX0
          (BindEnvs.neSelf_self hself hBindNe) hconf0 hinj0 hBind h0 hrest
      exact sim_ext_compose (.letOp (.call b m args) k) k env (v :: env) w w0
        (fun g hgfalse => by
          have ⟨hrun, _, _, _, _⟩ := hg g hgfalse
          simp only [Core.denote, Tx.run_bind, hrun])
        hncalls ⟨fo', fun g hagree => by simpa using hfo' g hagree⟩

/-- Call-free `letOp` head: `op_sim` then `ih`. -/
theorem sim_ext_letOp_m1 {I : Interface} {S X E ε : Type} {t : RetTy}
    {c : ContractDef} {Γ : ContractSchema S X E ε} {κ : List UInt8 → U256}
    {ctx : Ctx} {haltUnit : Bool} {bs : List (BindEnv I S X)} {calls : ExternalCalls}
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound) (hign : BindEnvs.ignoresLocal bs)
    {op : Lsc.Op} {k : Core t}
    (hM1 : M1Op op) (hk : S2Frag k) (hslotK : BindEnvs.avoids Γ c bs k)
    (ih : SimExt tag bs c Γ κ ctx haltUnit (calls := calls) k)
    {w : World S X E} {env : List Nat} {V : VEnv (yulD calls)} {st : EvmState}
    (funs : FunEnv (yulD calls))
    (hfuns : noExtFuns funs = true)
    (hopWF : opWF c op = true) (hkWF : coreWF c k = true)
    (hn1 : identsNodup tag (env.length + 1) = true)
    (hnK : identsNodup tag ((env.length + 1) + coreExtraDepth k) = true)
    (hinv : Inv tag Γ c κ ctx w env V st) (hRX : RXs bs w st)
    (hBindNe : BindEnvs.neSelf bs ctx.self w.self)
    (hconf : BindEnvs.conforms bs ctx.self w.self calls)
    (hinj : BindEnvs.addrInj bs w.self)
    (hBind : BindEnvs.lookupWF c Γ bs)
    {e1 e0 : Emit}
    (hE : emitLetOp tag c {} env.length op = some e1)
    (h0 : emitCore tag c {} (env.length + 1) haltUnit k = some e0)
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hexec : ExecStmts (yulD calls) funs V st (e1.stmts ++ e0.stmts) V' st' o) :
    ∃ fo, ∀ g, oracleAgrees w.ncalls fo g →
      match (Tx.run (Core.denote Γ (.letOp op k) env) ctx { w with faults := g } :
          Except (Err ε) (t.denote × World S X E)) with
      | .ok (v, w') =>
          o = Outcome.halt ∧ haltSuccess t v st'.halted ∧
            R c Γ κ w' st' ∧ RXs bs w' st'
      | .error e =>
          ∃ bytes, o = Outcome.halt ∧ st'.halted = some (HaltKind.revert, bytes) ∧
            haltError c Γ e bytes := by
  have hno : noExtBlock e1.stmts = true :=
    noExt_letOp_m1 tag hM1 (by simp [Emit.stmts_nil]) hE
  have hsim :=
    op_sim tag (funEnvUncast calls funs) hinv hΓ hκ hlen hM1 hopWF hn1
  simp only [hE] at hsim
  cases hopr : Tx.run (Op.denote Γ env op) ctx w with
  | error err =>
    rw [hopr] at hsim
    obtain ⟨V1, st1, bytes, hexecS1, hh, herr⟩ := hsim
    have ⟨ho, hVeq, hsteq⟩ := s1_match_prefix_halt hfuns hno hexec hexecS1
    subst hVeq; subst hsteq
    refine ⟨fun _ => false, ?_⟩
    intro g _hg
    have hmap := m1op_run_faults (Γ := Γ) hM1 env ctx w g
    rw [hopr] at hmap
    simp only [mapWorldFaults] at hmap
    have htx :
        Tx.run (Core.denote Γ (.letOp op k) env) ctx { w with faults := g } = .error err := by
      simp only [Core.denote, Tx.run_bind, hmap]
    rw [htx]
    simp only [except_error_prod]
    exact ⟨bytes, ho, hh, herr⟩
  | ok p =>
    rcases p with ⟨v, w1⟩
    rw [hopr] at hsim
    obtain ⟨st1, hexecS1, hinv1⟩ := hsim
    have hokd : Lsc.Op.denote Γ env op ctx w = .ok (v, w1) := by
      simpa [Tx.run] using hopr
    have hw1 : w1 = w := m1op_world hM1 env ctx w hokd
    have hrest := s1_match_prefix_ok hfuns hno hexec hexecS1
    have hRX1 : RXs bs w1 st1 :=
      RXs_noExt_normal hign hexecS1 hinv.ctxr hBindNe
        (fun e he => by simpa [hw1]) (by simpa [hw1]) (by simpa [hw1] using hRX)
    have hconf1 : BindEnvs.conforms bs ctx.self w1.self calls :=
      BindEnvs.conforms_self (congrArg World.self hw1) hconf
    have hinj1 : BindEnvs.addrInj bs w1.self :=
      BindEnvs.addrInj_self (congrArg World.self hw1) hinj
    obtain ⟨fo', hfo'⟩ :=
      ih (w := w1) (env := v :: env)
        (V := (identV tag env.length, BitVec.ofNat 256 v) :: V) (st := st1)
        funs hfuns hkWF (by simpa using hnK) hinv1 hRX1
        (BindEnvs.neSelf_self (congrArg World.self hw1) hBindNe) hconf1 hinj1 hBind h0 hrest
    refine ⟨fo', ?_⟩
    intro g hg
    have hmap := m1op_run_faults (Γ := Γ) hM1 env ctx w g
    rw [hopr] at hmap
    simp only [mapWorldFaults] at hmap
    have htx :
        Tx.run (Core.denote Γ (.letOp op k) env) ctx { w with faults := g } =
          Tx.run (Core.denote Γ k (v :: env)) ctx { w1 with faults := g } := by
      simp only [Core.denote, Tx.run_bind, hmap]
    rw [htx]
    have hg' : oracleAgrees w1.ncalls fo' g := by simpa [hw1] using hg
    exact hfo' g hg'

/-- Call-free `seq` head: `stmt_sim` then `ih`. -/
theorem sim_ext_seq_m1 {I : Interface} {S X E ε : Type} {t : RetTy}
    {c : ContractDef} {Γ : ContractSchema S X E ε} {κ : List UInt8 → U256}
    {ctx : Ctx} {haltUnit : Bool} {bs : List (BindEnv I S X)} {calls : ExternalCalls}
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound) (hign : BindEnvs.ignoresLocal bs)
    {s : Lsc.Stmt} {k : Core t}
    (hM1 : M1Stmt s) (hk : S2Frag k)
    (hslot : BindEnvs.avoids Γ c bs (.seq s k))
    (ih : SimExt tag bs c Γ κ ctx haltUnit (calls := calls) k)
    {w : World S X E} {env : List Nat} {V : VEnv (yulD calls)} {st : EvmState}
    (funs : FunEnv (yulD calls))
    (hfuns : noExtFuns funs = true)
    (hsWF : stmtWF c s = true) (hkWF : coreWF c k = true)
    (hn0 : identsNodup tag env.length = true)
    (hnK : identsNodup tag (env.length + coreExtraDepth k) = true)
    (hinv : Inv tag Γ c κ ctx w env V st) (hRX : RXs bs w st)
    (hBindNe : BindEnvs.neSelf bs ctx.self w.self)
    (hconf : BindEnvs.conforms bs ctx.self w.self calls)
    (hinj : BindEnvs.addrInj bs w.self)
    (hBind : BindEnvs.lookupWF c Γ bs)
    {e0 : Emit} (h0 : emitCore tag c {} env.length haltUnit k = some e0)
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hexec : ExecStmts (yulD calls) funs V st
      ((emitStmt tag c {} env.length s).stmts ++ e0.stmts) V' st' o) :
    ∃ fo, ∀ g, oracleAgrees w.ncalls fo g →
      match (Tx.run (Core.denote Γ (.seq s k) env) ctx { w with faults := g } :
          Except (Err ε) (t.denote × World S X E)) with
      | .ok (v, w') =>
          o = Outcome.halt ∧ haltSuccess t v st'.halted ∧
            R c Γ κ w' st' ∧ RXs bs w' st'
      | .error e =>
          ∃ bytes, o = Outcome.halt ∧ st'.halted = some (HaltKind.revert, bytes) ∧
            haltError c Γ e bytes := by
  have hslotK : BindEnvs.avoids Γ c bs k := BindEnvs.avoids_seq hslot
  have hno : noExtBlock (emitStmt tag c {} env.length s).stmts = true :=
    noExt_stmt_m1 tag hM1 (by simp [Emit.stmts_nil])
  have hsim := stmt_sim tag (funEnvUncast calls funs) hinv hΓ hκ hlen hM1 hsWF hn0
  cases hrun : Tx.run (Stmt.denote Γ env s) ctx w with
  | error err =>
    rw [hrun] at hsim
    obtain ⟨V1, st1, bytes, hexecS1, hh, herr⟩ := hsim
    have ⟨ho, hVeq, hsteq⟩ := s1_match_prefix_halt hfuns hno hexec hexecS1
    subst hVeq; subst hsteq
    refine ⟨fun _ => false, ?_⟩
    intro g _hg
    have hmap := m1stmt_run_faults (Γ := Γ) hM1 env ctx w g
    rw [hrun] at hmap
    simp only [mapWorldFaults] at hmap
    have hseq :
        Tx.run (Core.denote Γ (.seq s k) env) ctx { w with faults := g } = .error err := by
      simp only [Core.denote, Tx.run_bind, hmap]
    rw [hseq]
    simp only [except_error_prod]
    exact ⟨bytes, ho, hh, herr⟩
  | ok p =>
    rcases p with ⟨u, w1⟩
    rw [hrun] at hsim
    obtain ⟨st1, hexecS1, hinv1⟩ := hsim
    have hokd : Lsc.Stmt.denote Γ env s ctx w = .ok ((), w1) := by
      simpa [Tx.run] using hrun
    have hrest := s1_match_prefix_ok hfuns hno hexec hexecS1
    have haddr1 : ∀ e ∈ bs, e.bind.addr w1.self = e.bind.addr w.self := by
      intro e he
      obtain ⟨slot, hs, hk, hav⟩ := hslot e he
      exact m1stmt_preserves_addr (bind := e.bind) hΓ hs hk hM1 hsWF hav.1 env ctx w hokd
    have hghost := m1stmt_preserves_ghost (Γ := Γ) hM1 env ctx w hokd
    have hRX1 : RXs bs w1 st1 :=
      RXs_noExt_normal hign hexecS1 hinv.ctxr hBindNe haddr1 hghost.1 hRX
    have hconf1 := BindEnvs.conforms_of_addr hconf haddr1
    have hinj1 := BindEnvs.addrInj_of_addr hinj haddr1
    have hBindNe1 := BindEnvs.neSelf_of_addr hBindNe haddr1
    obtain ⟨fo', hfo'⟩ :=
      ih (w := w1) (env := env) (V := V)
        (st := st1) funs hfuns hkWF hnK hinv1 hRX1
        hBindNe1 hconf1 hinj1 hBind h0 hrest
    refine ⟨fo', ?_⟩
    intro g hg
    have hmap := m1stmt_run_faults (Γ := Γ) hM1 env ctx w g
    rw [hrun] at hmap
    simp only [mapWorldFaults] at hmap
    have hseq :
        Tx.run (Core.denote Γ (.seq s k) env) ctx { w with faults := g } =
          Tx.run (Core.denote Γ k env) ctx { w1 with faults := g } := by
      simp only [Core.denote, Tx.run_bind, hmap]
    rw [hseq]
    have hnc : w1.ncalls = w.ncalls := hghost.2.2
    have hg' : oracleAgrees w1.ncalls fo' g := by simpa [hnc] using hg
    simpa using hfo' g hg'

/-- `stmtTail` call: `stmt_sim_call_bwd` then `stop`. -/
theorem sim_ext_stmtTail_call {I : Interface} {S X E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S X E ε} {κ : List UInt8 → U256}
    {ctx : Ctx} {bs : List (BindEnv I S X)} {calls : ExternalCalls}
    (hsame : BindEnvs.sameAbs bs) (horth : BindEnvs.orthogonal bs)
    (hign : BindEnvs.ignoresLocal bs)
    {b m : Nat} {args : List Atom}
    {w : World S X E} {env : List Nat} {V : VEnv (yulD calls)} {st : EvmState}
    (funs : FunEnv (yulD calls))
    (hfuns : noExtFuns funs = true)
    (hopWF : callWF c b m args = true)
    (hn0 : identsNodup tag env.length = true)
    (hinv : Inv tag Γ c κ ctx w env V st) (hRX : RXs bs w st)
    (hBindNe : BindEnvs.neSelf bs ctx.self w.self)
    (hconf : BindEnvs.conforms bs ctx.self w.self calls)
    (hinj : BindEnvs.addrInj bs w.self)
    (hBind : BindEnvs.lookupWF c Γ bs)
    {V' : VEnv (yulD calls)} {st' : (yulD calls).State} {o : Outcome}
    (hexec : ExecStmts (yulD calls) funs V st
      ((emitStmt tag c {} env.length (.call b m args)).stmts ++ [stopStmt]) V' st' o) :
    ∃ fo, ∀ g, oracleAgrees w.ncalls fo g →
      match (Tx.run (Core.denote Γ (.stmtTail (.call b m args)) env) ctx { w with faults := g } :
          Except (Err ε) (RetTy.unit.denote × World S X E)) with
      | .ok (v, w') =>
          o = Outcome.halt ∧ haltSuccess .unit v st'.halted ∧
            R c Γ κ w' st' ∧ RXs bs w' st'
      | .error e =>
          ∃ bytes, o = Outcome.halt ∧ st'.halted = some (HaltKind.revert, bytes) ∧
            haltError c Γ e bytes := by
  obtain ⟨eCall, heCall, meth, hbd⟩ := hBind b m args hopWF
  cases execStmts_append_inv hexec with
  | inr hstop =>
    obtain ⟨bit, hfail, hok⟩ :=
      stmt_sim_call_bwd tag (α := eCall.α) heCall hsame horth hinj hinv hbd hRX
        (hconf eCall heCall) hfuns hopWF hn0 hstop.2
    cases bit with
    | false =>
      obtain ⟨_, _, _, _, hg⟩ := hok rfl
      obtain ⟨_, ho, _⟩ := hg (fun _ => false) rfl
      exact (hstop.1 ho).elim
    | true =>
      refine ⟨fun _ => true, ?_⟩
      intro g hg
      have gnc : g w.ncalls = true := by simpa using hg w.ncalls (Nat.le_refl _)
      have ⟨hrun, ho', hh'⟩ := hfail rfl g gnc
      have htx :
          Tx.run (Core.denote Γ (.stmtTail (.call b m args)) env) ctx { w with faults := g } =
            .error .callFailed := by
        simpa [Core.denote, RetTy.denote] using hrun
      rw [htx]
      simp only [except_error_prod]
      exact ⟨[], ho', hh', rfl⟩
  | inl hokPre =>
    obtain ⟨V1, st1, hcallE, hrest⟩ := hokPre
    obtain ⟨bit, hfail, hok⟩ :=
      stmt_sim_call_bwd tag (α := eCall.α) heCall hsame horth hinj hinv hbd hRX
        (hconf eCall heCall) hfuns hopWF hn0 hcallE
    cases bit with
    | true =>
      have ⟨_, ho, _⟩ := hfail rfl (fun _ => true) rfl
      cases ho
    | false =>
      obtain ⟨w0, hself, _hlog, hncalls, hg⟩ := hok rfl
      let g0 : Nat → Bool := fun _ => false
      obtain ⟨_hrun0, _ho0, _hVeq, hInv0, _hRX0⟩ := hg g0 rfl
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
      refine ⟨trivial, haltSuccess_unit_stop rfl, (R_faults g).mpr (R_halted_update hInv0.rel _),
        RXs_noExt_halt (w := { w0 with faults := g }) hign hfuns hnoStop hrest
          hInv0.ctxr (BindEnvs.neSelf_self hself hBindNe) hRXg⟩

end Lsc.Compiler
