import Lsc.Compiler.Proof.ExtAgreeLocal
import Lsc.Compiler.Proof.CallBwd
import Lsc.Compiler.Proof.CoreProof
import Lsc.Lang.CoreTheorems

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

/-!
Call-head helpers for `core_sim_ext`: `op_sim_call_bwd` / `stmt_sim_call_bwd`
(and the STATICCALL twins) composed with a continuation. The only callee
hypothesis is `ExtOracle.NoReentry` (reentrancy is not modelled).
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

/-- Inner `∀` of `core_sim_ext` (after `hS2`). Reentrancy is excluded by
`hNR`; everything else about the callee is adversarial. -/
def SimExt {S E ε : Type}
    (c : ContractDef) (Γ : ContractSchema S ExtState E ε)
    (κ : List UInt8 → U256) (o : ExtOracle) (ctx : Ctx) (haltUnit : Bool)
    {t} (core : Core t) : Prop :=
  ∀ (w : World S ExtState E) (env : List Nat)
    (V : VEnv (yulD (toCalls o))) (st : EvmState)
    (funs : FunEnv (yulD (toCalls o)))
    (hfuns : noExtFuns funs = true) (hwf : coreWF c core = true)
    (hn : identsNodup tag (env.length + coreExtraDepth core) = true)
    (hinv : Inv tag Γ c κ ctx w env V st)
    (hAgr : ExtAgree ctx.self w.ext st)
    (hOr : w.oracle = Oracle.ofExt o)
    (hNR : ExtOracle.NoReentry o ctx.self)
    {clearLock : Bool} {e' : Emit}
    (hem : emitCore tag c {} env.length haltUnit core clearLock = some e')
    {V' : VEnv (yulD (toCalls o))} {st' : EvmState} {out : Outcome}
    (hexec : ExecStmts (yulD (toCalls o)) funs V st e'.stmts V' st' out),
    match Tx.run (Core.denote Γ core env) ctx w with
    | .ok (v, w') =>
        out = Outcome.halt ∧ haltSuccess t v st'.halted ∧
          R c Γ κ w' st' ∧ ExtAgree ctx.self w'.ext st'
    | .error e =>
        ∃ bytes, out = Outcome.halt ∧ st'.halted = some (HaltKind.revert, bytes) ∧
          haltError c Γ e bytes

theorem sim_ext_error_callFailed {S E ε : Type} {t : RetTy}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε} {κ : List UInt8 → U256}
    {ctx : Ctx} {core : Core t}
    {env : List Nat} {w : World S ExtState E} {st' : EvmState} {out : Outcome}
    (hrun : Tx.run (Core.denote Γ core env) ctx w = .error .callFailed)
    (ho : out = .halt)
    (hh : st'.halted = some (HaltKind.revert, [])) :
    match Tx.run (Core.denote Γ core env) ctx w with
    | .ok (v, w') =>
        out = Outcome.halt ∧ haltSuccess t v st'.halted ∧
          R c Γ κ w' st' ∧ ExtAgree ctx.self w'.ext st'
    | .error e =>
        ∃ bytes, out = Outcome.halt ∧ st'.halted = some (HaltKind.revert, bytes) ∧
          haltError c Γ e bytes := by
  rw [hrun]
  simp only [except_error_prod]
  exact ⟨[], ho, hh, rfl⟩

private theorem noExt_returnVar (d : Nat) :
    noExtBlock (emitReturnWords {} [atomE tag d (.var 0)]).stmts = true :=
  noExt_returnWords _ _ (by simp [Emit.stmts_nil]) (by
    intro x hx; simp at hx; subst hx; exact noExt_atomE tag _ _)

theorem denote_call_ok_oracle {S E ε : Type} {Γ : ContractSchema S ExtState E ε}
    {env : List Nat} {ctx : Ctx} {w : World S ExtState E}
    {t : Atom} {sel : Nat} {args : List Atom} {ret : AbiRet}
    {v : Nat} {w' : World S ExtState E}
    (h : Tx.run (Op.denote Γ env (.call t sel args ret)) ctx w = .ok (v, w')) :
    w'.oracle = w.oracle := by
  simp only [Op.denote] at h
  exact Tx.callAsNat_oracle (S := S) (X := ExtState) (E := E) (ε := ε) ret
    (Atom.eval env t) sel (args.map (Atom.eval env)) h

theorem denote_view_ok_world {S E ε : Type} {Γ : ContractSchema S ExtState E ε}
    {env : List Nat} {ctx : Ctx} {w : World S ExtState E}
    {t : Atom} {sel : Nat} {args : List Atom} {ret : AbiRet}
    {v : Nat} {w' : World S ExtState E}
    (h : Tx.run (Op.denote Γ env (.view t sel args ret)) ctx w = .ok (v, w')) :
    w' = w := by
  simp only [Op.denote] at h
  exact Tx.viewAsNat_world (S := S) (X := ExtState) (E := E) (ε := ε) ret
    (Atom.eval env t) sel (args.map (Atom.eval env)) h

theorem stmt_call_ok_op {S E ε : Type} {Γ : ContractSchema S ExtState E ε}
    {env : List Nat} {ctx : Ctx} {w w0 : World S ExtState E}
    {target : Atom} {sel : Nat} {args : List Atom} {ret : AbiRet} {u : Unit}
    (h : Tx.run (Stmt.denote Γ env (.call target sel args ret)) ctx w = .ok (u, w0)) :
    ∃ v, Tx.run (Op.denote Γ env (.call target sel args ret)) ctx w = .ok (v, w0) := by
  simp only [Stmt.denote, Tx.run_bind] at h
  cases hop : Tx.run (Op.denote Γ env (.call target sel args ret)) ctx w with
  | error _ => simp [hop] at h
  | ok p =>
    simp [hop, Tx.run_pure] at h
    exact ⟨p.1, by cases h; rfl⟩

theorem stmt_view_ok_op {S E ε : Type} {Γ : ContractSchema S ExtState E ε}
    {env : List Nat} {ctx : Ctx} {w w0 : World S ExtState E}
    {target : Atom} {sel : Nat} {args : List Atom} {ret : AbiRet} {u : Unit}
    (h : Tx.run (Stmt.denote Γ env (.view target sel args ret)) ctx w = .ok (u, w0)) :
    ∃ v, Tx.run (Op.denote Γ env (.view target sel args ret)) ctx w = .ok (v, w0) := by
  simp only [Stmt.denote, Tx.run_bind] at h
  cases hop : Tx.run (Op.denote Γ env (.view target sel args ret)) ctx w with
  | error _ => simp [hop] at h
  | ok p =>
    simp [hop, Tx.run_pure] at h
    exact ⟨p.1, by cases h; rfl⟩

/-- Call op as a tail: `op_sim_call_bwd` then `return_word_sim`. -/
theorem sim_ext_op_call_return {S E ε : Type} {t : RetTy}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε} {κ : List UInt8 → U256}
    {ctx : Ctx} {o : ExtOracle}
    {core : Core t} {target : Atom} {sel : Nat} {args : List Atom} {ret : AbiRet}
    (toVal : Nat → t.denote)
    (hsucc : ∀ {v : Nat} {h}, h = some (.ret, wordBytes v) → haltSuccess t (toVal v) h)
    (hokCore : ∀ {v : Nat} {w' : World S ExtState E} {env : List Nat}
        {w : World S ExtState E},
      Tx.run (Op.denote Γ env (.call target sel args ret)) ctx w = .ok (v, w') →
      Tx.run (Core.denote Γ core env) ctx w = .ok (toVal v, w'))
    (herrCore : ∀ {w : World S ExtState E} {env : List Nat},
      Tx.run (Op.denote Γ env (.call target sel args ret)) ctx w = .error .callFailed →
      Tx.run (Core.denote Γ core env) ctx w = .error .callFailed)
    {w : World S ExtState E} {env : List Nat}
    {V : VEnv (yulD (toCalls o))} {st : EvmState}
    (funs : FunEnv (yulD (toCalls o)))
    (hfuns : noExtFuns funs = true)
    (hwfCall : callWF target args = true) (hsel : sel < 2 ^ 32)
    (hn1 : identsNodup tag (env.length + 1) = true)
    (hinv : Inv tag Γ c κ ctx w env V st)
    (hAgr : ExtAgree ctx.self w.ext st)
    (hOr : w.oracle = Oracle.ofExt o)
    (hNR : ExtOracle.NoReentry o ctx.self)
    {clearLock : Bool} {e1 : Emit}
    (hE : emitLetOp tag c {} env.length (.call target sel args ret) = some e1)
    {V' : VEnv (yulD (toCalls o))} {st' : EvmState} {out : Outcome}
    (hexec : ExecStmts (yulD (toCalls o)) funs V st
      (e1.stmts ++ ((if clearLock then [lockClearStmt] else []) ++
        (emitReturnWords {} [atomE tag (env.length + 1) (.var 0)]).stmts))
      V' st' out) :
    match Tx.run (Core.denote Γ core env) ctx w with
    | .ok (v, w') =>
        out = Outcome.halt ∧ haltSuccess t v st'.halted ∧
          R c Γ κ w' st' ∧ ExtAgree ctx.self w'.ext st'
    | .error e =>
        ∃ bytes, out = Outcome.halt ∧ st'.halted = some (HaltKind.revert, bytes) ∧
          haltError c Γ e bytes := by
  have hE' : emitLetOp tag ({} : ContractDef) {} env.length
      (.call target sel args ret) = some e1 := by
    simpa [emitLetOp] using hE
  cases execStmts_append_inv hexec with
  | inr hstop =>
    have hexec1 : ExecStmts (yulD (toCalls o)) funs V st
        ((emitLetOp tag ({} : ContractDef) {} env.length
          (.call target sel args ret)).getD {}).stmts V' st' out := by
      simpa [hE'] using hstop.2
    have hbit :=
      op_sim_call_bwd tag o hinv hAgr hOr hNR hfuns hwfCall hsel hn1 hexec1
    cases hrun : Tx.run (Op.denote Γ env (.call target sel args ret)) ctx w with
    | ok p =>
      simp only [hrun, except_ok_prod] at hbit
      exact (hstop.1 hbit.1).elim
    | error e =>
      simp only [hrun, except_error_prod] at hbit
      obtain ⟨ho, hh, he⟩ := hbit
      subst he
      exact sim_ext_error_callFailed (herrCore hrun) ho hh
  | inl hokPre =>
    obtain ⟨V1, st1, hcallE, hrest⟩ := hokPre
    have hexec1 : ExecStmts (yulD (toCalls o)) funs V st
        ((emitLetOp tag ({} : ContractDef) {} env.length
          (.call target sel args ret)).getD {}).stmts V1 st1 .normal := by
      simpa [hE'] using hcallE
    have hbit :=
      op_sim_call_bwd tag o hinv hAgr hOr hNR hfuns hwfCall hsel hn1 hexec1
    cases hrun : Tx.run (Op.denote Γ env (.call target sel args ret)) ctx w with
    | error e =>
      simp only [hrun, except_error_prod] at hbit
      cases hbit.1
    | ok p =>
      rcases p with ⟨v, w0⟩
      simp only [hrun, except_ok_prod] at hbit
      obtain ⟨-, hInv0, hAgr0⟩ := hbit
      have hstatic := ctxRel_static hInv0.ctxr
      have hrest' :=
        s1_match_prefix_ok hfuns (noExt_maybeLock clearLock) hrest
          (execStmts_maybeLock clearLock hstatic)
      have hMO := memOnly_stAfterLockClear clearLock st1
      have hInv1 := Inv_memOnly tag hInv0 hMO
      have haddr0 := ctxRel_address hInv0.ctxr
      have hAgr1 := ExtAgree_stAfterLockClear clearLock hAgr0 haddr0
      have he := eval_atom_ok tag (funEnvUncast (toCalls o) funs)
        (st := stAfterLockClear clearLock st1) hInv0.venv (.var 0)
      have hv : v < wordBound := hInv0.wf v (by simp)
      obtain ⟨_stR, hret, hh, hR'⟩ :=
        return_word_sim (funEnvUncast (toCalls o) funs) V1 hv he hInv1.rel
      have hnoRet := noExt_returnVar tag (env.length + 1)
      have hdesc := execStmts_descend hfuns hnoRet hrest'
      obtain ⟨hVeq', hsteq, hoeq⟩ := execStmts_det_evm hdesc hret
      subst hVeq'; subst hsteq; subst hoeq
      have haddr := ctxRel_address hInv1.ctxr
      have hAgr' := ExtAgree_noExt hAgr1 haddr hfuns hnoRet hrest'
      rw [hokCore hrun]
      simp only [except_ok_prod]
      exact ⟨trivial, hsucc hh, hR', hAgr'⟩

/-- STATICCALL op as a tail. -/
theorem sim_ext_op_view_return {S E ε : Type} {t : RetTy}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε} {κ : List UInt8 → U256}
    {ctx : Ctx} {o : ExtOracle}
    {core : Core t} {target : Atom} {sel : Nat} {args : List Atom} {ret : AbiRet}
    (toVal : Nat → t.denote)
    (hsucc : ∀ {v : Nat} {h}, h = some (.ret, wordBytes v) → haltSuccess t (toVal v) h)
    (hokCore : ∀ {v : Nat} {w' : World S ExtState E} {env : List Nat}
        {w : World S ExtState E},
      Tx.run (Op.denote Γ env (.view target sel args ret)) ctx w = .ok (v, w') →
      Tx.run (Core.denote Γ core env) ctx w = .ok (toVal v, w'))
    (herrCore : ∀ {w : World S ExtState E} {env : List Nat},
      Tx.run (Op.denote Γ env (.view target sel args ret)) ctx w = .error .callFailed →
      Tx.run (Core.denote Γ core env) ctx w = .error .callFailed)
    {w : World S ExtState E} {env : List Nat}
    {V : VEnv (yulD (toCalls o))} {st : EvmState}
    (funs : FunEnv (yulD (toCalls o)))
    (hfuns : noExtFuns funs = true)
    (hwfCall : callWF target args = true) (hsel : sel < 2 ^ 32)
    (hn1 : identsNodup tag (env.length + 1) = true)
    (hinv : Inv tag Γ c κ ctx w env V st)
    (hAgr : ExtAgree ctx.self w.ext st)
    (hOr : w.oracle = Oracle.ofExt o)
    (hNR : ExtOracle.NoReentry o ctx.self)
    {clearLock : Bool} {e1 : Emit}
    (hE : emitLetOp tag c {} env.length (.view target sel args ret) = some e1)
    {V' : VEnv (yulD (toCalls o))} {st' : EvmState} {out : Outcome}
    (hexec : ExecStmts (yulD (toCalls o)) funs V st
      (e1.stmts ++ ((if clearLock then [lockClearStmt] else []) ++
        (emitReturnWords {} [atomE tag (env.length + 1) (.var 0)]).stmts))
      V' st' out) :
    match Tx.run (Core.denote Γ core env) ctx w with
    | .ok (v, w') =>
        out = Outcome.halt ∧ haltSuccess t v st'.halted ∧
          R c Γ κ w' st' ∧ ExtAgree ctx.self w'.ext st'
    | .error e =>
        ∃ bytes, out = Outcome.halt ∧ st'.halted = some (HaltKind.revert, bytes) ∧
          haltError c Γ e bytes := by
  have hE' : emitLetOp tag ({} : ContractDef) {} env.length
      (.view target sel args ret) = some e1 := by
    simpa [emitLetOp] using hE
  cases execStmts_append_inv hexec with
  | inr hstop =>
    have hexec1 : ExecStmts (yulD (toCalls o)) funs V st
        ((emitLetOp tag ({} : ContractDef) {} env.length
          (.view target sel args ret)).getD {}).stmts V' st' out := by
      simpa [hE'] using hstop.2
    have hbit :=
      op_sim_view_bwd tag o hinv hAgr hOr hNR hfuns hwfCall hsel hn1 hexec1
    cases hrun : Tx.run (Op.denote Γ env (.view target sel args ret)) ctx w with
    | ok p =>
      simp only [hrun, except_ok_prod] at hbit
      exact (hstop.1 hbit.1).elim
    | error e =>
      simp only [hrun, except_error_prod] at hbit
      obtain ⟨ho, hh, he⟩ := hbit
      subst he
      exact sim_ext_error_callFailed (herrCore hrun) ho hh
  | inl hokPre =>
    obtain ⟨V1, st1, hcallE, hrest⟩ := hokPre
    have hexec1 : ExecStmts (yulD (toCalls o)) funs V st
        ((emitLetOp tag ({} : ContractDef) {} env.length
          (.view target sel args ret)).getD {}).stmts V1 st1 .normal := by
      simpa [hE'] using hcallE
    have hbit :=
      op_sim_view_bwd tag o hinv hAgr hOr hNR hfuns hwfCall hsel hn1 hexec1
    cases hrun : Tx.run (Op.denote Γ env (.view target sel args ret)) ctx w with
    | error e =>
      simp only [hrun, except_error_prod] at hbit
      cases hbit.1
    | ok p =>
      rcases p with ⟨v, w0⟩
      simp only [hrun, except_ok_prod] at hbit
      obtain ⟨-, hInv0, hAgr0⟩ := hbit
      have hstatic := ctxRel_static hInv0.ctxr
      have hrest' :=
        s1_match_prefix_ok hfuns (noExt_maybeLock clearLock) hrest
          (execStmts_maybeLock clearLock hstatic)
      have hMO := memOnly_stAfterLockClear clearLock st1
      have hInv1 := Inv_memOnly tag hInv0 hMO
      have haddr0 := ctxRel_address hInv0.ctxr
      have hAgr1 := ExtAgree_stAfterLockClear clearLock hAgr0 haddr0
      have he := eval_atom_ok tag (funEnvUncast (toCalls o) funs)
        (st := stAfterLockClear clearLock st1) hInv0.venv (.var 0)
      have hv : v < wordBound := hInv0.wf v (by simp)
      obtain ⟨_stR, hret, hh, hR'⟩ :=
        return_word_sim (funEnvUncast (toCalls o) funs) V1 hv he hInv1.rel
      have hnoRet := noExt_returnVar tag (env.length + 1)
      have hdesc := execStmts_descend hfuns hnoRet hrest'
      obtain ⟨hVeq', hsteq, hoeq⟩ := execStmts_det_evm hdesc hret
      subst hVeq'; subst hsteq; subst hoeq
      have haddr := ctxRel_address hInv1.ctxr
      have hAgr' := ExtAgree_noExt hAgr1 haddr hfuns hnoRet hrest'
      rw [hokCore hrun]
      simp only [except_ok_prod]
      exact ⟨trivial, hsucc hh, hR', hAgr'⟩

/-- `stmt_sim_call_bwd` composed with the continuation `ih`. -/
theorem sim_ext_seq_call {S E ε : Type} {t : RetTy}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε} {κ : List UInt8 → U256}
    {ctx : Ctx} {haltUnit : Bool} {o : ExtOracle}
    {k : Core t} {target : Atom} {sel : Nat} {args : List Atom} {ret : AbiRet}
    (ih : SimExt tag c Γ κ o ctx haltUnit k) :
    SimExt tag c Γ κ o ctx haltUnit (.seq (.call target sel args ret) k) := by
  intro w env V st funs hfuns hwf hn hinv hAgr hOr hNR clearLock e' hem V' st' out hexec
  have ⟨hsWF, hkWF⟩ := coreWF_seq.mp hwf
  simp only [emitCore] at hem
  obtain ⟨e0, h0, hst⟩ := emitCore_prefix tag hem
  rw [hst] at hexec
  have hn0 : identsNodup tag env.length = true :=
    identsNodup_mono tag (by simp [coreExtraDepth]) hn
  have hnK : identsNodup tag (env.length + coreExtraDepth k) = true := by
    simpa [coreExtraDepth] using hn
  have hpair :=
    stmtWF_call (c := c) (t := target) (sel := sel) (args := args) (ret := ret)
      (by simpa [stmtWF] using hsWF)
  rcases hpair with ⟨hwfCall, hsel⟩
  cases execStmts_append_inv hexec with
  | inr hstop =>
    have hbit :=
      stmt_sim_call_bwd tag o hinv hAgr hOr hNR hfuns hwfCall hsel hn0 hstop.2
    cases hrun : Tx.run (Stmt.denote Γ env (.call target sel args ret)) ctx w with
    | ok p =>
      simp only [hrun, except_ok_prod] at hbit
      exact (hstop.1 hbit.1).elim
    | error e =>
      simp only [hrun, except_error_prod] at hbit
      obtain ⟨ho, hh, he⟩ := hbit
      subst he
      exact sim_ext_error_callFailed (by
        simp only [Core.denote, Tx.run_bind, hrun]) ho hh
  | inl hokPre =>
    obtain ⟨V1, st1, hcallE, hrest⟩ := hokPre
    have hbit :=
      stmt_sim_call_bwd tag o hinv hAgr hOr hNR hfuns hwfCall hsel hn0 hcallE
    cases hrun : Tx.run (Stmt.denote Γ env (.call target sel args ret)) ctx w with
    | error e =>
      simp only [hrun, except_error_prod] at hbit
      cases hbit.1
    | ok p =>
      rcases p with ⟨_, w0⟩
      simp only [hrun, except_ok_prod] at hbit
      obtain ⟨-, hInv0, hAgr0⟩ := hbit
      have ⟨_, hop⟩ := stmt_call_ok_op hrun
      have hOr0 : w0.oracle = Oracle.ofExt o :=
        (denote_call_ok_oracle hop).trans hOr
      have hsim :=
        ih w0 env V1 st1 funs hfuns hkWF hnK hInv0 hAgr0 hOr0 hNR h0 hrest
      simp only [Core.denote, Tx.run_bind, hrun]
      exact hsim

/-- `stmt_sim_view_bwd` composed with the continuation `ih`. -/
theorem sim_ext_seq_view {S E ε : Type} {t : RetTy}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε} {κ : List UInt8 → U256}
    {ctx : Ctx} {haltUnit : Bool} {o : ExtOracle}
    {k : Core t} {target : Atom} {sel : Nat} {args : List Atom} {ret : AbiRet}
    (ih : SimExt tag c Γ κ o ctx haltUnit k) :
    SimExt tag c Γ κ o ctx haltUnit (.seq (.view target sel args ret) k) := by
  intro w env V st funs hfuns hwf hn hinv hAgr hOr hNR clearLock e' hem V' st' out hexec
  have ⟨hsWF, hkWF⟩ := coreWF_seq.mp hwf
  simp only [emitCore] at hem
  obtain ⟨e0, h0, hst⟩ := emitCore_prefix tag hem
  rw [hst] at hexec
  have hn0 : identsNodup tag env.length = true :=
    identsNodup_mono tag (by simp [coreExtraDepth]) hn
  have hnK : identsNodup tag (env.length + coreExtraDepth k) = true := by
    simpa [coreExtraDepth] using hn
  have hpair :=
    stmtWF_view (c := c) (t := target) (sel := sel) (args := args) (ret := ret)
      (by simpa [stmtWF] using hsWF)
  rcases hpair with ⟨hwfCall, hsel⟩
  cases execStmts_append_inv hexec with
  | inr hstop =>
    have hbit :=
      stmt_sim_view_bwd tag o hinv hAgr hOr hNR hfuns hwfCall hsel hn0 hstop.2
    cases hrun : Tx.run (Stmt.denote Γ env (.view target sel args ret)) ctx w with
    | ok p =>
      simp only [hrun, except_ok_prod] at hbit
      exact (hstop.1 hbit.1).elim
    | error e =>
      simp only [hrun, except_error_prod] at hbit
      obtain ⟨ho, hh, he⟩ := hbit
      subst he
      exact sim_ext_error_callFailed (by
        simp only [Core.denote, Tx.run_bind, hrun]) ho hh
  | inl hokPre =>
    obtain ⟨V1, st1, hcallE, hrest⟩ := hokPre
    have hbit :=
      stmt_sim_view_bwd tag o hinv hAgr hOr hNR hfuns hwfCall hsel hn0 hcallE
    cases hrun : Tx.run (Stmt.denote Γ env (.view target sel args ret)) ctx w with
    | error e =>
      simp only [hrun, except_error_prod] at hbit
      cases hbit.1
    | ok p =>
      rcases p with ⟨_, w0⟩
      simp only [hrun, except_ok_prod] at hbit
      obtain ⟨-, hInv0, hAgr0⟩ := hbit
      have ⟨_, hop⟩ := stmt_view_ok_op hrun
      have hOr0 : w0.oracle = Oracle.ofExt o := by
        rw [denote_view_ok_world hop, hOr]
      have hsim :=
        ih w0 env V1 st1 funs hfuns hkWF hnK hInv0 hAgr0 hOr0 hNR h0 hrest
      simp only [Core.denote, Tx.run_bind, hrun]
      exact hsim

theorem emitCore_letOp_split {c : ContractDef} {halt : Bool} {clearLock : Bool} {t : RetTy}
    {op : Lsc.Op} {k : Core t} {e' : Emit} {d : Nat}
    (hem : emitCore tag c {} d halt (.letOp op k) clearLock = some e') :
    ∃ e1 e0, emitLetOp tag c {} d op = some e1 ∧
      emitCore tag c {} (d + 1) halt k clearLock = some e0 ∧
      e'.stmts = e1.stmts ++ e0.stmts := by
  simp only [emitCore] at hem
  cases hE : emitLetOp tag c {} d op with
  | none => simp [hE] at hem
  | some e1 =>
    simp only [hE] at hem
    obtain ⟨e0, h0, hst⟩ := emitCore_prefix tag hem
    exact ⟨e1, e0, rfl, h0, hst⟩

/-- `op_sim_call_bwd` composed with the continuation `ih`. -/
theorem sim_ext_letOp_call {S E ε : Type} {t : RetTy}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε} {κ : List UInt8 → U256}
    {ctx : Ctx} {haltUnit : Bool} {o : ExtOracle}
    {k : Core t} {target : Atom} {sel : Nat} {args : List Atom} {ret : AbiRet}
    (ih : SimExt tag c Γ κ o ctx haltUnit k) :
    SimExt tag c Γ κ o ctx haltUnit (.letOp (.call target sel args ret) k) := by
  intro w env V st funs hfuns hwf hn hinv hAgr hOr hNR clearLock e' hem V' st' out hexec
  have ⟨hopWF0, hkWF⟩ := coreWF_letOp.mp hwf
  obtain ⟨e1, e0, hE, h0, hst⟩ := emitCore_letOp_split tag hem
  rw [hst] at hexec
  have hn1 : identsNodup tag (env.length + 1) = true :=
    identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
  have hnK : identsNodup tag ((env.length + 1) + coreExtraDepth k) = true := by
    simpa [coreExtraDepth, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
  have hpair :=
    opWF_call (c := c) (t := target) (sel := sel) (args := args) (ret := ret)
      (by simpa [opWF] using hopWF0)
  rcases hpair with ⟨hwfCall, hsel⟩
  have hE' : emitLetOp tag ({} : ContractDef) {} env.length
      (.call target sel args ret) = some e1 := by
    simpa [emitLetOp] using hE
  cases execStmts_append_inv hexec with
  | inr hstop =>
    have hexec1 : ExecStmts (yulD (toCalls o)) funs V st
        ((emitLetOp tag ({} : ContractDef) {} env.length
          (.call target sel args ret)).getD {}).stmts V' st' out := by
      simpa [hE'] using hstop.2
    have hbit :=
      op_sim_call_bwd tag o hinv hAgr hOr hNR hfuns hwfCall hsel hn1 hexec1
    cases hrun : Tx.run (Op.denote Γ env (.call target sel args ret)) ctx w with
    | ok p =>
      simp only [hrun, except_ok_prod] at hbit
      exact (hstop.1 hbit.1).elim
    | error e =>
      simp only [hrun, except_error_prod] at hbit
      obtain ⟨ho, hh, he⟩ := hbit
      subst he
      exact sim_ext_error_callFailed (by
        simp only [Core.denote, Tx.run_bind, hrun]) ho hh
  | inl hokPre =>
    obtain ⟨V1, st1, hcallE, hrest⟩ := hokPre
    have hexec1 : ExecStmts (yulD (toCalls o)) funs V st
        ((emitLetOp tag ({} : ContractDef) {} env.length
          (.call target sel args ret)).getD {}).stmts V1 st1 .normal := by
      simpa [hE'] using hcallE
    have hbit :=
      op_sim_call_bwd tag o hinv hAgr hOr hNR hfuns hwfCall hsel hn1 hexec1
    cases hrun : Tx.run (Op.denote Γ env (.call target sel args ret)) ctx w with
    | error e =>
      simp only [hrun, except_error_prod] at hbit
      cases hbit.1
    | ok p =>
      rcases p with ⟨v, w0⟩
      simp only [hrun, except_ok_prod] at hbit
      obtain ⟨-, hInv0, hAgr0⟩ := hbit
      have hOr0 : w0.oracle = Oracle.ofExt o :=
        (denote_call_ok_oracle hrun).trans hOr
      have hsim :=
        ih w0 (v :: env) V1 st1 funs hfuns hkWF (by simpa using hnK)
          hInv0 hAgr0 hOr0 hNR h0 hrest
      simp only [Core.denote, Tx.run_bind, hrun]
      exact hsim

/-- `op_sim_view_bwd` composed with the continuation `ih`. -/
theorem sim_ext_letOp_view {S E ε : Type} {t : RetTy}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε} {κ : List UInt8 → U256}
    {ctx : Ctx} {haltUnit : Bool} {o : ExtOracle}
    {k : Core t} {target : Atom} {sel : Nat} {args : List Atom} {ret : AbiRet}
    (ih : SimExt tag c Γ κ o ctx haltUnit k) :
    SimExt tag c Γ κ o ctx haltUnit (.letOp (.view target sel args ret) k) := by
  intro w env V st funs hfuns hwf hn hinv hAgr hOr hNR clearLock e' hem V' st' out hexec
  have ⟨hopWF0, hkWF⟩ := coreWF_letOp.mp hwf
  obtain ⟨e1, e0, hE, h0, hst⟩ := emitCore_letOp_split tag hem
  rw [hst] at hexec
  have hn1 : identsNodup tag (env.length + 1) = true :=
    identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
  have hnK : identsNodup tag ((env.length + 1) + coreExtraDepth k) = true := by
    simpa [coreExtraDepth, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
  have hpair :=
    opWF_view (c := c) (t := target) (sel := sel) (args := args) (ret := ret)
      (by simpa [opWF] using hopWF0)
  rcases hpair with ⟨hwfCall, hsel⟩
  have hE' : emitLetOp tag ({} : ContractDef) {} env.length
      (.view target sel args ret) = some e1 := by
    simpa [emitLetOp] using hE
  cases execStmts_append_inv hexec with
  | inr hstop =>
    have hexec1 : ExecStmts (yulD (toCalls o)) funs V st
        ((emitLetOp tag ({} : ContractDef) {} env.length
          (.view target sel args ret)).getD {}).stmts V' st' out := by
      simpa [hE'] using hstop.2
    have hbit :=
      op_sim_view_bwd tag o hinv hAgr hOr hNR hfuns hwfCall hsel hn1 hexec1
    cases hrun : Tx.run (Op.denote Γ env (.view target sel args ret)) ctx w with
    | ok p =>
      simp only [hrun, except_ok_prod] at hbit
      exact (hstop.1 hbit.1).elim
    | error e =>
      simp only [hrun, except_error_prod] at hbit
      obtain ⟨ho, hh, he⟩ := hbit
      subst he
      exact sim_ext_error_callFailed (by
        simp only [Core.denote, Tx.run_bind, hrun]) ho hh
  | inl hokPre =>
    obtain ⟨V1, st1, hcallE, hrest⟩ := hokPre
    have hexec1 : ExecStmts (yulD (toCalls o)) funs V st
        ((emitLetOp tag ({} : ContractDef) {} env.length
          (.view target sel args ret)).getD {}).stmts V1 st1 .normal := by
      simpa [hE'] using hcallE
    have hbit :=
      op_sim_view_bwd tag o hinv hAgr hOr hNR hfuns hwfCall hsel hn1 hexec1
    cases hrun : Tx.run (Op.denote Γ env (.view target sel args ret)) ctx w with
    | error e =>
      simp only [hrun, except_error_prod] at hbit
      cases hbit.1
    | ok p =>
      rcases p with ⟨v, w0⟩
      simp only [hrun, except_ok_prod] at hbit
      obtain ⟨-, hInv0, hAgr0⟩ := hbit
      have hOr0 : w0.oracle = Oracle.ofExt o := by
        rw [denote_view_ok_world hrun, hOr]
      have hsim :=
        ih w0 (v :: env) V1 st1 funs hfuns hkWF (by simpa using hnK)
          hInv0 hAgr0 hOr0 hNR h0 hrest
      simp only [Core.denote, Tx.run_bind, hrun]
      exact hsim

/-- Call-free `letOp` head: `op_sim` then `ih`. -/
theorem sim_ext_letOp_m1 {S E ε : Type} {t : RetTy}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε} {κ : List UInt8 → U256}
    {ctx : Ctx} {haltUnit : Bool} {o : ExtOracle}
    {op : Lsc.Op} {k : Core t}
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    (hM1 : M1Op op)
    (ih : SimExt tag c Γ κ o ctx haltUnit k)
    {w : World S ExtState E} {env : List Nat}
    {V : VEnv (yulD (toCalls o))} {st : EvmState}
    (funs : FunEnv (yulD (toCalls o)))
    (hfuns : noExtFuns funs = true)
    (hopWF : opWF c op = true) (hkWF : coreWF c k = true)
    (hn1 : identsNodup tag (env.length + 1) = true)
    (hnK : identsNodup tag ((env.length + 1) + coreExtraDepth k) = true)
    (hinv : Inv tag Γ c κ ctx w env V st)
    (hAgr : ExtAgree ctx.self w.ext st)
    (hOr : w.oracle = Oracle.ofExt o)
    (hNR : ExtOracle.NoReentry o ctx.self)
    {clearLock : Bool} {e1 e0 : Emit}
    (hE : emitLetOp tag c {} env.length op = some e1)
    (h0 : emitCore tag c {} (env.length + 1) haltUnit k clearLock = some e0)
    {V' : VEnv (yulD (toCalls o))} {st' : EvmState} {out : Outcome}
    (hexec : ExecStmts (yulD (toCalls o)) funs V st (e1.stmts ++ e0.stmts) V' st' out) :
    match Tx.run (Core.denote Γ (.letOp op k) env) ctx w with
    | .ok (v, w') =>
        out = Outcome.halt ∧ haltSuccess t v st'.halted ∧
          R c Γ κ w' st' ∧ ExtAgree ctx.self w'.ext st'
    | .error e =>
        ∃ bytes, out = Outcome.halt ∧ st'.halted = some (HaltKind.revert, bytes) ∧
          haltError c Γ e bytes := by
  have hno : noExtBlock e1.stmts = true :=
    noExt_letOp_m1 tag hM1 (by simp [Emit.stmts_nil]) hE
  have hsim :=
    op_sim tag (funEnvUncast (toCalls o) funs) hinv hΓ hκ hlen hM1 hopWF hn1
  simp only [hE] at hsim
  cases hopr : Tx.run (Op.denote Γ env op) ctx w with
  | error err =>
    rw [hopr] at hsim
    obtain ⟨V1, st1, bytes, hexecS1, hh, herr⟩ := hsim
    have ⟨ho, hVeq, hsteq⟩ := s1_match_prefix_halt hfuns hno hexec hexecS1
    subst hVeq; subst hsteq
    have htx :
        Tx.run (Core.denote Γ (.letOp op k) env) ctx w = .error err := by
      simp only [Core.denote, Tx.run_bind, hopr]
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
    have hAgr1 : ExtAgree ctx.self w1.ext st1 := by
      subst hw1
      have haddr := ctxRel_address hinv.ctxr
      cases execStmts_append_inv hexec with
      | inr hstop =>
        have hdesc := execStmts_descend hfuns hno hstop.2
        have ⟨_, _, ho⟩ := execStmts_det_evm hexecS1 hdesc
        exact (hstop.1 ho.symm).elim
      | inl hok =>
        obtain ⟨_, _, hpre, _⟩ := hok
        have hdesc := execStmts_descend hfuns hno hpre
        have ⟨_, hsteq, _⟩ := execStmts_det_evm hexecS1 hdesc
        subst hsteq
        exact ExtAgree_noExt hAgr haddr hfuns hno hpre
    have hOr1 : w1.oracle = Oracle.ofExt o := by simpa [hw1] using hOr
    have hsimK :=
      ih w1 (v :: env)
        ((identV tag env.length, BitVec.ofNat 256 v) :: V) st1
        funs hfuns hkWF (by simpa using hnK) hinv1 hAgr1 hOr1 hNR h0 hrest
    have htx :
        Tx.run (Core.denote Γ (.letOp op k) env) ctx w =
          Tx.run (Core.denote Γ k (v :: env)) ctx w1 := by
      simp only [Core.denote, Tx.run_bind, hopr]
    rw [htx]
    exact hsimK

/-- Call-free `seq` head: `stmt_sim` then `ih`. -/
theorem sim_ext_seq_m1 {S E ε : Type} {t : RetTy}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε} {κ : List UInt8 → U256}
    {ctx : Ctx} {haltUnit : Bool} {o : ExtOracle}
    {s : Lsc.Stmt} {k : Core t}
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    (hM1 : M1Stmt s)
    (ih : SimExt tag c Γ κ o ctx haltUnit k)
    {w : World S ExtState E} {env : List Nat}
    {V : VEnv (yulD (toCalls o))} {st : EvmState}
    (funs : FunEnv (yulD (toCalls o)))
    (hfuns : noExtFuns funs = true)
    (hsWF : stmtWF c s = true) (hkWF : coreWF c k = true)
    (hn0 : identsNodup tag env.length = true)
    (hnK : identsNodup tag (env.length + coreExtraDepth k) = true)
    (hinv : Inv tag Γ c κ ctx w env V st)
    (hAgr : ExtAgree ctx.self w.ext st)
    (hOr : w.oracle = Oracle.ofExt o)
    (hNR : ExtOracle.NoReentry o ctx.self)
    {clearLock : Bool} {e0 : Emit} (h0 : emitCore tag c {} env.length haltUnit k clearLock = some e0)
    {V' : VEnv (yulD (toCalls o))} {st' : EvmState} {out : Outcome}
    (hexec : ExecStmts (yulD (toCalls o)) funs V st
      ((emitStmt tag c {} env.length s).stmts ++ e0.stmts) V' st' out) :
    match Tx.run (Core.denote Γ (.seq s k) env) ctx w with
    | .ok (v, w') =>
        out = Outcome.halt ∧ haltSuccess t v st'.halted ∧
          R c Γ κ w' st' ∧ ExtAgree ctx.self w'.ext st'
    | .error e =>
        ∃ bytes, out = Outcome.halt ∧ st'.halted = some (HaltKind.revert, bytes) ∧
          haltError c Γ e bytes := by
  have hno : noExtBlock (emitStmt tag c {} env.length s).stmts = true :=
    noExt_stmt_m1 tag hM1 (by simp [Emit.stmts_nil])
  have hsim := stmt_sim tag (funEnvUncast (toCalls o) funs) hinv hΓ hκ hlen hM1 hsWF hn0
  cases hrun : Tx.run (Stmt.denote Γ env s) ctx w with
  | error err =>
    rw [hrun] at hsim
    obtain ⟨V1, st1, bytes, hexecS1, hh, herr⟩ := hsim
    have ⟨ho, hVeq, hsteq⟩ := s1_match_prefix_halt hfuns hno hexec hexecS1
    subst hVeq; subst hsteq
    have htx :
        Tx.run (Core.denote Γ (.seq s k) env) ctx w = .error err := by
      simp only [Core.denote, Tx.run_bind, hrun]
    rw [htx]
    simp only [except_error_prod]
    exact ⟨bytes, ho, hh, herr⟩
  | ok p =>
    rcases p with ⟨_, w1⟩
    rw [hrun] at hsim
    obtain ⟨st1, hexecS1, hinv1⟩ := hsim
    have hokd : Lsc.Stmt.denote Γ env s ctx w = .ok ((), w1) := by
      simpa [Tx.run] using hrun
    have hghost := m1stmt_preserves_ghost hM1 env ctx w hokd
    have hrest := s1_match_prefix_ok hfuns hno hexec hexecS1
    have hAgr1 : ExtAgree ctx.self w1.ext st1 := by
      rw [hghost.1]
      have haddr := ctxRel_address hinv.ctxr
      cases execStmts_append_inv hexec with
      | inr hstop =>
        have hdesc := execStmts_descend hfuns hno hstop.2
        have ⟨_, _, ho⟩ := execStmts_det_evm hexecS1 hdesc
        exact (hstop.1 ho.symm).elim
      | inl hok =>
        obtain ⟨_, _, hpre, _⟩ := hok
        have hdesc := execStmts_descend hfuns hno hpre
        have ⟨_, hsteq, _⟩ := execStmts_det_evm hexecS1 hdesc
        subst hsteq
        exact ExtAgree_noExt hAgr haddr hfuns hno hpre
    have hOr1 : w1.oracle = Oracle.ofExt o := hghost.2.trans hOr
    have hsimK :=
      ih w1 env V st1 funs hfuns hkWF hnK hinv1 hAgr1 hOr1 hNR h0 hrest
    have htx :
        Tx.run (Core.denote Γ (.seq s k) env) ctx w =
          Tx.run (Core.denote Γ k env) ctx w1 := by
      simp only [Core.denote, Tx.run_bind, hrun]
    rw [htx]
    exact hsimK

/-- Call as `stmtTail`: `stmt_sim_call_bwd` then `stop`. -/
theorem sim_ext_stmtTail_call {S E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε} {κ : List UInt8 → U256}
    {ctx : Ctx} {haltUnit : Bool} {o : ExtOracle}
    {target : Atom} {sel : Nat} {args : List Atom} {ret : AbiRet}
    (hhalt : haltUnit = true) :
    SimExt tag c Γ κ o ctx haltUnit (.stmtTail (.call target sel args ret)) := by
  intro w env V st funs hfuns hwf hn hinv hAgr hOr hNR clearLock e' hem V' st' out hexec
  simp only [emitCore] at hem
  rw [hhalt] at hem
  cases hem
  rw [emitReturnUnit_lock_if] at hexec
  have hpair :=
    stmtWF_call (c := c) (t := target) (sel := sel) (args := args) (ret := ret)
      (by simpa [coreWF] using hwf)
  rcases hpair with ⟨hwfCall, hsel⟩
  have hn0 : identsNodup tag env.length = true :=
    identsNodup_mono tag (by simp [coreExtraDepth]) hn
  cases execStmts_append_inv hexec with
  | inr hstop =>
    have hbit :=
      stmt_sim_call_bwd tag o hinv hAgr hOr hNR hfuns hwfCall hsel hn0 hstop.2
    cases hrun : Tx.run (Stmt.denote Γ env (.call target sel args ret)) ctx w with
    | ok p =>
      simp only [hrun, except_ok_prod] at hbit
      exact (hstop.1 hbit.1).elim
    | error e =>
      simp only [hrun, except_error_prod] at hbit
      obtain ⟨ho, hh, he⟩ := hbit
      subst he
      have hcore :
          Tx.run (Core.denote Γ (.stmtTail (.call target sel args ret)) env) ctx w =
            .error .callFailed := hrun
      rw [hcore]
      simp only [except_error_prod]
      exact ⟨[], ho, hh, rfl⟩
  | inl hokPre =>
    obtain ⟨V1, st1, hcallE, hrest⟩ := hokPre
    have hbit :=
      stmt_sim_call_bwd tag o hinv hAgr hOr hNR hfuns hwfCall hsel hn0 hcallE
    cases hrun : Tx.run (Stmt.denote Γ env (.call target sel args ret)) ctx w with
    | error e =>
      simp only [hrun, except_error_prod] at hbit
      cases hbit.1
    | ok p =>
      rcases p with ⟨_, w0⟩
      simp only [hrun, except_ok_prod] at hbit
      obtain ⟨-, hInv0, hAgr0⟩ := hbit
      have hstatic := ctxRel_static hInv0.ctxr
      have hMO := memOnly_stAfterLockClear clearLock st1
      have hInv1 := Inv_memOnly tag hInv0 hMO
      have haddr0 := ctxRel_address hInv0.ctxr
      have hAgr1 := ExtAgree_stAfterLockClear clearLock hAgr0 haddr0
      have hrest' :=
        s1_match_prefix_ok hfuns (noExt_maybeLock clearLock) hrest
          (execStmts_maybeLock clearLock hstatic)
      have hnoStop : noExtBlock [stopStmt] = true := by
        simp [noExtBlock, noExtStmts, noExt_stop]
      have hdesc := execStmts_descend hfuns hnoStop hrest'
      obtain ⟨hVeq', hsteq, hoeq⟩ := execStmts_det_evm hdesc
        (stop_sim (funEnvUncast (toCalls o) funs) V1 (stAfterLockClear clearLock st1))
      subst hVeq'; subst hsteq; subst hoeq
      have haddr := ctxRel_address hInv1.ctxr
      have hAgr' := ExtAgree_noExt hAgr1 haddr hfuns hnoStop hrest'
      have htx :
          Tx.run (Core.denote Γ (.stmtTail (.call target sel args ret)) env) ctx w =
            .ok ((), w0) := hrun
      rw [htx]
      simp only [except_ok_prod]
      exact ⟨trivial, haltSuccess_unit_stop rfl,
        R_halted_update hInv1.rel _, hAgr'⟩

/-- View as `stmtTail`. -/
theorem sim_ext_stmtTail_view {S E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε} {κ : List UInt8 → U256}
    {ctx : Ctx} {haltUnit : Bool} {o : ExtOracle}
    {target : Atom} {sel : Nat} {args : List Atom} {ret : AbiRet}
    (hhalt : haltUnit = true) :
    SimExt tag c Γ κ o ctx haltUnit (.stmtTail (.view target sel args ret)) := by
  intro w env V st funs hfuns hwf hn hinv hAgr hOr hNR clearLock e' hem V' st' out hexec
  simp only [emitCore] at hem
  rw [hhalt] at hem
  cases hem
  rw [emitReturnUnit_lock_if] at hexec
  have hpair :=
    stmtWF_view (c := c) (t := target) (sel := sel) (args := args) (ret := ret)
      (by simpa [coreWF] using hwf)
  rcases hpair with ⟨hwfCall, hsel⟩
  have hn0 : identsNodup tag env.length = true :=
    identsNodup_mono tag (by simp [coreExtraDepth]) hn
  cases execStmts_append_inv hexec with
  | inr hstop =>
    have hbit :=
      stmt_sim_view_bwd tag o hinv hAgr hOr hNR hfuns hwfCall hsel hn0 hstop.2
    cases hrun : Tx.run (Stmt.denote Γ env (.view target sel args ret)) ctx w with
    | ok p =>
      simp only [hrun, except_ok_prod] at hbit
      exact (hstop.1 hbit.1).elim
    | error e =>
      simp only [hrun, except_error_prod] at hbit
      obtain ⟨ho, hh, he⟩ := hbit
      subst he
      have hcore :
          Tx.run (Core.denote Γ (.stmtTail (.view target sel args ret)) env) ctx w =
            .error .callFailed := hrun
      rw [hcore]
      simp only [except_error_prod]
      exact ⟨[], ho, hh, rfl⟩
  | inl hokPre =>
    obtain ⟨V1, st1, hcallE, hrest⟩ := hokPre
    have hbit :=
      stmt_sim_view_bwd tag o hinv hAgr hOr hNR hfuns hwfCall hsel hn0 hcallE
    cases hrun : Tx.run (Stmt.denote Γ env (.view target sel args ret)) ctx w with
    | error e =>
      simp only [hrun, except_error_prod] at hbit
      cases hbit.1
    | ok p =>
      rcases p with ⟨_, w0⟩
      simp only [hrun, except_ok_prod] at hbit
      obtain ⟨-, hInv0, hAgr0⟩ := hbit
      have hstatic := ctxRel_static hInv0.ctxr
      have hMO := memOnly_stAfterLockClear clearLock st1
      have hInv1 := Inv_memOnly tag hInv0 hMO
      have haddr0 := ctxRel_address hInv0.ctxr
      have hAgr1 := ExtAgree_stAfterLockClear clearLock hAgr0 haddr0
      have hrest' :=
        s1_match_prefix_ok hfuns (noExt_maybeLock clearLock) hrest
          (execStmts_maybeLock clearLock hstatic)
      have hnoStop : noExtBlock [stopStmt] = true := by
        simp [noExtBlock, noExtStmts, noExt_stop]
      have hdesc := execStmts_descend hfuns hnoStop hrest'
      obtain ⟨hVeq', hsteq, hoeq⟩ := execStmts_det_evm hdesc
        (stop_sim (funEnvUncast (toCalls o) funs) V1 (stAfterLockClear clearLock st1))
      subst hVeq'; subst hsteq; subst hoeq
      have haddr := ctxRel_address hInv1.ctxr
      have hAgr' := ExtAgree_noExt hAgr1 haddr hfuns hnoStop hrest'
      have htx :
          Tx.run (Core.denote Γ (.stmtTail (.view target sel args ret)) env) ctx w =
            .ok ((), w0) := hrun
      rw [htx]
      simp only [except_ok_prod]
      exact ⟨trivial, haltSuccess_unit_stop rfl,
        R_halted_update hInv1.rel _, hAgr'⟩

end Lsc.Compiler
