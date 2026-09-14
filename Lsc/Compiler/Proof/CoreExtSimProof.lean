import Lsc.Compiler.Proof.CoreExtCall
import Lsc.Lang.CoreTheorems
import Lsc.Compiler.CoreExtSimDefs

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

/-!
Proofs of S2 backward `core_sim_ext` / `toYulFn_correct_ext`.
Statements live in `CoreExtSimTheorems`. The only callee hypothesis is
`ExtOracle.NoReentry` (reentrancy is not modelled).
-/

namespace Lsc.Compiler.Proof

variable (tag : String)

open YulSemantics
open YulSemantics.EVM
open Lsc hiding Op Stmt
open Lsc.Compiler

/-- Call-free backward simulation: S1 `core_sim` + descend + `ExtAgree_noExt`. -/
theorem core_sim_ext_callFree {S E ε}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε} {κ : List UInt8 → U256}
    {ctx : Ctx} {haltUnit : Bool} {o : ExtOracle}
    (hhalt : haltUnit = true) (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    {t} (core : Core t) (hM1 : CallFree core) :
    SimExt tag c Γ κ o ctx haltUnit core := by
  intro w env V st funs hfuns hwf hn hinv hAgr _hOr _hNR clearLock e' hem V' st' out hexec
  have hno : noExtBlock e'.stmts = true :=
    noExt_core_callFree tag hM1 {} env.length hem (by simp [Emit.stmts_nil])
  have hdesc := execStmts_descend hfuns hno hexec
  have hS1 :=
    core_sim (tag := tag) (c := c) (Γ := Γ) (κ := κ) (ctx := ctx) hhalt hΓ hκ hlen
      core hM1 (funEnvUncast (toCalls o) funs) hwf hn hinv hem
  cases hTx : Tx.run (Core.denote Γ core env) ctx w with
  | ok p =>
    rcases p with ⟨v, w0⟩
    have hok : Core.denote Γ core env ctx w = .ok (v, w0) := by
      simpa [Tx.run] using hTx
    have hg := callFree_preserves_ghost (Γ := Γ) hM1 env ctx w hok
    rw [hTx] at hS1
    simp only [except_ok_prod] at hS1 ⊢
    obtain ⟨V1, st1, hexecS1, hsucc, hR⟩ := hS1
    obtain ⟨hVeq, hsteq, hoeq⟩ := execStmts_det_evm hdesc hexecS1
    subst hVeq; subst hsteq; subst hoeq
    have haddr := ctxRel_address hinv.ctxr
    have hAgr' : ExtAgree ctx.self w0.ext st' := by
      rw [hg.1]
      exact ExtAgree_noExt hAgr haddr hfuns hno hexec
    exact ⟨rfl, hsucc, hR, hAgr'⟩
  | error err =>
    rw [hTx] at hS1
    simp only [except_error_prod] at hS1 ⊢
    obtain ⟨V1, st1, bytes, hexecS1, hh, herr⟩ := hS1
    obtain ⟨hVeq, hsteq, hoeq⟩ := execStmts_det_evm hdesc hexecS1
    subst hVeq; subst hsteq; subst hoeq
    exact ⟨bytes, rfl, hh, herr⟩

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
delegate to `core_sim_ext_callFree`. A `.call` / `.view` head uses the
selector-driven `sim_ext_*` helpers. Reentrancy is excluded by `NoReentry`;
everything else about the callee is adversarial. -/
theorem core_sim_ext {S E ε}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε} {κ : List UInt8 → U256}
    {ctx : Ctx} {haltUnit : Bool} {o : ExtOracle}
    (hhalt : haltUnit = true) (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    {t} (core : Core t) (hS2 : S2Frag core) :
    SimExt tag c Γ κ o ctx haltUnit core := by
  revert hS2
  induction core with
  | ret r =>
    intro hS2
    cases r with
    | pair x y =>
      cases x with
      | word _ =>
        cases y with
        | word _ =>
          exact core_sim_ext_callFree tag hhalt hΓ hκ hlen _
            (by simp [CallFree, M1Frag])
        | _ => cases hS2
      | _ => cases hS2
    | unit | word _ | addr _ | flag _ =>
      exact core_sim_ext_callFree tag hhalt hΓ hκ hlen _
        (by simp [CallFree, M1Frag])
  | revertTail err args =>
    intro hS2
    exact core_sim_ext_callFree tag hhalt hΓ hκ hlen _
      (by simpa [CallFree, M1Frag, S2Frag] using hS2)
  | opTail op =>
    intro hS2 w env V st funs hfuns hwf hn hinv hAgr hOr hNR clearLock e' hem V' st' out hexec
    cases s2op_elim (by simpa [S2Frag] using hS2) with
    | inl hcall =>
      obtain ⟨target, sel, args, ret, rfl⟩ := hcall
      simp only [emitCore] at hem
      cases hE : emitLetOp tag c {} env.length (.call target sel args ret) with
      | none => simp [hE] at hem
      | some e1 =>
        simp only [hE] at hem
        cases hem
        have hretE := emitRet_word_stmts_if tag e1 (env.length + 1) haltUnit (.var 0) clearLock
        rw [hretE] at hexec
        have hpair :=
          opWF_call (c := c) (t := target) (sel := sel) (args := args) (ret := ret)
            (by simpa [coreWF] using hwf)
        rcases hpair with ⟨hwfCall, hsel⟩
        have hn1 : identsNodup tag (env.length + 1) = true :=
          identsNodup_mono tag (by simp [coreExtraDepth]) hn
        exact sim_ext_op_call_return tag
          (core := .opTail (.call target sel args ret)) id haltSuccess_word
          (fun h => by simpa [Core.denote, RetTy.denote] using h)
          (fun h => by simpa [Core.denote, RetTy.denote] using h)
          funs hfuns hwfCall hsel hn1 hinv hAgr hOr hNR hE hexec
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
          have hretE := emitRet_word_stmts_if tag e1 (env.length + 1) haltUnit (.var 0) clearLock
          rw [hretE] at hexec
          have hpair :=
            opWF_view (c := c) (t := target) (sel := sel) (args := args) (ret := ret)
              (by simpa [coreWF] using hwf)
          rcases hpair with ⟨hwfCall, hsel⟩
          have hn1 : identsNodup tag (env.length + 1) = true :=
            identsNodup_mono tag (by simp [coreExtraDepth]) hn
          exact sim_ext_op_view_return tag
            (core := .opTail (.view target sel args ret)) id haltSuccess_word
            (fun h => by simpa [Core.denote, RetTy.denote] using h)
            (fun h => by simpa [Core.denote, RetTy.denote] using h)
            funs hfuns hwfCall hsel hn1 hinv hAgr hOr hNR hE hexec
      | inr hM1 =>
        exact core_sim_ext_callFree tag hhalt hΓ hκ hlen (.opTail op)
          (by simpa [CallFree, M1Frag] using hM1)
          w env V st funs hfuns hwf hn hinv hAgr hOr hNR hem hexec
  | opTailAddr op =>
    intro hS2 w env V st funs hfuns hwf hn hinv hAgr hOr hNR clearLock e' hem V' st' out hexec
    cases s2op_elim (by simpa [S2Frag] using hS2) with
    | inl hcall =>
      obtain ⟨target, sel, args, ret, rfl⟩ := hcall
      simp only [emitCore] at hem
      cases hE : emitLetOp tag c {} env.length (.call target sel args ret) with
      | none => simp [hE] at hem
      | some e1 =>
        simp only [hE] at hem
        cases hem
        have hretE := emitRet_addr_stmts_if tag e1 (env.length + 1) haltUnit (.var 0) clearLock
        rw [hretE] at hexec
        have hpair :=
          opWF_call (c := c) (t := target) (sel := sel) (args := args) (ret := ret)
            (by simpa [coreWF] using hwf)
        rcases hpair with ⟨hwfCall, hsel⟩
        have hn1 : identsNodup tag (env.length + 1) = true :=
          identsNodup_mono tag (by simp [coreExtraDepth]) hn
        exact sim_ext_op_call_return tag
          (core := .opTailAddr (.call target sel args ret))
          (fun n => (n : Address)) haltSuccess_addr
          (fun h => by simpa [Core.denote, RetTy.denote, Address] using h)
          (fun h => by simpa [Core.denote, RetTy.denote, Address] using h)
          funs hfuns hwfCall hsel hn1 hinv hAgr hOr hNR hE hexec
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
          have hretE := emitRet_addr_stmts_if tag e1 (env.length + 1) haltUnit (.var 0) clearLock
          rw [hretE] at hexec
          have hpair :=
            opWF_view (c := c) (t := target) (sel := sel) (args := args) (ret := ret)
              (by simpa [coreWF] using hwf)
          rcases hpair with ⟨hwfCall, hsel⟩
          have hn1 : identsNodup tag (env.length + 1) = true :=
            identsNodup_mono tag (by simp [coreExtraDepth]) hn
          exact sim_ext_op_view_return tag
            (core := .opTailAddr (.view target sel args ret))
            (fun n => (n : Address)) haltSuccess_addr
            (fun h => by simpa [Core.denote, RetTy.denote, Address] using h)
            (fun h => by simpa [Core.denote, RetTy.denote, Address] using h)
            funs hfuns hwfCall hsel hn1 hinv hAgr hOr hNR hE hexec
      | inr hM1 =>
        exact core_sim_ext_callFree tag hhalt hΓ hκ hlen (.opTailAddr op)
          (by simpa [CallFree, M1Frag] using hM1)
          w env V st funs hfuns hwf hn hinv hAgr hOr hNR hem hexec
  | opTailFlag op =>
    intro hS2 w env V st funs hfuns hwf hn hinv hAgr hOr hNR clearLock e' hem V' st' out hexec
    cases s2op_elim (by simpa [S2Frag] using hS2) with
    | inl hcall =>
      obtain ⟨target, sel, args, ret, rfl⟩ := hcall
      simp only [emitCore] at hem
      cases hE : emitLetOp tag c {} env.length (.call target sel args ret) with
      | none => simp [hE] at hem
      | some e1 =>
        simp only [hE] at hem
        cases hem
        have hretE := emitRet_flag_stmts_if tag e1 (env.length + 1) haltUnit (.var 0) clearLock
        rw [hretE] at hexec
        have hpair :=
          opWF_call (c := c) (t := target) (sel := sel) (args := args) (ret := ret)
            (by simpa [coreWF] using hwf)
        rcases hpair with ⟨hwfCall, hsel⟩
        have hn1 : identsNodup tag (env.length + 1) = true :=
          identsNodup_mono tag (by simp [coreExtraDepth]) hn
        exact sim_ext_op_call_return tag
          (core := .opTailFlag (.call target sel args ret))
          (fun n => (n : Flag)) haltSuccess_flag
          (fun h => by simpa [Core.denote, RetTy.denote, Flag] using h)
          (fun h => by simpa [Core.denote, RetTy.denote, Flag] using h)
          funs hfuns hwfCall hsel hn1 hinv hAgr hOr hNR hE hexec
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
          have hretE := emitRet_flag_stmts_if tag e1 (env.length + 1) haltUnit (.var 0) clearLock
          rw [hretE] at hexec
          have hpair :=
            opWF_view (c := c) (t := target) (sel := sel) (args := args) (ret := ret)
              (by simpa [coreWF] using hwf)
          rcases hpair with ⟨hwfCall, hsel⟩
          have hn1 : identsNodup tag (env.length + 1) = true :=
            identsNodup_mono tag (by simp [coreExtraDepth]) hn
          exact sim_ext_op_view_return tag
            (core := .opTailFlag (.view target sel args ret))
            (fun n => (n : Flag)) haltSuccess_flag
            (fun h => by simpa [Core.denote, RetTy.denote, Flag] using h)
            (fun h => by simpa [Core.denote, RetTy.denote, Flag] using h)
            funs hfuns hwfCall hsel hn1 hinv hAgr hOr hNR hE hexec
      | inr hM1 =>
        exact core_sim_ext_callFree tag hhalt hΓ hκ hlen (.opTailFlag op)
          (by simpa [CallFree, M1Frag] using hM1)
          w env V st funs hfuns hwf hn hinv hAgr hOr hNR hem hexec
  | stmtTail s =>
    intro hS2
    cases s2stmt_elim (by simpa [S2Frag] using hS2) with
    | inl hcall =>
      obtain ⟨target, sel, args, ret, rfl⟩ := hcall
      exact sim_ext_stmtTail_call (target := target) (sel := sel)
        (args := args) (ret := ret) tag hhalt
    | inr hrest =>
      cases hrest with
      | inl hview =>
        obtain ⟨target, sel, args, ret, rfl⟩ := hview
        exact sim_ext_stmtTail_view (target := target) (sel := sel)
          (args := args) (ret := ret) tag hhalt
      | inr hM1 =>
        exact core_sim_ext_callFree tag hhalt hΓ hκ hlen (.stmtTail s)
          (by simpa [CallFree, M1Frag] using hM1)
  | letOp op k ih =>
    intro hS2
    have ⟨hop, hk⟩ := s2frag_letOp.mp hS2
    cases s2op_elim hop with
    | inl hcall =>
      obtain ⟨target, sel, args, ret, rfl⟩ := hcall
      exact sim_ext_letOp_call (target := target) (sel := sel)
        (args := args) (ret := ret) tag
        (ih hk : SimExt tag c Γ κ o ctx haltUnit k)
    | inr hrest =>
      cases hrest with
      | inl hview =>
        obtain ⟨target, sel, args, ret, rfl⟩ := hview
        exact sim_ext_letOp_view (target := target) (sel := sel)
          (args := args) (ret := ret) tag
          (ih hk : SimExt tag c Γ κ o ctx haltUnit k)
      | inr hM1 =>
        intro w env V st funs hfuns hwf hn hinv hAgr hOr hNR clearLock e' hem V' st' out hexec
        have ⟨hopWF0, hkWF⟩ := coreWF_letOp.mp hwf
        obtain ⟨e1, e0, hE, h0, hst⟩ := emitCore_letOp_split tag hem
        rw [hst] at hexec
        have hn1 : identsNodup tag (env.length + 1) = true :=
          identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
        have hnK : identsNodup tag ((env.length + 1) + coreExtraDepth k) = true := by
          simpa [coreExtraDepth, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
        exact sim_ext_letOp_m1 tag hΓ hκ hlen hM1 (ih hk)
          funs hfuns hopWF0 hkWF hn1 hnK hinv hAgr hOr hNR hE h0 hexec
  | seq s k ih =>
    intro hS2
    have ⟨hs, hk⟩ := s2frag_seq.mp hS2
    cases s2stmt_elim hs with
    | inl hcall =>
      obtain ⟨target, sel, args, ret, rfl⟩ := hcall
      exact sim_ext_seq_call (target := target) (sel := sel)
        (args := args) (ret := ret) tag
        (ih hk : SimExt tag c Γ κ o ctx haltUnit k)
    | inr hrest =>
      cases hrest with
      | inl hview =>
        obtain ⟨target, sel, args, ret, rfl⟩ := hview
        exact sim_ext_seq_view (target := target) (sel := sel)
          (args := args) (ret := ret) tag
          (ih hk : SimExt tag c Γ κ o ctx haltUnit k)
      | inr hM1 =>
        intro w env V st funs hfuns hwf hn hinv hAgr hOr hNR clearLock e' hem V' st' out hexec
        have ⟨hsWF, hkWF⟩ := coreWF_seq.mp hwf
        simp only [emitCore] at hem
        obtain ⟨e0, h0, hst⟩ := emitCore_prefix tag hem
        rw [hst] at hexec
        have hn0 : identsNodup tag env.length = true :=
          identsNodup_mono tag (by simp [coreExtraDepth]) hn
        have hnK : identsNodup tag (env.length + coreExtraDepth k) = true := by
          simpa [coreExtraDepth] using hn
        exact sim_ext_seq_m1 tag hΓ hκ hlen hM1 (ih hk)
          funs hfuns hsWF hkWF hn0 hnK hinv hAgr hOr hNR h0 hexec
  | letPure p args k ih =>
    intro hS2 w env V st funs hfuns hwf hn hinv hAgr hOr hNR clearLock e' hem V' st' out hexec
    have ⟨hp, hargs, hk⟩ := s2frag_letPure.mp hS2
    subst hp
    have ⟨a, hargs'⟩ := length_eq_one.mp hargs
    subst hargs'
    have ⟨hwfA, hkWF⟩ : atomWF a = true ∧ coreWF c k = true := by
      simpa [coreWF, Bool.and_eq_true] using hwf
    simp only [emitCore, emitPrim] at hem
    obtain ⟨e0, h0, hst⟩ := emitCore_prefix tag hem
    rw [hst] at hexec
    have hn0 : identsNodup tag env.length = true :=
      identsNodup_mono tag (by simp [coreExtraDepth]; try omega) hn
    have hnK : identsNodup tag ((env.length + 1) + coreExtraDepth k) = true := by
      simpa [coreExtraDepth, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
    have he := eval_atom tag (funEnvUncast (toCalls o) funs) (st := st) hinv.venv hn0 a
    have hv := atom_eval_lt hinv.wf hwfA
    have hlet :
        ExecStmt evm (funEnvUncast (toCalls o) funs) V st
          (.letDecl [identV tag env.length] (some (atomE tag env.length a)))
          ((identV tag env.length, BitVec.ofNat 256 (a.eval env)) :: V) st .normal :=
      Step.letVal he rfl
    have hpre : ExecStmts evm (funEnvUncast (toCalls o) funs) V st
        [.letDecl [identV tag env.length] (some (atomE tag env.length a))]
        ((identV tag env.length, BitVec.ofNat 256 (a.eval env)) :: V) st .normal :=
      Step.seqCons hlet Step.seqNil
    have hnoLet : noExtBlock [.letDecl [identV tag env.length] (some (atomE tag env.length a))] = true :=
      noExt_let (e := {}) (by simp [Emit.stmts_nil]) (noExt_atomE tag _ _)
    simp only [emitLet, Emit.stmts_push, Emit.stmts_nil, List.nil_append] at hexec hnoLet
    have hrest := s1_match_prefix_ok hfuns hnoLet hexec hpre
    have hinv1 : Inv tag Γ c κ ctx w (a.eval env :: env)
        ((identV tag env.length, BitVec.ofNat 256 (a.eval env)) :: V) st :=
      ⟨by rw [hinv.venv, toVEnv_cons], envWF_cons hv hinv.wf, hinv.rel, hinv.ctxr⟩
    have hsim :=
      ih hk w (a.eval env :: env)
        ((identV tag env.length, BitVec.ofNat 256 (a.eval env)) :: V) st
        funs hfuns hkWF (by simpa using hnK) hinv1 hAgr hOr hNR h0 hrest
    simp only [Core.denote]
    have hpe : Prim.eval .id (List.map (Atom.eval env) [a]) = a.eval env := rfl
    rw [hpe]
    exact hsim
  | ite cond a b iha ihb =>
    intro hS2 w env V st funs hfuns hwf hn hinv hAgr hOr hNR clearLock e' hem V' st' out hexec
    have ⟨hC, ha, hb⟩ := s2frag_ite.mp hS2
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
    have hpush :
        (Emit.push ({} : Emit) (.switch (emitCond tag env.length cond)
          [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts))).stmts =
          [.switch (emitCond tag env.length cond)
            [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts)] := by
      simp [Emit.stmts_push, Emit.stmts_nil]
    rw [hpush] at hexec
    have hsw := execStmts_one hexec
    have hcond := eval_cond tag (st := st) (funEnvUncast (toCalls o) funs) hinv.venv hinv.wf hn0 hC hcWF
    have hfunsN := noExtFuns_cons_nil (calls := toCalls o) hfuns
    cases hsw with
    | switchHalt he =>
      have hdesc := evalExpr_descend hfuns (noExt_emitCond tag env.length cond) he
      have := evalExpr_det_evm hcond hdesc
      cases this
    | switchExec he hbody =>
      have hdesc := evalExpr_descend hfuns (noExt_emitCond tag env.length cond) he
      have heq := evalExpr_det_evm hcond hdesc
      simp [eresUncast] at heq
      obtain ⟨rfl, rfl⟩ := heq
      cases hbody with
      | block hss =>
        have hhoistA : hoist (yulD (toCalls o)) eA.stmts = [] :=
          hoist_yulD_of_evm (hoist_emitCore tag hA)
        have hhoistB : hoist (yulD (toCalls o)) eB.stmts = [] :=
          hoist_yulD_of_evm (hoist_emitCore tag hB)
        simp only [Core.denote]
        split_ifs with hc
        · have hsel :
              selectSwitch (yulD (toCalls o)) (b2w (decide (cond.denote env)))
                [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) = eA.stmts :=
            selectSwitch_nonzero_yulD (by simp [hc, b2w])
          rw [hsel, hhoistA] at hss
          exact iha ha w env V st ([] :: funs) hfunsN haWF hnA hinv hAgr hOr hNR hA hss
        · have hsel :
              selectSwitch (yulD (toCalls o)) (b2w (decide (cond.denote env)))
                [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) = eB.stmts := by
            simp [hc, b2w]
            exact selectSwitch_zero_yulD
          rw [hsel, hhoistB] at hss
          exact ihb hb w env V st ([] :: funs) hfunsN hbWF hnB hinv hAgr hOr hNR hB hss

/-- S2 backward `toYulFn` for `S2Frag` cores. Every Yul run is predicted by
`Core.denote` with `w.oracle = Oracle.ofExt o`. Reentrancy is not modelled
(`NoReentry`); everything else about the callee is adversarial. -/
theorem toYulFn_correct_ext {S E ε : Type}
    {c : ContractDef} {Γ : ContractSchema S ExtState E ε}
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (o : ExtOracle) (f : FnDef) (hf : f.kind ≠ .constructor)
    (hS2 : S2Frag f.core) (hlen : c.fields.length < wordBound)
    (hbound : 4 + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : toYulFn c f = some yul)
    (ctx : Ctx) (w : World S ExtState E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0)
    (hAgr : ExtAgree ctx.self w.ext st0)
    (hOr : w.oracle = Oracle.ofExt o)
    (hNR : ExtOracle.NoReentry o ctx.self) :
    ToYulFnCorrectExt c Γ κ o f yul ctx w st0 := by
  intro st' out hrun
  have ⟨hwf, hnod, e, hem, hy⟩ := toYulFn_inv hyul hf
  obtain ⟨e0, h0, hst⟩ := emitCore_prefix (tag := f.name) hem
  obtain ⟨Vb, hbody, _hV⟩ := run_block_inv hrun
  have hhoist_evm := toYulFn_hoist hyul hf
  have hhoist : hoist (yulD (toCalls o)) yul = [] := hoist_yulD_of_evm hhoist_evm
  rw [hhoist] at hbody
  have hfuns : noExtFuns ([] :: [] : FunEnv (yulD (toCalls o))) = true := noExtFuns_nilScope
  rw [hy, hst] at hbody
  set args := decodeArgs f st0.env.calldata
  have henv : EnvWF args.reverse := decodeArgs_wf f st0.env.calldata
  have hdec := decodeArgs_runtime (f := f) (cd := st0.env.calldata) hf
  have hpar := params_sim (tag := f.name) (funEnvUncast (toCalls o) [[]]) st0 4 f.params.length hbound
  have hpar' : ExecStmts evm (funEnvUncast (toCalls o) [[]]) [] st0
      (emitParams f.name {} 4 f.params.length).stmts (toVEnv f.name args.reverse) st0 .normal := by
    convert hpar
    try simp [args, hdec]
  have hrest :=
    s1_match_prefix_ok (calls := toCalls o) hfuns
      (noExt_params (tag := f.name) 4 f.params.length) hbody hpar'
  have hinv : Inv f.name Γ c κ ctx w args.reverse (toVEnv f.name args.reverse) st0 :=
    ⟨rfl, henv, hR, hctx⟩
  have hn : identsNodup f.name (f.params.length + coreExtraDepth f.core) = true := by
    simpa [maxDepth] using hnod
  have hn' : identsNodup f.name (args.reverse.length + coreExtraDepth f.core) = true := by
    simpa [args, decodeArgs_length, List.length_reverse] using hn
  have h0' : emitCore f.name c {} args.reverse.length true f.core (locks f) = some e0 := by
    simpa [args, decodeArgs_length, List.length_reverse] using h0
  have hsim :=
    core_sim_ext (tag := f.name) (haltUnit := true) rfl hΓ hκ hlen f.core hS2
      w args.reverse (toVEnv f.name args.reverse) st0
      [[]] hfuns hwf hn' hinv hAgr hOr hNR h0' hrest
  cases hTx : Tx.run (Core.denote Γ f.core args.reverse) ctx w with
  | ok p =>
    rcases p with ⟨v, w'⟩
    simp only [hTx, except_ok_prod] at hsim ⊢
    obtain ⟨ho, hsucc, hR', hAgr'⟩ := hsim
    obtain ⟨k, bts, hh, hk⟩ := haltSuccess_commits hsucc
    rw [committedState_commit hh hk]
    exact ⟨ho, hsucc, hR', hAgr'⟩
  | error err =>
    simp only [hTx, except_error_prod] at hsim ⊢
    obtain ⟨bytes, ho, hh, herr⟩ := hsim
    refine ⟨bytes, ho, ?_, herr, R_rollback_obs hR hh HaltKind.revert_commits⟩
    simp [committedState_rollback hh HaltKind.revert_commits, hh]

end Lsc.Compiler.Proof
