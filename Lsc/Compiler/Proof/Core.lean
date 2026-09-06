import Lsc.Compiler.Proof.OpsMulDiv
import Lsc.Compiler.Proof.OpsCtx
import YulSemantics.Observation

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Core simulation. Each `core_sim` constructor is one case calling one `op_sim_*` / `stmt_sim_*`.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc

def M1Frag : {t : RetTy} → Core t → Prop
  | .unit, .ret _ => True
  | .word, .ret _ => True
  | .addr, .ret _ => True
  | .flag, .ret _ => True
  | .word, .opTail op => M1Op op
  | .addr, .opTailAddr op => M1Op op
  | .flag, .opTailFlag op => M1Op op
  | _, .stmtTail s => M1Stmt s
  | _, .revertTail _ args => args.length = 0
  | _, .letOp op k => M1Op op ∧ M1Frag k
  | _, .seq s k => M1Stmt s ∧ M1Frag k
  | _, .letPure p args k => p = .id ∧ args.length = 1 ∧ M1Frag k
  | _, .ite c a b => M1Cond c ∧ M1Frag a ∧ M1Frag b
  | _, _ => False

/-- Call-free fragment: no `Op.call`/`Stmt.call`. Covered operators are the S1 Token/Counter
set plus checked `mul`/`div`/`mulDiv*`, remaining ctx reads, 0-arg `emit`, and `addr`/`flag`
(single-word) returns. Still excluded: wrapping `letPure`, `require`/`revert`/`emit` with
other arities, `pair` returns. -/
def CallFreeOp : Lsc.Op → Prop := M1Op
def CallFreeStmt : Lsc.Stmt → Prop := M1Stmt
def CallFree : {t : RetTy} → Core t → Prop := M1Frag

theorem m1frag_letOp {t op} {k : Core t} :
    M1Frag (.letOp op k) ↔ M1Op op ∧ M1Frag k := by
  simp [M1Frag]

theorem m1frag_seq {t s} {k : Core t} :
    M1Frag (.seq s k) ↔ M1Stmt s ∧ M1Frag k := by
  simp [M1Frag]

theorem m1frag_letPure {t p args} {k : Core t} :
    M1Frag (.letPure p args k) ↔ p = .id ∧ args.length = 1 ∧ M1Frag k := by
  simp [M1Frag]

theorem m1frag_ite {t c} {a b : Core t} :
    M1Frag (.ite c a b) ↔ M1Cond c ∧ M1Frag a ∧ M1Frag b := by
  simp [M1Frag]

theorem except_ok_prod {ε α β γ} (p : α × β) (f : α → β → γ) (g : ε → γ) :
    (match (Except.ok p : Except ε (α × β)) with
      | .ok (a, b) => f a b
      | .error e => g e) = f p.1 p.2 := by
  rcases p with ⟨a, b⟩
  rfl

theorem except_error_prod {ε α β γ} (err : ε) (f : α → β → γ) (g : ε → γ) :
    (match (Except.error err : Except ε (α × β)) with
      | .ok (a, b) => f a b
      | .error e => g e) = g err := rfl

theorem coreWF_letOp {c op t} {k : Core t} :
    coreWF c (.letOp op k) = true ↔ opWF c op = true ∧ coreWF c k = true := by
  simp [coreWF, Bool.and_eq_true]

theorem coreWF_seq {c s t} {k : Core t} :
    coreWF c (.seq s k) = true ↔ stmtWF c s = true ∧ coreWF c k = true := by
  simp [coreWF, Bool.and_eq_true]

theorem length_eq_one {α} {l : List α} : l.length = 1 ↔ ∃ a, l = [a] := by
  cases l with
  | nil => simp
  | cons a rest =>
    cases rest with
    | nil => simp
    | cons _ _ => simp

theorem length_eq_three {α} {l : List α} : l.length = 3 ↔ ∃ a b c, l = [a, b, c] := by
  cases l with
  | nil => simp
  | cons a l1 =>
    cases l1 with
    | nil => simp
    | cons b l2 =>
      cases l2 with
      | nil => simp
      | cons c l3 =>
        cases l3 with
        | nil => simp
        | cons _ _ => simp


theorem HaltKind.stop_commits : HaltKind.stop.commits = true := rfl
theorem HaltKind.revert_commits : HaltKind.revert.commits = false := rfl
theorem HaltKind.ret_commits : HaltKind.ret.commits = true := rfl

theorem haltSuccess_commits {t : RetTy} {v : t.denote} {h} (hs : haltSuccess t v h) :
    ∃ k bs, h = some (k, bs) ∧ k.commits = true := by
  unfold haltSuccess at hs
  split at hs
  · exact ⟨.stop, [], hs, rfl⟩
  · exact ⟨.ret, abiBytes (retWords (t := t) v), hs, rfl⟩

theorem haltSuccess_word {v : Nat} {h}
    (hh : h = some (.ret, wordBytes v)) : haltSuccess .word v h := by
  simp [haltSuccess, hh, retWords, abiBytes_singleton]

theorem haltSuccess_addr {v : Address} {h}
    (hh : h = some (.ret, wordBytes (v : Nat))) : haltSuccess .addr v h := by
  simp [haltSuccess, hh, retWords]
  exact (abiBytes_singleton (v : Nat)).symm

theorem haltSuccess_flag {v : Flag} {h}
    (hh : h = some (.ret, wordBytes (v : Nat))) : haltSuccess .flag v h := by
  simp [haltSuccess, hh, retWords]
  exact (abiBytes_singleton (v : Nat)).symm

theorem exec_switch_halt {funs V st V' st'} {cnd : YExpr} {eA eB body : YBlock} {cv : U256}
    (he : EvalExpr evm funs V st cnd (.vals [cv] st))
    (hsel : selectSwitch evm cv [(YulSemantics.Literal.number 0, eB)] (some eA) = body)
    (hhoist : hoist evm body = [])
    (hexec : ExecStmts evm ([] :: funs) V st body V' st' .halt) :
    ExecStmts evm funs V st
      [.switch cnd [(YulSemantics.Literal.number 0, eB)] (some eA)]
      (restore V V') st' .halt := by
  refine Step.seqStop ?_ halt_ne_normal
  refine Step.switchExec he ?_
  refine Step.block (D := evm) ?_
  rwa [hsel, hhoist]

theorem execStmts_stop_after {funs V st ss V1 st1}
    (h : ExecStmts evm funs V st ss V1 st1 .normal) :
    ExecStmts evm funs V st (ss ++ [stopStmt]) V1
      { st1 with halted := some (.stop, []) } .halt :=
  execStmts_append h (stop_sim funs V1 st1)

theorem stmt_sim {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {s : Lsc.Stmt}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    (hM1 : M1Stmt s) (hwf : stmtWF c s = true)
    (hn : identsNodup env.length = true) :
    match Tx.run (Stmt.denote Γ env s) ctx w with
    | .ok (_, w') =>
        ∃ st', ExecStmts evm funs V st (emitStmt c {} env.length s).stmts V st' .normal ∧
          Inv Γ c κ ctx w' env V st'
    | .error e =>
        ∃ V' st' bytes,
          ExecStmts evm funs V st (emitStmt c {} env.length s).stmts V' st' .halt ∧
          st'.halted = some (.revert, bytes) ∧ haltError c Γ e bytes := by
  match s with
  | .store f val =>
    simp [Stmt.denote, Tx.run_store]
    exact stmt_sim_store funs hinv hΓ hκ hlen hwf hn
  | .storeMap f k val =>
    simp [Stmt.denote, Tx.run_storeMap]
    exact stmt_sim_storeMap funs hinv hΓ hκ hlen hwf hn
  | .storeMap2 f k1 k2 val =>
    simp [Stmt.denote, Tx.run_storeMap2]
    exact stmt_sim_storeMap2 funs hinv hΓ hκ hlen hwf hn
  | .emit ev args =>
    rcases (hM1 : args.length = 0 ∨ args.length = 1 ∨ args.length = 3) with h0 | h1 | h3
    · match args with
      | [] =>
        simp [Stmt.denote, Tx.run_emit]
        exact stmt_sim_emit0 funs hinv hwf
      | _ :: _ => cases h0
    · have ⟨a, hargs⟩ := length_eq_one.mp h1
      subst hargs
      simp [Stmt.denote, Tx.run_emit]
      exact stmt_sim_emit funs hinv hwf hn
    · have ⟨a, b, c, hargs⟩ := length_eq_three.mp h3
      subst hargs
      simp [Stmt.denote, Tx.run_emit]
      exact stmt_sim_emit3 funs hinv hwf hn
  | .require cond err args =>
    have ⟨hC, hlen⟩ := (hM1 : M1Cond cond ∧ args.length = 0)
    match args with
    | [] => exact stmt_sim_require funs hinv hC hwf hn
    | _ :: _ => cases hlen
  | .revert err args =>
    have hnil : args.length = 0 := hM1
    match args with
    | [] => exact stmt_sim_revert funs hinv hwf
    | _ :: _ => cases hnil
  | .call .. =>
    exact (show False from hM1).elim

theorem op_sim {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {op : Lsc.Op}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    (hM1 : M1Op op) (hwf : opWF c op = true)
    (hn : identsNodup (env.length + 1) = true) :
    match Tx.run (Op.denote Γ env op) ctx w with
    | .ok (v, w') =>
        ∃ st',
          ExecStmts evm funs V st ((emitLetOp c {} env.length op).getD {}).stmts
            ((identV env.length, BitVec.ofNat 256 v) :: V) st' .normal ∧
          Inv Γ c κ ctx w' (v :: env)
            ((identV env.length, BitVec.ofNat 256 v) :: V) st'
    | .error e =>
        ∃ V' st' bytes,
          ExecStmts evm funs V st ((emitLetOp c {} env.length op).getD {}).stmts
            V' st' .halt ∧
          st'.halted = some (.revert, bytes) ∧ haltError c Γ e bytes := by
  match op with
  | .load f =>
    simp [emitLetOp_load, Op.denote, Tx.run_load]
    exact op_sim_load funs hinv hwf
  | .loadMap f k =>
    simp only [emitLetOp_loadMap]
    simp [Op.denote, Tx.run_loadMap]
    exact op_sim_loadMap funs hinv hlen hwf hn
  | .loadMap2 f k1 k2 =>
    simp only [emitLetOp_loadMap2]
    simp [Op.denote, Tx.run_loadMap2]
    exact op_sim_loadMap2 funs hinv hlen hwf hn
  | .sender =>
    simp only [emitLetOp]
    simp [Op.denote, Tx.run_sender]
    exact op_sim_sender funs hinv
  | .value =>
    simp only [emitLetOp]
    simp [Op.denote, Tx.run_value]
    exact op_sim_value funs hinv
  | .timestamp =>
    simp only [emitLetOp]
    simp [Op.denote, Tx.run_timestamp]
    exact op_sim_timestamp funs hinv
  | .blockNumber =>
    simp only [emitLetOp]
    simp [Op.denote, Tx.run_blockNumber]
    exact op_sim_blockNumber funs hinv
  | .selfAddress =>
    simp only [emitLetOp]
    simp [Op.denote, Tx.run_selfAddress]
    exact op_sim_selfAddress funs hinv
  | .addChecked a b =>
    simp only [emitLetOp_addChecked]
    exact op_sim_addChecked funs hinv hwf hn
  | .subChecked a b =>
    simp only [emitLetOp_subChecked]
    exact op_sim_subChecked funs hinv hwf hn
  | .mulChecked a b =>
    simp only [emitLetOp_mulChecked]
    exact op_sim_mulChecked funs hinv hwf hn
  | .divChecked a b =>
    simp only [emitLetOp_divChecked]
    exact op_sim_divChecked funs hinv hwf hn
  | .mulDivDown a b d =>
    simp only [emitLetOp_mulDivDown]
    exact op_sim_mulDivDown funs hinv hwf hn
  | .mulDivUp a b d =>
    simp only [emitLetOp_mulDivUp]
    exact op_sim_mulDivUp funs hinv hwf hn
  | .pure a =>
    simp only [emitLetOp_pure]
    exact op_sim_pure funs hinv hwf hn
  | .call .. =>
    exact (show False from hM1).elim

theorem core_sim {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx haltUnit} (hhalt : haltUnit = true)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound)
    {t} (core : Core t) (hM1 : M1Frag core) :
    ∀ {w : World S X E} {env V st} (funs : FunEnv evm)
      (hwf : coreWF c core = true)
      (hn : identsNodup (env.length + coreExtraDepth core) = true)
      (hinv : Inv Γ c κ ctx w env V st)
      {e' : Emit} (hem : emitCore c {} env.length haltUnit core = some e'),
      match Tx.run (Core.denote Γ core env) ctx w with
      | .ok (v, w') =>
          ∃ V' st', ExecStmts evm funs V st e'.stmts V' st' .halt ∧
            haltSuccess t v st'.halted ∧ R c Γ κ w' st'
      | .error e =>
          ∃ V' st' bytes,
            ExecStmts evm funs V st e'.stmts V' st' .halt ∧
            st'.halted = some (.revert, bytes) ∧ haltError c Γ e bytes := by
  revert hM1
  induction core with
  | ret r =>
    intro hM1 w env V st funs hwf hn hinv e' hem
    cases r with
    | unit =>
      simp only [emitCore, emitRet, hhalt, emitReturnUnit_true, Emit.stmts_nil] at hem
      cases hem
      rw [Core.denote, Tx.run_pure]
      refine ⟨V, { st with halted := some (.stop, []) }, stop_sim funs V st, rfl, ?_⟩
      exact R_halted_update hinv.rel _
    | word a =>
      simp only [emitCore, emitRet] at hem
      cases hem
      have hn0 : identsNodup env.length = true :=
        identsNodup_mono (by simp [coreExtraDepth]) hn
      have hwfA : atomWF a = true := by simpa [coreWF, retWF] using hwf
      have hv := atom_eval_lt hinv.wf hwfA
      have he := eval_atom funs (st := st) hinv.venv hn0 a
      obtain ⟨st', hexec, hh, hR'⟩ := return_word_sim funs V hv he hinv.rel
      rw [Core.denote, Tx.run_pure]
      exact ⟨V, st', hexec, haltSuccess_word hh, hR'⟩
    | addr a =>
      simp only [emitCore, emitRet] at hem
      cases hem
      have hn0 : identsNodup env.length = true :=
        identsNodup_mono (by simp [coreExtraDepth]) hn
      have hwfA : atomWF a = true := by simpa [coreWF, retWF] using hwf
      have hv := atom_eval_lt hinv.wf hwfA
      have he := eval_atom funs (st := st) hinv.venv hn0 a
      obtain ⟨st', hexec, hh, hR'⟩ := return_word_sim funs V hv he hinv.rel
      rw [Core.denote, Tx.run_pure]
      exact ⟨V, st', hexec, haltSuccess_addr hh, hR'⟩
    | flag a =>
      simp only [emitCore, emitRet] at hem
      cases hem
      have hn0 : identsNodup env.length = true :=
        identsNodup_mono (by simp [coreExtraDepth]) hn
      have hwfA : atomWF a = true := by simpa [coreWF, retWF] using hwf
      have hv := atom_eval_lt hinv.wf hwfA
      have he := eval_atom funs (st := st) hinv.venv hn0 a
      obtain ⟨st', hexec, hh, hR'⟩ := return_word_sim funs V hv he hinv.rel
      rw [Core.denote, Tx.run_pure]
      exact ⟨V, st', hexec, haltSuccess_flag hh, hR'⟩
    | pair _ _ =>
      simp [M1Frag] at hM1
  | stmtTail s =>
    intro hM1 w env V st funs hwf hn hinv e' hem
    simp only [emitCore, hhalt, emitReturnUnit_true] at hem
    cases hem
    have hn0 : identsNodup env.length = true :=
      identsNodup_mono (by simp [coreExtraDepth]) hn
    have hsim := stmt_sim funs hinv hΓ hκ hlen (show M1Stmt s by simpa [M1Frag] using hM1)
      (show stmtWF c s = true by simpa [coreWF] using hwf) hn0
    cases hrun : Tx.run (Core.denote Γ (.stmtTail s) env) ctx w with
    | ok p =>
      simp only [RetTy.denote, Core.denote] at hrun
      rw [hrun] at hsim
      obtain ⟨st1, hexec, hinv1⟩ := hsim
      simp only [except_ok_prod]
      refine ⟨V, { st1 with halted := some (.stop, []) },
        (by simpa [emitReturnUnit_true] using execStmts_stop_after hexec),
        rfl, R_halted_update hinv1.rel _⟩
    | error err =>
      simp only [RetTy.denote, Core.denote] at hrun
      rw [hrun] at hsim
      obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
      simp only [except_error_prod]
      refine ⟨V', st', bytes,
        (by simpa [emitReturnUnit_true] using
          execStmts_append_halt (ss2 := [stopStmt]) hexec), hh, herr⟩
  | letOp op k ih =>
    intro hM1 w env V st funs hwf hn hinv e' hem
    have ⟨hop, hk⟩ := m1frag_letOp.mp hM1
    have ⟨hopWF, hkWF⟩ := coreWF_letOp.mp hwf
    simp only [Core.denote, Tx.run_bind]
    simp only [emitCore] at hem
    cases hE : emitLetOp c {} env.length op with
    | none =>
      simp [hE] at hem
    | some e1 =>
      simp only [hE] at hem
      obtain ⟨e0, h0, hst⟩ := emitCore_prefix hem
      have hn1 : identsNodup (env.length + 1) = true :=
        identsNodup_mono (by simp [coreExtraDepth]; try omega) hn
      have hnK : identsNodup ((env.length + 1) + coreExtraDepth k) = true := by
        simpa [coreExtraDepth, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
      cases hopr : Tx.run (Op.denote Γ env op) ctx w with
      | ok p =>
        have hsim := op_sim funs hinv hΓ hκ hlen hop hopWF hn1
        rw [hopr] at hsim
        simp only [hE] at hsim
        obtain ⟨st1, hexec, hinv1⟩ := hsim
        have ih' := ih hk funs hkWF (by simpa using hnK) hinv1 h0
        cases hK : Tx.run (Core.denote Γ k (p.1 :: env)) ctx p.2 with
        | ok q =>
          rw [hK] at ih'
          obtain ⟨V', st', hexeck, hhaltS, hR⟩ := ih'
          rcases p with ⟨v, w'⟩
          rcases q with ⟨r, w''⟩
          simp only [except_ok_prod, hK]
          refine ⟨V', st', ?_, hhaltS, hR⟩
          rw [hst]
          exact execStmts_append hexec hexeck
        | error err =>
          rw [hK] at ih'
          obtain ⟨V', st', bytes, hexeck, hh, herr⟩ := ih'
          rcases p with ⟨v, w'⟩
          simp only [except_ok_prod, hK, except_error_prod]
          refine ⟨V', st', bytes, ?_, hh, herr⟩
          rw [hst]
          exact execStmts_append hexec hexeck
      | error err =>
        have hsim := op_sim funs hinv hΓ hκ hlen hop hopWF hn1
        rw [hopr] at hsim
        simp only [hE] at hsim
        obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
        simp only [except_error_prod]
        refine ⟨V', st', bytes, ?_, hh, herr⟩
        rw [hst]
        exact execStmts_append_halt hexec
  | seq s k ih =>
    intro hM1 w env V st funs hwf hn hinv e' hem
    have ⟨hs, hk⟩ := m1frag_seq.mp hM1
    have ⟨hsWF, hkWF⟩ := coreWF_seq.mp hwf
    simp only [Core.denote, Tx.run_bind]
    simp only [emitCore] at hem
    obtain ⟨e0, h0, hst⟩ := emitCore_prefix hem
    have hn0 : identsNodup env.length = true :=
      identsNodup_mono (by simp [coreExtraDepth]) hn
    have hnK : identsNodup (env.length + coreExtraDepth k) = true := by
      simpa [coreExtraDepth] using hn
    cases hrun : Tx.run (Stmt.denote Γ env s) ctx w with
    | ok p =>
      have hsim := stmt_sim funs hinv hΓ hκ hlen hs hsWF hn0
      rw [hrun] at hsim
      obtain ⟨st1, hexec, hinv1⟩ := hsim
      have ih' := ih hk funs hkWF hnK hinv1 h0
      cases hK : Tx.run (Core.denote Γ k env) ctx p.2 with
      | ok q =>
        rw [hK] at ih'
        obtain ⟨V', st', hexeck, hhaltS, hR⟩ := ih'
        rcases p with ⟨u, w'⟩
        rcases q with ⟨r, w''⟩
        simp only [except_ok_prod, hK]
        refine ⟨V', st', ?_, hhaltS, hR⟩
        rw [hst]
        exact execStmts_append hexec hexeck
      | error err =>
        rw [hK] at ih'
        obtain ⟨V', st', bytes, hexeck, hh, herr⟩ := ih'
        rcases p with ⟨u, w'⟩
        simp only [except_ok_prod, hK, except_error_prod]
        refine ⟨V', st', bytes, ?_, hh, herr⟩
        rw [hst]
        exact execStmts_append hexec hexeck
    | error err =>
      have hsim := stmt_sim funs hinv hΓ hκ hlen hs hsWF hn0
      rw [hrun] at hsim
      obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
      simp only [except_error_prod]
      refine ⟨V', st', bytes, ?_, hh, herr⟩
      rw [hst]
      exact execStmts_append_halt hexec
  | opTail op =>
    intro hM1 w env V st funs hwf hn hinv e' hem
    simp only [Core.denote, RetTy.denote]
    simp only [emitCore] at hem
    cases hE : emitLetOp c {} env.length op with
    | none => simp [hE] at hem
    | some e1 =>
      simp only [hE] at hem
      cases hem
      have hop : M1Op op := by simpa [M1Frag] using hM1
      have hopWF : opWF c op = true := by simpa [coreWF] using hwf
      have hn1 : identsNodup (env.length + 1) = true :=
        identsNodup_mono (by simp [coreExtraDepth]) hn
      have hretE :
          (emitRet e1 (env.length + 1) haltUnit (.word (.var 0))).stmts =
            e1.stmts ++ (emitReturnWords {} [atomE (env.length + 1) (.var 0)]).stmts :=
        emitRet_word_stmts _ _ _ _
      cases hopr : Tx.run (Op.denote Γ env op) ctx w with
      | ok p =>
        have hsim := op_sim funs hinv hΓ hκ hlen hop hopWF hn1
        rw [hopr] at hsim
        simp only [hE] at hsim
        obtain ⟨st1, hexec, hinv1⟩ := hsim
        rcases p with ⟨v, w'⟩
        simp only [except_ok_prod]
        have hn0 : identsNodup (v :: env).length = true := by
          simpa using hn1
        have he := eval_atom funs (st := st1) hinv1.venv hn0 (.var 0)
        have hv : v < wordBound := hinv1.wf v (by simp)
        obtain ⟨st', hret, hh, hR'⟩ :=
          return_word_sim funs ((identV env.length, BitVec.ofNat 256 v) :: V) hv he hinv1.rel
        refine ⟨(identV env.length, BitVec.ofNat 256 v) :: V, st', ?_, haltSuccess_word hh, hR'⟩
        rw [hretE]
        exact execStmts_append hexec hret
      | error err =>
        have hsim := op_sim funs hinv hΓ hκ hlen hop hopWF hn1
        rw [hopr] at hsim
        simp only [hE] at hsim
        obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
        simp only [except_error_prod]
        refine ⟨V', st', bytes, ?_, hh, herr⟩
        rw [hretE]
        exact execStmts_append_halt hexec
  | letPure p args k ih =>
    intro hM1 w env V st funs hwf hn hinv e' hem
    have ⟨hp, hargs, hk⟩ := m1frag_letPure.mp hM1
    subst hp
    have ⟨a, hargs'⟩ := length_eq_one.mp hargs
    subst hargs'
    have ⟨hwfA, hkWF⟩ : atomWF a = true ∧ coreWF c k = true := by
      simpa [coreWF, Bool.and_eq_true] using hwf
    simp only [Core.denote]
    have hpe : Prim.eval .id (List.map (Atom.eval env) [a]) = a.eval env := rfl
    rw [hpe]
    simp only [emitCore, emitPrim] at hem
    obtain ⟨e0, h0, hst⟩ := emitCore_prefix hem
    have hn0 : identsNodup env.length = true :=
      identsNodup_mono (by simp [coreExtraDepth]; try omega) hn
    have hn1 : identsNodup (env.length + 1) = true :=
      identsNodup_mono (by simp [coreExtraDepth]; try omega) hn
    have hnK : identsNodup ((env.length + 1) + coreExtraDepth k) = true := by
      simpa [coreExtraDepth, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
    have he := eval_atom funs (st := st) hinv.venv hn0 a
    have hv := atom_eval_lt hinv.wf hwfA
    have hlet :
        ExecStmt evm funs V st
          (.letDecl [identV env.length] (some (atomE env.length a)))
          ((identV env.length, BitVec.ofNat 256 (a.eval env)) :: V) st .normal :=
      Step.letVal he rfl
    have hinv1 : Inv Γ c κ ctx w (a.eval env :: env)
        ((identV env.length, BitVec.ofNat 256 (a.eval env)) :: V) st :=
      ⟨by rw [hinv.venv, toVEnv_cons], envWF_cons hv hinv.wf, hinv.rel, hinv.ctxr⟩
    have ih' := ih hk funs hkWF (by simpa using hnK) hinv1 h0
    cases hK : Tx.run (Core.denote Γ k (a.eval env :: env)) ctx w with
    | ok q =>
      rw [hK] at ih'
      obtain ⟨V', st', hexeck, hhaltS, hR⟩ := ih'
      rcases q with ⟨r, w''⟩
      simp only [except_ok_prod]
      refine ⟨V', st', ?_, hhaltS, hR⟩
      rw [hst]
      simp only [emitLet, Emit.stmts_push, Emit.stmts_nil, List.nil_append]
      exact execStmts_append (Step.seqCons hlet Step.seqNil) hexeck
    | error err =>
      rw [hK] at ih'
      obtain ⟨V', st', bytes, hexeck, hh, herr⟩ := ih'
      simp only [except_error_prod]
      refine ⟨V', st', bytes, ?_, hh, herr⟩
      rw [hst]
      simp only [emitLet, Emit.stmts_push, Emit.stmts_nil, List.nil_append]
      exact execStmts_append (Step.seqCons hlet Step.seqNil) hexeck
  | ite cond a b iha ihb =>
    intro hM1 w env V st funs hwf hn hinv e' hem
    have ⟨hC, ha, hb⟩ := m1frag_ite.mp hM1
    have hwf' := hwf
    simp [coreWF, Bool.and_eq_true] at hwf'
    obtain ⟨⟨hcWF, haWF⟩, hbWF⟩ := hwf'
    simp only [Core.denote]
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
    have hcond := eval_cond (st := st) funs hinv.venv hinv.wf hn0 hC hcWF
    have hpush :
        (Emit.push ({} : Emit) (.switch (emitCond env.length cond)
          [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts))).stmts =
          [.switch (emitCond env.length cond)
            [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts)] := by
      simp [Emit.stmts_push, Emit.stmts_nil]
    rw [hpush]
    split_ifs with hc
    · have hsel :
          selectSwitch evm (b2w (decide (cond.denote env)))
            [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) = eA.stmts :=
        selectSwitch_nonzero (by simp [hc, b2w])
      have ihA := iha ha ([] :: funs) haWF hnA hinv hA
      cases hrun : Tx.run (Core.denote Γ a env) ctx w with
      | ok q =>
        rw [hrun] at ihA
        obtain ⟨V', st', hexec, hhaltS, hR⟩ := ihA
        rcases q with ⟨r, w''⟩
        simp only [except_ok_prod]
        refine ⟨restore V V', st', ?_, hhaltS, hR⟩
        exact exec_switch_halt hcond hsel (hoist_emitCore hA) hexec
      | error err =>
        rw [hrun] at ihA
        obtain ⟨V', st', bytes, hexec, hh, herr⟩ := ihA
        simp only [except_error_prod]
        refine ⟨restore V V', st', bytes, ?_, hh, herr⟩
        exact exec_switch_halt hcond hsel (hoist_emitCore hA) hexec
    · have hsel :
          selectSwitch evm (b2w (decide (cond.denote env)))
            [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) = eB.stmts := by
        simp [hc, b2w]
        exact selectSwitch_zero
      have ihB := ihb hb ([] :: funs) hbWF hnB hinv hB
      cases hrun : Tx.run (Core.denote Γ b env) ctx w with
      | ok q =>
        rw [hrun] at ihB
        obtain ⟨V', st', hexec, hhaltS, hR⟩ := ihB
        rcases q with ⟨r, w''⟩
        simp only [except_ok_prod]
        refine ⟨restore V V', st', ?_, hhaltS, hR⟩
        exact exec_switch_halt hcond hsel (hoist_emitCore hB) hexec
      | error err =>
        rw [hrun] at ihB
        obtain ⟨V', st', bytes, hexec, hh, herr⟩ := ihB
        simp only [except_error_prod]
        refine ⟨restore V V', st', bytes, ?_, hh, herr⟩
        exact exec_switch_halt hcond hsel (hoist_emitCore hB) hexec
  | opTailAddr op =>
    intro hM1 w env V st funs hwf hn hinv e' hem
    simp only [Core.denote, RetTy.denote, Address]
    simp only [emitCore] at hem
    cases hE : emitLetOp c {} env.length op with
    | none => simp [hE] at hem
    | some e1 =>
      simp only [hE] at hem
      cases hem
      have hop : M1Op op := by simpa [M1Frag] using hM1
      have hopWF : opWF c op = true := by simpa [coreWF] using hwf
      have hn1 : identsNodup (env.length + 1) = true :=
        identsNodup_mono (by simp [coreExtraDepth]) hn
      have hretE :
          (emitRet e1 (env.length + 1) haltUnit (.addr (.var 0))).stmts =
            e1.stmts ++ (emitReturnWords {} [atomE (env.length + 1) (.var 0)]).stmts :=
        emitRet_addr_stmts _ _ _ _
      cases hopr : Tx.run (Op.denote Γ env op) ctx w with
      | ok p =>
        have hsim := op_sim funs hinv hΓ hκ hlen hop hopWF hn1
        rw [hopr] at hsim
        simp only [hE] at hsim
        obtain ⟨st1, hexec, hinv1⟩ := hsim
        rcases p with ⟨v, w'⟩
        simp only [except_ok_prod]
        have hn0 : identsNodup (v :: env).length = true := by
          simpa using hn1
        have he := eval_atom funs (st := st1) hinv1.venv hn0 (.var 0)
        have hv : v < wordBound := hinv1.wf v (by simp)
        obtain ⟨st', hret, hh, hR'⟩ :=
          return_word_sim funs ((identV env.length, BitVec.ofNat 256 v) :: V) hv he hinv1.rel
        refine ⟨(identV env.length, BitVec.ofNat 256 v) :: V, st', ?_, haltSuccess_addr hh, hR'⟩
        rw [hretE]
        exact execStmts_append hexec hret
      | error err =>
        have hsim := op_sim funs hinv hΓ hκ hlen hop hopWF hn1
        rw [hopr] at hsim
        simp only [hE] at hsim
        obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
        simp only [except_error_prod]
        refine ⟨V', st', bytes, ?_, hh, herr⟩
        rw [hretE]
        exact execStmts_append_halt hexec
  | opTailFlag op =>
    intro hM1 w env V st funs hwf hn hinv e' hem
    simp only [Core.denote, RetTy.denote, Flag]
    simp only [emitCore] at hem
    cases hE : emitLetOp c {} env.length op with
    | none => simp [hE] at hem
    | some e1 =>
      simp only [hE] at hem
      cases hem
      have hop : M1Op op := by simpa [M1Frag] using hM1
      have hopWF : opWF c op = true := by simpa [coreWF] using hwf
      have hn1 : identsNodup (env.length + 1) = true :=
        identsNodup_mono (by simp [coreExtraDepth]) hn
      have hretE :
          (emitRet e1 (env.length + 1) haltUnit (.flag (.var 0))).stmts =
            e1.stmts ++ (emitReturnWords {} [atomE (env.length + 1) (.var 0)]).stmts :=
        emitRet_flag_stmts _ _ _ _
      cases hopr : Tx.run (Op.denote Γ env op) ctx w with
      | ok p =>
        have hsim := op_sim funs hinv hΓ hκ hlen hop hopWF hn1
        rw [hopr] at hsim
        simp only [hE] at hsim
        obtain ⟨st1, hexec, hinv1⟩ := hsim
        rcases p with ⟨v, w'⟩
        simp only [except_ok_prod]
        have hn0 : identsNodup (v :: env).length = true := by
          simpa using hn1
        have he := eval_atom funs (st := st1) hinv1.venv hn0 (.var 0)
        have hv : v < wordBound := hinv1.wf v (by simp)
        obtain ⟨st', hret, hh, hR'⟩ :=
          return_word_sim funs ((identV env.length, BitVec.ofNat 256 v) :: V) hv he hinv1.rel
        refine ⟨(identV env.length, BitVec.ofNat 256 v) :: V, st', ?_, haltSuccess_flag hh, hR'⟩
        rw [hretE]
        exact execStmts_append hexec hret
      | error err =>
        have hsim := op_sim funs hinv hΓ hκ hlen hop hopWF hn1
        rw [hopr] at hsim
        simp only [hE] at hsim
        obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
        simp only [except_error_prod]
        refine ⟨V', st', bytes, ?_, hh, herr⟩
        rw [hretE]
        exact execStmts_append_halt hexec
  | revertTail err args =>
    intro hM1 w env V st funs hwf hn hinv e' hem
    have hnil : args.length = 0 := by simpa [M1Frag] using hM1
    match args with
    | _ :: _ => cases hnil
    | [] =>
      simp only [emitCore] at hem
      cases hem
      simp only [Core.denote, Tx.run_revert]
      exact revertTail_sim funs hinv hwf

theorem params_sim_zero (funs : FunEnv evm) (V : VEnv evm) (st : EvmState) (off : Nat) :
    ExecStmts evm funs V st (emitParams {} off 0).stmts V st .normal := by
  simp [emitParams_zero, Emit.stmts_nil]
  exact Step.seqNil

theorem toYulFn_inv {c f yul} (h : toYulFn c f = some yul) (hk : f.kind ≠ .constructor) :
    coreWF c f.core = true ∧
    identsNodup (maxDepth f) = true ∧
    ∃ e, emitCore c (emitParams {} 4 f.params.length) f.params.length true f.core = some e ∧
      yul = e.stmts := by
  unfold toYulFn at h
  have hwfB : coreWF c f.core = true := by
    by_contra hne
    have : (!coreWF c f.core) = true := by
      cases hcore : coreWF c f.core
      · rfl
      · exact (hne hcore).elim
    simp [this] at h
  have hnodB : identsNodup (maxDepth f) = true := by
    by_contra hne
    have : (!identsNodup (maxDepth f)) = true := by
      cases hnd : identsNodup (maxDepth f)
      · rfl
      · exact (hne hnd).elim
    simp [hwfB, this] at h
  have hoffset : (if f.kind = FnKind.constructor then 0 else 4) = 4 := by
    simp [hk]
  have hhalt : decide (f.kind ≠ FnKind.constructor) = true := by simp [hk]
  simp [hwfB, hnodB, hoffset, hhalt] at h
  obtain ⟨e, hem⟩ := emitCore_some (c := c) (halt := true) f.core
    (emitParams {} 4 f.params.length) f.params.length
  simp [hem] at h
  exact ⟨hwfB, hnodB, e, hem, by cases h; rfl⟩

theorem toYulFn_execStmts_callFree {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (f : FnDef) (hf : f.kind ≠ .constructor)
    (hM1 : CallFree f.core) (hlen : c.fields.length < wordBound)
    (hbound : 4 + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : toYulFn c f = some yul)
    (ctx : Ctx) (w : World S X E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0) (funs : FunEnv evm) :
    match Tx.run (Core.denote Γ f.core (decodeArgs f st0.env.calldata).reverse) ctx w with
    | .ok (v, w') =>
        ∃ V' st', ExecStmts evm funs [] st0 yul V' st' .halt ∧
          haltSuccess f.ret v st'.halted ∧ R c Γ κ w' st'
    | .error e =>
        ∃ V' st' bytes,
          ExecStmts evm funs [] st0 yul V' st' .halt ∧
            st'.halted = some (.revert, bytes) ∧ haltError c Γ e bytes := by
  have ⟨hwf, hnod, e, hem, hy⟩ := toYulFn_inv hyul hf
  subst hy
  set args := decodeArgs f st0.env.calldata
  have hargs : args = decodeArgs f st0.env.calldata := rfl
  simp only [← hargs]
  have henv : EnvWF args.reverse := decodeArgs_wf f st0.env.calldata
  have hdec := decodeArgs_runtime (f := f) (cd := st0.env.calldata) hf
  have hpar := params_sim (funs := funs) st0 4 f.params.length hbound
  have hinv : Inv Γ c κ ctx w args.reverse (toVEnv args.reverse) st0 :=
    ⟨rfl, henv, hR, hctx⟩
  obtain ⟨e0, h0, hst⟩ := emitCore_prefix hem
  have hn : identsNodup (f.params.length + coreExtraDepth f.core) = true := by
    simpa [maxDepth] using hnod
  have hn' : identsNodup (args.reverse.length + coreExtraDepth f.core) = true := by
    simpa [args, decodeArgs_length, List.length_reverse] using hn
  have h0' : emitCore c {} args.reverse.length true f.core = some e0 := by
    simpa [args, decodeArgs_length, List.length_reverse] using h0
  have hsim := core_sim (c := c) (Γ := Γ) (κ := κ) (ctx := ctx) (haltUnit := true) rfl
    hΓ hκ hlen f.core hM1 (funs := funs) hwf hn' hinv h0'
  cases hrun : Tx.run (Core.denote Γ f.core args.reverse) ctx w with
  | ok p =>
    simp only [hrun, except_ok_prod] at hsim ⊢
    obtain ⟨V', st', hexec, hsucc, hR'⟩ := hsim
    rcases p with ⟨v, w'⟩
    refine ⟨V', st', ?_, hsucc, hR'⟩
    rw [hst]
    have hpar' : ExecStmts evm funs [] st0 (emitParams {} 4 f.params.length).stmts
        (toVEnv args.reverse) st0 .normal := by
      convert hpar
      try simp [args, hdec]
    exact execStmts_append hpar' hexec
  | error err =>
    simp only [hrun, except_error_prod] at hsim ⊢
    obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
    refine ⟨V', st', bytes, ?_, hh, herr⟩
    rw [hst]
    have hpar' : ExecStmts evm funs [] st0 (emitParams {} 4 f.params.length).stmts
        (toVEnv args.reverse) st0 .normal := by
      convert hpar
      try simp [args, hdec]
    exact execStmts_append hpar' hexec

theorem toYulFn_hoist {c f yul} (h : toYulFn c f = some yul)
    (hk : f.kind ≠ .constructor) : hoist evm yul = [] := by
  have ⟨_, _, e, hem, hy⟩ := toYulFn_inv h hk
  subst hy
  obtain ⟨e0, h0, hst⟩ := emitCore_prefix hem
  rw [hst, hoist_append, hoist_params, hoist_emitCore h0]
  simp

theorem toYulFn_correct_callFree {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (f : FnDef) (hf : f.kind ≠ .constructor)
    (hM1 : CallFree f.core) (hlen : c.fields.length < wordBound)
    (hbound : 4 + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : toYulFn c f = some yul)
    (ctx : Ctx) (w : World S X E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0) :
    ToYulFnCorrect c Γ κ f yul ctx w st0 := by
  have hsim := toYulFn_execStmts_callFree (c := c) (Γ := Γ) hΓ κ hκ f hf hM1 hlen
    hbound yul hyul ctx w st0 hctx hR [[]]
  have hhoist := toYulFn_hoist hyul hf
  set args := decodeArgs f st0.env.calldata
  have hargs : args = decodeArgs f st0.env.calldata := rfl
  simp only [← hargs] at hsim
  change match Tx.run (Core.denote Γ f.core args.reverse) ctx w with
    | .ok (v, w') =>
        ∃ stObs, RunCommitted yul st0 [] stObs .halt ∧
          haltSuccess f.ret v stObs.halted ∧ R c Γ κ w' stObs
    | .error e =>
        ∃ stObs bytes,
          RunCommitted yul st0 [] stObs .halt ∧
            stObs.halted = some (.revert, bytes) ∧
            haltError c Γ e bytes ∧ R c Γ κ w stObs
  cases hrun : Tx.run (Core.denote Γ f.core args.reverse) ctx w with
  | ok p =>
    simp only [hrun, except_ok_prod] at hsim ⊢
    obtain ⟨V', st', hexec, hsucc, hR'⟩ := hsim
    have hRun : Run evm yul st0 [] st' .halt := by
      have hblock := Step.block (D := evm) (by
        rw [hhoist]
        exact hexec)
      rw [restore_nil] at hblock
      exact hblock
    refine ⟨st', ⟨st', hRun, ?_⟩, hsucc, hR'⟩
    obtain ⟨k, bs, hh, hk⟩ := haltSuccess_commits hsucc
    exact (committedState_commit hh hk).symm
  | error err =>
    simp only [hrun, except_error_prod] at hsim ⊢
    obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
    have hRun : Run evm yul st0 [] st' .halt := by
      have hblock := Step.block (D := evm) (by
        rw [hhoist]
        exact hexec)
      rw [restore_nil] at hblock
      exact hblock
    refine ⟨committedState st0 st', bytes, ⟨st', hRun, rfl⟩, ?_, herr,
      R_rollback_obs hR hh HaltKind.revert_commits⟩
    simp [committedState_rollback hh HaltKind.revert_commits, hh]

end Lsc.Compiler
