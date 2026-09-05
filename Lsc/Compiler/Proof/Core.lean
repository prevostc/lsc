import Lsc.Compiler.Proof.Ops
import Lsc.Examples.Counter
import YulSemantics.Observation

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.defProp false

/-!
M1 core simulation: `letOp` / `seq` / `stmtTail` / `ret` unit, `params_sim` with n = 0.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc

def M1Frag : {t : RetTy} → Core t → Prop
  | .unit, .ret _ => True
  | _, .stmtTail s => M1Stmt s
  | _, .letOp op k => M1Op op ∧ M1Frag k
  | _, .seq s k => M1Stmt s ∧ M1Frag k
  | _, _ => False

theorem m1frag_letOp {t op} {k : Core t} :
    M1Frag (.letOp op k) ↔ M1Op op ∧ M1Frag k := by
  simp [M1Frag]

theorem m1frag_seq {t s} {k : Core t} :
    M1Frag (.seq s k) ↔ M1Stmt s ∧ M1Frag k := by
  simp [M1Frag]

theorem m1frag_stmtTail {s} : M1Frag (.stmtTail s) ↔ M1Stmt s := by
  simp [M1Frag]

theorem length_eq_one {α} {l : List α} : l.length = 1 ↔ ∃ a, l = [a] := by
  cases l with
  | nil => simp
  | cons a rest =>
    cases rest with
    | nil => simp
    | cons _ _ => simp

theorem emit_map_acc (e e0 : Emit) :
    ({ acc := e0.acc ++ e.acc } : Emit).stmts = e.stmts ++ e0.stmts := by
  simp [Emit.stmts, List.reverse_append]

theorem emitReturnUnit_acc (e : Emit) (halt : Bool) :
    emitReturnUnit e halt =
      { acc := (emitReturnUnit {} halt).acc ++ e.acc } := by
  cases halt <;> simp [emitReturnUnit, Emit.push]

theorem emitLet_acc (e : Emit) (n : YIdent) (x : YExpr) :
    emitLet e n x = { acc := (emitLet {} n x).acc ++ e.acc } := by
  simp [emitLet, Emit.push]

theorem emitAddChecked_acc (e : Emit) (name : YIdent) (a b : YExpr) :
    emitAddChecked e name a b =
      { acc := (emitAddChecked {} name a b).acc ++ e.acc } := by
  simp [emitAddChecked, emitLet, emitIf, Emit.push]

theorem emitStmt_acc {c : ContractDef} {d : Nat} {s : Lsc.Stmt} (h : M1Stmt s) (e : Emit) :
    emitStmt c e d s = { acc := (emitStmt c {} d s).acc ++ e.acc } := by
  match s with
  | .store f v =>
    simp only [emitStmt, emitDo, Emit.push]
    rfl
  | .emit ev args =>
    have ⟨a, hargs⟩ := length_eq_one.mp (h : args.length = 1)
    subst hargs
    simp only [emitStmt, emitLog1, emitDo, Emit.push]
    rfl
  | .storeMap .. | .storeMap2 .. | .require .. | .revert .. | .call .. =>
    exact (show False from h).elim

theorem emitLetOp_acc {c : ContractDef} {d : Nat} {op : Lsc.Op} (h : M1Op op) (e : Emit) :
    emitLetOp c e d op = (emitLetOp c {} d op).map fun e0 =>
      { acc := e0.acc ++ e.acc } := by
  match op with
  | .load f =>
    rw [emitLetOp_load, emitLetOp_load]
    simp only [Option.map_some]
    exact congrArg some (emitLet_acc e _ _)
  | .addChecked a b =>
    rw [emitLetOp_addChecked, emitLetOp_addChecked]
    simp only [Option.map_some]
    exact congrArg some (emitAddChecked_acc e _ _ _)
  | .loadMap .. | .loadMap2 .. | .sender | .value | .timestamp | .blockNumber
  | .selfAddress | .subChecked .. | .mulChecked .. | .divChecked ..
  | .mulDivDown .. | .mulDivUp .. | .call .. | .pure .. =>
    exact (show False from h).elim

theorem emitCore_acc {c : ContractDef} {halt : Bool} {t : RetTy} :
    ∀ (core : Core t) (hM1 : M1Frag core) (e : Emit) (d : Nat),
      emitCore c e d halt core = (emitCore c {} d halt core).map fun e0 =>
        { acc := e0.acc ++ e.acc } := by
  intro core
  induction core with
  | ret r =>
    intro hM1 e d
    cases r with
    | unit =>
      simp only [emitCore, emitRet, Option.map_some]
      rw [emitReturnUnit_acc]
    | word _ | addr _ | flag _ | pair _ _ =>
      simp [M1Frag] at hM1
  | stmtTail s =>
    intro hM1 e d
    simp only [emitCore, Option.map_some]
    rw [emitStmt_acc (m1frag_stmtTail.mp hM1)]
    rw [emitReturnUnit_acc, emitReturnUnit_acc (emitStmt c {} d s) halt]
    simp [List.append_assoc]
  | letOp op k ih =>
    intro hM1 e d
    have ⟨hop, hk⟩ := m1frag_letOp.mp hM1
    simp only [emitCore]
    rw [emitLetOp_acc hop]
    cases hE : emitLetOp c {} d op with
    | none => simp [hE]
    | some e0 =>
      simp only [hE, Option.map_some, Bind.bind, Option.bind]
      rw [ih hk { acc := e0.acc ++ e.acc } (d + 1), ih hk e0 (d + 1)]
      cases emitCore c {} (d + 1) halt k with
      | none => simp
      | some e1 => simp [List.append_assoc]
  | seq s k ih =>
    intro hM1 e d
    have ⟨hs, hk⟩ := m1frag_seq.mp hM1
    simp only [emitCore]
    rw [emitStmt_acc hs]
    rw [ih hk { acc := (emitStmt c {} d s).acc ++ e.acc } d, ih hk (emitStmt c {} d s) d]
    cases emitCore c {} d halt k with
    | none => simp
    | some e1 => simp [List.append_assoc]
  | opTail _ => intro hM1; simp [M1Frag] at hM1
  | opTailAddr _ => intro hM1; simp [M1Frag] at hM1
  | opTailFlag _ => intro hM1; simp [M1Frag] at hM1
  | revertTail _ _ => intro hM1; simp [M1Frag] at hM1
  | letPure _ _ _ => intro hM1; simp [M1Frag] at hM1
  | ite _ _ _ => intro hM1; simp [M1Frag] at hM1

theorem emitCore_prefix {c halt t} {core : Core t} (hM1 : M1Frag core)
    {e e' : Emit} {d : Nat} (hem : emitCore c e d halt core = some e') :
    ∃ e0, emitCore c {} d halt core = some e0 ∧ e'.stmts = e.stmts ++ e0.stmts := by
  have h := emitCore_acc (c := c) (halt := halt) core hM1 e d
  rw [h] at hem
  cases h0 : emitCore c {} d halt core with
  | none => simp [h0] at hem
  | some e0 =>
    simp [h0] at hem
    exact ⟨e0, rfl, by cases hem; exact emit_map_acc e e0⟩

theorem emitReturnUnit_true (e : Emit) :
    (emitReturnUnit e true).stmts = e.stmts ++ [stopStmt] := by
  simp [emitReturnUnit, Emit.stmts_push]

@[simp] theorem notFunDef_letDecl {xs e} : notFunDef (.letDecl xs e) = true := rfl
@[simp] theorem notFunDef_expr {e} : notFunDef (.exprStmt e) = true := rfl
@[simp] theorem notFunDef_cond {c b} : notFunDef (.cond c b) = true := rfl
@[simp] theorem notFunDef_stop : notFunDef stopStmt = true := rfl

theorem mem_append_elim {α} {a : α} {l₁ l₂ : List α} :
    a ∈ l₁ ++ l₂ → a ∈ l₁ ∨ a ∈ l₂ := List.mem_append.mp

theorem emitLet_notFunDef (e : Emit) (n : YIdent) (x : YExpr)
    (he : ∀ s ∈ e.stmts, notFunDef s = true) :
    ∀ s ∈ (emitLet e n x).stmts, notFunDef s = true := by
  intro s hs
  rcases mem_append_elim (emitLet_stmts e n x ▸ hs) with h | h
  · exact he s h
  · simp [List.mem_singleton.mp h]

theorem emitAddChecked_notFunDef (e : Emit) (name : YIdent) (a b : YExpr)
    (he : ∀ s ∈ e.stmts, notFunDef s = true) :
    ∀ s ∈ (emitAddChecked e name a b).stmts, notFunDef s = true := by
  intro s hs
  rcases mem_append_elim (emitAddChecked_stmts e name a b ▸ hs) with h | h
  · exact he s h
  · simp [List.mem_cons, List.mem_singleton] at h
    rcases h with rfl | rfl <;> simp [notFunDef]

theorem emitStmt_notFunDef {c : ContractDef} {d : Nat} {s : Lsc.Stmt}
    (h : M1Stmt s) (e : Emit) (he : ∀ t ∈ e.stmts, notFunDef t = true) :
    ∀ t ∈ (emitStmt c e d s).stmts, notFunDef t = true := by
  match s with
  | .store f v =>
    intro t ht
    rcases mem_append_elim (emitStmt_store c e d f v ▸ ht) with h | h
    · exact he t h
    · simp [List.mem_singleton.mp h]
  | .emit ev args =>
    have ⟨a, hargs⟩ := length_eq_one.mp (h : args.length = 1)
    subst hargs
    intro t ht
    simp only [emitStmt] at ht
    rw [show [a].map (atomE d) = [atomE d a] from rfl] at ht
    rw [emitLog1_one] at ht
    rcases mem_append_elim ht with h | h
    · exact he t h
    · simp [List.mem_cons, List.mem_singleton] at h
      rcases h with rfl | rfl <;> simp [notFunDef]
  | .storeMap .. | .storeMap2 .. | .require .. | .revert .. | .call .. =>
    exact (show False from h).elim

theorem emitLetOp_notFunDef {c d op} (h : M1Op op) (e : Emit)
    (he : ∀ s ∈ e.stmts, notFunDef s = true) {e1}
    (h1 : emitLetOp c e d op = some e1) :
    ∀ s ∈ e1.stmts, notFunDef s = true := by
  match op with
  | .load f =>
    simp [emitLetOp_load] at h1
    cases h1
    exact emitLet_notFunDef e _ _ he
  | .addChecked a b =>
    simp [emitLetOp_addChecked] at h1
    cases h1
    exact emitAddChecked_notFunDef e _ _ _ he
  | .loadMap .. | .loadMap2 .. | .sender | .value | .timestamp | .blockNumber
  | .selfAddress | .subChecked .. | .mulChecked .. | .divChecked ..
  | .mulDivDown .. | .mulDivUp .. | .call .. | .pure .. =>
    exact (show False from h).elim

theorem emitReturnUnit_notFunDef (e : Emit) (halt : Bool)
    (he : ∀ s ∈ e.stmts, notFunDef s = true) :
    ∀ s ∈ (emitReturnUnit e halt).stmts, notFunDef s = true := by
  cases halt with
  | false => simpa [emitReturnUnit] using he
  | true =>
    intro s hs
    rcases mem_append_elim (emitReturnUnit_true e ▸ hs) with h | h
    · exact he s h
    · simp [List.mem_singleton.mp h]

theorem m1_notFunDef {c halt t} :
    ∀ (core : Core t) (hM1 : M1Frag core) (e : Emit) (d : Nat) (e' : Emit),
      emitCore c e d halt core = some e' →
      (∀ s ∈ e.stmts, notFunDef s = true) →
      ∀ s ∈ e'.stmts, notFunDef s = true := by
  intro core
  induction core with
  | ret r =>
    intro hM1 e d e' hem he
    cases r with
    | unit =>
      simp [emitCore, emitRet] at hem
      cases hem
      exact emitReturnUnit_notFunDef e halt he
    | word _ | addr _ | flag _ | pair _ _ => simp [M1Frag] at hM1
  | stmtTail s =>
    intro hM1 e d e' hem he
    simp [emitCore] at hem
    cases hem
    exact emitReturnUnit_notFunDef _ halt (emitStmt_notFunDef (m1frag_stmtTail.mp hM1) e he)
  | letOp op k ih =>
    intro hM1 e d e' hem he
    have ⟨hop, hk⟩ := m1frag_letOp.mp hM1
    simp [emitCore] at hem
    cases hE : emitLetOp c e d op with
    | none => simp [hE] at hem
    | some e1 =>
      simp [hE] at hem
      exact ih hk e1 (d + 1) e' hem (emitLetOp_notFunDef hop e he hE)
  | seq s k ih =>
    intro hM1 e d e' hem he
    have ⟨hs, hk⟩ := m1frag_seq.mp hM1
    simp [emitCore] at hem
    exact ih hk (emitStmt c e d s) d e' hem (emitStmt_notFunDef hs e he)
  | opTail _ => intro hM1; simp [M1Frag] at hM1
  | opTailAddr _ => intro hM1; simp [M1Frag] at hM1
  | opTailFlag _ => intro hM1; simp [M1Frag] at hM1
  | revertTail _ _ => intro hM1; simp [M1Frag] at hM1
  | letPure _ _ _ => intro hM1; simp [M1Frag] at hM1
  | ite _ _ _ => intro hM1; simp [M1Frag] at hM1

theorem hoist_emitCore {c halt t} {core : Core t} (hM1 : M1Frag core)
    {e' d} (hem : emitCore c {} d halt core = some e') :
    hoist evm e'.stmts = [] :=
  hoist_nil_of (m1_notFunDef core hM1 {} d e' hem (by intro _ h; cases h))

theorem execStmts_stop_after {funs V st ss V1 st1}
    (h : ExecStmts evm funs V st ss V1 st1 .normal) :
    ExecStmts evm funs V st (ss ++ [stopStmt]) V1
      { st1 with halted := some (.stop, []) } .halt :=
  execStmts_append h (stop_sim funs V1 st1)

theorem HaltKind.stop_commits : HaltKind.stop.commits = true := rfl
theorem HaltKind.revert_commits : HaltKind.revert.commits = false := rfl

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

theorem coreWF_stmtTail {c s} :
    coreWF c (.stmtTail s) = true ↔ stmtWF c s = true := by
  simp [coreWF]

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
  | .emit ev args =>
    have ⟨a, hargs⟩ := length_eq_one.mp (hM1 : args.length = 1)
    subst hargs
    simp [Stmt.denote, Tx.run_emit]
    exact stmt_sim_emit funs hinv hwf hn
  | .storeMap .. | .storeMap2 .. | .require .. | .revert .. | .call .. =>
    exact (show False from hM1).elim

theorem op_sim {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ ctx} {w : World S X E} {env V st} {op : Lsc.Op}
    (funs : FunEnv evm) (hinv : Inv Γ c κ ctx w env V st)
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
  | .addChecked a b =>
    simp only [emitLetOp_addChecked]
    exact op_sim_addChecked funs hinv hwf hn
  | .loadMap .. | .loadMap2 .. | .sender | .value | .timestamp | .blockNumber
  | .selfAddress | .subChecked .. | .mulChecked .. | .divChecked ..
  | .mulDivDown .. | .mulDivUp .. | .call .. | .pure .. =>
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
    | word _ | addr _ | flag _ | pair _ _ =>
      simp [M1Frag] at hM1
  | stmtTail s =>
    intro hM1 w env V st funs hwf hn hinv e' hem
    simp only [emitCore, hhalt, emitReturnUnit_true] at hem
    cases hem
    have hn0 : identsNodup env.length = true :=
      identsNodup_mono (by simp [coreExtraDepth]) hn
    have hsim := stmt_sim funs hinv hΓ hκ hlen (m1frag_stmtTail.mp hM1)
      (coreWF_stmtTail.mp hwf) hn0
    cases hrun : Tx.run (Core.denote Γ (.stmtTail s) env) ctx w with
    | ok p =>
      simp only [RetTy.denote, Core.denote] at hrun
      simp [hrun] at hsim
      obtain ⟨st1, hexec, hinv1⟩ := hsim
      simp only [except_ok_prod]
      refine ⟨V, { st1 with halted := some (.stop, []) },
        (by simpa [emitReturnUnit_true] using execStmts_stop_after hexec),
        rfl, R_halted_update hinv1.rel _⟩
    | error err =>
      simp only [RetTy.denote, Core.denote] at hrun
      simp [hrun] at hsim
      obtain ⟨V', st', hexec, bytes, hh, herr⟩ := hsim
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
      obtain ⟨e0, h0, hst⟩ := emitCore_prefix hk hem
      have hn1 : identsNodup (env.length + 1) = true :=
        identsNodup_mono (by simp [coreExtraDepth]; try omega) hn
      have hnK : identsNodup ((env.length + 1) + coreExtraDepth k) = true := by
        simpa [coreExtraDepth, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
      cases hopr : Tx.run (Op.denote Γ env op) ctx w with
      | ok p =>
        have hsim := op_sim funs hinv hop hopWF hn1
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
        have hsim := op_sim funs hinv hop hopWF hn1
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
    obtain ⟨e0, h0, hst⟩ := emitCore_prefix hk hem
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
  | opTail _ =>
    intro hM1; simp [M1Frag] at hM1
  | opTailAddr _ =>
    intro hM1; simp [M1Frag] at hM1
  | opTailFlag _ =>
    intro hM1; simp [M1Frag] at hM1
  | revertTail _ _ =>
    intro hM1; simp [M1Frag] at hM1
  | letPure _ _ _ =>
    intro hM1; simp [M1Frag] at hM1
  | ite _ _ _ =>
    intro hM1; simp [M1Frag] at hM1

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
  cases hE : emitCore c (emitParams {} 4 f.params.length) f.params.length true f.core with
  | none => simp [hE] at h
  | some e =>
    simp [hE] at h
    exact ⟨hwfB, hnodB, e, rfl, by cases h; rfl⟩

theorem toYulFn_correct_m1 {S X E ε : Type} (c : ContractDef) (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (f : FnDef) (hf : f.kind ≠ .constructor) (hp : f.params.length = 0)
    (hM1 : M1Frag f.core) (hlen : c.fields.length < wordBound)
    (hret : f.ret = .unit)
    (yul : YBlock) (hyul : toYulFn c f = some yul)
    (ctx : Ctx) (w : World S X E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0) :
    match Tx.run (Core.denote Γ f.core (decodeArgs f st0.env.calldata).reverse) ctx w with
    | .ok (v, w') =>
        ∃ stObs,
          RunCommitted yul st0 [] stObs .halt ∧
          haltSuccess f.ret v stObs.halted ∧
          R c Γ κ w' stObs
    | .error e =>
        ∃ stObs bytes,
          RunCommitted yul st0 [] stObs .halt ∧
          stObs.halted = some (.revert, bytes) ∧
          haltError c Γ e bytes ∧
          R c Γ κ w stObs := by
  have ⟨hwf, hnod, e, hem, hy⟩ := toYulFn_inv hyul hf
  subst hy
  have henv : EnvWF ([] : List Nat) := envWF_nil
  have hinv : Inv Γ c κ ctx w [] [] st0 :=
    ⟨toVEnv_nil, henv, hR, hctx⟩
  have hp0 : emitParams {} 4 f.params.length = ({} : Emit) := by
    simp [hp, emitParams_zero]
  rw [hp0] at hem
  have hdepth : f.params.length + coreExtraDepth f.core = coreExtraDepth f.core := by
    simp [hp]
  have hn : identsNodup (0 + coreExtraDepth f.core) = true := by
    simpa [maxDepth, hdepth] using hnod
  have hdec : decodeArgs f st0.env.calldata = [] := by
    simp [decodeArgs, hp]
  simp only [hdec, List.reverse_nil]
  have hem0 : emitCore c {} 0 true f.core = some e := by
    simpa [hp] using hem
  have hsim := core_sim (c := c) (Γ := Γ) (κ := κ) (ctx := ctx) (haltUnit := true) rfl
    hΓ hκ hlen f.core hM1 (funs := [[]]) hwf (by simpa using hn) hinv hem0
  cases hrun : Tx.run (Core.denote Γ f.core []) ctx w with
  | ok p =>
    rw [hrun] at hsim
    obtain ⟨V', st', hexec, hsucc, hR'⟩ := hsim
    have hhoist : hoist evm e.stmts = [] := hoist_emitCore hM1 hem0
    have hRun : Run evm e.stmts st0 [] st' .halt := by
      have hblock := Step.block (D := evm) (by
        rw [hhoist]
        exact hexec)
      rw [restore_nil] at hblock
      exact hblock
    rcases p with ⟨v, w'⟩
    simp only [except_ok_prod]
    refine ⟨st', ⟨st', hRun, ?_⟩, hsucc, hR'⟩
    have hstop : st'.halted = some (.stop, []) := by
      simp [haltSuccess, hret] at hsucc
      exact hsucc
    exact (committedState_commit hstop HaltKind.stop_commits).symm
  | error err =>
    rw [hrun] at hsim
    obtain ⟨V', st', bytes, hexec, hh, herr⟩ := hsim
    have hhoist : hoist evm e.stmts = [] := hoist_emitCore hM1 hem0
    have hRun : Run evm e.stmts st0 [] st' .halt := by
      have hblock := Step.block (D := evm) (by
        rw [hhoist]
        exact hexec)
      rw [restore_nil] at hblock
      exact hblock
    simp only [except_error_prod]
    refine ⟨committedState st0 st', bytes, ⟨st', hRun, rfl⟩, ?_, herr,
      R_rollback_obs hR hh HaltKind.revert_commits⟩
    simp [committedState_rollback hh HaltKind.revert_commits, hh]

def incrementFn : FnDef where
  name := "increment"
  decl := ``Counter.increment
  kind := .tx
  params := []
  ret := .unit
  core := Counter.increment.core

theorem increment_m1 : M1Frag incrementFn.core := by
  simp [incrementFn, M1Frag, M1Op, M1Stmt, Counter.increment.core]

theorem increment_kind : incrementFn.kind ≠ .constructor := by
  simp [incrementFn]

theorem increment_params : incrementFn.params.length = 0 := rfl

theorem increment_ret : incrementFn.ret = .unit := rfl

theorem counter_fields_lt : Counter.contract.fields.length < wordBound := by
  have h : Counter.contract.fields.length = 1 := by
    simp [Counter.contract]
  rw [h]
  exact one_lt_wordBound

/-- `toYulFn_correct` for `Counter.increment`. -/
def counter_increment_correct
    (κ : List UInt8 → U256) (hκ : KeccakSep Counter.contract κ)
    (yul : YBlock) (hyul : toYulFn Counter.contract incrementFn = some yul)
    (ctx : Ctx) (w : World Counter.Storage Unit Counter.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Counter.contract Counter.schema κ w st0) :=
  toYulFn_correct_m1 (S := Counter.Storage) (X := Unit) (E := Counter.Event)
    (ε := Counter.Error)
    Counter.contract Counter.schema Counter.schema_lawful κ hκ
    incrementFn increment_kind increment_params increment_m1 counter_fields_lt
    increment_ret yul hyul ctx w st0 hctx hR

end Lsc.Compiler
