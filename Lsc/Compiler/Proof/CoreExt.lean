import Lsc.Compiler.Proof.Core
import Lsc.Compiler.Proof.Call
import Lsc.Compiler.Proof.Descend

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

/-!
Backward `toYulFn_correct_ext` for **call-free** cores: invert `Run` → `step_descend` →
S1 `toYulFn_execStmts_callFree` → `execStmts_det_evm`. Call-free Yul never consults `calls`,
so `fo := w.faults`. Extra `hstab` (ghost independent of this execution's `EvmState`) plus
`haddr` (binding address independent of `self`) close `RX`; `Abs.ignoresLocal` is not
enough because `sstore` also updates `env.storageOf` at the executing address.

`Op.call`/`Stmt.call` (`op_sim_call_bwd`, `core_sim_ext`) remain M1: the call reads
`w.ncalls`. Failure uses `composeFault ncalls true rest` (Core does not bump `ncalls`).
Success uses `composeFault ncalls false rest`; a continuation sees indices `≥ ncalls + 1`.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc hiding Op Stmt

/-! ## S2 fragment (`CallFree ∪ {Op.call, Stmt.call}`) -/

def S2Op : Lsc.Op → Prop
  | .call _ _ _ => True
  | op => M1Op op

def S2Stmt : Lsc.Stmt → Prop
  | .call _ _ _ => True
  | s => M1Stmt s

def S2Frag : {t : RetTy} → Core t → Prop
  | .unit, .ret _ => True
  | .word, .ret _ => True
  | .addr, .ret _ => True
  | .flag, .ret _ => True
  | .word, .opTail op => S2Op op
  | .addr, .opTailAddr op => S2Op op
  | .flag, .opTailFlag op => S2Op op
  | _, .stmtTail s => S2Stmt s
  | _, .revertTail _ args => args.length = 0
  | _, .letOp op k => S2Op op ∧ S2Frag k
  | _, .seq s k => S2Stmt s ∧ S2Frag k
  | _, .letPure p args k => p = .id ∧ args.length = 1 ∧ S2Frag k
  | _, .ite c a b => M1Cond c ∧ S2Frag a ∧ S2Frag b
  | _, _ => False

theorem s2op_of_m1 {op} (h : M1Op op) : S2Op op := by
  cases op <;> first | exact h | simp [S2Op, M1Op] at h

theorem s2stmt_of_m1 {s} (h : M1Stmt s) : S2Stmt s := by
  cases s <;> first | exact h | simp [S2Stmt, M1Stmt] at h

theorem s2frag_of_callFree {t} {core : Core t} (h : CallFree core) : S2Frag core := by
  revert h
  induction core with
  | ret r =>
    intro h; cases r <;> simp [S2Frag, CallFree, M1Frag] at h ⊢
  | opTail op | opTailAddr op | opTailFlag op =>
    intro h; simp [S2Frag, CallFree, M1Frag] at h ⊢; exact s2op_of_m1 h
  | stmtTail s =>
    intro h; simp [S2Frag, CallFree, M1Frag] at h ⊢; exact s2stmt_of_m1 h
  | revertTail _ args =>
    intro h; simpa [S2Frag, CallFree, M1Frag] using h
  | letOp op k ih =>
    intro h
    have ⟨hop, hk⟩ := m1frag_letOp.mp h
    simpa [S2Frag] using And.intro (s2op_of_m1 hop) (ih hk)
  | seq s k ih =>
    intro h
    have ⟨hs, hk⟩ := m1frag_seq.mp h
    simpa [S2Frag] using And.intro (s2stmt_of_m1 hs) (ih hk)
  | letPure p args k ih =>
    intro h
    have ⟨hp, hlen, hk⟩ := m1frag_letPure.mp h
    simpa [S2Frag] using And.intro hp (And.intro hlen (ih hk))
  | ite c a b iha ihb =>
    intro h
    have ⟨hc, ha, hb⟩ := m1frag_ite.mp h
    simpa [S2Frag] using And.intro hc (And.intro (iha ha) (ihb hb))

/-! ## `NoExternalOps` of CallFree emit -/

theorem noExt_letOp_m1 {c : ContractDef} {e : Emit} {d : Nat} {op : Lsc.Op} {e' : Emit}
    (hM1 : M1Op op) (he : noExtBlock e.stmts = true)
    (h1 : emitLetOp c e d op = some e') : noExtBlock e'.stmts = true := by
  cases op with
  | load _ =>
    simp [emitLetOp] at h1; cases h1
    exact noExt_let he (noExt_bop (op := YulSemantics.EVM.Op.sload) rfl
      (noExtExprs_cons_true (noExt_lit _) noExtExprs_nil))
  | loadMap _ k =>
    simp [emitLetOp] at h1; cases h1
    exact noExt_let (noExt_mapSlotPrep e _ (atomE d k) he (noExt_atomE d k))
      (noExt_bop (op := YulSemantics.EVM.Op.sload) rfl (noExtExprs_cons_true noExt_keccak064 noExtExprs_nil))
  | loadMap2 _ k₁ k₂ =>
    simp [emitLetOp] at h1; cases h1
    exact noExt_let (noExt_map2SlotPrep e _ (atomE d k₁) (atomE d k₂) he
        (noExt_atomE d k₁) (noExt_atomE d k₂))
      (noExt_bop (op := YulSemantics.EVM.Op.sload) rfl (noExtExprs_cons_true noExt_keccak064 noExtExprs_nil))
  | sender =>
    simp [emitLetOp] at h1; cases h1
    exact noExt_let he (noExt_bop (op := YulSemantics.EVM.Op.caller) rfl noExtExprs_nil)
  | value =>
    simp [emitLetOp] at h1; cases h1
    exact noExt_let he (noExt_bop (op := YulSemantics.EVM.Op.callvalue) rfl noExtExprs_nil)
  | timestamp =>
    simp [emitLetOp] at h1; cases h1
    exact noExt_let he (noExt_bop (op := YulSemantics.EVM.Op.timestamp) rfl noExtExprs_nil)
  | blockNumber =>
    simp [emitLetOp] at h1; cases h1
    exact noExt_let he (noExt_bop (op := YulSemantics.EVM.Op.number) rfl noExtExprs_nil)
  | selfAddress =>
    simp [emitLetOp] at h1; cases h1
    exact noExt_let he (noExt_bop (op := YulSemantics.EVM.Op.address) rfl noExtExprs_nil)
  | addChecked a b =>
    simp [emitLetOp] at h1; cases h1
    exact noExt_addChecked e _ (atomE d a) (atomE d b) he (noExt_atomE d a) (noExt_atomE d b)
  | subChecked a b =>
    simp [emitLetOp] at h1; cases h1
    exact noExt_subChecked e _ (atomE d a) (atomE d b) he (noExt_atomE d a) (noExt_atomE d b)
  | mulChecked a b =>
    simp [emitLetOp] at h1; cases h1
    exact noExt_mulChecked e _ (atomE d a) (atomE d b) he (noExt_atomE d a) (noExt_atomE d b)
  | divChecked a b =>
    simp [emitLetOp] at h1; cases h1
    exact noExt_divChecked e _ (atomE d a) (atomE d b) he (noExt_atomE d a) (noExt_atomE d b)
  | mulDivDown a b c =>
    simp [emitLetOp] at h1; cases h1
    exact noExt_mulDivDown e _ (atomE d a) (atomE d b) (atomE d c) he
      (noExt_atomE d a) (noExt_atomE d b) (noExt_atomE d c)
  | mulDivUp a b c =>
    simp [emitLetOp] at h1; cases h1
    exact noExt_mulDivUp e _ (atomE d a) (atomE d b) (atomE d c) he
      (noExt_atomE d a) (noExt_atomE d b) (noExt_atomE d c)
  | pure a =>
    simp [emitLetOp] at h1; cases h1
    exact noExt_let he (noExt_atomE d a)
  | call _ _ _ => exact (show False from hM1).elim

theorem noExt_stmt_m1 {c : ContractDef} {e : Emit} {d : Nat} {s : Lsc.Stmt}
    (hM1 : M1Stmt s) (he : noExtBlock e.stmts = true) :
    noExtBlock (emitStmt c e d s).stmts = true := by
  cases s with
  | store _ v =>
    simp only [emitStmt]
    exact noExt_do he (op := YulSemantics.EVM.Op.sstore) rfl
      (noExtExprs_cons_true (noExt_lit _) (noExtExprs_cons_true (noExt_atomE d v) noExtExprs_nil))
  | storeMap _ k v =>
    simp only [emitStmt]
    exact noExt_do (noExt_mapSlotPrep e _ (atomE d k) he (noExt_atomE d k))
      (op := YulSemantics.EVM.Op.sstore) rfl
      (noExtExprs_cons_true noExt_keccak064 (noExtExprs_cons_true (noExt_atomE d v) noExtExprs_nil))
  | storeMap2 _ k₁ k₂ v =>
    simp only [emitStmt]
    exact noExt_do (noExt_map2SlotPrep e _ (atomE d k₁) (atomE d k₂) he
        (noExt_atomE d k₁) (noExt_atomE d k₂))
      (op := YulSemantics.EVM.Op.sstore) rfl
      (noExtExprs_cons_true noExt_keccak064 (noExtExprs_cons_true (noExt_atomE d v) noExtExprs_nil))
  | require cond err args =>
    have ⟨_, hlen⟩ : M1Cond cond ∧ args.length = 0 := hM1
    match args with
    | _ :: _ => cases hlen
    | [] =>
      simp only [emitStmt, List.map_nil]
      exact noExt_if he
        (noExt_bop (op := YulSemantics.EVM.Op.iszero) rfl
          (noExtExprs_cons_true (noExt_emitCond d cond) noExtExprs_nil))
        (noExt_customError c {} err [] noExt_nil (fun _ hx => by cases hx))
  | emit _ args =>
    simp only [emitStmt]
    exact noExt_log1 e _ _ he (noExt_atomEs d args)
  | revert err args =>
    have hlen : args.length = 0 := hM1
    match args with
    | _ :: _ => cases hlen
    | [] =>
      simp only [emitStmt, List.map_nil]
      exact noExt_customError c e err [] he (fun _ hx => by cases hx)
  | call _ _ _ => exact (show False from hM1).elim

theorem noExt_core_callFree {c halt t} {core : Core t} (hM1 : CallFree core) :
    ∀ (e : Emit) (d : Nat) {e' : Emit},
      emitCore c e d halt core = some e' →
      noExtBlock e.stmts = true → noExtBlock e'.stmts = true := by
  revert hM1
  induction core with
  | ret r =>
    intro hM1 e d e' hem he
    simp [emitCore] at hem; cases hem
    exact noExt_ret e d halt r he
  | opTail op | opTailAddr op | opTailFlag op =>
    intro hM1 e d e' hem he
    simp [emitCore] at hem
    obtain ⟨e1, h1⟩ := emitLetOp_some c e d op
    simp [h1] at hem; cases hem
    have hop : M1Op op := by simpa [CallFree, M1Frag] using hM1
    exact noExt_ret e1 (d + 1) halt _ (noExt_letOp_m1 hop he h1)
  | stmtTail s =>
    intro hM1 e d e' hem he
    simp [emitCore] at hem; cases hem
    exact noExt_ret _ d halt .unit (noExt_stmt_m1 (by simpa [CallFree, M1Frag] using hM1) he)
  | revertTail err args =>
    intro hM1 e d e' hem he
    have hnil : args.length = 0 := by simpa [CallFree, M1Frag] using hM1
    match args with
    | _ :: _ => cases hnil
    | [] =>
      simp [emitCore] at hem; cases hem
      exact noExt_customError c e err [] he (fun _ hx => by cases hx)
  | letOp op k ih =>
    intro hM1 e d e' hem he
    have ⟨hop, hk⟩ := m1frag_letOp.mp hM1
    simp [emitCore] at hem
    obtain ⟨e1, h1⟩ := emitLetOp_some c e d op
    simp [h1] at hem
    exact ih hk e1 (d + 1) hem (noExt_letOp_m1 hop he h1)
  | seq s k ih =>
    intro hM1 e d e' hem he
    have ⟨hs, hk⟩ := m1frag_seq.mp hM1
    simp [emitCore] at hem
    exact ih hk (emitStmt c e d s) d hem (noExt_stmt_m1 hs he)
  | letPure p args k ih =>
    intro hM1 e d e' hem he
    have ⟨_, _, hk⟩ := m1frag_letPure.mp hM1
    simp [emitCore] at hem
    exact ih hk _ (d + 1) hem (noExt_let he (noExt_emitPrim d p args))
  | ite cond a b iha ihb =>
    intro hM1 e d e' hem he
    have ⟨_, ha, hb⟩ := m1frag_ite.mp hM1
    simp [emitCore] at hem
    obtain ⟨eA, hA⟩ := emitCore_some (c := c) (halt := halt) a ({} : Emit) d
    obtain ⟨eB, hB⟩ := emitCore_some (c := c) (halt := halt) b ({} : Emit) d
    simp [hA, hB] at hem; cases hem
    exact noExt_switch he (noExt_emitCond d cond)
      (by
        change (noExtStmts eB.stmts && noExtCases []) = true
        simpa [noExtBlock] using ihb hb {} d hB noExt_nil)
      (iha ha {} d hA noExt_nil)

theorem noExt_toYulFn_callFree {c f yul} (hM1 : CallFree f.core)
    (hy : toYulFn c f = some yul) (hk : f.kind ≠ .constructor) :
    noExtBlock yul = true := by
  have ⟨_, _, e, hem, hy'⟩ := toYulFn_inv hy hk
  subst hy'
  obtain ⟨e0, h0, hst⟩ := emitCore_prefix hem
  rw [hst]
  exact noExtBlock_append (noExt_params 4 f.params.length)
    (noExt_core_callFree hM1 {} _ h0 noExt_nil)

/-! ## Descend glue -/

theorem hoist_yulD_of_evm {calls : ExternalCalls} {ss : YBlock}
    (h : hoist evm ss = []) : hoist (yulD calls) ss = [] := by
  have hcast := hoist_uncast calls ss
  rw [h] at hcast
  cases hss : hoist (yulD calls) ss with
  | nil => rfl
  | cons _ _ =>
    rw [hss] at hcast
    simp [fscopeCast] at hcast

theorem noExtFuns_nilScope {calls : ExternalCalls} :
    noExtFuns ([] :: [] : FunEnv (yulD calls)) = true :=
  noExtFuns_cons_nil noExtFuns_nil

theorem funEnvUncast_nilScope (calls : ExternalCalls) :
    funEnvUncast calls [[]] = [[]] := by
  delta funEnvUncast funEnvCast fscopeCast
  rfl

theorem run_block_inv {calls : ExternalCalls} {yul : YBlock} {st0 : EvmState}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (h : Run (yulD calls) yul st0 V' st' o) :
    ∃ Vb, ExecStmts (yulD calls) (hoist (yulD calls) yul :: []) [] st0 yul Vb st' o ∧
      V' = restore [] Vb :=
  exec_block_inv h

theorem m1op_preserves_ghost {S X E ε} {Γ : ContractSchema S X E ε}
    {op : Lsc.Op} (h : M1Op op) (env : List Nat) (ctx : Ctx) (w : World S X E)
    {v : Nat} {w' : World S X E}
    (hok : Lsc.Op.denote Γ env op ctx w = .ok (v, w')) :
    w'.ext = w.ext ∧ w'.faults = w.faults ∧ w'.ncalls = w.ncalls := by
  cases op with
  | call _ _ _ => exact (show False from h).elim
  | load f =>
    have hred : Lsc.Op.denote Γ env (.load f) ctx w =
        .ok (Γ.st.scalar f w.self, w) := rfl
    rw [hred] at hok; cases hok; simp
  | loadMap f k =>
    have hred : Lsc.Op.denote Γ env (.loadMap f k) ctx w =
        .ok (Γ.st.map1 f w.self (k.eval env), w) := rfl
    rw [hred] at hok; cases hok; simp
  | loadMap2 f k₁ k₂ =>
    have hred : Lsc.Op.denote Γ env (.loadMap2 f k₁ k₂) ctx w =
        .ok (Γ.st.map2 f w.self (k₁.eval env) (k₂.eval env), w) := rfl
    rw [hred] at hok; cases hok; simp
  | sender =>
    have hred : Lsc.Op.denote (Γ := Γ) env .sender ctx w = .ok (ctx.sender, w) := rfl
    rw [hred] at hok; cases hok; simp
  | value =>
    have hred : Lsc.Op.denote (Γ := Γ) env .value ctx w = .ok (ctx.value, w) := rfl
    rw [hred] at hok; cases hok; simp
  | timestamp =>
    have hred : Lsc.Op.denote (Γ := Γ) env .timestamp ctx w = .ok (ctx.timestamp, w) := rfl
    rw [hred] at hok; cases hok; simp
  | blockNumber =>
    have hred : Lsc.Op.denote (Γ := Γ) env .blockNumber ctx w = .ok (ctx.blockNumber, w) := rfl
    rw [hred] at hok; cases hok; simp
  | selfAddress =>
    have hred : Lsc.Op.denote (Γ := Γ) env .selfAddress ctx w = .ok (ctx.self, w) := rfl
    rw [hred] at hok; cases hok; simp
  | addChecked a b =>
    have hred : Lsc.Op.denote Γ env (.addChecked a b) ctx w =
        if a.eval env + b.eval env < wordBound then .ok (a.eval env + b.eval env, w)
        else .error (.arith .overflow) := rfl
    rw [hred] at hok; split at hok <;> cases hok <;> simp
  | subChecked a b =>
    have hred : Lsc.Op.denote Γ env (.subChecked a b) ctx w =
        if b.eval env ≤ a.eval env then .ok (a.eval env - b.eval env, w)
        else .error (.arith .underflow) := rfl
    rw [hred] at hok; split at hok <;> cases hok <;> simp
  | mulChecked a b =>
    have hred : Lsc.Op.denote Γ env (.mulChecked a b) ctx w =
        if a.eval env * b.eval env < wordBound then .ok (a.eval env * b.eval env, w)
        else .error (.arith .overflow) := rfl
    rw [hred] at hok; split at hok <;> cases hok <;> simp
  | divChecked a b =>
    have hred : Lsc.Op.denote Γ env (.divChecked a b) ctx w =
        if b.eval env ≠ 0 then .ok (a.eval env / b.eval env, w)
        else .error (.arith .divByZero) := rfl
    rw [hred] at hok; split at hok <;> cases hok <;> simp
  | mulDivDown a b c =>
    have hred : Lsc.Op.denote Γ env (.mulDivDown a b c) ctx w =
        if c.eval env = 0 then .error (.arith .divByZero)
        else if a.eval env * b.eval env < wordBound then
          .ok (a.eval env * b.eval env / c.eval env, w)
        else .error (.arith .overflow) := rfl
    rw [hred] at hok; split_ifs at hok <;> cases hok <;> simp
  | mulDivUp a b c =>
    have hred : Lsc.Op.denote Γ env (.mulDivUp a b c) ctx w =
        if c.eval env = 0 then .error (.arith .divByZero)
        else if a.eval env * b.eval env < wordBound then
          .ok (a.eval env * b.eval env / c.eval env +
            if a.eval env * b.eval env % c.eval env = 0 then 0 else 1, w)
        else .error (.arith .overflow) := rfl
    rw [hred] at hok; split_ifs at hok <;> cases hok <;> simp
  | pure a =>
    have hred : Lsc.Op.denote Γ env (.pure a) ctx w = .ok (a.eval env, w) := rfl
    rw [hred] at hok; cases hok; simp

theorem m1stmt_preserves_ghost {S X E ε} {Γ : ContractSchema S X E ε}
    {s : Lsc.Stmt} (h : M1Stmt s) (env : List Nat) (ctx : Ctx) (w : World S X E)
    {v : Unit} {w' : World S X E}
    (hok : Lsc.Stmt.denote Γ env s ctx w = .ok (v, w')) :
    w'.ext = w.ext ∧ w'.faults = w.faults ∧ w'.ncalls = w.ncalls := by
  cases s with
  | call _ _ _ => exact (show False from h).elim
  | store f val =>
    have hred : Lsc.Stmt.denote Γ env (.store f val) ctx w =
        .ok ((), { w with self := Γ.st.scalarUpd f w.self (val.eval env) }) := rfl
    rw [hred] at hok; cases hok; simp
  | storeMap f k val =>
    have hred : Lsc.Stmt.denote Γ env (.storeMap f k val) ctx w =
        .ok ((), { w with self :=
          (Γ.st.map1Upd f w.self
            (Function.update (Γ.st.map1 f w.self) (k.eval env) (val.eval env))) }) := rfl
    rw [hred] at hok; cases hok; simp
  | storeMap2 f k₁ k₂ val =>
    have hred : Lsc.Stmt.denote Γ env (.storeMap2 f k₁ k₂ val) ctx w =
        .ok ((), { w with self :=
          (Γ.st.map2Upd f w.self
            (Function.update (Γ.st.map2 f w.self) (k₁.eval env)
              (Function.update (Γ.st.map2 f w.self (k₁.eval env)) (k₂.eval env)
                (val.eval env)))) }) := rfl
    rw [hred] at hok; cases hok; simp
  | require c err args =>
    have hred : Lsc.Stmt.denote Γ env (.require c err args) ctx w =
        if c.denote env then .ok ((), w)
        else .error (.user (Γ.err.build err (args.map (·.eval env)))) := rfl
    rw [hred] at hok; split at hok <;> cases hok <;> simp
  | emit ev args =>
    have hred : Lsc.Stmt.denote Γ env (.emit ev args) ctx w =
        .ok ((), { w with log := w.log ++ [Γ.ev.build ev (args.map (·.eval env))] }) := rfl
    rw [hred] at hok; cases hok; simp
  | revert err args =>
    have hred : Lsc.Stmt.denote Γ env (.revert err args) ctx w =
        (.error (.user (Γ.err.build err (args.map (·.eval env)))) : Except _ (Unit × World S X E)) := rfl
    rw [hred] at hok; cases hok

theorem callFree_preserves_ghost {S X E ε} {Γ : ContractSchema S X E ε} {t}
    {core : Core t} (hM1 : CallFree core) (env : List Nat) (ctx : Ctx) (w : World S X E)
    {v : t.denote} {w' : World S X E}
    (hok : Core.denote Γ core env ctx w = .ok (v, w')) :
    w'.ext = w.ext ∧ w'.faults = w.faults ∧ w'.ncalls = w.ncalls := by
  revert hM1 env w v w' hok
  induction core with
  | ret r =>
    intro h env w v w' hok
    have hred : Core.denote Γ (.ret r) env ctx w = .ok (r.eval env, w) := rfl
    rw [hred] at hok; cases hok; simp
  | opTail op | opTailAddr op | opTailFlag op =>
    intro h env w v w' hok
    have hop : M1Op op := by simpa [CallFree, M1Frag] using h
    apply m1op_preserves_ghost (Γ := Γ) hop env ctx w
    exact hok
  | stmtTail s =>
    intro h env w v w' hok
    have hs : M1Stmt s := by simpa [CallFree, M1Frag] using h
    apply m1stmt_preserves_ghost (Γ := Γ) hs env ctx w
    exact hok
  | revertTail err args =>
    intro h env w v w' hok
    simp [Core.denote] at hok
    nomatch hok
  | letOp op k ih =>
    intro h env w v w' hok
    have ⟨hop, hk⟩ := m1frag_letOp.mp h
    simp [Core.denote] at hok
    change Tx.run (Lsc.Op.denote Γ env op >>= fun x => Core.denote Γ k (x :: env))
        ctx w = .ok (v, w') at hok
    rw [Tx.run_bind] at hok
    cases hopr : Tx.run (Lsc.Op.denote Γ env op) ctx w with
    | error _ => simp [hopr] at hok
    | ok p =>
      have hopg := m1op_preserves_ghost hop env ctx w (by simpa [Tx.run] using hopr)
      simp [hopr] at hok
      have ih' := ih hk (p.1 :: env) p.2 hok
      exact ⟨ih'.1.trans hopg.1, ih'.2.1.trans hopg.2.1, ih'.2.2.trans hopg.2.2⟩
  | seq s k ih =>
    intro h env w v w' hok
    have ⟨hs, hk⟩ := m1frag_seq.mp h
    simp [Core.denote] at hok
    change Tx.run (Lsc.Stmt.denote Γ env s >>= fun _ => Core.denote Γ k env)
        ctx w = .ok (v, w') at hok
    rw [Tx.run_bind] at hok
    cases hsr : Tx.run (Lsc.Stmt.denote Γ env s) ctx w with
    | error _ => simp [hsr] at hok
    | ok p =>
      have hsg := m1stmt_preserves_ghost hs env ctx w (by simpa [Tx.run] using hsr)
      simp [hsr] at hok
      have ih' := ih hk env p.2 hok
      exact ⟨ih'.1.trans hsg.1, ih'.2.1.trans hsg.2.1, ih'.2.2.trans hsg.2.2⟩
  | letPure p args k ih =>
    intro h env w v w' hok
    have ⟨_, _, hk⟩ := m1frag_letPure.mp h
    simp [Core.denote] at hok
    exact ih hk _ w hok
  | ite c a b iha ihb =>
    intro h env w v w' hok
    have ⟨_, ha, hb⟩ := m1frag_ite.mp h
    simp [Core.denote] at hok
    by_cases hc : c.denote env
    · simp [hc] at hok; exact iha ha env w hok
    · simp [hc] at hok; exact ihb hb env w hok

theorem RX_callFree {I : Interface} {S X E} {α : Abs I.Ghost}
    {bind : Binding I S X} {w w' : World S X E} {st0 st' : EvmState}
    (hRX : RX α bind w st0)
    (hstab : α.ofState st' (bind.addr w.self) = α.ofState st0 (bind.addr w.self))
    (hext : w'.ext = w.ext)
    (haddr : bind.addr w'.self = bind.addr w.self) :
    RX α bind w' st' := by
  unfold RX at *
  rw [haddr, hstab, hext]
  exact hRX

/-! ## `toYulFn_correct_ext` (call-free) -/

theorem toYulFn_correct_ext {I : Interface} {S X E ε : Type}
    (α : Abs I.Ghost) (bind : Binding I S X)
    (c : ContractDef) (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (calls : ExternalCalls) (f : FnDef) (hf : f.kind ≠ .constructor)
    (hM1 : CallFree f.core) (hlen : c.fields.length < wordBound)
    (hbound : 4 + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : toYulFn c f = some yul)
    (ctx : Ctx) (w : World S X E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0)
    (hRX : RX α bind w st0) (_hign : α.ignoresLocal)
    (haddr : ∀ σ : S, bind.addr σ = bind.addr w.self)
    (hstab : ∀ st'', α.ofState st'' (bind.addr w.self) = α.ofState st0 (bind.addr w.self)) :
    ToYulFnCorrectExt α bind c Γ κ calls f yul ctx w st0 := by
  intro st' o hrun
  refine ⟨w.faults, ?_⟩
  have hwfo : { w with faults := w.faults } = w := rfl
  have hhoist_evm := toYulFn_hoist hyul hf
  have hhoist : hoist (yulD calls) yul = [] := hoist_yulD_of_evm hhoist_evm
  have hno : noExtBlock yul = true := noExt_toYulFn_callFree hM1 hyul hf
  obtain ⟨Vb, hbody, hV⟩ := run_block_inv hrun
  rw [hhoist] at hbody
  have hdesc : ExecStmts evm [[]] [] st0 yul Vb st' o := by
    have h := execStmts_descend (calls := calls) noExtFuns_nilScope hno hbody
    rw [funEnvUncast_nilScope] at h
    exact h
  have hsim := toYulFn_execStmts_callFree (c := c) (Γ := Γ) hΓ κ hκ f hf hM1 hlen
    hbound yul hyul ctx w st0 hctx hR [[]]
  set args := decodeArgs f st0.env.calldata
  have hargs : args = decodeArgs f st0.env.calldata := rfl
  simp only [hwfo, ← hargs] at hsim ⊢
  cases hTx : Tx.run (Core.denote Γ f.core args.reverse) ctx w with
  | ok p =>
    simp only [hTx, except_ok_prod] at hsim ⊢
    obtain ⟨V1, st1, hexec, hsucc, hR'⟩ := hsim
    obtain ⟨_, hst, ho⟩ := execStmts_det_evm hdesc hexec
    subst hst; subst ho
    rcases p with ⟨v, w'⟩
    have hg := callFree_preserves_ghost (Γ := Γ) hM1 args.reverse ctx w (by
      simpa [Tx.run] using hTx)
    obtain ⟨k, bs, hh, hk⟩ := haltSuccess_commits hsucc
    rw [committedState_commit hh hk]
    refine ⟨rfl, hsucc, hR', RX_callFree hRX (hstab st') hg.1 (haddr w'.self)⟩
  | error err =>
    simp only [hTx, except_error_prod] at hsim ⊢
    obtain ⟨V1, st1, bytes, hexec, hh, herr⟩ := hsim
    obtain ⟨_, hst, ho⟩ := execStmts_det_evm hdesc hexec
    subst hst; subst ho
    refine ⟨bytes, rfl, ?_, herr, R_rollback_obs hR hh HaltKind.revert_commits⟩
    simp [committedState_rollback hh HaltKind.revert_commits, hh]

end Lsc.Compiler
