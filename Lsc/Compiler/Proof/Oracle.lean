import Lsc.Compiler.Proof.CoreExt
import Lsc.Lang.CoreTheorems

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

/-!
Fault oracle agreement and M1/`CallFree` independence from `faults`.
-/

namespace Lsc.Compiler

variable (tag : String)

open YulSemantics
open YulSemantics.EVM
open Lsc hiding Op Stmt

/-- Copy `faults := fo` through a `Tx.run` result. Shared so M1 and `CallFree`
lemmas do not each generate a distinct `match` auxiliary (`Nat` vs
`RetTy.word.denote` then fail `exact`). -/
def mapWorldFaults {S X E ε α} (fo : Nat → Bool) :
    Except (Err ε) (α × World S X E) → Except (Err ε) (α × World S X E)
  | .ok (v, w') => .ok (v, { w' with faults := fo })
  | .error e => .error e

/-! ## Observational fault independence (M1) -/

theorem m1op_world {S X E ε} {Γ : ContractSchema S X E ε}
    {op : Lsc.Op} (h : M1Op op) (env : List Nat) (ctx : Ctx) (w : World S X E)
    {v : Nat} {w' : World S X E}
    (hok : Lsc.Op.denote Γ env op ctx w = .ok (v, w')) : w' = w := by
  cases op with
  | call _ _ _ => exact (show False from h).elim
  | load f =>
    have hred : Lsc.Op.denote Γ env (.load f) ctx w =
        .ok (Γ.st.scalar f w.self, w) := rfl
    rw [hred] at hok; cases hok; rfl
  | loadMap f k =>
    have hred : Lsc.Op.denote Γ env (.loadMap f k) ctx w =
        .ok (Γ.st.map1 f w.self (k.eval env), w) := rfl
    rw [hred] at hok; cases hok; rfl
  | loadMap2 f k₁ k₂ =>
    have hred : Lsc.Op.denote Γ env (.loadMap2 f k₁ k₂) ctx w =
        .ok (Γ.st.map2 f w.self (k₁.eval env) (k₂.eval env), w) := rfl
    rw [hred] at hok; cases hok; rfl
  | sender =>
    have hred : Lsc.Op.denote (Γ := Γ) env .sender ctx w = .ok (ctx.sender, w) := rfl
    rw [hred] at hok; cases hok; rfl
  | value =>
    have hred : Lsc.Op.denote (Γ := Γ) env .value ctx w = .ok (ctx.value, w) := rfl
    rw [hred] at hok; cases hok; rfl
  | timestamp =>
    have hred : Lsc.Op.denote (Γ := Γ) env .timestamp ctx w = .ok (ctx.timestamp, w) := rfl
    rw [hred] at hok; cases hok; rfl
  | blockNumber =>
    have hred : Lsc.Op.denote (Γ := Γ) env .blockNumber ctx w = .ok (ctx.blockNumber, w) := rfl
    rw [hred] at hok; cases hok; rfl
  | selfAddress =>
    have hred : Lsc.Op.denote (Γ := Γ) env .selfAddress ctx w = .ok (ctx.self, w) := rfl
    rw [hred] at hok; cases hok; rfl
  | addChecked a b =>
    have hred : Lsc.Op.denote Γ env (.addChecked a b) ctx w =
        if a.eval env + b.eval env < wordBound then .ok (a.eval env + b.eval env, w)
        else .error (.arith .overflow) := rfl
    rw [hred] at hok; split at hok <;> cases hok; rfl
  | subChecked a b =>
    have hred : Lsc.Op.denote Γ env (.subChecked a b) ctx w =
        if b.eval env ≤ a.eval env then .ok (a.eval env - b.eval env, w)
        else .error (.arith .underflow) := rfl
    rw [hred] at hok; split at hok <;> cases hok; rfl
  | mulChecked a b =>
    have hred : Lsc.Op.denote Γ env (.mulChecked a b) ctx w =
        if a.eval env * b.eval env < wordBound then .ok (a.eval env * b.eval env, w)
        else .error (.arith .overflow) := rfl
    rw [hred] at hok; split at hok <;> cases hok; rfl
  | divChecked a b =>
    have hred : Lsc.Op.denote Γ env (.divChecked a b) ctx w =
        if b.eval env ≠ 0 then .ok (a.eval env / b.eval env, w)
        else .error (.arith .divByZero) := rfl
    rw [hred] at hok; split at hok <;> cases hok; rfl
  | mulDivDown a b c =>
    have hred : Lsc.Op.denote Γ env (.mulDivDown a b c) ctx w =
        if c.eval env = 0 then .error (.arith .divByZero)
        else if a.eval env * b.eval env < wordBound then
          .ok (a.eval env * b.eval env / c.eval env, w)
        else .error (.arith .overflow) := rfl
    rw [hred] at hok
    split_ifs at hok <;> try cases hok
    all_goals rfl
  | mulDivUp a b c =>
    have hred : Lsc.Op.denote Γ env (.mulDivUp a b c) ctx w =
        if c.eval env = 0 then .error (.arith .divByZero)
        else if a.eval env * b.eval env < wordBound then
          .ok (a.eval env * b.eval env / c.eval env +
            if a.eval env * b.eval env % c.eval env = 0 then 0 else 1, w)
        else .error (.arith .overflow) := rfl
    rw [hred] at hok
    split_ifs at hok <;> try cases hok
    all_goals rfl
  | pure a =>
    have hred : Lsc.Op.denote Γ env (.pure a) ctx w = .ok (a.eval env, w) := rfl
    rw [hred] at hok; cases hok; rfl

/-! ## Prefix identification (S1 forward + descend + det) -/

theorem m1op_run_faults {S X E ε} {Γ : ContractSchema S X E ε}
    {op : Lsc.Op} (h : M1Op op) (env : List Nat) (ctx : Ctx) (w : World S X E)
    (fo : Nat → Bool) :
    Tx.run (Lsc.Op.denote Γ env op) ctx { w with faults := fo } =
      mapWorldFaults (ε := ε) fo (Tx.run (Lsc.Op.denote Γ env op) ctx w) := by
  simp only [mapWorldFaults]
  cases op with
  | call _ _ _ => exact (show False from h).elim
  | load f =>
    have h1 : Tx.run (Lsc.Op.denote Γ env (.load f)) ctx { w with faults := fo } =
        .ok (Γ.st.scalar f w.self, { w with faults := fo }) := rfl
    have h2 : Tx.run (Lsc.Op.denote Γ env (.load f)) ctx w =
        .ok (Γ.st.scalar f w.self, w) := rfl
    simp [h1, h2]
  | loadMap f k =>
    have h1 : Tx.run (Lsc.Op.denote Γ env (.loadMap f k)) ctx { w with faults := fo } =
        .ok (Γ.st.map1 f w.self (k.eval env), { w with faults := fo }) := rfl
    have h2 : Tx.run (Lsc.Op.denote Γ env (.loadMap f k)) ctx w =
        .ok (Γ.st.map1 f w.self (k.eval env), w) := rfl
    simp [h1, h2]
  | loadMap2 f k₁ k₂ =>
    have h1 : Tx.run (Lsc.Op.denote Γ env (.loadMap2 f k₁ k₂)) ctx { w with faults := fo } =
        .ok (Γ.st.map2 f w.self (k₁.eval env) (k₂.eval env), { w with faults := fo }) := rfl
    have h2 : Tx.run (Lsc.Op.denote Γ env (.loadMap2 f k₁ k₂)) ctx w =
        .ok (Γ.st.map2 f w.self (k₁.eval env) (k₂.eval env), w) := rfl
    simp [h1, h2]
  | sender =>
    have h1 : Tx.run (Lsc.Op.denote (Γ := Γ) env .sender) ctx { w with faults := fo } =
        .ok (ctx.sender, { w with faults := fo }) := rfl
    have h2 : Tx.run (Lsc.Op.denote (Γ := Γ) env .sender) ctx w = .ok (ctx.sender, w) := rfl
    simp [h1, h2]
  | value =>
    have h1 : Tx.run (Lsc.Op.denote (Γ := Γ) env .value) ctx { w with faults := fo } =
        .ok (ctx.value, { w with faults := fo }) := rfl
    have h2 : Tx.run (Lsc.Op.denote (Γ := Γ) env .value) ctx w = .ok (ctx.value, w) := rfl
    simp [h1, h2]
  | timestamp =>
    have h1 : Tx.run (Lsc.Op.denote (Γ := Γ) env .timestamp) ctx { w with faults := fo } =
        .ok (ctx.timestamp, { w with faults := fo }) := rfl
    have h2 : Tx.run (Lsc.Op.denote (Γ := Γ) env .timestamp) ctx w = .ok (ctx.timestamp, w) := rfl
    simp [h1, h2]
  | blockNumber =>
    have h1 : Tx.run (Lsc.Op.denote (Γ := Γ) env .blockNumber) ctx { w with faults := fo } =
        .ok (ctx.blockNumber, { w with faults := fo }) := rfl
    have h2 : Tx.run (Lsc.Op.denote (Γ := Γ) env .blockNumber) ctx w = .ok (ctx.blockNumber, w) := rfl
    simp [h1, h2]
  | selfAddress =>
    have h1 : Tx.run (Lsc.Op.denote (Γ := Γ) env .selfAddress) ctx { w with faults := fo } =
        .ok (ctx.self, { w with faults := fo }) := rfl
    have h2 : Tx.run (Lsc.Op.denote (Γ := Γ) env .selfAddress) ctx w = .ok (ctx.self, w) := rfl
    simp [h1, h2]
  | pure a =>
    have h1 : Tx.run (Lsc.Op.denote Γ env (.pure a)) ctx { w with faults := fo } =
        .ok (a.eval env, { w with faults := fo }) := rfl
    have h2 : Tx.run (Lsc.Op.denote Γ env (.pure a)) ctx w = .ok (a.eval env, w) := rfl
    simp [h1, h2]
  | addChecked a b =>
    have h1 : Tx.run (Lsc.Op.denote Γ env (.addChecked a b)) ctx { w with faults := fo } =
        if a.eval env + b.eval env < wordBound then
          .ok (a.eval env + b.eval env, { w with faults := fo })
        else .error (.arith .overflow) := rfl
    have h2 : Tx.run (Lsc.Op.denote Γ env (.addChecked a b)) ctx w =
        if a.eval env + b.eval env < wordBound then
          .ok (a.eval env + b.eval env, w)
        else .error (.arith .overflow) := rfl
    simp [h1, h2]; split_ifs <;> rfl
  | subChecked a b =>
    have h1 : Tx.run (Lsc.Op.denote Γ env (.subChecked a b)) ctx { w with faults := fo } =
        if b.eval env ≤ a.eval env then
          .ok (a.eval env - b.eval env, { w with faults := fo })
        else .error (.arith .underflow) := rfl
    have h2 : Tx.run (Lsc.Op.denote Γ env (.subChecked a b)) ctx w =
        if b.eval env ≤ a.eval env then .ok (a.eval env - b.eval env, w)
        else .error (.arith .underflow) := rfl
    simp [h1, h2]; split_ifs <;> rfl
  | mulChecked a b =>
    have h1 : Tx.run (Lsc.Op.denote Γ env (.mulChecked a b)) ctx { w with faults := fo } =
        if a.eval env * b.eval env < wordBound then
          .ok (a.eval env * b.eval env, { w with faults := fo })
        else .error (.arith .overflow) := rfl
    have h2 : Tx.run (Lsc.Op.denote Γ env (.mulChecked a b)) ctx w =
        if a.eval env * b.eval env < wordBound then .ok (a.eval env * b.eval env, w)
        else .error (.arith .overflow) := rfl
    simp [h1, h2]; split_ifs <;> rfl
  | divChecked a b =>
    have h1 : Tx.run (Lsc.Op.denote Γ env (.divChecked a b)) ctx { w with faults := fo } =
        if b.eval env ≠ 0 then .ok (a.eval env / b.eval env, { w with faults := fo })
        else .error (.arith .divByZero) := rfl
    have h2 : Tx.run (Lsc.Op.denote Γ env (.divChecked a b)) ctx w =
        if b.eval env ≠ 0 then .ok (a.eval env / b.eval env, w)
        else .error (.arith .divByZero) := rfl
    simp [h1, h2]; split_ifs <;> rfl
  | mulDivDown a b c =>
    have h1 : Tx.run (Lsc.Op.denote Γ env (.mulDivDown a b c)) ctx { w with faults := fo } =
        if c.eval env = 0 then .error (.arith .divByZero)
        else if a.eval env * b.eval env < wordBound then
          .ok (a.eval env * b.eval env / c.eval env, { w with faults := fo })
        else .error (.arith .overflow) := rfl
    have h2 : Tx.run (Lsc.Op.denote Γ env (.mulDivDown a b c)) ctx w =
        if c.eval env = 0 then .error (.arith .divByZero)
        else if a.eval env * b.eval env < wordBound then
          .ok (a.eval env * b.eval env / c.eval env, w)
        else .error (.arith .overflow) := rfl
    simp [h1, h2]; split_ifs <;> rfl
  | mulDivUp a b c =>
    have h1 : Tx.run (Lsc.Op.denote Γ env (.mulDivUp a b c)) ctx { w with faults := fo } =
        if c.eval env = 0 then .error (.arith .divByZero)
        else if a.eval env * b.eval env < wordBound then
          .ok (a.eval env * b.eval env / c.eval env +
            if a.eval env * b.eval env % c.eval env = 0 then 0 else 1,
            { w with faults := fo })
        else .error (.arith .overflow) := rfl
    have h2 : Tx.run (Lsc.Op.denote Γ env (.mulDivUp a b c)) ctx w =
        if c.eval env = 0 then .error (.arith .divByZero)
        else if a.eval env * b.eval env < wordBound then
          .ok (a.eval env * b.eval env / c.eval env +
            if a.eval env * b.eval env % c.eval env = 0 then 0 else 1, w)
        else .error (.arith .overflow) := rfl
    simp [h1, h2]; split_ifs <;> rfl

theorem m1stmt_run_faults {S X E ε} {Γ : ContractSchema S X E ε}
    {s : Lsc.Stmt} (h : M1Stmt s) (env : List Nat) (ctx : Ctx) (w : World S X E)
    (fo : Nat → Bool) :
    Tx.run (Lsc.Stmt.denote Γ env s) ctx { w with faults := fo } =
      mapWorldFaults (ε := ε) fo (Tx.run (Lsc.Stmt.denote Γ env s) ctx w) := by
  simp only [mapWorldFaults]
  cases s with
  | call _ _ _ => exact (show False from h).elim
  | store _ _ => simp [Lsc.Stmt.denote, Tx.run_store]
  | storeMap _ _ _ => simp [Lsc.Stmt.denote, Tx.run_storeMap]
  | storeMap2 _ _ _ _ => simp [Lsc.Stmt.denote, Tx.run_storeMap2]
  | emit _ _ => simp [Lsc.Stmt.denote, Tx.run_emit]
  | require c err args =>
    simp [Lsc.Stmt.denote, Tx.run_require]; split_ifs <;> rfl
  | revert _ _ => simp [Lsc.Stmt.denote, Tx.run_revert]

/-! ## `CallWorld` of silent local builtins (`hstab` elimination) -/

theorem R_faults {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ} {w : World S X E} {st : EvmState} (g : Nat → Bool) :
    R c Γ κ { w with faults := g } st ↔ R c Γ κ w st := by
  constructor <;> intro ⟨hs, hl, hk, hwf⟩ <;> exact ⟨hs, hl, hk, hwf⟩

theorem Inv_faults {S X E ε} {Γ : ContractSchema S X E ε} {c : ContractDef}
    {κ ctx} {w : World S X E} {env V st} (g : Nat → Bool) :
    Inv tag Γ c κ ctx { w with faults := g } env V st ↔ Inv tag Γ c κ ctx w env V st := by
  constructor
  · intro h; exact ⟨h.venv, h.wf, (R_faults g).mp h.rel, h.ctxr⟩
  · intro h; exact ⟨h.venv, h.wf, (R_faults g).mpr h.rel, h.ctxr⟩

theorem RX_faults {I : Interface} {S X E} {α : Abs I.Ghost} {bind : Binding I S X}
    {w : World S X E} {st : EvmState} (g : Nat → Bool) :
    RX α bind { w with faults := g } st ↔ RX α bind w st :=
  Iff.rfl

theorem callFree_run_faults {S X E ε} {Γ : ContractSchema S X E ε} {t}
    {core : Core t} (hM1 : CallFree core) (env : List Nat) (ctx : Ctx) (w : World S X E)
    (fo : Nat → Bool) :
    Tx.run (Core.denote Γ core env) ctx { w with faults := fo } =
      mapWorldFaults (ε := ε) fo (Tx.run (Core.denote Γ core env) ctx w) := by
  revert hM1 env w
  induction core with
  | ret r =>
    intro h env w
    simp [Core.denote, Tx.run_pure, mapWorldFaults]
  | opTail op =>
    intro h env w
    have hop : M1Op op := by simpa [CallFree, M1Frag] using h
    simp only [Core.denote]
    exact m1op_run_faults (Γ := Γ) hop env ctx w fo
  | opTailAddr op =>
    intro h env w
    have hop : M1Op op := by simpa [CallFree, M1Frag] using h
    simp only [Core.denote, RetTy.denote, Address]
    exact m1op_run_faults (Γ := Γ) hop env ctx w fo
  | opTailFlag op =>
    intro h env w
    have hop : M1Op op := by simpa [CallFree, M1Frag] using h
    simp only [Core.denote, RetTy.denote, Flag]
    exact m1op_run_faults (Γ := Γ) hop env ctx w fo
  | stmtTail s =>
    intro h env w
    have hs : M1Stmt s := by simpa [CallFree, M1Frag] using h
    simp only [Core.denote, RetTy.denote]
    exact m1stmt_run_faults (Γ := Γ) hs env ctx w fo
  | revertTail err args =>
    intro h env w
    simp [Core.denote, Tx.run_revert, mapWorldFaults]
  | letOp op k ih =>
    intro h env w
    have ⟨hop, hk⟩ := m1frag_letOp.mp h
    simp [Core.denote, Tx.run_bind]
    rw [m1op_run_faults (Γ := Γ) hop env ctx w fo]
    cases hrun : Tx.run (Lsc.Op.denote Γ env op) ctx w with
    | error e => simp [mapWorldFaults]
    | ok p =>
      simp [mapWorldFaults]
      exact ih hk (p.1 :: env) p.2
  | seq s k ih =>
    intro h env w
    have ⟨hs, hk⟩ := m1frag_seq.mp h
    simp [Core.denote, Tx.run_bind]
    rw [m1stmt_run_faults (Γ := Γ) hs env ctx w fo]
    cases hrun : Tx.run (Lsc.Stmt.denote Γ env s) ctx w with
    | error e => simp [mapWorldFaults]
    | ok p =>
      simp [mapWorldFaults]
      exact ih hk env p.2
  | letPure p args k ih =>
    intro h env w
    have ⟨hp, hlen, hk⟩ := m1frag_letPure.mp h
    subst hp
    simp [Core.denote]
    exact ih hk (Prim.eval .id (args.map (·.eval env)) :: env) w
  | ite c a b iha ihb =>
    intro h env w
    have ⟨_, ha, hb⟩ := m1frag_ite.mp h
    simp [Core.denote]
    split_ifs
    · exact iha ha env w
    · exact ihb hb env w

/-- Oracle that agrees with `fo` from the current `ncalls` onward. -/
def oracleAgrees (n : Nat) (fo g : Nat → Bool) : Prop :=
  ∀ k, n ≤ k → g k = fo k

theorem oracleAgrees_compose_false {n fo' g}
    (h : oracleAgrees n (composeFault n false fo') g) :
    g n = false ∧ oracleAgrees (n + 1) fo' g := by
  refine ⟨?_, ?_⟩
  · simpa [composeFault] using h n (Nat.le_refl _)
  · intro k hk
    have hne : k ≠ n := Nat.ne_of_gt (Nat.lt_of_succ_le hk)
    have := h k (Nat.le_trans (Nat.le_succ _) hk)
    simpa [composeFault, hne] using this

end Lsc.Compiler
