import Lsc.Compiler.Proof.CoreExt
import Lsc.Compiler.Proof.CallBwd
import Lsc.Lang.CoreProof

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

/-!
S2 backward helpers for `core_sim_ext`.

Do **not** prove `Tx.run` equality on `{w with faults := f1}` vs `f2` as `World`
equality (`faults` is a field). M1/`CallFree` use `mapWorldFaults`. Call lemmas
quantify `∀ g, g w.ncalls = bit`. Resume: `stepOp_ok_ofState` →
`execStmts_normal_ofState` → `core_sim_ext` (`letOp`/`seq` `.call` via
`op_sim_call_bwd` + `composeFault`).
-/

namespace Lsc.Compiler

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

/-! ## `ofState` across local Yul steps (`hstab` elimination) -/

theorem ofState_of_CallWorld {G} (α : Abs G) {st st' : EvmState} {a : Address}
    (h : CallWorld.ofState st' = CallWorld.ofState st) :
    α.ofState st' a = α.ofState st a :=
  (α.ofState_proj st' a).trans ((congrArg (α.ofWorld · a) h).trans (α.ofState_proj st a).symm)

theorem ofState_halt {G} (α : Abs G) (st : EvmState) (h : Option (HaltKind × List UInt8))
    (a : Address) :
    α.ofState { st with halted := h } a = α.ofState st a := by
  apply ofState_of_CallWorld
  simp [CallWorld.ofState]

/-- Local `sstore` does not change a foreign ghost (`Abs.ignoresLocal` allows
`storageOf` at the executing address to move). -/
theorem ofState_of_sstore {G} {α : Abs G} (hign : α.ignoresLocal)
    (st : EvmState) (slot val : U256) (a : Address) :
    α.ofState
      { st with
        storage := upd st.storage slot val
        env := { st.env with
          storageOf := updAccount st.env.storageOf st.env.address slot val } } a =
      α.ofState st a := by
  refine hign st (upd st.storage slot val) st.transient
    (updAccount st.env.storageOf st.env.address slot val) st.env.transientOf a ?_ ?_
  · intro addr k hne
    simp [updAccount, hne]
  · intros; rfl

/-- Binding address is the scalar at `slot`. Other-field stores (Lawful) leave it
unchanged; read through `R`/`storageRel`, not `∀ σ, bind.addr σ = bind.addr w.self`. -/
theorem bind_addr_store {I : Interface} {S X E ε}
    {Γ : ContractSchema S X E ε} {c : ContractDef} {bind : Binding I S X}
    (hΓ : Γ.st.Lawful c.fields) {slot f : Nat}
    (haddr : ∀ σ, Γ.st.scalar slot σ = bind.addr σ)
    (hkind : (c.fields[f]?).map (·.kind) = some FieldKind.scalar)
    (hne : slot ≠ f) (σ : S) (v : Nat) :
    bind.addr (Γ.st.scalarUpd f σ v) = bind.addr σ := by
  rw [← haddr, ← haddr, hΓ.scalar_scalar slot f σ v hkind, if_neg hne]

/-! ## Fault-irrelevance of M1 ops (worlds differ only in `faults`) -/

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

theorem ofState_appendLog {G} (α : Abs G) (st : EvmState)
    (topics : List U256) (p n : U256) (a : Address) :
    α.ofState (appendLog st topics p n) a = α.ofState st a := by
  apply ofState_of_CallWorld
  simp [CallWorld.ofState, appendLog, touchMemory]

/-! ## Fault-irrelevance of `R` / `Inv` / `RX` -/

theorem R_faults {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ} {w : World S X E} {st : EvmState} (g : Nat → Bool) :
    R c Γ κ { w with faults := g } st ↔ R c Γ κ w st := by
  constructor <;> intro ⟨hs, hl, hk, hwf⟩ <;> exact ⟨hs, hl, hk, hwf⟩

theorem Inv_faults {S X E ε} {Γ : ContractSchema S X E ε} {c : ContractDef}
    {κ ctx} {w : World S X E} {env V st} (g : Nat → Bool) :
    Inv Γ c κ ctx { w with faults := g } env V st ↔ Inv Γ c κ ctx w env V st := by
  constructor
  · intro h; exact ⟨h.venv, h.wf, (R_faults g).mp h.rel, h.ctxr⟩
  · intro h; exact ⟨h.venv, h.wf, (R_faults g).mpr h.rel, h.ctxr⟩

theorem RX_faults {I : Interface} {S X E} {α : Abs I.Ghost} {bind : Binding I S X}
    {w : World S X E} {st : EvmState} (g : Nat → Bool) :
    RX α bind { w with faults := g } st ↔ RX α bind w st :=
  Iff.rfl

/-! ## Binding address is not stored (`haddr` elimination) -/

def stmtAvoids (slot : Nat) : Lsc.Stmt → Prop
  | .store f _ => f ≠ slot
  | _ => True

def coreAvoids (slot : Nat) : {t : RetTy} → Core t → Prop
  | _, .seq s k => stmtAvoids slot s ∧ coreAvoids slot k
  | _, .stmtTail s => stmtAvoids slot s
  | _, .letOp _ k => coreAvoids slot k
  | _, .letPure _ _ k => coreAvoids slot k
  | _, .ite _ a b => coreAvoids slot a ∧ coreAvoids slot b
  | _, _ => True

theorem m1stmt_preserves_addr {I : Interface} {S X E ε}
    {Γ : ContractSchema S X E ε} {c : ContractDef} {bind : Binding I S X}
    {slot : Nat} (hΓ : Γ.st.Lawful c.fields)
    (haddr : ∀ σ, Γ.st.scalar slot σ = bind.addr σ)
    (hkind : (c.fields[slot]?).map (·.kind) = some FieldKind.scalar)
    {s : Lsc.Stmt} (hM1 : M1Stmt s) (hwf : stmtWF c s = true)
    (hav : stmtAvoids slot s)
    (env : List Nat) (ctx : Ctx) (w : World S X E)
    {w' : World S X E}
    (hok : Lsc.Stmt.denote Γ env s ctx w = .ok ((), w')) :
    bind.addr w'.self = bind.addr w.self := by
  match s with
  | .store f v =>
    simp [Lsc.Stmt.denote, Tx.run_store] at hok
    cases hok
    have hfkind : (c.fields[f]?).map (·.kind) = some FieldKind.scalar := by
      have hpair : fieldKindOK c f FieldKind.scalar = true ∧ atomWF v = true := by
        simpa [stmtWF, Bool.and_eq_true] using hwf
      have ⟨fd, hfd, hk⟩ := (fieldKindOK_iff c f FieldKind.scalar).mp hpair.1
      simp [hfd, hk]
    exact bind_addr_store (bind := bind) hΓ haddr hfkind (Ne.symm hav) w.self (v.eval env)
  | .storeMap f k v =>
    simp [Lsc.Stmt.denote, Tx.run_storeMap] at hok
    cases hok
    have hfkind : (c.fields[f]?).map (·.kind) = some FieldKind.map1 := by
      have hpair :
          (fieldKindOK c f FieldKind.map1 = true ∧ atomWF k = true) ∧ atomWF v = true := by
        simpa [stmtWF, Bool.and_eq_true] using hwf
      have ⟨fd, hfd, hk⟩ := (fieldKindOK_iff c f FieldKind.map1).mp hpair.1.1
      simp [hfd, hk]
    rw [← haddr, ← haddr, hΓ.map1_scalar slot f w.self _ hfkind]
  | .storeMap2 f k₁ k₂ v =>
    simp [Lsc.Stmt.denote, Tx.run_storeMap2] at hok
    cases hok
    have hfkind : (c.fields[f]?).map (·.kind) = some FieldKind.map2 := by
      have hpair :
          ((fieldKindOK c f FieldKind.map2 = true ∧ atomWF k₁ = true) ∧ atomWF k₂ = true) ∧
            atomWF v = true := by
        simpa [stmtWF, Bool.and_eq_true] using hwf
      have ⟨fd, hfd, hk⟩ := (fieldKindOK_iff c f FieldKind.map2).mp hpair.1.1.1
      simp [hfd, hk]
    rw [← haddr, ← haddr, hΓ.map2_scalar slot f w.self _ hfkind]
  | .emit ev args =>
    have hred : Lsc.Stmt.denote Γ env (.emit ev args) ctx w =
        .ok ((), { w with log := w.log ++ [Γ.ev.build ev (args.map (·.eval env))] }) := rfl
    rw [hred] at hok; cases hok; rfl
  | .require cnd err args =>
    simp [Lsc.Stmt.denote, Tx.require] at hok
    split_ifs at hok <;> cases hok; rfl
  | .revert _ _ =>
    simp [Lsc.Stmt.denote, Tx.revert] at hok
  | .call .. => exact (show False from hM1).elim

/-! ## `CallFree` Core ignores the oracle except copying `faults` through -/

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

/-! ## `ofState` for local `stepOp` success (hstab) -/

theorem ofState_of_tstore {G} {α : Abs G} (hign : α.ignoresLocal)
    (st : EvmState) (slot val : U256) (a : Address) :
    α.ofState
      { st with
        transient := upd st.transient slot val
        env := { st.env with
          transientOf := updAccount st.env.transientOf st.env.address slot val } } a =
      α.ofState st a := by
  refine hign st st.storage (upd st.transient slot val)
    st.env.storageOf (updAccount st.env.transientOf st.env.address slot val) a ?_ ?_
  · intros; rfl
  · intro addr k hne
    simp [updAccount, hne]

theorem ofState_touchMemory {G} (α : Abs G) (st : EvmState) (p n : Nat) (a : Address) :
    α.ofState (touchMemory st p n) a = α.ofState st a :=
  ofState_of_CallWorld α (CallWorld.ofState_touch st p n)

/- Oracle that agrees with `fo` from the current `ncalls` onward. -/

def oracleAgrees (n : Nat) (fo g : Nat → Bool) : Prop :=
  ∀ k, n ≤ k → g k = fo k

theorem oracleAgrees_at {n fo g} (h : oracleAgrees n fo g) : g n = fo n :=
  h n (Nat.le_refl _)

theorem oracleAgrees_compose_false {n fo' g}
    (h : oracleAgrees n (composeFault n false fo') g) :
    g n = false ∧ oracleAgrees (n + 1) fo' g := by
  refine ⟨?_, ?_⟩
  · simpa [composeFault] using h n (Nat.le_refl _)
  · intro k hk
    have hne : k ≠ n := Nat.ne_of_gt (Nat.lt_of_succ_le hk)
    have := h k (Nat.le_trans (Nat.le_succ _) hk)
    simpa [composeFault, hne] using this

theorem oracleAgrees_compose_true {n rest g}
    (h : oracleAgrees n (composeFault n true rest) g) : g n = true := by
  simpa [composeFault] using h n (Nat.le_refl _)

/-! ## Binding address across `CallFree` success (`haddr` elimination) -/

theorem callFree_preserves_addr {I : Interface} {S X E ε}
    {Γ : ContractSchema S X E ε} {c : ContractDef} {bind : Binding I S X}
    {slot : Nat} (hΓ : Γ.st.Lawful c.fields)
    (haddr : ∀ σ, Γ.st.scalar slot σ = bind.addr σ)
    (hkind : (c.fields[slot]?).map (·.kind) = some FieldKind.scalar)
    {t} {core : Core t} (hM1 : CallFree core) (hwf : coreWF c core = true)
    (hav : coreAvoids slot core)
    (env : List Nat) (ctx : Ctx) (w : World S X E)
    {v : t.denote} {w' : World S X E}
    (hok : Core.denote Γ core env ctx w = .ok (v, w')) :
    bind.addr w'.self = bind.addr w.self := by
  revert hM1 hwf hav env w v w' hok
  induction core with
  | ret r =>
    intro h hwf hav env w v w' hok
    have hred : Core.denote Γ (.ret r) env ctx w = .ok (r.eval env, w) := rfl
    rw [hred] at hok; cases hok; rfl
  | opTail op | opTailAddr op | opTailFlag op =>
    intro h hwf hav env w v w' hok
    have hop : M1Op op := by simpa [CallFree, M1Frag] using h
    simp only [Core.denote] at hok
    have hw := m1op_world (Γ := Γ) hop env ctx w hok
    rw [hw]
  | stmtTail s =>
    intro h hwf hav env w v w' hok
    have hs : M1Stmt s := by simpa [CallFree, M1Frag] using h
    have hswf : stmtWF c s = true := by simpa [coreWF] using hwf
    simp only [Core.denote, RetTy.denote] at hok
    exact m1stmt_preserves_addr (bind := bind) hΓ haddr hkind hs hswf hav env ctx w hok
  | revertTail _ _ =>
    intro h hwf hav env w v w' hok
    simp [Core.denote] at hok
    nomatch hok
  | letOp op k ih =>
    intro h hwf hav env w v w' hok
    have ⟨hop, hk⟩ := m1frag_letOp.mp h
    have ⟨hopWF, hkWF⟩ := coreWF_letOp.mp hwf
    simp [Core.denote] at hok
    change Tx.run (Lsc.Op.denote Γ env op >>= fun x => Core.denote Γ k (x :: env))
        ctx w = .ok (v, w') at hok
    rw [Tx.run_bind] at hok
    cases hopr : Tx.run (Lsc.Op.denote Γ env op) ctx w with
    | error _ => simp [hopr] at hok
    | ok p =>
      have hw := m1op_world (Γ := Γ) hop env ctx w (by simpa [Tx.run] using hopr)
      simp [hopr] at hok
      have := ih hk hkWF hav (p.1 :: env) p.2 hok
      rw [this, hw]
  | seq s k ih =>
    intro h hwf hav env w v w' hok
    have ⟨hs, hk⟩ := m1frag_seq.mp h
    have ⟨hsWF, hkWF⟩ := coreWF_seq.mp hwf
    have ⟨havs, havk⟩ := hav
    simp [Core.denote] at hok
    change Tx.run (Lsc.Stmt.denote Γ env s >>= fun _ => Core.denote Γ k env)
        ctx w = .ok (v, w') at hok
    rw [Tx.run_bind] at hok
    cases hsr : Tx.run (Lsc.Stmt.denote Γ env s) ctx w with
    | error _ => simp [hsr] at hok
    | ok p =>
      have ha := m1stmt_preserves_addr (bind := bind) hΓ haddr hkind hs hsWF havs env ctx w
        (by simpa [Tx.run] using hsr)
      simp [hsr] at hok
      have := ih hk hkWF havk env p.2 hok
      exact this.trans ha
  | letPure p args k ih =>
    intro h hwf hav env w v w' hok
    have ⟨hp, hlen, hk⟩ := m1frag_letPure.mp h
    subst hp
    have hkWF : coreWF c k = true := by
      have hpair : (∀ x ∈ args, atomWF x = true) ∧ coreWF c k = true := by
        simpa [coreWF, Bool.and_eq_true] using hwf
      exact hpair.2
    simp [Core.denote] at hok
    exact ih hk hkWF hav (Prim.eval .id (args.map (·.eval env)) :: env) w hok
  | ite cnd a b iha ihb =>
    intro h hwf hav env w v w' hok
    have ⟨_, ha, hb⟩ := m1frag_ite.mp h
    have ⟨hava, havb⟩ := hav
    have hwf' := hwf
    simp [coreWF, Bool.and_eq_true] at hwf'
    simp [Core.denote] at hok
    split_ifs at hok
    · exact iha ha hwf'.1.2 hava env w hok
    · exact ihb hb hwf'.2 havb env w hok

end Lsc.Compiler
