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

/-! ## `α.ofState` across non-halting local `stepOp` / `ExecStmts` (`hstab`) -/

theorem ofState_touchMemory2 {G} (α : Abs G) (st : EvmState)
    (p1 n1 p2 n2 : Nat) (a : Address) :
    α.ofState (touchMemory2 st p1 n1 p2 n2) a = α.ofState st a := by
  apply ofState_of_CallWorld
  simp [CallWorld.ofState, touchMemory2, touchMemory]

theorem some_ok_state {xs ys : List U256} {s s' : EvmState}
    (h : some (BuiltinResult.ok xs s) = some (BuiltinResult.ok ys s')) :
    s' = s := by
  injection h with h'
  injection h' with _ hs
  exact hs.symm

theorem not_none_some {β} {x : β}
    (h : (none : Option β) = some x) : False := by
  cases h

theorem not_halt_ok {rets : List U256} {stH st' : EvmState}
    (h : BuiltinResult.halt stH = BuiltinResult.ok rets st') : False := by
  cases h

/-- Non-halting `stepOp` leaves `α.ofState` unchanged (`ignoresLocal` for `sstore`/`tstore`). -/
theorem stepOp_ok_ofState {G} {α : Abs G} (hign : α.ignoresLocal)
    {op : EVM.Op} {args : List U256} {st : EvmState} {rets : List U256} {st' : EvmState}
    (h : stepOp op args st = some (.ok rets st')) (a : Address) :
    α.ofState st' a = α.ofState st a := by
  cases op
  -- `all_goals (try t)` not `try all_goals t`: one failing goal must not roll back the rest.
  all_goals (try simp [stepOp, un, bin, ter, rd0, rd1, guardStatic] at h)
  all_goals (try split at h)
  all_goals (try split at h)
  all_goals (try exact (not_none_some h).elim)
  all_goals (try exact (not_halt_ok (Option.some.inj h)).elim)
  all_goals (try (have hst := some_ok_state h; subst hst))
  all_goals (try rfl)
  all_goals (try exact ofState_of_sstore hign st _ _ a)
  all_goals (try exact ofState_of_tstore hign st _ _ a)
  all_goals (try exact ofState_appendLog α st _ _ _ a)
  all_goals (try exact ofState_touchMemory α st _ _ a)
  all_goals (try apply ofState_of_CallWorld α)
  all_goals (try simp [CallWorld.ofState, touchMemory, touchMemory2, appendLog])

theorem some_halt_state {s s' : EvmState}
    (h : (some (BuiltinResult.halt s) : Option (BuiltinResult U256 EvmState)) =
          some (BuiltinResult.halt s')) :
    s' = s := by
  injection h with h'
  injection h' with hs
  exact hs.symm

theorem noExt_all_loop {c post body}
    (hc : noExtExpr c = true) (hp : noExtBlock post = true) (hb : noExtBlock body = true) :
    NoExternalOps (.loop c post body) := by
  simp [NoExternalOps, noExtCode, hc, hp, hb]

/-- Halting `stepOp` other than `selfdestruct` leaves `α.ofState` unchanged. -/
theorem stepOp_halt_ofState {G} {α : Abs G} (hign : α.ignoresLocal)
    {op : EVM.Op} {args : List U256} {st st' : EvmState}
    (h : stepOp op args st = some (.halt st')) (a : Address)
    (hnsd : op ≠ .selfdestruct) :
    α.ofState st' a = α.ofState st a := by
  cases op
  all_goals (try exact (hnsd rfl).elim)
  all_goals (try simp [stepOp, un, bin, ter, rd0, rd1, guardStatic] at h)
  all_goals (try split at h)
  all_goals (try split at h)
  all_goals (try exact (not_none_some h).elim)
  all_goals (try exact (not_halt_ok (Option.some.inj h).symm).elim)
  all_goals (try (have hst := some_halt_state h; subst hst))
  all_goals (try exact ofState_halt α st _ a)
  all_goals (try exact (ofState_halt α (touchMemory st _ _) _ a).trans (ofState_touchMemory α st _ _ a))


theorem step_ok_ofState {G} {α : Abs G} (hign : α.ignoresLocal)
    {funs : FunEnv evm} {V : VEnv evm} {st : EvmState} {code : Code evm.Op}
    {res : Res evm} (h : Step evm funs V st code res) (a : Address) :
    (∀ vs st', res = Res.eres (EResult.vals vs st') →
      α.ofState st' a = α.ofState st a) ∧
    (∀ V' st' o, res = Res.sres V' st' o → o ≠ Outcome.halt →
      α.ofState st' a = α.ofState st a) := by
  induction h generalizing a with
  | lit | var | argsNil =>
    constructor
    · intro vs st' heq; cases heq; rfl
    · intro V' st' o heq; cases heq
  | funDef | letZero | seqNil | «break» | «continue» | «leave» =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq _; cases heq; rfl
  | builtinOk hargs hbu ih =>
    constructor
    · intro vs st' heq
      injection heq with hr; injection hr with _ hst; subst hst
      exact (stepOp_ok_ofState hign hbu a).trans ((ih a).1 _ _ rfl)
    · intro _ _ _ heq; cases heq
  | builtinHalt | builtinArgsHalt | callHalt | callArgsHalt
  | argsRestHalt | argsHeadHalt =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq; cases heq
  | callOk hargs hlk hlen hbody ho ihArgs ihBody =>
    constructor
    · intro vs st' heq
      injection heq with hr; injection hr with _ hst; subst hst
      rcases ho with hn | hl
      · subst hn
        exact ((ihBody a).2 _ _ _ rfl (by intro hh; cases hh)).trans ((ihArgs a).1 _ _ rfl)
      · subst hl
        exact ((ihBody a).2 _ _ _ rfl (by intro hh; cases hh)).trans ((ihArgs a).1 _ _ rfl)
    · intro _ _ _ heq; cases heq
  | argsCons hrest hhead ihRest ihHead =>
    constructor
    · intro vs st' heq
      injection heq with hr; injection hr with _ hst; subst hst
      exact ((ihHead a).1 _ _ rfl).trans ((ihRest a).1 _ _ rfl)
    · intro _ _ _ heq; cases heq
  | block hbody ih =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq ho; cases heq; exact (ih a).2 _ _ _ rfl ho
  | letVal he _ ih | assignVal he _ ih | exprStmt he ih =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq _; cases heq; exact (ih a).1 _ _ rfl
  | letHalt | assignHalt | exprStmtHalt | ifHalt | switchHalt
  | forInitHalt | loopCondHalt | loopPostHalt | loopBodyHalt =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq ho; cases heq; exact (ho rfl).elim
  | ifTrue he _ hbody ihE ihB | switchExec he hbody ihE ihB =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq ho; cases heq
      exact ((ihB a).2 _ _ _ rfl ho).trans ((ihE a).1 _ _ rfl)
  | ifFalse he _ ih | loopDone he _ ih =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq _; cases heq; exact (ih a).1 _ _ rfl
  | forLoop hi hl ihI ihL =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq ho; cases heq
      exact ((ihL a).2 _ _ _ rfl ho).trans ((ihI a).2 _ _ _ rfl (by intro hh; cases hh))
  | seqCons hs hr ihs ihr =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq ho; cases heq
      exact ((ihr a).2 _ _ _ rfl ho).trans ((ihs a).2 _ _ _ rfl (by intro hh; cases hh))
  | seqStop hs _ ih =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq ho; cases heq; exact (ih a).2 _ _ _ rfl ho
  | loopStep he hne hbody hob hp hrest ihE ihB ihP ihR =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq ho; cases heq
      rcases hob with hn | hc
      · subst hn
        exact ((ihR a).2 _ _ _ rfl ho).trans
          (((ihP a).2 _ _ _ rfl (by intro hh; cases hh)).trans
            (((ihB a).2 _ _ _ rfl (by intro hh; cases hh)).trans ((ihE a).1 _ _ rfl)))
      · subst hc
        exact ((ihR a).2 _ _ _ rfl ho).trans
          (((ihP a).2 _ _ _ rfl (by intro hh; cases hh)).trans
            (((ihB a).2 _ _ _ rfl (by intro hh; cases hh)).trans ((ihE a).1 _ _ rfl)))
  | loopBreak he _ hbody ihE ihB | loopLeave he _ hbody ihE ihB =>
    constructor
    · intro vs st' heq; cases heq
    · intro V' st' o heq _; cases heq
      exact ((ihB a).2 _ _ _ rfl (by intro hh; cases hh)).trans ((ihE a).1 _ _ rfl)

theorem execStmts_normal_ofState {G} {α : Abs G} (hign : α.ignoresLocal)
    {funs : FunEnv evm} {V : VEnv evm} {st : EvmState} {ss : YBlock}
    {V' : VEnv evm} {st' : EvmState}
    (h : ExecStmts evm funs V st ss V' st' .normal) (a : Address) :
    α.ofState st' a = α.ofState st a :=
  (step_ok_ofState hign h a).2 V' st' .normal rfl (by intro hh; cases hh)

theorem execStmts_normal_ofState_open {I : Interface} {α : Abs I.Ghost}
    (hign : α.ignoresLocal)
    {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {ss : YBlock}
    {V' : VEnv (yulD calls)} {st' : EvmState}
    (hfuns : noExtFuns funs = true) (hno : noExtBlock ss = true)
    (h : ExecStmts (yulD calls) funs V st ss V' st' .normal) (a : Address) :
    α.ofState st' a = α.ofState st a :=
  execStmts_normal_ofState hign (execStmts_descend hfuns hno h) a

/-- `α.ofState` along any `noExt` `Step` (`selfdestruct` excluded by `noExtOp`).
`code`/`res` are variables so `induction` is legal (`ExecStmts` indexes `Code.stmts`). -/
theorem step_ofState {calls : ExternalCalls} {G} {α : Abs G} (hign : α.ignoresLocal)
    {funs : FunEnv (yulD calls)} {V : VEnv (yulD calls)} {st : EvmState}
    {code : Code YOp} {res : Res (yulD calls)}
    (h : Step (yulD calls) funs V st code res) (a : Address)
    (hfuns : noExtFuns funs = true) (hcode : NoExternalOps code) :
    (∀ vs st', res = Res.eres (EResult.vals vs st') →
      α.ofState st' a = α.ofState st a) ∧
    (∀ V' st' o, res = Res.sres V' st' o →
      α.ofState st' a = α.ofState st a) ∧
    (∀ st', res = Res.eres (EResult.halt st') →
      α.ofState st' a = α.ofState st a) := by
  revert hfuns hcode
  induction h generalizing a with
  | lit | var | argsNil =>
    intro _ _
    constructor
    · intro vs st' heq; cases heq; rfl
    constructor
    · intro V' st' o heq; cases heq
    · intro st' heq; cases heq
  | funDef | letZero | seqNil | «break» | «continue» | «leave» =>
    intro _ _
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro V' st' o heq; cases heq; rfl
    · intro st' heq; cases heq
  | builtinOk hargs hbu ih =>
    intro hfuns hcode
    have ⟨hop', hargs'⟩ := noExt_expr_builtin (noExt_code_expr hcode)
    have hstep := builtin_descend hop' hbu
    constructor
    · intro vs st' heq
      injection heq with hr; injection hr with _ hst; subst hst
      exact (stepOp_ok_ofState hign hstep a).trans
        ((ih a hfuns (noExt_all_args hargs')).1 _ _ rfl)
    constructor
    · intro _ _ _ heq; cases heq
    · intro _ heq; cases heq
  | builtinHalt hargs hbu ih =>
    intro hfuns hcode
    have ⟨hop', hargs'⟩ := noExt_expr_builtin (noExt_code_expr hcode)
    have hstep := builtin_descend hop' hbu
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro _ _ _ heq; cases heq
    · intro st' heq
      injection heq with hr; cases hr
      exact (stepOp_halt_ofState hign hstep a (by
          intro hopEq; subst hopEq; simp [noExtOp] at hop')).trans
        ((ih a hfuns (noExt_all_args hargs')).1 _ _ rfl)
  | builtinArgsHalt hargs ih =>
    intro hfuns hcode
    have ⟨_, hargs'⟩ := noExt_expr_builtin (noExt_code_expr hcode)
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro _ _ _ heq; cases heq
    · intro st' heq
      injection heq with hr; cases hr
      exact (ih a hfuns (noExt_all_args hargs')).2.2 _ rfl
  | callOk hargs hlu _hln hbody ho ihArgs ihBody =>
    intro hfuns hcode
    have hargs' := noExt_expr_call (noExt_code_expr hcode)
    obtain ⟨hbod, hcenv⟩ := lookupFun_noExt hfuns hlu
    constructor
    · intro vs st' heq
      injection heq with hr; injection hr with _ hst; subst hst
      rcases ho with hn | hl
      · subst hn
        exact ((ihBody a hcenv (noExt_all_block_stmt hbod)).2.1 _ _ _ rfl).trans
          ((ihArgs a hfuns (noExt_all_args hargs')).1 _ _ rfl)
      · subst hl
        exact ((ihBody a hcenv (noExt_all_block_stmt hbod)).2.1 _ _ _ rfl).trans
          ((ihArgs a hfuns (noExt_all_args hargs')).1 _ _ rfl)
    constructor
    · intro _ _ _ heq; cases heq
    · intro _ heq; cases heq
  | callHalt hargs hlu _hln hbody ihArgs ihBody =>
    intro hfuns hcode
    have hargs' := noExt_expr_call (noExt_code_expr hcode)
    obtain ⟨hbod, hcenv⟩ := lookupFun_noExt hfuns hlu
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro _ _ _ heq; cases heq
    · intro st' heq
      injection heq with hr; cases hr
      exact ((ihBody a hcenv (noExt_all_block_stmt hbod)).2.1 _ _ _ rfl).trans
        ((ihArgs a hfuns (noExt_all_args hargs')).1 _ _ rfl)
  | callArgsHalt hargs ih =>
    intro hfuns hcode
    have hargs' := noExt_expr_call (noExt_code_expr hcode)
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro _ _ _ heq; cases heq
    · intro st' heq
      injection heq with hr; cases hr
      exact (ih a hfuns (noExt_all_args hargs')).2.2 _ rfl
  | argsCons hrest hhead ihRest ihHead =>
    intro hfuns hcode
    have ⟨he', hrest'⟩ := noExt_args_cons (noExt_code_args hcode)
    constructor
    · intro vs st' heq
      injection heq with hr; injection hr with _ hst; subst hst
      exact ((ihHead a hfuns (noExt_all_expr he')).1 _ _ rfl).trans
        ((ihRest a hfuns (noExt_all_args hrest')).1 _ _ rfl)
    constructor
    · intro _ _ _ heq; cases heq
    · intro _ heq; cases heq
  | argsRestHalt hrest ih =>
    intro hfuns hcode
    have ⟨_, hrest'⟩ := noExt_args_cons (noExt_code_args hcode)
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro _ _ _ heq; cases heq
    · intro st' heq
      injection heq with hr; cases hr
      exact (ih a hfuns (noExt_all_args hrest')).2.2 _ rfl
  | argsHeadHalt hrest he ihRest ihHead =>
    intro hfuns hcode
    have ⟨he', hrest'⟩ := noExt_args_cons (noExt_code_args hcode)
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro _ _ _ heq; cases heq
    · intro st' heq
      injection heq with hr; cases hr
      exact ((ihHead a hfuns (noExt_all_expr he')).2.2 _ rfl).trans
        ((ihRest a hfuns (noExt_all_args hrest')).1 _ _ rfl)
  | block hbody ih =>
    intro hfuns hcode
    have hb := noExt_stmt_block (noExt_code_stmt hcode)
    have hf' := noExtFuns_hoist_cons hb hfuns
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro V' st' o heq; cases heq
      exact (ih a hf' (noExt_all_stmts hb)).2.1 _ _ _ rfl
    · intro st' heq; cases heq
  | letVal he _hlen ih =>
    intro hfuns hcode
    have he' := noExt_stmt_let (noExt_code_stmt hcode)
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro V' st' o heq; cases heq
      exact (ih a hfuns (noExt_all_expr he')).1 _ _ rfl
    · intro st' heq; cases heq
  | assignVal he _hlen ih =>
    intro hfuns hcode
    have he' := noExt_stmt_assign (noExt_code_stmt hcode)
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro V' st' o heq; cases heq
      exact (ih a hfuns (noExt_all_expr he')).1 _ _ rfl
    · intro st' heq; cases heq
  | exprStmt he ih =>
    intro hfuns hcode
    have he' := noExt_stmt_expr (noExt_code_stmt hcode)
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro V' st' o heq; cases heq
      exact (ih a hfuns (noExt_all_expr he')).1 _ _ rfl
    · intro st' heq; cases heq
  | letHalt he ih =>
    intro hfuns hcode
    have he' := noExt_stmt_let (noExt_code_stmt hcode)
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro V' st' o heq; cases heq
      exact (ih a hfuns (noExt_all_expr he')).2.2 _ rfl
    · intro st' heq; cases heq
  | assignHalt he ih =>
    intro hfuns hcode
    have he' := noExt_stmt_assign (noExt_code_stmt hcode)
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro V' st' o heq; cases heq
      exact (ih a hfuns (noExt_all_expr he')).2.2 _ rfl
    · intro st' heq; cases heq
  | exprStmtHalt he ih =>
    intro hfuns hcode
    have he' := noExt_stmt_expr (noExt_code_stmt hcode)
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro V' st' o heq; cases heq
      exact (ih a hfuns (noExt_all_expr he')).2.2 _ rfl
    · intro st' heq; cases heq
  | ifHalt he ih =>
    intro hfuns hcode
    have ⟨hc, _⟩ := noExt_stmt_cond (noExt_code_stmt hcode)
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro V' st' o heq; cases heq
      exact (ih a hfuns (noExt_all_expr hc)).2.2 _ rfl
    · intro st' heq; cases heq
  | switchHalt he ih =>
    intro hfuns hcode
    have ⟨hc, _, _⟩ := noExt_stmt_switch (noExt_code_stmt hcode)
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro V' st' o heq; cases heq
      exact (ih a hfuns (noExt_all_expr hc)).2.2 _ rfl
    · intro st' heq; cases heq
  | loopCondHalt he ih =>
    intro hfuns hcode
    have ⟨hc, _, _⟩ := noExt_code_loop hcode
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro V' st' o heq; cases heq
      exact (ih a hfuns (noExt_all_expr hc)).2.2 _ rfl
    · intro st' heq; cases heq
  | ifTrue he _hne hbody ihE ihB =>
    intro hfuns hcode
    have ⟨hc, hb⟩ := noExt_stmt_cond (noExt_code_stmt hcode)
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro V' st' o heq; cases heq
      exact ((ihB a hfuns (noExt_all_block_stmt hb)).2.1 _ _ _ rfl).trans
        ((ihE a hfuns (noExt_all_expr hc)).1 _ _ rfl)
    · intro st' heq; cases heq
  | switchExec he hbody ihE ihB =>
    intro hfuns hcode
    rename_i _funs _V _st cnd cases dflt cv _st1 _V2 _st2 _o
    have ⟨hc, hcases, hd⟩ := noExt_stmt_switch (noExt_code_stmt hcode)
    have hsel := noExt_selectSwitch (calls := calls) (cv := cv) cases dflt hcases hd
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro V' st' o heq; cases heq
      exact ((ihB a hfuns (noExt_all_block_stmt hsel)).2.1 _ _ _ rfl).trans
        ((ihE a hfuns (noExt_all_expr hc)).1 _ _ rfl)
    · intro st' heq; cases heq
  | ifFalse he _hz ih =>
    intro hfuns hcode
    have ⟨hc, _⟩ := noExt_stmt_cond (noExt_code_stmt hcode)
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro V' st' o heq; cases heq
      exact (ih a hfuns (noExt_all_expr hc)).1 _ _ rfl
    · intro st' heq; cases heq
  | loopDone he _hz ih =>
    intro hfuns hcode
    have ⟨hc, _, _⟩ := noExt_code_loop hcode
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro V' st' o heq; cases heq
      exact (ih a hfuns (noExt_all_expr hc)).1 _ _ rfl
    · intro st' heq; cases heq
  | forLoop hi hl ihI ihL =>
    intro hfuns hcode
    have ⟨hi', hc, hp, hb⟩ := noExt_stmt_for (noExt_code_stmt hcode)
    have hf' := noExtFuns_hoist_cons hi' hfuns
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro V' st' o heq; cases heq
      exact ((ihL a hf' (noExt_all_loop hc hp hb)).2.1 _ _ _ rfl).trans
        ((ihI a hf' (noExt_all_stmts hi')).2.1 _ _ _ rfl)
    · intro st' heq; cases heq
  | forInitHalt hi ih =>
    intro hfuns hcode
    have ⟨hi', _, _, _⟩ := noExt_stmt_for (noExt_code_stmt hcode)
    have hf' := noExtFuns_hoist_cons hi' hfuns
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro V' st' o heq; cases heq
      exact (ih a hf' (noExt_all_stmts hi')).2.1 _ _ _ rfl
    · intro st' heq; cases heq
  | seqCons hs hr ihs ihr =>
    intro hfuns hcode
    have ⟨hs', hr'⟩ := noExt_block_cons (noExt_code_stmts hcode)
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro V' st' o heq; cases heq
      exact ((ihr a hfuns (noExt_all_stmts hr')).2.1 _ _ _ rfl).trans
        ((ihs a hfuns (noExt_all_stmt hs')).2.1 _ _ _ rfl)
    · intro st' heq; cases heq
  | seqStop hs _hne ih =>
    intro hfuns hcode
    have ⟨hs', _⟩ := noExt_block_cons (noExt_code_stmts hcode)
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro V' st' o heq; cases heq
      exact (ih a hfuns (noExt_all_stmt hs')).2.1 _ _ _ rfl
    · intro st' heq; cases heq
  | loopStep he _hne hbody _ho hp hrest ihE ihB ihP ihR =>
    intro hfuns hcode
    have ⟨hc, hp', hb'⟩ := noExt_code_loop hcode
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro V' st' o heq; cases heq
      exact ((ihR a hfuns hcode).2.1 _ _ _ rfl).trans
        (((ihP a hfuns (noExt_all_block_stmt hp')).2.1 _ _ _ rfl).trans
          (((ihB a hfuns (noExt_all_block_stmt hb')).2.1 _ _ _ rfl).trans
            ((ihE a hfuns (noExt_all_expr hc)).1 _ _ rfl)))
    · intro st' heq; cases heq
  | loopPostHalt he _hne hbody _ho hp ihE ihB ihP =>
    intro hfuns hcode
    have ⟨hc, hp', hb'⟩ := noExt_code_loop hcode
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro V' st' o heq; cases heq
      exact ((ihP a hfuns (noExt_all_block_stmt hp')).2.1 _ _ _ rfl).trans
        (((ihB a hfuns (noExt_all_block_stmt hb')).2.1 _ _ _ rfl).trans
          ((ihE a hfuns (noExt_all_expr hc)).1 _ _ rfl))
    · intro st' heq; cases heq
  | loopBreak he _hne hbody ihE ihB | loopLeave he _hne hbody ihE ihB
  | loopBodyHalt he _hne hbody ihE ihB =>
    intro hfuns hcode
    have ⟨hc, _, hb'⟩ := noExt_code_loop hcode
    constructor
    · intro vs st' heq; cases heq
    constructor
    · intro V' st' o heq; cases heq
      exact ((ihB a hfuns (noExt_all_block_stmt hb')).2.1 _ _ _ rfl).trans
        ((ihE a hfuns (noExt_all_expr hc)).1 _ _ rfl)
    · intro st' heq; cases heq

theorem ofState_noExt_halt {calls : ExternalCalls} {G} {α : Abs G}
    (hign : α.ignoresLocal)
    {funs : FunEnv (yulD calls)} {V : VEnv (yulD calls)} {st : EvmState} {ss : YBlock}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hfuns : noExtFuns funs = true) (hno : noExtBlock ss = true)
    (h : ExecStmts (yulD calls) funs V st ss V' st' o) (a : Address) :
    α.ofState st' a = α.ofState st a :=
  (step_ofState (calls := calls) hign h a hfuns (noExt_all_stmts hno)).2.1 V' st' o rfl

theorem callFree_addr_of_exists {I : Interface} {S X E ε}
    {Γ : ContractSchema S X E ε} {c : ContractDef} {bind : Binding I S X}
    (hΓ : Γ.st.Lawful c.fields) {t} {core : Core t}
    (hM1 : CallFree core) (hwf : coreWF c core = true)
    (hslot : ∃ slot : Nat,
        (∀ σ, Γ.st.scalar slot σ = bind.addr σ) ∧
        (c.fields[slot]?).map (·.kind) = some FieldKind.scalar ∧
        coreAvoids slot core)
    (env : List Nat) (ctx : Ctx) (w : World S X E)
    {v : t.denote} {w' : World S X E}
    (hok : Core.denote Γ core env ctx w = .ok (v, w')) :
    bind.addr w'.self = bind.addr w.self := by
  obtain ⟨slot, hs, hk, hav⟩ := hslot
  exact callFree_preserves_addr (I := I) (bind := bind) hΓ hs hk hM1 hwf hav env ctx w hok

/-- Call-free backward simulation: S1 `core_sim` + descend + fault remapping. -/
theorem core_sim_ext_callFree {I : Interface} {S X E ε} (α : Abs I.Ghost)
    (bind : Binding I S X) {c Γ κ ctx haltUnit}
    (hhalt : haltUnit = true) (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound) (hign : α.ignoresLocal)
    {calls : ExternalCalls} {t} (core : Core t) (hM1 : CallFree core)
    (hslot : ∃ slot : Nat,
        (∀ σ, Γ.st.scalar slot σ = bind.addr σ) ∧
        (c.fields[slot]?).map (·.kind) = some FieldKind.scalar ∧
        coreAvoids slot core) :
    ∀ {w : World S X E} {env V st} (funs : FunEnv (yulD calls))
      (hfuns : noExtFuns funs = true) (hwf : coreWF c core = true)
      (hn : identsNodup (env.length + coreExtraDepth core) = true)
      (hinv : Inv Γ c κ ctx w env V st) (hRX : RX α bind w st)
      (hconf : Conforms I ctx.self (bind.addr w.self) calls α)
      (hBind : ∀ b m args, callWF c b m args = true → ∃ meth, BindWF c Γ bind b m meth)
      {e'} (hem : emitCore c {} env.length haltUnit core = some e')
      {V' st' o} (hexec : ExecStmts (yulD calls) funs V st e'.stmts V' st' o),
      ∃ fo, ∀ g, oracleAgrees w.ncalls fo g →
        match (Tx.run (Core.denote Γ core env) ctx { w with faults := g } :
            Except (Err ε) (t.denote × World S X E)) with
        | .ok (v, w') =>
            o = Outcome.halt ∧ haltSuccess t v st'.halted ∧
              R c Γ κ w' st' ∧ RX α bind w' st'
        | .error e =>
            ∃ bytes, o = Outcome.halt ∧ st'.halted = some (HaltKind.revert, bytes) ∧
              haltError c Γ e bytes := by
  intro w env V st funs hfuns hwf hn hinv hRX _hconf _hBind e' hem V' st' o hexec
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
    have haddr :=
      callFree_addr_of_exists (I := I) (bind := bind) hΓ hM1 hwf hslot env ctx w hok
    have hg := callFree_preserves_ghost (Γ := Γ) hM1 env ctx w hok
    rw [hTx] at hS1 hmap
    simp only [except_ok_prod, mapWorldFaults] at hS1 hmap ⊢
    rw [hmap]
    simp only [mapWorldFaults]
    obtain ⟨V1, st1, hexecS1, hsucc, hR⟩ := hS1
    obtain ⟨hVeq, hsteq, hoeq⟩ := execStmts_det_evm hdesc hexecS1
    subst hVeq; subst hsteq; subst hoeq
    refine ⟨rfl, hsucc, (R_faults g).mpr hR, ?_⟩
    exact RX_callFree (α := α) ((RX_faults g).mpr hRX)
      (ofState_noExt_halt hign hfuns hno hexec (bind.addr w.self)) hg.1 haddr
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
theorem core_sim_ext {I : Interface} {S X E ε} (α : Abs I.Ghost)
    (bind : Binding I S X) {c Γ κ ctx haltUnit}
    (hhalt : haltUnit = true) (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
    (hlen : c.fields.length < wordBound) (hign : α.ignoresLocal)
    {calls : ExternalCalls} {t} (core : Core t) (hS2 : S2Frag core)
    (hslot : ∃ slot : Nat,
        (∀ σ, Γ.st.scalar slot σ = bind.addr σ) ∧
        (c.fields[slot]?).map (·.kind) = some FieldKind.scalar ∧
        coreAvoids slot core) :
    ∀ {w : World S X E} {env V st} (funs : FunEnv (yulD calls))
      (hfuns : noExtFuns funs = true) (hwf : coreWF c core = true)
      (hn : identsNodup (env.length + coreExtraDepth core) = true)
      (hinv : Inv Γ c κ ctx w env V st) (hRX : RX α bind w st)
      (hconf : Conforms I ctx.self (bind.addr w.self) calls α)
      (hBind : ∀ b m args, callWF c b m args = true → ∃ meth, BindWF c Γ bind b m meth)
      {e'} (hem : emitCore c {} env.length haltUnit core = some e')
      {V' st' o} (hexec : ExecStmts (yulD calls) funs V st e'.stmts V' st' o),
      ∃ fo, ∀ g, oracleAgrees w.ncalls fo g →
        match (Tx.run (Core.denote Γ core env) ctx { w with faults := g } :
            Except (Err ε) (t.denote × World S X E)) with
        | .ok (v, w') =>
            o = Outcome.halt ∧ haltSuccess t v st'.halted ∧
              R c Γ κ w' st' ∧ RX α bind w' st'
        | .error e =>
            ∃ bytes, o = Outcome.halt ∧ st'.halted = some (HaltKind.revert, bytes) ∧
              haltError c Γ e bytes := by
  revert hS2 hslot
  induction core with
  | ret r =>
    intro hS2 hslot
    cases r with
    | pair _ _ => cases hS2
    | unit | word _ | addr _ | flag _ =>
      exact core_sim_ext_callFree (α := α) bind hhalt hΓ hκ hlen hign _
        (by simp [CallFree, M1Frag]) hslot
  | revertTail err args =>
    intro hS2 hslot
    exact core_sim_ext_callFree (α := α) bind hhalt hΓ hκ hlen hign _
      (by simpa [CallFree, M1Frag, S2Frag] using hS2) hslot
  | opTail op =>
    intro hS2 hslot w env V st funs hfuns hwf hn hinv hRX hconf hBind e' hem V' st' o hexec
    cases s2op_elim (by simpa [S2Frag] using hS2) with
    | inr hM1 =>
      exact core_sim_ext_callFree (α := α) bind hhalt hΓ hκ hlen hign (.opTail op)
        (by simpa [CallFree, M1Frag] using hM1) hslot
        funs hfuns hwf hn hinv hRX hconf hBind hem hexec
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
        obtain ⟨meth, hbd⟩ := hBind b m args hopWF
        have hn1 : identsNodup (env.length + 1) = true :=
          identsNodup_mono (by simp [coreExtraDepth]) hn
        cases execStmts_append_inv hexec with
        | inr hstop =>
          have hexec1 : ExecStmts (yulD calls) funs V st
              ((emitLetOp c {} env.length (.call b m args)).getD {}).stmts V' st' o := by
            simpa [hE] using hstop.2
          obtain ⟨bit, hfail, hok⟩ :=
            op_sim_call_bwd (α := α) hinv hbd hRX hconf hfuns hopWF hn1 hexec1
          cases bit with
          | false =>
            obtain ⟨_, _, _, _, _, hg⟩ := hok rfl
            obtain ⟨_, ho, _⟩ := hg (fun _ => false) rfl
            exact (hstop.1 ho).elim
          | true =>
            refine ⟨fun _ => true, ?_⟩
            intro g hg
            have gnc : g w.ncalls = true := by
              simpa using hg w.ncalls (Nat.le_refl _)
            have ⟨hrun, ho, hh⟩ := hfail rfl g gnc
            have htx :
                Tx.run (Core.denote Γ (.opTail (.call b m args)) env) ctx { w with faults := g } =
                  .error .callFailed := by
              simpa [Core.denote, RetTy.denote, Address] using hrun
            rw [htx]
            simp only [except_error_prod]
            exact ⟨[], ho, hh, rfl⟩
        | inl hokPre =>
          obtain ⟨V1, st1, hcallE, hrest⟩ := hokPre
          have hexec1 : ExecStmts (yulD calls) funs V st
              ((emitLetOp c {} env.length (.call b m args)).getD {}).stmts V1 st1 .normal := by
            simpa [hE] using hcallE
          obtain ⟨bit, hfail, hok⟩ :=
            op_sim_call_bwd (α := α) hinv hbd hRX hconf hfuns hopWF hn1 hexec1
          cases bit with
          | true =>
            have ⟨_, ho, _⟩ := hfail rfl (fun _ => true) rfl
            cases ho
          | false =>
            obtain ⟨v, w0, hself, _hlog, hncalls, hg⟩ := hok rfl
            let g0 : Nat → Bool := fun _ => false
            obtain ⟨_hrun0, _ho0, hVeq, hInv0, hRX0⟩ := hg g0 rfl
            have hn0 : identsNodup (v :: env).length = true := by simpa using hn1
            have he := eval_atom (funEnvUncast calls funs) (st := st1) hVeq hn0 (.var 0)
            have hv : v < wordBound := hInv0.wf v (by simp)
            obtain ⟨stR, hret, hh, hR'⟩ :=
              return_word_sim (funEnvUncast calls funs) V1 hv he hInv0.rel
            have hnoRet : noExtBlock (emitReturnWords {} [atomE (env.length + 1) (.var 0)]).stmts = true :=
              noExt_returnWords _ _ (by simp [Emit.stmts_nil]) (by
                intro x hx; simp at hx; subst hx; exact noExt_atomE _ _)
            have hdesc := execStmts_descend hfuns hnoRet hrest
            obtain ⟨hVeq', hsteq, hoeq⟩ := execStmts_det_evm hdesc hret
            subst hVeq'; subst hsteq; subst hoeq
            refine ⟨composeFault w.ncalls false (fun _ => false), ?_⟩
            intro g hgA
            have ⟨hgfalse, _⟩ := oracleAgrees_compose_false hgA
            obtain ⟨hrun, _ho, _hV, hInvg, hRXg⟩ := hg g hgfalse
            have htx :
                Tx.run (Core.denote Γ (.opTail (.call b m args)) env) ctx { w with faults := g } =
                  .ok (v, { w0 with faults := g }) := by
              simpa [Core.denote, RetTy.denote, Address] using hrun
            rw [htx]
            simp only [except_ok_prod]
            refine ⟨trivial, haltSuccess_word hh, (R_faults g).mpr hR', ?_⟩
            have hstab := ofState_noExt_halt (α := α) hign hfuns hnoRet hrest
              (bind.addr w0.self)
            have hRX' : RX α bind { w0 with faults := g } st' := by
              simpa [RX, hstab] using hRXg
            exact hRX'
  | opTailAddr op =>
    intro hS2 hslot w env V st funs hfuns hwf hn hinv hRX hconf hBind e' hem V' st' o hexec
    cases s2op_elim (by simpa [S2Frag] using hS2) with
    | inr hM1 =>
      exact core_sim_ext_callFree (α := α) bind hhalt hΓ hκ hlen hign (.opTailAddr op)
        (by simpa [CallFree, M1Frag] using hM1) hslot
        funs hfuns hwf hn hinv hRX hconf hBind hem hexec
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
        obtain ⟨meth, hbd⟩ := hBind b m args hopWF
        have hn1 : identsNodup (env.length + 1) = true :=
          identsNodup_mono (by simp [coreExtraDepth]) hn
        cases execStmts_append_inv hexec with
        | inr hstop =>
          have hexec1 : ExecStmts (yulD calls) funs V st
              ((emitLetOp c {} env.length (.call b m args)).getD {}).stmts V' st' o := by
            simpa [hE] using hstop.2
          obtain ⟨bit, hfail, hok⟩ :=
            op_sim_call_bwd (α := α) hinv hbd hRX hconf hfuns hopWF hn1 hexec1
          cases bit with
          | false =>
            obtain ⟨_, _, _, _, _, hg⟩ := hok rfl
            obtain ⟨_, ho, _⟩ := hg (fun _ => false) rfl
            exact (hstop.1 ho).elim
          | true =>
            refine ⟨fun _ => true, ?_⟩
            intro g hg
            have gnc : g w.ncalls = true := by
              simpa using hg w.ncalls (Nat.le_refl _)
            have ⟨hrun, ho, hh⟩ := hfail rfl g gnc
            have htx :
                Tx.run (Core.denote Γ (.opTailAddr (.call b m args)) env) ctx { w with faults := g } =
                  .error .callFailed := by
              simpa [Core.denote, RetTy.denote, Address] using hrun
            rw [htx]
            simp only [except_error_prod]
            exact ⟨[], ho, hh, rfl⟩
        | inl hokPre =>
          obtain ⟨V1, st1, hcallE, hrest⟩ := hokPre
          have hexec1 : ExecStmts (yulD calls) funs V st
              ((emitLetOp c {} env.length (.call b m args)).getD {}).stmts V1 st1 .normal := by
            simpa [hE] using hcallE
          obtain ⟨bit, hfail, hok⟩ :=
            op_sim_call_bwd (α := α) hinv hbd hRX hconf hfuns hopWF hn1 hexec1
          cases bit with
          | true =>
            have ⟨_, ho, _⟩ := hfail rfl (fun _ => true) rfl
            cases ho
          | false =>
            obtain ⟨v, w0, hself, _hlog, hncalls, hg⟩ := hok rfl
            let g0 : Nat → Bool := fun _ => false
            obtain ⟨_hrun0, _ho0, hVeq, hInv0, hRX0⟩ := hg g0 rfl
            have hn0 : identsNodup (v :: env).length = true := by simpa using hn1
            have he := eval_atom (funEnvUncast calls funs) (st := st1) hVeq hn0 (.var 0)
            have hv : v < wordBound := hInv0.wf v (by simp)
            obtain ⟨stR, hret, hh, hR'⟩ :=
              return_word_sim (funEnvUncast calls funs) V1 hv he hInv0.rel
            have hnoRet : noExtBlock (emitReturnWords {} [atomE (env.length + 1) (.var 0)]).stmts = true :=
              noExt_returnWords _ _ (by simp [Emit.stmts_nil]) (by
                intro x hx; simp at hx; subst hx; exact noExt_atomE _ _)
            have hdesc := execStmts_descend hfuns hnoRet hrest
            obtain ⟨hVeq', hsteq, hoeq⟩ := execStmts_det_evm hdesc hret
            subst hVeq'; subst hsteq; subst hoeq
            refine ⟨composeFault w.ncalls false (fun _ => false), ?_⟩
            intro g hgA
            have ⟨hgfalse, _⟩ := oracleAgrees_compose_false hgA
            obtain ⟨hrun, _ho, _hV, hInvg, hRXg⟩ := hg g hgfalse
            have htx :
                Tx.run (Core.denote Γ (.opTailAddr (.call b m args)) env) ctx { w with faults := g } =
                  .ok ((v : Address), { w0 with faults := g }) := by
              simpa [Core.denote, RetTy.denote, Address] using hrun
            rw [htx]
            simp only [except_ok_prod]
            refine ⟨trivial, haltSuccess_addr hh, (R_faults g).mpr hR', ?_⟩
            have hstab := ofState_noExt_halt (α := α) hign hfuns hnoRet hrest
              (bind.addr w0.self)
            have hRX' : RX α bind { w0 with faults := g } st' := by
              simpa [RX, hstab] using hRXg
            exact hRX'
  | opTailFlag op =>
    intro hS2 hslot w env V st funs hfuns hwf hn hinv hRX hconf hBind e' hem V' st' o hexec
    cases s2op_elim (by simpa [S2Frag] using hS2) with
    | inr hM1 =>
      exact core_sim_ext_callFree (α := α) bind hhalt hΓ hκ hlen hign (.opTailFlag op)
        (by simpa [CallFree, M1Frag] using hM1) hslot
        funs hfuns hwf hn hinv hRX hconf hBind hem hexec
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
        obtain ⟨meth, hbd⟩ := hBind b m args hopWF
        have hn1 : identsNodup (env.length + 1) = true :=
          identsNodup_mono (by simp [coreExtraDepth]) hn
        cases execStmts_append_inv hexec with
        | inr hstop =>
          have hexec1 : ExecStmts (yulD calls) funs V st
              ((emitLetOp c {} env.length (.call b m args)).getD {}).stmts V' st' o := by
            simpa [hE] using hstop.2
          obtain ⟨bit, hfail, hok⟩ :=
            op_sim_call_bwd (α := α) hinv hbd hRX hconf hfuns hopWF hn1 hexec1
          cases bit with
          | false =>
            obtain ⟨_, _, _, _, _, hg⟩ := hok rfl
            obtain ⟨_, ho, _⟩ := hg (fun _ => false) rfl
            exact (hstop.1 ho).elim
          | true =>
            refine ⟨fun _ => true, ?_⟩
            intro g hg
            have gnc : g w.ncalls = true := by
              simpa using hg w.ncalls (Nat.le_refl _)
            have ⟨hrun, ho, hh⟩ := hfail rfl g gnc
            have htx :
                Tx.run (Core.denote Γ (.opTailFlag (.call b m args)) env) ctx { w with faults := g } =
                  .error .callFailed := by
              simpa [Core.denote, RetTy.denote, Flag] using hrun
            rw [htx]
            simp only [except_error_prod]
            exact ⟨[], ho, hh, rfl⟩
        | inl hokPre =>
          obtain ⟨V1, st1, hcallE, hrest⟩ := hokPre
          have hexec1 : ExecStmts (yulD calls) funs V st
              ((emitLetOp c {} env.length (.call b m args)).getD {}).stmts V1 st1 .normal := by
            simpa [hE] using hcallE
          obtain ⟨bit, hfail, hok⟩ :=
            op_sim_call_bwd (α := α) hinv hbd hRX hconf hfuns hopWF hn1 hexec1
          cases bit with
          | true =>
            have ⟨_, ho, _⟩ := hfail rfl (fun _ => true) rfl
            cases ho
          | false =>
            obtain ⟨v, w0, hself, _hlog, hncalls, hg⟩ := hok rfl
            let g0 : Nat → Bool := fun _ => false
            obtain ⟨_hrun0, _ho0, hVeq, hInv0, hRX0⟩ := hg g0 rfl
            have hn0 : identsNodup (v :: env).length = true := by simpa using hn1
            have he := eval_atom (funEnvUncast calls funs) (st := st1) hVeq hn0 (.var 0)
            have hv : v < wordBound := hInv0.wf v (by simp)
            obtain ⟨stR, hret, hh, hR'⟩ :=
              return_word_sim (funEnvUncast calls funs) V1 hv he hInv0.rel
            have hnoRet : noExtBlock (emitReturnWords {} [atomE (env.length + 1) (.var 0)]).stmts = true :=
              noExt_returnWords _ _ (by simp [Emit.stmts_nil]) (by
                intro x hx; simp at hx; subst hx; exact noExt_atomE _ _)
            have hdesc := execStmts_descend hfuns hnoRet hrest
            obtain ⟨hVeq', hsteq, hoeq⟩ := execStmts_det_evm hdesc hret
            subst hVeq'; subst hsteq; subst hoeq
            refine ⟨composeFault w.ncalls false (fun _ => false), ?_⟩
            intro g hgA
            have ⟨hgfalse, _⟩ := oracleAgrees_compose_false hgA
            obtain ⟨hrun, _ho, _hV, hInvg, hRXg⟩ := hg g hgfalse
            have htx :
                Tx.run (Core.denote Γ (.opTailFlag (.call b m args)) env) ctx { w with faults := g } =
                  .ok ((v : Flag), { w0 with faults := g }) := by
              simpa [Core.denote, RetTy.denote, Flag] using hrun
            rw [htx]
            simp only [except_ok_prod]
            refine ⟨trivial, haltSuccess_flag hh, (R_faults g).mpr hR', ?_⟩
            have hstab := ofState_noExt_halt (α := α) hign hfuns hnoRet hrest
              (bind.addr w0.self)
            have hRX' : RX α bind { w0 with faults := g } st' := by
              simpa [RX, hstab] using hRXg
            exact hRX'
  | stmtTail s =>
    intro hS2 hslot w env V st funs hfuns hwf hn hinv hRX hconf hBind e' hem V' st' o hexec
    cases s2stmt_elim (by simpa [S2Frag] using hS2) with
    | inr hM1 =>
      exact core_sim_ext_callFree (α := α) bind hhalt hΓ hκ hlen hign (.stmtTail s)
        (by simpa [CallFree, M1Frag] using hM1) hslot
        funs hfuns hwf hn hinv hRX hconf hBind hem hexec
    | inl hcall =>
      obtain ⟨b, m, args, rfl⟩ := hcall
      simp only [emitCore] at hem
      rw [hhalt] at hem
      cases hem
      rw [emitReturnUnit_true] at hexec
      have hopWF : callWF c b m args = true := by simpa [coreWF, stmtWF] using hwf
      obtain ⟨meth, hbd⟩ := hBind b m args hopWF
      have hn0 : identsNodup env.length = true :=
        identsNodup_mono (by simp [coreExtraDepth]) hn
      cases execStmts_append_inv hexec with
      | inr hstop =>
        have hexec1 : ExecStmts (yulD calls) funs V st
            (emitStmt c {} env.length (.call b m args)).stmts V' st' o := hstop.2
        obtain ⟨bit, hfail, hok⟩ :=
          stmt_sim_call_bwd (α := α) hinv hbd hRX hconf hfuns hopWF hn0 hexec1
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
          stmt_sim_call_bwd (α := α) hinv hbd hRX hconf hfuns hopWF hn0 hcallE
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
          have hstab := ofState_noExt_halt (α := α) hign hfuns hnoStop hrest
            (bind.addr w0.self)
          simpa [RX, hstab] using hRXg
  | letOp op k ih =>
    intro hS2 hslot w env V st funs hfuns hwf hn hinv hRX hconf hBind e' hem V' st' o hexec
    have ⟨hop, hk⟩ := s2frag_letOp.mp hS2
    have ⟨hopWF0, hkWF⟩ := coreWF_letOp.mp hwf
    obtain ⟨e1, e0, hE, h0, hst⟩ := emitCore_letOp_split hem
    rw [hst] at hexec
    have hn1 : identsNodup (env.length + 1) = true :=
      identsNodup_mono (by simp [coreExtraDepth]; try omega) hn
    have hnK : identsNodup ((env.length + 1) + coreExtraDepth k) = true := by
      simpa [coreExtraDepth, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
    have hslotK : ∃ slot : Nat,
        (∀ σ, Γ.st.scalar slot σ = bind.addr σ) ∧
        (c.fields[slot]?).map (·.kind) = some FieldKind.scalar ∧
        coreAvoids slot k := by
      obtain ⟨slot, haddr, hkind, hav⟩ := hslot
      exact ⟨slot, haddr, hkind, by simpa [coreAvoids] using hav⟩
    cases s2op_elim hop with
    | inl hcall =>
      obtain ⟨b, m, args, rfl⟩ := hcall
      have hopWF : callWF c b m args = true := by simpa [opWF] using hopWF0
      obtain ⟨meth, hbd⟩ := hBind b m args hopWF
      cases execStmts_append_inv hexec with
      | inr hstop =>
        have hexec1 : ExecStmts (yulD calls) funs V st
            ((emitLetOp c {} env.length (.call b m args)).getD {}).stmts V' st' o := by
          simpa [hE] using hstop.2
        obtain ⟨bit, hfail, hok⟩ :=
          op_sim_call_bwd (α := α) hinv hbd hRX hconf hfuns hopWF hn1 hexec1
        cases bit with
        | false =>
          obtain ⟨_, _, _, _, _, hg⟩ := hok rfl
          obtain ⟨_, ho, _⟩ := hg (fun _ => false) rfl
          exact (hstop.1 ho).elim
        | true =>
          refine ⟨fun _ => true, ?_⟩
          intro g hg
          have gnc : g w.ncalls = true := by
            simpa using hg w.ncalls (Nat.le_refl _)
          have ⟨hrun, ho, hh⟩ := hfail rfl g gnc
          have htx :
              Tx.run (Core.denote Γ (.letOp (.call b m args) k) env) ctx { w with faults := g } =
                .error .callFailed := by
            simp only [Core.denote, Tx.run_bind, hrun]
          rw [htx]
          simp only [except_error_prod]
          exact ⟨[], ho, hh, rfl⟩
      | inl hokPre =>
        obtain ⟨V1, st1, hcallE, hrest⟩ := hokPre
        have hexec1 : ExecStmts (yulD calls) funs V st
            ((emitLetOp c {} env.length (.call b m args)).getD {}).stmts V1 st1 .normal := by
          simpa [hE] using hcallE
        obtain ⟨bit, hfail, hok⟩ :=
          op_sim_call_bwd (α := α) hinv hbd hRX hconf hfuns hopWF hn1 hexec1
        cases bit with
        | true =>
          have ⟨_, ho, _⟩ := hfail rfl (fun _ => true) rfl
          cases ho
        | false =>
          obtain ⟨v, w0, hself, _hlog, hncalls, hg⟩ := hok rfl
          -- Success bit: instantiate the op lemma at `g₀ := fun _ => false` to
          -- get `Inv`/`RX` at `{w0 with faults := g₀}`, then IH for `k`.
          -- `fo := composeFault w.ncalls false fo'`. For `oracleAgrees w.ncalls fo g`,
          -- `g w.ncalls = false` so the op lemma at `g` gives
          -- `Tx.run Op = .ok (v, {w0 with faults := g})`; `Tx.run (letOp)` unfolds
          -- to the continuation. IH's `∀ g'` at `g' := g` needs
          -- `oracleAgrees w0.ncalls fo' g` (`w0.ncalls = w.ncalls + 1`). The IH
          -- was stated at `{w0 with faults := g₀}`; its conclusion is about
          -- `Tx.run … {({w0 with faults := g₀}) with faults := g}` which is
          -- `{w0 with faults := g}` (record update collapses).
          let g0 : Nat → Bool := fun _ => false
          obtain ⟨_hrun0, _ho0, hVeq, hInv0, hRX0⟩ := hg g0 rfl
          have hconf0 : Conforms I ctx.self (bind.addr w0.self) calls α := by
            simpa [hself] using hconf
          obtain ⟨fo', hfo'⟩ :=
            ih hk hslotK (w := { w0 with faults := g0 }) (env := v :: env) (V := V1)
              (st := st1) funs hfuns hkWF (by simpa using hnK) hInv0 hRX0 hconf0 hBind h0 hrest
          refine ⟨composeFault w.ncalls false fo', ?_⟩
          intro g hgA
          have ⟨hgfalse, hgtail⟩ := oracleAgrees_compose_false hgA
          obtain ⟨hrun, _ho, _hV, _hInvg, _hRXg⟩ := hg g hgfalse
          simp [Core.denote, Tx.run_bind, hrun, except_ok_prod]
          have hagree : oracleAgrees w0.ncalls fo' g := by
            simpa [hncalls] using hgtail
          simpa using hfo' g hagree
    | inr hM1 =>
      have hno : noExtBlock e1.stmts = true :=
        noExt_letOp_m1 hM1 (by simp [Emit.stmts_nil]) hE
      have hsim :=
        op_sim (funEnvUncast calls funs) hinv hΓ hκ hlen hM1 hopWF0 hn1
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
        have hRX1 : RX α bind w1 st1 := by
          have hst := execStmts_normal_ofState hign hexecS1 (bind.addr w.self)
          simpa [RX, hst, hw1] using hRX
        have hconf1 : Conforms I ctx.self (bind.addr w1.self) calls α := by
          simpa [hw1] using hconf
        obtain ⟨fo', hfo'⟩ :=
          ih hk hslotK (w := w1) (env := v :: env)
            (V := (identV env.length, BitVec.ofNat 256 v) :: V) (st := st1)
            funs hfuns hkWF (by simpa using hnK) hinv1 hRX1 hconf1 hBind h0 hrest
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
  | seq s k ih =>
    intro hS2 hslot w env V st funs hfuns hwf hn hinv hRX hconf hBind e' hem V' st' o hexec
    have ⟨hs, hk⟩ := s2frag_seq.mp hS2
    have ⟨hsWF, hkWF⟩ := coreWF_seq.mp hwf
    simp only [emitCore] at hem
    obtain ⟨e0, h0, hst⟩ := emitCore_prefix hem
    rw [hst] at hexec
    have hn0 : identsNodup env.length = true :=
      identsNodup_mono (by simp [coreExtraDepth]) hn
    have hnK : identsNodup (env.length + coreExtraDepth k) = true := by
      simpa [coreExtraDepth] using hn
    have hslotK : ∃ slot : Nat,
        (∀ σ, Γ.st.scalar slot σ = bind.addr σ) ∧
        (c.fields[slot]?).map (·.kind) = some FieldKind.scalar ∧
        coreAvoids slot k := by
      obtain ⟨slot, haddr, hkind, hav⟩ := hslot
      exact ⟨slot, haddr, hkind, hav.2⟩
    cases s2stmt_elim hs with
    | inl hcall =>
      obtain ⟨b, m, args, rfl⟩ := hcall
      have hopWF : callWF c b m args = true := by simpa [stmtWF] using hsWF
      obtain ⟨meth, hbd⟩ := hBind b m args hopWF
      cases execStmts_append_inv hexec with
      | inr hstop =>
        obtain ⟨bit, hfail, hok⟩ :=
          stmt_sim_call_bwd (α := α) hinv hbd hRX hconf hfuns hopWF hn0 hstop.2
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
              Tx.run (Core.denote Γ (.seq (.call b m args) k) env) ctx { w with faults := g } =
                .error .callFailed := by
            simp only [Core.denote, Tx.run_bind, hrun]
          rw [htx]
          simp only [except_error_prod]
          exact ⟨[], ho, hh, rfl⟩
      | inl hokPre =>
        obtain ⟨V1, st1, hcallE, hrest⟩ := hokPre
        obtain ⟨bit, hfail, hok⟩ :=
          stmt_sim_call_bwd (α := α) hinv hbd hRX hconf hfuns hopWF hn0 hcallE
        cases bit with
        | true =>
          have ⟨_, ho, _⟩ := hfail rfl (fun _ => true) rfl
          cases ho
        | false =>
          obtain ⟨w0, hself, _hlog, hncalls, hg⟩ := hok rfl
          let g0 : Nat → Bool := fun _ => false
          obtain ⟨_hrun0, _ho0, hVeq, hInv0, hRX0⟩ := hg g0 rfl
          have hconf0 : Conforms I ctx.self (bind.addr w0.self) calls α := by
            simpa [hself] using hconf
          obtain ⟨fo', hfo'⟩ :=
            ih hk hslotK (w := { w0 with faults := g0 }) (env := env) (V := V1)
              (st := st1) funs hfuns hkWF hnK hInv0 hRX0 hconf0 hBind h0 hrest
          refine ⟨composeFault w.ncalls false fo', ?_⟩
          intro g hgA
          have ⟨hgfalse, hgtail⟩ := oracleAgrees_compose_false hgA
          obtain ⟨hrun, _ho, _hV, _hInvg, _hRXg⟩ := hg g hgfalse
          have htx :
              Tx.run (Core.denote Γ (.seq (.call b m args) k) env) ctx { w with faults := g } =
                Tx.run (Core.denote Γ k env) ctx { w0 with faults := g } := by
            simp only [Core.denote, Tx.run_bind, hrun]
          rw [htx]
          have hagree : oracleAgrees w0.ncalls fo' g := by
            simpa [hncalls] using hgtail
          simpa using hfo' g hagree
    | inr hM1 =>
      have hno : noExtBlock (emitStmt c {} env.length s).stmts = true :=
        noExt_stmt_m1 hM1 (by simp [Emit.stmts_nil])
      have hsim := stmt_sim (funEnvUncast calls funs) hinv hΓ hκ hlen hM1 hsWF hn0
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
        obtain ⟨slot, haddr, hkind, hav⟩ := hslot
        have haddr1 :=
          m1stmt_preserves_addr (bind := bind) hΓ haddr hkind hM1 hsWF hav.1 env ctx w hokd
        have hghost := m1stmt_preserves_ghost (Γ := Γ) hM1 env ctx w hokd
        have hRX1 : RX α bind w1 st1 := by
          have hst := execStmts_normal_ofState hign hexecS1 (bind.addr w.self)
          simpa [RX, hst, hghost.1, haddr1] using hRX
        have hconf1 : Conforms I ctx.self (bind.addr w1.self) calls α := by
          simpa [haddr1] using hconf
        obtain ⟨fo', hfo'⟩ :=
          ih hk ⟨slot, haddr, hkind, hav.2⟩ (w := w1) (env := env) (V := V)
            (st := st1) funs hfuns hkWF hnK hinv1 hRX1 hconf1 hBind h0 hrest
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
  | letPure p args k ih =>
    intro hS2 hslot w env V st funs hfuns hwf hn hinv hRX hconf hBind e' hem V' st' o hexec
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
    have hslotK : ∃ slot : Nat,
        (∀ σ, Γ.st.scalar slot σ = bind.addr σ) ∧
        (c.fields[slot]?).map (·.kind) = some FieldKind.scalar ∧
        coreAvoids slot k := by
      obtain ⟨slot, haddr, hkind, hav⟩ := hslot
      exact ⟨slot, haddr, hkind, by simpa [coreAvoids] using hav⟩
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
      ih hk hslotK funs hfuns hkWF (by simpa using hnK) hinv1 hRX hconf hBind h0 hrest
    refine ⟨fo', ?_⟩
    intro g hg
    simp only [Core.denote]
    have hpe : Prim.eval .id (List.map (Atom.eval env) [a]) = a.eval env := rfl
    rw [hpe]
    exact hfo' g hg
  | ite cond a b iha ihb =>
    intro hS2 hslot w env V st funs hfuns hwf hn hinv hRX hconf hBind e' hem V' st' o hexec
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
    obtain ⟨slot, haddr, hkind, hav⟩ := hslot
    have hslotA : ∃ slot : Nat,
        (∀ σ, Γ.st.scalar slot σ = bind.addr σ) ∧
        (c.fields[slot]?).map (·.kind) = some FieldKind.scalar ∧
        coreAvoids slot a := ⟨slot, haddr, hkind, hav.1⟩
    have hslotB : ∃ slot : Nat,
        (∀ σ, Γ.st.scalar slot σ = bind.addr σ) ∧
        (c.fields[slot]?).map (·.kind) = some FieldKind.scalar ∧
        coreAvoids slot b := ⟨slot, haddr, hkind, hav.2⟩
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
            iha ha hslotA ([] :: funs) hfunsN haWF hnA hinv hRX hconf hBind hA hss
          exact ⟨fo', hfo'⟩
        · have hsel :
              selectSwitch (yulD calls) (b2w (decide (cond.denote env)))
                [(YulSemantics.Literal.number 0, eB.stmts)] (some eA.stmts) = eB.stmts := by
            simp [hc, b2w]
            exact selectSwitch_zero_yulD
          rw [hsel, hhoistB] at hss
          obtain ⟨fo', hfo'⟩ :=
            ihb hb hslotB ([] :: funs) hfunsN hbWF hnB hinv hRX hconf hBind hB hss
          exact ⟨fo', hfo'⟩


/-- S2 backward `toYulFn` for `S2Frag` cores: invert `Run` → params prefix → `core_sim_ext`. -/
theorem toYulFn_correct_ext {I : Interface} {S X E ε : Type}
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
    (hconf : Conforms I ctx.self (bind.addr w.self) calls α)
    (hBind : ∀ b m args, callWF c b m args = true → ∃ meth, BindWF c Γ bind b m meth)
    (hslot : ∃ slot : Nat,
        (∀ σ, Γ.st.scalar slot σ = bind.addr σ) ∧
        (c.fields[slot]?).map (·.kind) = some FieldKind.scalar ∧
        coreAvoids slot f.core) :
    ToYulFnCorrectExt α bind c Γ κ calls f yul ctx w st0 := by
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
    core_sim_ext (α := α) bind (haltUnit := true) rfl hΓ hκ hlen hign f.core hS2 hslot
      (funs := [[]]) hfuns hwf hn' hinv hRX hconf hBind h0' hrest
  obtain ⟨fo, hfo⟩ := hsim
  refine ⟨fo, ?_⟩
  have hmatch := hfo fo (fun _ _ => rfl)
  cases hTx : Tx.run (Core.denote Γ f.core args.reverse) ctx { w with faults := fo } with
  | ok p =>
    rcases p with ⟨v, w'⟩
    simp only [hTx, except_ok_prod] at hmatch ⊢
    obtain ⟨ho, hsucc, hR', hRX'⟩ := hmatch
    obtain ⟨k, bs, hh, hk⟩ := haltSuccess_commits hsucc
    rw [committedState_commit hh hk]
    exact ⟨ho, hsucc, hR', hRX'⟩
  | error err =>
    simp only [hTx, except_error_prod] at hmatch ⊢
    obtain ⟨bytes, ho, hh, herr⟩ := hmatch
    refine ⟨bytes, ho, ?_, herr, R_rollback_obs hR hh HaltKind.revert_commits⟩
    simp [committedState_rollback hh HaltKind.revert_commits, hh]

end Lsc.Compiler
