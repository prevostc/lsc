import Lsc.Compiler.Proof.CoreExt
import Lsc.Compiler.Proof.CallBwd
import Lsc.Lang.CoreProof

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

/-!
S2 backward helpers for `core_sim_ext`.

`Tx.run` equality on `{w with faults := f1}` vs `f2` is **false** in general:
every successful op returns the input `World`, which stores the `faults`
function. Load/store therefore yield `.ok (v, {w with faults := f1})` vs
`.ok (v, {w with faults := f2})`. The usable lemma is observational
(`self`/`ext`/`log`/`ncalls`/value/error), proved here for M1; the S2
induction (`core_faults_congr`) is the resume point below.

Oracle composition (for `core_sim_ext`): call at `n = w.ncalls`. `bit = true`
⇒ halt, `fo := composeFault n true w.faults`. `bit = false` ⇒ IH at `w'`
(`ncalls = n+1`) gives `fo'` for `≥ n+1`, `fo := composeFault n false fo'`.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc hiding Op Stmt

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
      match Tx.run (Lsc.Op.denote Γ env op) ctx w with
      | .ok (v, w') => .ok (v, { w' with faults := fo })
      | .error e => .error e := by
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
      match Tx.run (Lsc.Stmt.denote Γ env s) ctx w with
      | .ok (v, w') => .ok (v, { w' with faults := fo })
      | .error e => .error e := by
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

/-- Observational Core run: drop the `faults` field (not in `R`/`RX`). -/
def runShape {S X E ε α} :
    Except (Err ε) (α × World S X E) → Except (Err ε) (α × S × X × List E × Nat)
  | .ok (v, w) => .ok (v, w.self, w.ext, w.log, w.ncalls)
  | .error e => .error e

theorem m1op_runShape_faults {S X E ε} {Γ : ContractSchema S X E ε}
    {op : Lsc.Op} (h : M1Op op) (env : List Nat) (ctx : Ctx) (w : World S X E)
    (fo : Nat → Bool) :
    runShape (Tx.run (Lsc.Op.denote Γ env op) ctx { w with faults := fo }) =
      runShape (Tx.run (Lsc.Op.denote Γ env op) ctx w) := by
  rw [m1op_run_faults h]
  cases Tx.run (Lsc.Op.denote Γ env op) ctx w <;> simp [runShape]

theorem m1stmt_runShape_faults {S X E ε} {Γ : ContractSchema S X E ε}
    {s : Lsc.Stmt} (h : M1Stmt s) (env : List Nat) (ctx : Ctx) (w : World S X E)
    (fo : Nat → Bool) :
    runShape (Tx.run (Lsc.Stmt.denote Γ env s) ctx { w with faults := fo }) =
      runShape (Tx.run (Lsc.Stmt.denote Γ env s) ctx w) := by
  rw [m1stmt_run_faults h]
  cases Tx.run (Lsc.Stmt.denote Γ env s) ctx w <;> simp [runShape]

/- Resume (2): `s2_faults_congr` by induction on `S2Frag` using `runShape` + `BindWF.hext`
   (`Tx.run_call`); then `core_sim_ext` (M1 via `s1_match_prefix_*` + `op_sim`/`stmt_sim`,
   calls via `op_sim_call_bwd`/`stmt_sim_call_bwd` + `composeFault`). `stepOp_callWorld`
   for `noSstoreOp` is the remaining `hstab` piece (selfdestruct is not silent). -/

end Lsc.Compiler
