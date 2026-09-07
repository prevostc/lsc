import Lsc.Compiler.EndToEnd
import Lsc.Compiler.Proof.DispatchExt
import Lsc.Compiler.Proof.ProgressCore
import YulEvmCompiler.Correctness
import YulEvmCompiler.LowerDefs

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
S2 bytecode glue. powdr `compile_correct` is **forward only** (`Run → ∃ Steps`).
There is no `compile_complete` / adequacy. `CallsTotal` gives a Yul `Run`
(`yul_progress`); that run plus `compile_correct` plus `steps_halted_unique`
gives `EvmCallRunExtAll`: every halted matching EVM execution has the unique
post-storage predicted by Core under some `fo`. powdr adequacy is still not
used (and not needed).
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open EvmSemantics.EVM (State Steps)

/-- Same triple as `yulD`: `creates := .none`, `gas := .none` (not the class default). -/
@[instance_reducible] def openModel (calls : ExternalCalls) : ExternalModel where
  calls := calls
  creates := ExternalCreates.none
  gas := ExternalGas.none

theorem externalsRealized_open {calls : ExternalCalls}
    (h : CallsRealized calls) :
    ExternalsRealized (openModel calls) :=
  ⟨h, CreatesRealized.none, GasCallsRealized.noneOracle calls⟩

/-- Given a Yul run, Core under some `fo` predicts the committed observation. -/
def EvmCallRunExt {I : Interface} {S X E ε : Type}
    (α : Abs I.Ghost) (bind : Binding I S X)
    (c : ContractDef) (Γ : ContractSchema S X E ε) (κ : List UInt8 → U256)
    (calls : ExternalCalls) (ctx : Ctx) (w : World S X E)
    (yst0 st' : EvmState) (o : Outcome) : Prop :=
  ∃ fo : Nat → Bool,
    let wfo : World S X E := { w with faults := fo }
    let stObs := committedState yst0 st'
    match selectedFn c yst0.env.calldata with
    | none =>
        o = Outcome.halt ∧ stObs.halted = some (.revert, []) ∧ R c Γ κ w stObs
    | some f =>
        match Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse)
            ctx wfo with
        | .ok (v, w') =>
            o = Outcome.halt ∧ haltSuccess f.ret v stObs.halted ∧
              R c Γ κ w' stObs ∧ RX α bind w' stObs
        | .error e =>
            ∃ bytes, o = Outcome.halt ∧ stObs.halted = some (.revert, bytes) ∧
              haltError c Γ e bytes ∧ R c Γ κ w stObs

/-- Backward bytecode theorem: every Yul `Run` of the compiled runtime is
predicted (`EvmCallRunExt`) and has matching EVM `Steps` (`compile_correct`).
Every halted `Steps` from a matching start has the same post-storage and
post-foreign-storage. `ξ'` is read from the halted EVM state
(`postForeign` / `accountForeign`); `StateMatch.externalCode.storage`
identifies it with Yul `st.foreign`. -/
def BytecodeCallCorrectExt {I : Interface} {S X E ε : Type}
    (α : Abs I.Ghost) (bind : Binding I S X)
    (c : ContractDef) (Γ : ContractSchema S X E ε) (κ : List UInt8 → U256)
    (calls : ExternalCalls) (ctx : Ctx) (w : World S X E)
    (yst0 : EvmState) (rt : YBlock) (is : List Instr) : Prop :=
  ∀ (st' : EvmState) (o : Outcome),
    Run (yulD calls) rt yst0 [] st' o →
      EvmCallRunExt α bind c Γ κ calls ctx w yst0 st' o ∧
      EvmCallRunξ is yst0 (committedState yst0 st').storage
        (evmForeign (committedState yst0 st'))

theorem bytecode_call_correct_ext {I : Interface} {S X E ε : Type}
    (α : Abs I.Ghost) (bind : Binding I S X)
    (c : ContractDef) (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (calls : ExternalCalls) (hCalls : CallsRealized calls)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (ctx : Ctx) (w : World S X E) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
    (hRX : RX α bind w yst0) (hign : α.ignoresLocal)
    (hBindNe : accountKey (BitVec.ofNat 256 (bind.addr w.self)) ≠
      accountKey (BitVec.ofNat 256 ctx.self))
    (hconf : Conforms I ctx.self (bind.addr w.self) calls α)
    (hBind : ∀ b m args, callWF c b m args = true → ∃ meth, BindWF c Γ bind b m meth)
    (hslot : ∀ f ∈ c.functions, ∃ slot : Nat,
        (∀ σ, Γ.st.scalar slot σ = bind.addr σ) ∧
        (c.fields[slot]?).map (·.kind) = some FieldKind.scalar ∧
        coreAvoids slot f.core)
    (himm0 : ∀ k, yst0.env.immutable k = 0) :
    BytecodeCallCorrectExt α bind c Γ evmKeccak calls ctx w yst0 rt is := by
  intro st' o hrun
  have hpred : EvmCallRunExt α bind c Γ evmKeccak calls ctx w yst0 st' o :=
    runtimeBlock_correct_ext (I := I) α bind c Γ hΓ evmKeccak hκ calls
      hctor hS2 hlen hbound rt hrt ctx w yst0 hctx hR hRX hign hBindNe hconf hBind hslot
      st' o hrun
  refine ⟨hpred, ?_⟩
  let _model : ExternalModel := openModel calls
  have himm : ∀ key, unpatchedImmutables key =
      yst0.env.immutable (litValue (.string key)) := by
    intro key
    simp [unpatchedImmutables, himm0]
  have ⟨b, hb⟩ :=
    compile_correct (model := openModel calls) (externalsRealized_open hCalls)
      hcomp himm hrun
  obtain ⟨fo, hconcl⟩ := hpred
  let stObs := committedState yst0 st'
  have hobs : stObs = committedState yst0 st' := rfl
  have hhalted : stObs.halted = st'.halted := committedState_halted yst0 st'
  refine ⟨b, ?_⟩
  intro s0 hstart hgas
  rcases hstart with ⟨hOK, hM, hpc, hstk⟩
  obtain ⟨s', hSteps, hcs, hSM, hOut⟩ := hb s0 hOK hM hpc hstk hgas
  have hH : Halted s' := Halted_of_compile_out hcs hOut
  have ho : o = Outcome.halt := by
    cases hsel : selectedFn c yst0.env.calldata with
    | none =>
      simp only [hsel] at hconcl
      exact hconcl.1
    | some f =>
      simp only [hsel] at hconcl
      cases htx : Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse)
          ctx { w with faults := fo } with
      | ok prod =>
        simp only [htx] at hconcl
        exact hconcl.1
      | error e =>
        simp only [htx] at hconcl
        rcases hconcl with ⟨_, ⟨ho', _⟩⟩
        exact ho'
  have hHM : HaltedMatch st' s' := by
    rcases hOut with ⟨hn, _⟩ | ⟨_, hH'⟩
    · cases (hn.symm.trans ho)
    · exact hH'
  have hpost : stObs.storage = postStorage yst0 s' := by
    cases hsel : selectedFn c yst0.env.calldata with
    | none =>
      simp only [hsel] at hconcl
      rcases hconcl with ⟨_, ⟨hh, _⟩⟩
      have hr := reverted_of_halted (bytes := []) (hhalted ▸ hh) hHM
      rw [postStorage_reverted hr.1, obs_storage_rollback hobs hhalted hh]
    | some f =>
      simp only [hsel] at hconcl
      cases htx : Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse)
          ctx { w with faults := fo } with
      | ok prod =>
        rcases prod with ⟨v, w'⟩
        simp only [htx] at hconcl
        rcases hconcl with ⟨_, ⟨hsucc, _⟩⟩
        obtain ⟨k, bs, hh, hk⟩ := haltSuccess_commits hsucc
        have heq : stObs = st' := obs_eq_of_commit hobs hhalted hh hk
        have hsucc' : haltSuccess f.ret v st'.halted := by rw [← heq]; exact hsucc
        have hOK' := haltOK_of_success hsucc' hHM
        have hnr : s'.halt ≠ .Reverted := by
          unfold haltOK at hOK'
          split at hOK'
          · intro h; cases (hOK'.symm.trans h)
          · intro h; cases (hOK'.1.symm.trans h)
        rw [postStorage_commit hnr, storage_eq_account hSM, heq]
      | error e =>
        simp only [htx] at hconcl
        rcases hconcl with ⟨bytes, ⟨_, ⟨hh, _⟩⟩⟩
        have hr := reverted_of_halted (hhalted ▸ hh) hHM
        rw [postStorage_reverted hr.1, obs_storage_rollback hobs hhalted hh]
  have hpostξ : evmForeign stObs = postForeign yst0 s' := by
    cases hsel : selectedFn c yst0.env.calldata with
    | none =>
      simp only [hsel] at hconcl
      rcases hconcl with ⟨_, ⟨hh, _⟩⟩
      have hr := reverted_of_halted (bytes := []) (hhalted ▸ hh) hHM
      rw [postForeign_reverted hr.1, obs_foreign_rollback hobs hhalted hh]
    | some f =>
      simp only [hsel] at hconcl
      cases htx : Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse)
          ctx { w with faults := fo } with
      | ok prod =>
        rcases prod with ⟨v, w'⟩
        simp only [htx] at hconcl
        rcases hconcl with ⟨_, ⟨hsucc, _⟩⟩
        obtain ⟨k, bs, hh, hk⟩ := haltSuccess_commits hsucc
        have heq : stObs = st' := obs_eq_of_commit hobs hhalted hh hk
        have hsucc' : haltSuccess f.ret v st'.halted := by rw [← heq]; exact hsucc
        have hOK' := haltOK_of_success hsucc' hHM
        have hnr : s'.halt ≠ .Reverted := by
          unfold haltOK at hOK'
          split at hOK'
          · intro h; cases (hOK'.symm.trans h)
          · intro h; cases (hOK'.1.symm.trans h)
        rw [postForeign_commit hnr, foreign_eq_account hSM, heq]
      | error e =>
        simp only [htx] at hconcl
        rcases hconcl with ⟨bytes, ⟨_, ⟨hh, _⟩⟩⟩
        have hr := reverted_of_halted (hhalted ▸ hh) hHM
        rw [postForeign_reverted hr.1, obs_foreign_rollback hobs hhalted hh]
  refine ⟨⟨s', hSteps, hH⟩, ?_⟩
  intro s'' hS'' hH''
  rw [steps_halted_unique hS'' hSteps hH'' hH]
  exact ⟨hpost, hpostξ⟩

/-- Universal over halted EVM runs: some gas bound, a halted `Steps` exists, every
halted `Steps` has post-storage `σ'` and post-foreign-storage `ξ'`, and Core
under some `fo` predicts that storage (`storageRel` / `RX` on a witnessing
committed Yul state whose `foreign` is `ξ'`). `ξ'` is read from the halted
EVM account map (`postForeign`); `StateMatch.externalCode.storage` identifies
it with Yul `foreign`. -/
def EvmCallRunExtAll {I : Interface} {S X E ε : Type}
    (α : Abs I.Ghost) (bind : Binding I S X)
    (c : ContractDef) (Γ : ContractSchema S X E ε) (κ : List UInt8 → U256)
    (calls : ExternalCalls) (ctx : Ctx) (w : World S X E)
    (is : List Instr) (yst0 : EvmState) (σ' : U256 → U256) (ξ' : Foreign) : Prop :=
  ∃ b : Nat, ∀ s0 : State,
    EvmStartOK is yst0 s0 → b ≤ s0.gasAvailable →
    (∃ s', Steps s0 s' ∧ Halted s') ∧
    ∀ s', Steps s0 s' → Halted s' →
      σ' = postStorage yst0 s' ∧ ξ' = postForeign yst0 s' ∧
      ∃ fo : Nat → Bool,
        let wfo : World S X E := { w with faults := fo }
        match selectedFn c yst0.env.calldata with
        | none => σ' = yst0.storage ∧ ξ' = evmForeign yst0
        | some f =>
            match Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse)
                ctx wfo with
            | .ok (_, w') =>
                storageRel c Γ κ w'.self σ' ∧
                  ∃ stObs : EvmState, stObs.storage = σ' ∧ evmForeign stObs = ξ' ∧
                    R c Γ κ w' stObs ∧ RX α bind w' stObs
            | .error _ => σ' = yst0.storage ∧ ξ' = evmForeign yst0

theorem evmCallRunExtAll_of_progress {I : Interface} {S X E ε : Type}
    (α : Abs I.Ghost) (bind : Binding I S X)
    (c : ContractDef) (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (calls : ExternalCalls) (hCalls : CallsRealized calls) (htot : CallsTotal calls)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (ctx : Ctx) (w : World S X E) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
    (hRX : RX α bind w yst0) (hign : α.ignoresLocal)
    (hBindNe : accountKey (BitVec.ofNat 256 (bind.addr w.self)) ≠
      accountKey (BitVec.ofNat 256 ctx.self))
    (hconf : Conforms I ctx.self (bind.addr w.self) calls α)
    (hBind : ∀ b m args, callWF c b m args = true → ∃ meth, BindWF c Γ bind b m meth)
    (hslot : ∀ f ∈ c.functions, ∃ slot : Nat,
        (∀ σ, Γ.st.scalar slot σ = bind.addr σ) ∧
        (c.fields[slot]?).map (·.kind) = some FieldKind.scalar ∧
        coreAvoids slot f.core)
    (himm0 : ∀ k, yst0.env.immutable k = 0) :
    ∃ σ' ξ', EvmCallRunExtAll α bind c Γ evmKeccak calls ctx w is yst0 σ' ξ' := by
  obtain ⟨st', o, hrun⟩ :=
    yul_progress (I := I) α bind c Γ hΓ evmKeccak hκ calls htot hctor hS2 hlen hbound
      rt hrt ctx w yst0 hctx hR hconf hBind hslot
  have ⟨hpred, hEvm⟩ :=
    bytecode_call_correct_ext (I := I) α bind c Γ hΓ hκ calls hCalls hctor hS2
      hlen hbound rt hrt is hcomp ctx w yst0 hctx hR hRX hign hBindNe hconf hBind hslot himm0
      st' o hrun
  set stObs := committedState yst0 st'
  refine ⟨stObs.storage, evmForeign stObs, ?_⟩
  obtain ⟨b, hb⟩ := hEvm
  refine ⟨b, ?_⟩
  intro s0 hstart hgas
  obtain ⟨hex, huni⟩ := hb s0 hstart hgas
  refine ⟨hex, ?_⟩
  intro s'' hS hH
  refine ⟨(huni s'' hS hH).1, (huni s'' hS hH).2, ?_⟩
  obtain ⟨fo, hconcl⟩ := hpred
  refine ⟨fo, ?_⟩
  have hhalted : stObs.halted = st'.halted := committedState_halted yst0 st'
  cases hsel : selectedFn c yst0.env.calldata with
  | none =>
    simp only [hsel] at hconcl ⊢
    rcases hconcl with ⟨_, ⟨hh, _⟩⟩
    exact ⟨obs_storage_rollback rfl hhalted hh, obs_foreign_rollback rfl hhalted hh⟩
  | some f =>
    simp only [hsel] at hconcl ⊢
    cases htx : Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse)
        ctx { w with faults := fo } with
    | ok prod =>
      rcases prod with ⟨v, w'⟩
      simp only [htx] at hconcl ⊢
      rcases hconcl with ⟨_, hsucc, hR', hRX'⟩
      exact ⟨hR'.1, stObs, rfl, rfl, hR', hRX'⟩
    | error e =>
      simp only [htx] at hconcl ⊢
      rcases hconcl with ⟨bytes, ⟨_, ⟨hh, _⟩⟩⟩
      exact ⟨obs_storage_rollback rfl hhalted hh, obs_foreign_rollback rfl hhalted hh⟩

theorem evmCallRun_of_correct_ext {I : Interface} {S X E ε : Type}
    (α : Abs I.Ghost) (bind : Binding I S X)
    (c : ContractDef) (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (calls : ExternalCalls) (hCalls : CallsRealized calls) (htot : CallsTotal calls)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (ctx : Ctx) (w : World S X E) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
    (hRX : RX α bind w yst0) (hign : α.ignoresLocal)
    (hBindNe : accountKey (BitVec.ofNat 256 (bind.addr w.self)) ≠
      accountKey (BitVec.ofNat 256 ctx.self))
    (hconf : Conforms I ctx.self (bind.addr w.self) calls α)
    (hBind : ∀ b m args, callWF c b m args = true → ∃ meth, BindWF c Γ bind b m meth)
    (hslot : ∀ f ∈ c.functions, ∃ slot : Nat,
        (∀ σ, Γ.st.scalar slot σ = bind.addr σ) ∧
        (c.fields[slot]?).map (·.kind) = some FieldKind.scalar ∧
        coreAvoids slot f.core)
    (himm0 : ∀ k, yst0.env.immutable k = 0) :
    ∃ σ' ξ', EvmCallRunξ is yst0 σ' ξ' ∧
      ∃ fo : Nat → Bool,
        match selectedFn c yst0.env.calldata with
        | none => σ' = yst0.storage ∧ ξ' = evmForeign yst0
        | some f =>
            match Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse)
                ctx { w with faults := fo } with
            | .ok (_, w') =>
                storageRel c Γ evmKeccak w'.self σ' ∧ WorldWF c Γ w' ∧
                  ∃ stObs : EvmState, stObs.storage = σ' ∧ evmForeign stObs = ξ' ∧
                    RX α bind w' stObs
            | .error _ => σ' = yst0.storage ∧ ξ' = evmForeign yst0 := by
  obtain ⟨st', o, hrun⟩ :=
    yul_progress (I := I) α bind c Γ hΓ evmKeccak hκ calls htot hctor hS2 hlen hbound
      rt hrt ctx w yst0 hctx hR hconf hBind hslot
  have ⟨hpred, hEvm⟩ :=
    bytecode_call_correct_ext (I := I) α bind c Γ hΓ hκ calls hCalls hctor hS2
      hlen hbound rt hrt is hcomp ctx w yst0 hctx hR hRX hign hBindNe hconf hBind hslot himm0
      st' o hrun
  set stObs := committedState yst0 st'
  refine ⟨stObs.storage, evmForeign stObs, hEvm, ?_⟩
  obtain ⟨fo, hconcl⟩ := hpred
  refine ⟨fo, ?_⟩
  have hhalted : stObs.halted = st'.halted := committedState_halted yst0 st'
  cases hsel : selectedFn c yst0.env.calldata with
  | none =>
    simp only [hsel] at hconcl ⊢
    rcases hconcl with ⟨_, ⟨hh, _⟩⟩
    exact ⟨obs_storage_rollback rfl hhalted hh, obs_foreign_rollback rfl hhalted hh⟩
  | some f =>
    simp only [hsel] at hconcl ⊢
    cases htx : Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse)
        ctx { w with faults := fo } with
    | ok prod =>
      rcases prod with ⟨v, w'⟩
      simp only [htx] at hconcl ⊢
      rcases hconcl with ⟨_, hsucc, hR', hRX'⟩
      exact ⟨hR'.1, hR'.2.2.2, stObs, rfl, rfl, hRX'⟩
    | error e =>
      simp only [htx] at hconcl ⊢
      rcases hconcl with ⟨bytes, ⟨_, ⟨hh, _⟩⟩⟩
      exact ⟨obs_storage_rollback rfl hhalted hh, obs_foreign_rollback rfl hhalted hh⟩

theorem mkEvmStateExt_foreign_ne (cd σ ξ κ ctx a)
    (hne : accountKey a ≠ accountKey (BitVec.ofNat 256 ctx.self)) :
    evmForeign (mkEvmStateExt cd σ ξ κ ctx) a = ξ a := by
  funext slot
  simp [mkEvmStateExt_foreign, hne]

theorem RX_mkEvmStateExt_ne {I : Interface} {S X E} {α : Abs I.Ghost}
    {bind : Binding I S X} (hF : α.ofState_foreign)
    {w : World S X E} {st : EvmState} {cd σ ξ κ ctx}
    (hRX : RX α bind w st) (hξ : ξ = evmForeign st)
    (hne : accountKey (BitVec.ofNat 256 (bind.addr w.self)) ≠
           accountKey (BitVec.ofNat 256 ctx.self)) :
    RX α bind w (mkEvmStateExt cd σ ξ κ ctx) :=
  RX_of_foreign hF (fun k => by rw [mkEvmStateExt_foreign, hξ, if_neg hne]) hRX

theorem RX_mkEvmStateExt_ctx {I : Interface} {S X E} {α : Abs I.Ghost}
    {bind : Binding I S X} (hF : α.ofState_foreign)
    {w : World S X E} {cd cd' σ ξ κ ctx ctx'}
    (hself : ctx.self = ctx'.self)
    (hRX : RX α bind w (mkEvmStateExt cd σ ξ κ ctx)) :
    RX α bind w (mkEvmStateExt cd' σ ξ κ ctx') :=
  RX_of_foreign hF (fun k => by
    simp only [mkEvmStateExt_foreign, hself]) hRX

/-- Forward S2 trace: each call is an `EvmCallRunξ` at `mkEvmStateExt`. -/
inductive EvmTraceRunExt (is : List Instr) :
    List EvmCall → (U256 → U256) → Foreign → (U256 → U256) → Foreign → Prop
  | nil (σ : U256 → U256) (ξ : Foreign) : EvmTraceRunExt is [] σ ξ σ ξ
  | cons {call : EvmCall} {tr : List EvmCall} {σ ξ σ₁ ξ₁ σ' ξ' : _}
      (h1 : EvmCallRunξ is (mkEvmStateExt call.calldata σ ξ evmKeccak call.ctx) σ₁ ξ₁)
      (htl : EvmTraceRunExt is tr σ₁ ξ₁ σ' ξ') :
      EvmTraceRunExt is (call :: tr) σ ξ σ' ξ'

/-- Universal S2 trace: each call is an `EvmCallRunξ` at `mkEvmStateExt`,
witnessed by a matching start (so post-storage and post-foreign-storage are
unique). -/
inductive EvmTraceRunExtAll (is : List Instr) :
    List EvmCall → (U256 → U256) → Foreign → (U256 → U256) → Foreign → Prop
  | nil (σ : U256 → U256) (ξ : Foreign) : EvmTraceRunExtAll is [] σ ξ σ ξ
  | cons {call : EvmCall} {tr : List EvmCall} {σ ξ σ₁ ξ₁ σ' ξ' : _} {s0 : State}
      (hstart : EvmStartOK is
        (mkEvmStateExt call.calldata σ ξ evmKeccak call.ctx) s0)
      (h1 : EvmCallRunξ is
        (mkEvmStateExt call.calldata σ ξ evmKeccak call.ctx) σ₁ ξ₁)
      (htl : EvmTraceRunExtAll is tr σ₁ ξ₁ σ' ξ') :
      EvmTraceRunExtAll is (call :: tr) σ ξ σ' ξ'

theorem evmCallRun_fnCalldata_ext {I : Interface} {S X E ε : Type}
    (α : Abs I.Ghost) (bind : Binding I S X)
    (c : ContractDef) (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
    (calls : ExternalCalls) (hCalls : CallsRealized calls) (htot : CallsTotal calls)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (hnd : selectorsNodup c = true)
    (rt : YBlock) (hrt : runtimeBlock c = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hign : α.ignoresLocal)
    (hBind : ∀ b m args, callWF c b m args = true → ∃ meth, BindWF c Γ bind b m meth)
    (hslot : ∀ f ∈ c.functions, ∃ slot : Nat,
        (∀ σ, Γ.st.scalar slot σ = bind.addr σ) ∧
        (c.fields[slot]?).map (·.kind) = some FieldKind.scalar ∧
        coreAvoids slot f.core)
    (ctx : Ctx) (f : FnDef) (args : List Nat) (w : World S X E)
    (σ : U256 → U256) (ξ : Foreign)
    (hf : f ∈ c.functions) (hk : f.kind ≠ .constructor)
    (hlenA : args.length = f.params.length)
    (hW : ∀ n ∈ args, n < wordBound)
    (hctxWF : CtxWF ctx)
    (hs : storageRel c Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF c Γ w)
    (hcd : (fnCalldata f args).length < wordBound)
    (hRX : RX α bind w (mkEvmStateExt (fnCalldata f args) σ ξ evmKeccak ctx))
    (hBindNe : accountKey (BitVec.ofNat 256 (bind.addr w.self)) ≠
      accountKey (BitVec.ofNat 256 ctx.self))
    (hconf : Conforms I ctx.self (bind.addr w.self) calls α) :
    let yst0 := mkEvmStateExt (fnCalldata f args) σ ξ evmKeccak ctx
    ∃ σ' ξ', EvmCallRunξ is yst0 σ' ξ' ∧
      ∃ fo : Nat → Bool,
        match Tx.run (Core.denote Γ f.core args.reverse) ctx { w with faults := fo } with
        | .ok (_, w') =>
            storageRel c Γ evmKeccak w'.self σ' ∧ WorldWF c Γ w' ∧
              ∃ stObs : EvmState, stObs.storage = σ' ∧ evmForeign stObs = ξ' ∧
                RX α bind w' stObs
        | .error _ => σ' = σ ∧ ξ' = evmForeign yst0 := by
  intro yst0
  have hsel : selectedFn c (fnCalldata f args) = some f :=
    selectedFn_fnCalldata c f args hf hnd hlenA
  have hdec : decodeArgs f (fnCalldata f args) = args :=
    decodeArgs_fnCalldata f args hk hlenA hW
  have hctx : ctxRel ctx yst0 := ctxRel_mkEvmStateExt _ _ _ _ _ hctxWF hcd
  have hR : R c Γ evmKeccak w yst0 := R_mkEvmStateExt evmKeccak w _ σ ξ ctx hs hlog hwf
  have himm0 : ∀ k, yst0.env.immutable k = 0 := fun k => mkEvmStateExt_immutable _ _ _ _ _ k
  obtain ⟨σ', ξ', hRun, fo, hpost⟩ :=
    evmCallRun_of_correct_ext (I := I) α bind c Γ hΓ hκ calls hCalls htot hctor hS2
      hlen hbound rt hrt is hcomp ctx w yst0 hctx hR hRX hign hBindNe hconf hBind hslot himm0
  refine ⟨σ', ξ', hRun, fo, ?_⟩
  rw [mkEvmStateExt_calldata] at hpost
  simp only [hsel] at hpost
  rw [hdec] at hpost
  rw [show yst0.storage = σ from mkEvmStateExt_storage _ _ _ _ _] at hpost
  exact hpost

end Lsc.Compiler
