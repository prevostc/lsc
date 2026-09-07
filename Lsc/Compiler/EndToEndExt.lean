import Lsc.Compiler.EndToEnd
import Lsc.Compiler.Proof.DispatchExt
import YulEvmCompiler.Correctness
import YulEvmCompiler.LowerDefs

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
S2 bytecode glue. powdr `compile_correct` is **forward only** (`Run → ∃ Steps`).
There is no `compile_complete` / adequacy. `EvmCallRunExt` is therefore Yul-level:
every `Run (yulD calls)` is predicted (`∃ fo`) and has matching EVM `Steps`;
halted `Steps` from the same start are unique (`steps_halted_unique`).
The converse (every EVM execution is a Yul run) is a TCB gap.
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
Every halted `Steps` from a matching start has the same post-storage. -/
def BytecodeCallCorrectExt {I : Interface} {S X E ε : Type}
    (α : Abs I.Ghost) (bind : Binding I S X)
    (c : ContractDef) (Γ : ContractSchema S X E ε) (κ : List UInt8 → U256)
    (calls : ExternalCalls) (ctx : Ctx) (w : World S X E)
    (yst0 : EvmState) (rt : YBlock) (is : List Instr) : Prop :=
  ∀ (st' : EvmState) (o : Outcome),
    Run (yulD calls) rt yst0 [] st' o →
      EvmCallRunExt α bind c Γ κ calls ctx w yst0 st' o ∧
      EvmCallRun is yst0 (committedState yst0 st').storage

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
      hctor hS2 hlen hbound rt hrt ctx w yst0 hctx hR hRX hign hconf hBind hslot
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
  refine ⟨⟨s', hSteps, hH⟩, ?_⟩
  intro s'' hS'' hH''
  rw [steps_halted_unique hS'' hSteps hH'' hH]
  exact hpost

end Lsc.Compiler
