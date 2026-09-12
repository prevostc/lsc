import Lsc.Compiler.ExtOracleTheorems
import Lsc.Compiler.EndToEndExtDefs
import Lsc.Compiler.Proof.GasLift
import Lsc.Compiler.Proof.NoGas
import Lsc.Compiler.Proof.MemFootprintLift
import Lsc.Compiler.Proof.SpillPath
import YulEvmCompiler.Correctness
import YulEvmCompiler.LowerDefs
import YulEvmCompiler.Optimizer.Implementation.MemorySpillSound
import YulEvmCompiler.Optimizer.Implementation.MemorySpillLayoutSound

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
S2 `compileBlock` simulation at `openModel` (`gas := .none`). The erase
branch is ordinary `compile_correct`. The spill branch lifts the erased
run to `ExternalGas.any`, applies `GuardedRunOfErased` and
`spillBlockRunSound` under a memory-blind `ExtOracle`, then returns to
`.none` because Lsc never emits `gas()` (`noGas_spillBlock`).
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open YulEvmCompiler.Optimizer
open YulEvmCompiler.Optimizer.MemorySpill
open YulEvmCompiler.Optimizer.MemorySpillSelect
open YulEvmCompiler.Optimizer.MemorySpillSound
open EvmSemantics.EVM (State Steps)

/-- A Yul run of the memoryguard-erased runtime, at the S2 dialect, is
simulated by the pinned compiler on whichever `compileBlock` branch
succeeded. The EVM `StateMatch` final is the erased state on the erase
path and the spilled state (scratch-related to the erased final) on the
spill path. -/
theorem compileBlock_open_sim {o : ExtOracle} {c : ContractDef}
    {rt : YBlock} {is : List Instr} {yst0 yst' : EvmState} {out : Outcome}
    (hCalls : CallsRealized (toCalls o))
    (hrt : runtimeBlock c = some rt)
    (hcomp : compileBlock rt = some is)
    (himm : ∀ key, unpatchedImmutables key =
      yst0.env.immutable (YulSemantics.EVM.litValue (.string key)))
    (hrun : Run (yulD (toCalls o)) (eraseMemoryGuardStmts rt) yst0 [] yst' out) :
    ∃ bound : Nat, ∀ s0 : State,
      FrameOK (assemble is) s0 → StateMatch yst0 s0 →
      s0.pc = EvmSemantics.UInt256.ofNat 0 → s0.stack = [] →
      bound ≤ s0.gasAvailable →
      ∃ s' ystF, Steps s0 s' ∧ s'.callStack = [] ∧
        StateMatch ystF s' ∧
        ((out = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (out = .halt ∧ HaltedMatch ystF s')) ∧
        (compileErased rt = some is → ystF = yst') ∧
        (∀ r, compileErased rt = none → spillRuntime? rt = some r →
          ScratchRel r.base r.reserved yst' ystF) := by
  let _model : ExternalModel := openModel (toCalls o)
  cases compileBlock_elim hcomp with
  | inl hce =>
    have ⟨bound, hb⟩ :=
      compile_correct (externalsRealized_open hCalls) hce himm hrun
    refine ⟨bound, ?_⟩
    intro s0 hOK hM hpc hstk hgas
    obtain ⟨s', hSteps, hcs, hSM, hOut⟩ := hb s0 hOK hM hpc hstk hgas
    refine ⟨s', yst', hSteps, hcs, hSM, hOut, fun _ => rfl, ?_⟩
    intro r hne _
    exact absurd (hce.symm.trans hne) (by simp)
  | inr hspair =>
    obtain ⟨hne, hsp⟩ := hspair
    obtain ⟨r, hr, hcr⟩ := compileSpilled_inv hsp
    have hrunA :=
      run_none_to_any (calls := toCalls o) (creates := ExternalCreates.none) hrun
    have hG :=
      GuardedRunOfErased (calls := toCalls o) (creates := ExternalCreates.none)
        hrt hr hrunA
    have hrB : spillBlock? rt = some r := by simpa [spillRuntime?] using hr
    obtain ⟨_, hfacts⟩ := spillBlock_facts hrB
    have hexternals := guardedExternals_oracle o r.base r.reserved
    obtain ⟨_, ystF, hrunSp, hrel⟩ :=
      spillBlockRunSound (calls := toCalls o) (creates := ExternalCreates.none)
        hfacts hexternals hG
    have hng := noGas_spillBlock hrB (noGas_runtimeBlock hrt)
    have hrunSp0 :=
      run_any_to_none (calls := toCalls o) (creates := ExternalCreates.none)
        hng hrunSp
    have ⟨bound, hb⟩ :=
      compile_correct (externalsRealized_open hCalls) hcr himm hrunSp0
    refine ⟨bound, ?_⟩
    intro s0 hOK hM hpc hstk hgas
    obtain ⟨s', hSteps, hcs, hSM, hOut⟩ := hb s0 hOK hM hpc hstk hgas
    refine ⟨s', ystF, hSteps, hcs, hSM, hOut, ?_, ?_⟩
    · intro hce
      exact absurd (hne.symm.trans hce) (by simp)
    · intro r' _ hsp'
      have heq : r' = r := Option.some.inj (hsp'.symm.trans hr)
      exact heq ▸ hrel

end Lsc.Compiler
