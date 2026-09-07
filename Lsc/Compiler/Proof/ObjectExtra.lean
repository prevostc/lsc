import Lsc.Util.OpenPrivate
import YulEvmCompiler.ObjectCompile

open_private compileResolvedObject_compileWitness from YulEvmCompiler.ObjectCompile

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
`compileObject_correct` specialised to exact `L.code`. CREATE init-code carries
Solidity ABI constructor args *after* that bytecode. This module re-applies
`compile_correct_withPayload` with payload `(origPayload ++ extra)`, using the
private compile witness for the `L.code = exec ++ 0 :: origPayload` split.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open EvmSemantics
open EvmSemantics.EVM

variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates model.gas

/-- `L.initState` with trailing bytes appended to `env.code` (CREATE ABI args). -/
def initStateWithExtra (L : Layout) (extra : List UInt8) : EvmState :=
  { L.initState with env := { L.env with code := L.code ++ extra } }

theorem initStateWithExtra_nil (L : Layout) :
    initStateWithExtra L [] = L.initState := by
  unfold initStateWithExtra
  rw [List.append_nil, show { L.env with code := L.code } = L.env from rfl,
    show L.env = L.initState.env from rfl]

theorem initStateWithExtra_code (L : Layout) (extra : List UInt8) :
    (initStateWithExtra L extra).env.code = L.code ++ extra :=
  rfl

theorem initStateWithExtra_immutable (L : Layout) (extra : List UInt8) :
    (initStateWithExtra L extra).env.immutable = L.immutable :=
  rfl

/-- `RunResolvedObject` from `env.code = L.code ++ extra` rather than `L.code`. -/
def RunResolvedObjectWithExtra (o : Object Op) (L : Layout) (extra : List UInt8)
    (V : VEnv yulD) (st : EvmState) (out : Outcome) : Prop :=
  Run yulD (resolveForLayoutStmts L o.codeBlock)
    (initStateWithExtra L extra) V st out

/-- Appending `extra` extends the witness payload after the STOP seam. -/
theorem compileObject_code_append_extra
    {L : Layout} {instructions : _} {payload extra : List UInt8}
    (hcode : L.code = assembleBytes instructions ++ 0 :: payload) :
    L.code ++ extra = assembleBytes instructions ++ 0 :: (payload ++ extra) := by
  rw [hcode, List.append_assoc, List.cons_append]

/-- **Object compiler correctness with extra trailing bytes.** Same as
`compileObject_correct`, but the EVM frame is `FrameOK (mkCode (L.code ++ extra))`
and the Yul source runs from `initStateWithExtra L extra`
(`env.code = L.code ++ extra`). On `.halt`, `HaltedMatch` identifies the EVM
return bytes with the Yul halt payload (not with `compileRuntime`). -/
theorem compileObject_correct_withExtra (hexternal : ExternalsRealized model)
    {o : Object Op} {L : Layout} (extra : List UInt8)
    (hcomp : compileObject o = some L)
    {V : VEnv yulD} {yst : EvmState} {out : Outcome}
    (hrun : RunResolvedObjectWithExtra o L extra V yst out) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (mkCode (L.code ++ extra)) s0 →
      StateMatch (initStateWithExtra L extra) s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst s' ∧
        ((out = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (out = .halt ∧ HaltedMatch yst s')) := by
  obtain ⟨resolved, instructions, payload, hresolved, hinstructions, hcode⟩ :=
    compileResolvedObject_compileWitness hcomp
  have hrun' : Run yulD resolved (initStateWithExtra L extra) V yst out := by
    rw [hresolved]; exact hrun
  obtain ⟨bound, hsim⟩ :=
    compile_correct_withPayload hexternal (payload := payload ++ extra) hinstructions
      (fun key => by
        rw [initStateWithExtra_immutable, compileObject_immutable hcomp]
        rfl) hrun'
  refine ⟨bound, ?_⟩
  intro s0 hframe hmatch hpc hstack hgas
  apply hsim s0
  · simpa [assembleWithPayload, compileObject_code_append_extra hcode] using hframe
  · exact hmatch
  · exact hpc
  · exact hstack
  · exact hgas

/-- `extra = []` recovers `compileObject_correct`. -/
theorem compileObject_correct_withExtra_of_exact
    (hexternal : ExternalsRealized model)
    {o : Object Op} {L : Layout}
    (hcomp : compileObject o = some L)
    {V : VEnv yulD} {yst : EvmState} {out : Outcome}
    (hrun : RunResolvedObject o L V yst out) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (mkCode L.code) s0 → StateMatch L.initState s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst s' ∧
        ((out = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (out = .halt ∧ HaltedMatch yst s')) := by
  have hrun' : RunResolvedObjectWithExtra o L [] V yst out := by
    unfold RunResolvedObjectWithExtra
    rw [initStateWithExtra_nil]
    exact hrun
  obtain ⟨bound, hsim⟩ := compileObject_correct_withExtra hexternal [] hcomp hrun'
  refine ⟨bound, ?_⟩
  intro s0 hframe hmatch hpc hstack hgas
  have hframe' : FrameOK (mkCode (L.code ++ [])) s0 := by
    simpa [List.append_nil] using hframe
  have hmatch' : StateMatch (initStateWithExtra L []) s0 := by
    rwa [initStateWithExtra_nil]
  exact hsim s0 hframe' hmatch' hpc hstack hgas

end Lsc.Compiler
