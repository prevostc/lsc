import Lsc.Compiler.Bytecode
import Lsc.Compiler.CorrectnessDefs
import YulEvmCompiler.ObjectCompile

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Proof of `bytecode_deploy_correct` and `deploy_installs_runtime`.
Statements live in `DeployTheorems`.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open EvmSemantics.EVM (State Steps)

namespace Proof

/-- Object compiler correctness, specialized to our deploy objects. -/
theorem bytecode_deploy_correct
    [model : ExternalModel] (hexternal : ExternalsRealized model)
    {o : Object YulSemantics.EVM.Op} {L : Layout}
    (hcomp : compileObject o = some L)
    {V : VEnv (evmWithExternal model.calls model.creates model.gas)}
    {yst : EvmState} {out : Outcome}
    (hrun : RunResolvedObject o L V yst out) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (mkCode L.code) s0 → StateMatch L.initState s0 →
      s0.pc = EvmSemantics.UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst s' ∧
        ((out = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (out = .halt ∧ HaltedMatch yst s')) :=
  compileObject_correct hexternal hcomp hrun

theorem deployObject_dataSegs {c : ContractDef} {rt : List UInt8} {o : YObject}
    (h : deployObject c rt = some o) :
    o.dataSegs = [("runtime", Data.hex rt)] ∧ o.subObjects = [] := by
  simp only [deployObject, Option.map_eq_some_iff] at h
  obtain ⟨_, _, rfl⟩ := h
  exact ⟨rfl, rfl⟩

theorem compileDeploy_inv {c : ContractDef} {d : List UInt8}
    (hd : compileDeploy c = some d) :
    ∃ rt o L,
      compileRuntime c = some rt ∧
      deployObject c rt = some o ∧
      compileObject o = some L ∧
      L.code = d := by
  simp only [compileDeploy, Option.bind_eq_bind] at hd
  obtain ⟨rt, hrt, hd⟩ := Option.bind_eq_some_iff.mp hd
  obtain ⟨o, ho, hd⟩ := Option.bind_eq_some_iff.mp hd
  obtain ⟨L, hL, hd⟩ := Option.map_eq_some_iff.mp hd
  exact ⟨rt, o, L, hrt, ho, hL, hd⟩

theorem deploy_installs_runtime {c : ContractDef} {rt d : List UInt8}
    (hrt : compileRuntime c = some rt)
    (hd : compileDeploy c = some d) :
    ∃ (o : YObject) (L : Layout),
      deployObject c rt = some o ∧
      compileObject o = some L ∧
      L.code = d ∧
      o.dataSegs = [("runtime", Data.hex rt)] ∧
      L.Consistent o ∧
      readBytes (byteFrom L.code)
        (L.dataOffset (litValue (.string "runtime"))).toNat rt.length = rt := by
  simp only [compileDeploy] at hd
  rw [hrt] at hd
  change (deployObject c rt).bind
      (fun o => (compileObject o).map (·.code)) = some d at hd
  obtain ⟨o, ho, hd⟩ := Option.bind_eq_some_iff.mp hd
  obtain ⟨L, hL, hcode⟩ := Option.map_eq_some_iff.mp hd
  have hseg := (deployObject_dataSegs ho).1
  have hcons : L.Consistent o := compileObject_consistent hL
  have hmem : ("runtime", Data.hex rt) ∈ o.dataSegs := by
    simp [hseg]
  obtain ⟨_, hbytes⟩ := hcons _ hmem
  refine ⟨o, L, ho, hL, hcode, hseg, hcons, ?_⟩
  simpa [Data.size, Data.bytes] using hbytes

end Proof

/-- After a successful Yul constructor (`constructor_correct`), `storageRel`
holds of the post-world. Runtime traces start from that storage rather than
an assumed `storageRel` of an arbitrary pre-state. -/
theorem storageRel_of_ctor {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ : List UInt8 → U256} {w : World S X E} {st : EvmState}
    (h : R c Γ κ w st) : storageRel c Γ κ w.self st.storage :=
  h.1

end Lsc.Compiler
