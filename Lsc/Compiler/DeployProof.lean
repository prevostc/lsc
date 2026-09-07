import Lsc.Compiler.Proof.ConstructorProof
import Lsc.Compiler.Bytecode
import YulEvmCompiler.ObjectCompile
import YulEvmCompiler.OpStep

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Proof of `bytecode_deploy_correct`. Statement lives in `DeployTheorems`.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open EvmSemantics.EVM (State Steps)

namespace Proof
/-- Object compiler correctness, specialized to our deploy objects. Returned
bytes (on `.halt` / `HaltedMatch`) are the Yul halt payload; they are **not**
identified with `compileRuntime` (`Layout.Consistent` covers data segments,
not nested `"runtime"` subobjects). -/
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

end Proof

/-- After a successful Yul constructor (`constructor_correct`), `storageRel`
holds of the post-world. Runtime traces start from that storage rather than
an assumed `storageRel` of an arbitrary pre-state. -/
theorem storageRel_of_ctor {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ : List UInt8 → U256} {w : World S X E} {st : EvmState}
    (h : R c Γ κ w st) : storageRel c Γ κ w.self st.storage :=
  h.1

end Lsc.Compiler
