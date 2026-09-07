import Lsc.Compiler.DeployProof
import YulEvmCompiler.ObjectCompile

set_option linter.unusedVariables false

/-!
EVM deploy via powdr `compileObject_correct`. Init frames have
`env.code = L.code` and empty calldata, so Solidity's appended constructor
args are not in this model.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open EvmSemantics.EVM (State Steps)

/-- If the Yul object runs to `yst`/`out`, every matching EVM start state with
enough gas has a `Steps` run to a halted frame matching `yst`. Returned bytes
are the Yul halt payload, not `compileRuntime` (nested `"runtime"` subobjects
are compiler artifacts). Does not cover CREATE with trailing constructor
args — use `constructor_correct` at Yul for those. -/
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
  Proof.bytecode_deploy_correct hexternal hcomp hrun

end Lsc.Compiler
