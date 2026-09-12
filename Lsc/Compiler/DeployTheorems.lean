import Lsc.Compiler.Proof.DeployProof
import YulEvmCompiler.ObjectCompile

set_option linter.unusedVariables false

/-!
EVM deploy of a compiled Yul object. Init frames have empty calldata and
init code equal to the object's code, so Solidity's appended constructor
arguments are not in this model.

Use `constructor_correct` at Yul for CREATE with trailing args. Token's
deploy-then-runtime theorem starts from a post-constructor state for
that reason.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open EvmSemantics.EVM (State Steps)

/-- If the compiled Yul object runs to a given halt, every matching EVM
start state with enough gas has a halted run that matches it. Returned
bytes are the Yul halt payload, not a nested "runtime" subobject.
Does not cover CREATE with trailing constructor arguments — Token's
constructor args live in that gap; use the Yul constructor theorem
there. -/
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
