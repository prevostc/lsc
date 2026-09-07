import Lsc.Compiler.Proof.Constructor
import Lsc.Compiler.Bytecode
import YulEvmCompiler.ObjectCompile
import YulEvmCompiler.OpStep

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
EVM deploy via powdr `compileObject_correct`.

`compileObject_correct` runs the object from `L.initState` (`env.code = L.code`,
empty calldata) under `FrameOK (mkCode L.code)`. That **cannot** express
Solidity's appended constructor args (`codesize = L.code.length + 32n`).
The Yul theorem `constructor_correct` uses `st0.env.code` suffix instead.
The witness `compileResolvedObject_compileWitness` is private, so we cannot
re-apply `compile_correct_withPayload` with extra trailing bytes.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open EvmSemantics.EVM (State Steps)

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

/-- After a successful Yul constructor (`constructor_correct`), `storageRel`
holds of the post-world. Runtime traces start from that storage rather than
an assumed `storageRel` of an arbitrary pre-state. -/
theorem storageRel_of_ctor {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ : List UInt8 → U256} {w : World S X E} {st : EvmState}
    (h : R c Γ κ w st) : storageRel c Γ κ w.self st.storage :=
  h.1

end Lsc.Compiler
