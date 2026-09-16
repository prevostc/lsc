import Lsc.Compiler.DispatchTheorems
import Lsc.Compiler.Proof.Lift
import Lsc.Compiler.Proof.Calldata
import Lsc.Compiler.EvmDetTheorems
import Lsc.Compiler.Bytecode
import Lsc.Compiler.YulExec
import Lsc.Security.Trace
import YulEvmCompiler.Correctness
import YulEvmCompiler.LowerDefs
import YulEvmCompiler.Optimizer.Implementation.MemorySpill
import Lsc.Compiler.Proof.SpillPath
import Lsc.Compiler.Proof.MemFootprintLift

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
End-to-end glue: call-free `RunCommitted` → powdr `compile_correct` → EVM `Steps`.
`EvmCallRun` is universal over halted executions (`steps_halted_unique`).
The compiler still does not import `Security` except in this module.
-/

namespace Lsc.Compiler

open Lsc
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open YulEvmCompiler.Optimizer
open YulEvmCompiler.Optimizer.MemorySpill
open YulEvmCompiler.Optimizer.MemorySpillSelect
open YulEvmCompiler.Optimizer.MemorySpillStateSound
open EvmSemantics.EVM (State Steps)

/-- Keccak oracle forced by `EnvMatch.keccak` (`targetKeccakOracle_agrees`). -/
abbrev evmKeccak : List UInt8 → U256 := targetKeccakOracle

@[instance_reducible] def closedModel : ExternalModel where
  calls := ExternalCalls.none
  creates := ExternalCreates.none

def ofConv (v : EvmSemantics.UInt256) : U256 := BitVec.ofNat 256 v.toNat


/-- Yul storage recovered from the executing account through `conv`. -/
def accountYulStorage (s : State) : U256 → U256 :=
  fun k => ofConv ((s.accountMap s.executionEnv.address).storage.get (conv k))

/-- Yul `storageOf` recovered from every EVM account through `conv`.
`StateMatch.externalCode.storage` identifies this with `evmForeign yst`. -/
def accountForeign (s : State) : Foreign :=
  fun addr slot =>
    ofConv ((s.accountMap (EvmSemantics.AccountAddress.ofUInt256 (conv addr))).storage.get
      (conv slot))

def storageRel' {S X E ε} (c : ContractDef) (Γ : ContractSchema S X E ε)
    (κ : List UInt8 → U256) (σ : S) (s : State) : Prop :=
  storageRel c Γ κ σ (accountYulStorage s)

def haltOK (t : RetTy) (v : t.denote) (s : State) : Prop :=
  if t = .unit then s.halt = .Success
  else s.halt = .Returned ∧ s.hReturn.toList = abiBytes (retWords (t := t) v)


/-- Observable post-storage of a top-level halted frame. Revert rollback is a
modelling assumption (`TRUSTED_COMPUTING_BASE.md`): raw `Steps` does not roll back. -/
def postStorage (yst0 : EvmState) (s' : State) : U256 → U256 :=
  match s'.halt with
  | .Reverted => yst0.storage
  | _ => accountYulStorage s'


/-- Observable post-foreign-storage of a top-level halted frame. Revert restores
the pre-state `storageOf` map, matching `postStorage`. -/
def postForeign (yst0 : EvmState) (s' : State) : Foreign :=
  match s'.halt with
  | .Reverted => evmForeign yst0
  | _ => accountForeign s'


def EvmStartOK (is : List Instr) (yst0 : EvmState) (s0 : State) : Prop :=
  FrameOK (assemble is) s0 ∧ StateMatch yst0 s0 ∧
  s0.pc = EvmSemantics.UInt256.ofNat 0 ∧ s0.stack = []

def setGas (s : State) (g : Nat) : State :=
  { s with gasAvailable := g }


/-- One compiled call: every matching start state with enough gas has a halted
`Steps` run, and **every** halted run determines the same post-storage `σ'`. -/
def EvmCallRun (is : List Instr) (yst0 : EvmState) (σ' : U256 → U256) : Prop :=
  ∃ b : Nat, ∀ s0 : State,
    EvmStartOK is yst0 s0 → b ≤ s0.gasAvailable →
    (∃ s', Steps s0 s' ∧ Halted s') ∧
    ∀ s', Steps s0 s' → Halted s' → σ' = postStorage yst0 s'


/-- Like `EvmCallRun`, also pinning post-foreign-storage `ξ'`. -/
def EvmCallRunξ (is : List Instr) (yst0 : EvmState)
    (σ' : U256 → U256) (ξ' : Foreign) : Prop :=
  ∃ b : Nat, ∀ s0 : State,
    EvmStartOK is yst0 s0 → b ≤ s0.gasAvailable →
    (∃ s', Steps s0 s' ∧ Halted s') ∧
    ∀ s', Steps s0 s' → Halted s' →
      σ' = postStorage yst0 s' ∧ ξ' = postForeign yst0 s'


structure EvmCall where
  ctx : Ctx
  calldata : List UInt8

inductive EvmTraceRun (is : List Instr) : List EvmCall → (U256 → U256) → (U256 → U256) → Prop
  | nil (σ : U256 → U256) : EvmTraceRun is [] σ σ
  | cons {call : EvmCall} {tr : List EvmCall} {σ σ₁ σ' : U256 → U256} {yst0 : EvmState}
      (hcd : yst0.env.calldata = call.calldata)
      (hσ : yst0.storage = σ)
      (h1 : EvmCallRun is yst0 σ₁)
      (htl : EvmTraceRun is tr σ₁ σ') :
      EvmTraceRun is (call :: tr) σ σ'

/-- Universal trace: each call is an `EvmCallRun` at `mkEvmState` of that
call, witnessed by some matching start state (so post-storage is unique). -/
inductive EvmTraceRunAll (is : List Instr) : List EvmCall → (U256 → U256) → (U256 → U256) → Prop
  | nil (σ : U256 → U256) : EvmTraceRunAll is [] σ σ
  | cons {call : EvmCall} {tr : List EvmCall} {σ σ₁ σ' : U256 → U256} {s0 : State}
      (hstart : EvmStartOK is (mkEvmState call.calldata σ evmKeccak call.ctx) s0)
      (h1 : EvmCallRun is (mkEvmState call.calldata σ evmKeccak call.ctx) σ₁)
      (htl : EvmTraceRunAll is tr σ₁ σ') :
      EvmTraceRunAll is (call :: tr) σ σ'

/-- Runtime trace starting from storage produced by a constructor (`constructor_correct`
gives `storageRel` of `w₁`), not from an assumed pre-state. `compileObject_correct`
cannot discharge this for appended CREATE args (see `Deploy.lean`). -/
def EvmDeployThenTrace (is : List Instr) (σ0 : U256 → U256)
    (tr : List EvmCall) (σ' : U256 → U256) : Prop :=
  EvmTraceRunAll is tr σ0 σ'

/-- Dispatcher conclusion, interpreted on the compiled bytecode. -/
def BytecodeCallCorrect {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε) (κ : List UInt8 → U256)
    (ctx : Ctx) (w : World S X E) (yst0 : EvmState) (is : List Instr) : Prop :=
  ∃ b : Nat, ∀ s0 : State,
    FrameOK (assemble is) s0 → StateMatch yst0 s0 →
    s0.pc = EvmSemantics.UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
    ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧
      match dispatchedFn c yst0.env.calldata ctx.value with
      | none => s'.halt = .Reverted ∧ s'.hReturn.toList = []
      | some f =>
        if f.payable && yst0.env.selfBalance.ult yst0.env.callvalue then
          s'.halt = .Reverted ∧ s'.hReturn.toList = []
        else
          match Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse) ctx w with
          | .ok (v, w') => haltOK f.ret v s' ∧ storageRel' c Γ κ w'.self s'
          | .error e =>
            s'.halt = .Reverted ∧ ∃ bytes, s'.hReturn.toList = bytes ∧ haltError c Γ e bytes


/-- Fold `Core.denote` like `Security.run` on encoded `(ctx, fn, args)` calls. -/
def coreRun {S X E ε : Type} (Γ : ContractSchema S X E ε) :
    List (Ctx × FnDef × List Nat) → World S X E → World S X E
  | [], w => w
  | (ctx, f, args) :: rest, w =>
    coreRun Γ rest
      { Security.worldAfter (Core.denote Γ f.core args.reverse) ctx w with log := [] }


end Lsc.Compiler

