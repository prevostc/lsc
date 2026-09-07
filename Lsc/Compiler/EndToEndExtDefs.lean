import Lsc.Compiler.EndToEnd
import Lsc.Compiler.EvmDetDefs
import Lsc.Compiler.Externals
import Lsc.Compiler.ExtOracle
import YulEvmCompiler.Optimizer.Implementation.MemorySpill
import YulEvmCompiler.LowerDefs

set_option linter.unusedVariables false

/-!
S2 glue definitions: open external model, Yul-run prediction, and universal
EVM-run conclusions used by `bytecode_call_correct_ext`.
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
    (bs : List (BindEnv I S X))
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
              R c Γ κ w' stObs ∧ RXs bs w' stObs
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
    (bs : List (BindEnv I S X))
    (c : ContractDef) (Γ : ContractSchema S X E ε) (κ : List UInt8 → U256)
    (calls : ExternalCalls) (ctx : Ctx) (w : World S X E)
    (yst0 : EvmState) (rt : YBlock) (is : List Instr) : Prop :=
  ∀ (st' : EvmState) (o : Outcome),
    Run (yulD calls) (YulEvmCompiler.Optimizer.MemorySpill.eraseMemoryGuardStmts rt)
        yst0 [] st' o →
      EvmCallRunExt bs c Γ κ calls ctx w yst0 st' o ∧
      EvmCallRunξ is yst0 (committedState yst0 st').storage
        (evmForeign (committedState yst0 st'))

/-- Universal over halted EVM runs: some gas bound, a halted `Steps` exists, every
halted `Steps` has post-storage `σ'` and post-foreign-storage `ξ'`, and Core
under some `fo` predicts that storage (`storageRel` / `RX` on a witnessing
committed Yul state whose `foreign` is `ξ'`). `ξ'` is read from the halted
EVM account map (`postForeign`); `StateMatch.externalCode.storage` identifies
it with Yul `foreign`. -/
def EvmCallRunExtAll {I : Interface} {S X E ε : Type}
    (bs : List (BindEnv I S X))
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
                    R c Γ κ w' stObs ∧ RXs bs w' stObs
            | .error _ => σ' = yst0.storage ∧ ξ' = evmForeign yst0

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

end Lsc.Compiler
