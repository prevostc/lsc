import Lsc.Compiler.EndToEnd
import Lsc.Compiler.EndToEndTheorems
import Lsc.Compiler.EvmDetDefs
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

/-- Given a Yul run, Core with `w.oracle = Oracle.ofExt o` predicts the
committed observation. -/
def EvmCallRunExt {S E ε : Type}
    (c : ContractDef) (Γ : ContractSchema S ExtState E ε) (κ : List UInt8 → U256)
    (o : ExtOracle) (ctx : Ctx) (w : World S ExtState E)
    (yst0 st' : EvmState) (out : Outcome) : Prop :=
  let stObs := committedState yst0 st'
  match dispatchedFn c yst0.env.calldata ctx.value with
  | none =>
      out = Outcome.halt ∧ stObs.halted = some (.revert, []) ∧ R c Γ κ w stObs
  | some f =>
      if f.payable && yst0.env.selfBalance.ult yst0.env.callvalue then
        out = Outcome.halt ∧ stObs.halted = some (.revert, []) ∧ R c Γ κ w stObs
      else
        match Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse)
            ctx w with
        | .ok (v, w') =>
            out = Outcome.halt ∧ haltSuccess f.ret v stObs.halted ∧
              R c Γ κ w' stObs ∧ ExtAgree ctx.self w'.ext stObs
        | .error e =>
            ∃ bytes, out = Outcome.halt ∧ stObs.halted = some (.revert, bytes) ∧
              haltError c Γ e bytes ∧ R c Γ κ w stObs

/-- Backward bytecode theorem: every Yul `Run` of the compiled runtime is
predicted (`EvmCallRunExt`) and has matching EVM `Steps` (`compile_correct`).
Every halted `Steps` from a matching start has the same post-storage and
post-foreign-storage. -/
def BytecodeCallCorrectExt {S E ε : Type}
    (c : ContractDef) (Γ : ContractSchema S ExtState E ε) (κ : List UInt8 → U256)
    (o : ExtOracle) (ctx : Ctx) (w : World S ExtState E)
    (yst0 : EvmState) (rt : YBlock) (is : List Instr) : Prop :=
  ∀ (st' : EvmState) (out : Outcome),
    Run (yulD (toCalls o))
        (YulEvmCompiler.Optimizer.MemorySpill.eraseMemoryGuardStmts rt)
        yst0 [] st' out →
      EvmCallRunExt c Γ κ o ctx w yst0 st' out ∧
      EvmCallRunξ is yst0 (committedState yst0 st').storage
        (evmForeign (committedState yst0 st'))

/-- Universal over halted EVM runs: some gas bound, a halted `Steps` exists,
every halted `Steps` has post-storage `σ'` and post-foreign-storage `ξ'`,
and Core predicts that storage. -/
def EvmCallRunExtAll {S E ε : Type}
    (c : ContractDef) (Γ : ContractSchema S ExtState E ε) (κ : List UInt8 → U256)
    (o : ExtOracle) (ctx : Ctx) (w : World S ExtState E)
    (is : List Instr) (yst0 : EvmState) (σ' : U256 → U256) (ξ' : Foreign) : Prop :=
  ∃ b : Nat, ∀ s0 : State,
    EvmStartOK is yst0 s0 → b ≤ s0.gasAvailable →
    (∃ s', Steps s0 s' ∧ Halted s') ∧
    ∀ s', Steps s0 s' → Halted s' →
      σ' = postStorage yst0 s' ∧ ξ' = postForeign yst0 s' ∧
      match dispatchedFn c yst0.env.calldata ctx.value with
      | none => σ' = yst0.storage ∧ ξ' = evmForeign yst0
      | some f =>
          if f.payable && yst0.env.selfBalance.ult yst0.env.callvalue then
            σ' = yst0.storage ∧ ξ' = evmForeign yst0
          else
            match Tx.run (Core.denote Γ f.core (decodeArgs f yst0.env.calldata).reverse)
                ctx w with
            | .ok (_, w') =>
                storageRel c Γ κ w'.self σ' ∧
                  ∃ stObs : EvmState, stObs.storage = σ' ∧ evmForeign stObs = ξ' ∧
                    R c Γ κ w' stObs ∧ ExtAgree ctx.self w'.ext stObs
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
