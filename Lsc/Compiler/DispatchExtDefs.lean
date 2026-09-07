import Lsc.Compiler.Correctness
import Lsc.Compiler.Externals
import Lsc.Compiler.Yul

/-!
S2 dispatcher conclusion: every Yul run of the runtime block is predicted by
the selected `Core.denote` under some fault oracle.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc

def RuntimeBlockCorrectExts {I : Interface} {S X E ε : Type}
    (bs : List (BindEnv I S X))
    (c : ContractDef) (Γ : ContractSchema S X E ε) (κ : List UInt8 → U256)
    (calls : ExternalCalls) (yul : YBlock) (ctx : Ctx) (w : World S X E)
    (st0 : EvmState) : Prop :=
  ∀ (st' : EvmState) (o : Outcome),
    Run (yulD calls) yul st0 [] st' o →
      ∃ fo : Nat → Bool,
        let wfo : World S X E := { w with faults := fo }
        let stObs := committedState st0 st'
        match selectedFn c st0.env.calldata with
        | none =>
            o = Outcome.halt ∧ stObs.halted = some (.revert, []) ∧ R c Γ κ w stObs
        | some f =>
            match Tx.run (Core.denote Γ f.core (decodeArgs f st0.env.calldata).reverse)
                ctx wfo with
            | .ok (v, w') =>
                o = Outcome.halt ∧ haltSuccess f.ret v stObs.halted ∧
                  R c Γ κ w' stObs ∧ RXs bs w' stObs
            | .error e =>
                ∃ bytes, o = Outcome.halt ∧ stObs.halted = some (.revert, bytes) ∧
                  haltError c Γ e bytes ∧ R c Γ κ w stObs

end Lsc.Compiler
