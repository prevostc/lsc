import Lsc.Compiler.Correctness
import Lsc.Compiler.Externals
import Lsc.Compiler.Yul

/-!
S2 family `toYulFn` conclusion: every Yul run is predicted by Core under some
fault oracle, and every binding package's `RX` is preserved.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc

/-- Family backward `toYulFn`: every Yul run is predicted by Core, and every
package's `RX` holds. The one-binding case is `bs = [⟨α, bind⟩]`. -/
def ToYulFnCorrectExts {I : Interface} {S X E ε : Type}
    (bs : List (BindEnv I S X))
    (c : ContractDef) (Γ : ContractSchema S X E ε) (κ : List UInt8 → U256)
    (calls : ExternalCalls) (f : FnDef) (yul : YBlock)
    (ctx : Ctx) (w : World S X E) (st0 : EvmState) : Prop :=
  ∀ (st' : EvmState) (o : Outcome),
    Run (yulD calls) yul st0 [] st' o →
      ∃ fo : Nat → Bool,
        let wfo : World S X E := { w with faults := fo }
        let stObs := committedState st0 st'
        match Tx.run (Core.denote Γ f.core (decodeArgs f st0.env.calldata).reverse)
            ctx wfo with
        | .ok (v, w') =>
            o = Outcome.halt ∧ haltSuccess f.ret v stObs.halted ∧
              R c Γ κ w' stObs ∧ RXs bs w' stObs
        | .error e =>
            ∃ bytes, o = Outcome.halt ∧ stObs.halted = some (.revert, bytes) ∧
              haltError c Γ e bytes ∧ R c Γ κ w stObs

end Lsc.Compiler
