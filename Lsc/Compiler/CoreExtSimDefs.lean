import Lsc.Compiler.Correctness
import Lsc.Compiler.ExtOracle
import Lsc.Compiler.Yul

/-!
S2 `toYulFn` conclusion: every Yul run is predicted by Core under
`Oracle.ofExt`, with `ExtAgree` in place of the old binding-ghost `RX`.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc

/-- Backward `toYulFn` for the call-carrying fragment. Every Yul run of the
emitted block is predicted by `Core.denote` with `w.oracle = Oracle.ofExt o`.
Reentrancy is excluded by `NoReentry` on the theorems that inhabit this. -/
def ToYulFnCorrectExt {S E ε : Type}
    (c : ContractDef) (Γ : ContractSchema S ExtState E ε) (κ : List UInt8 → U256)
    (o : ExtOracle) (f : FnDef) (yul : YBlock)
    (ctx : Ctx) (w : World S ExtState E) (st0 : EvmState) : Prop :=
  ∀ (st' : EvmState) (out : Outcome),
    Run (yulD (toCalls o)) yul st0 [] st' out →
      let stObs := committedState st0 st'
      match Tx.run (Core.denote Γ f.core (decodeArgs f st0.env.calldata).reverse)
          ctx w with
      | .ok (v, w') =>
          out = Outcome.halt ∧ haltSuccess f.ret v stObs.halted ∧
            R c Γ κ w' stObs ∧ ExtAgree ctx.self w'.ext stObs
      | .error e =>
          ∃ bytes, out = Outcome.halt ∧ stObs.halted = some (.revert, bytes) ∧
            haltError c Γ e bytes ∧ R c Γ κ w stObs

/-- Family name kept for the dispatcher/glue layering. Same as
`ToYulFnCorrectExt`. -/
abbrev ToYulFnCorrectExts {S E ε : Type} :=
  @ToYulFnCorrectExt S E ε

end Lsc.Compiler
