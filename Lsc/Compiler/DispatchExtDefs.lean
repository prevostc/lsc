import Lsc.Compiler.Correctness
import Lsc.Compiler.ExtOracle
import Lsc.Compiler.Yul
import YulEvmCompiler.Optimizer.Implementation.MemorySpill

/-!
S2 dispatcher conclusion: every Yul run of the runtime block is predicted by
the selected `Core.denote` under `Oracle.ofExt`.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc

def RuntimeBlockCorrectExt {S E ε : Type}
    (c : ContractDef) (Γ : ContractSchema S ExtState E ε) (κ : List UInt8 → U256)
    (o : ExtOracle) (yul : YBlock) (ctx : Ctx) (w : World S ExtState E)
    (st0 : EvmState) : Prop :=
  ∀ (st' : EvmState) (out : Outcome),
    Run (yulD (toCalls o))
        (YulEvmCompiler.Optimizer.MemorySpill.eraseMemoryGuardStmts yul)
        st0 [] st' out →
      let stObs := committedState st0 st'
      match dispatchedFn c st0.env.calldata ctx.value with
      | none =>
          out = Outcome.halt ∧ stObs.halted = some (.revert, []) ∧ R c Γ κ w stObs
      | some f =>
          match Tx.run (Core.denote Γ f.core (decodeArgs f st0.env.calldata).reverse)
              ctx w with
          | .ok (v, w') =>
              out = Outcome.halt ∧ haltSuccess f.ret v stObs.halted ∧
                R c Γ κ w' stObs ∧ ExtAgree ctx.self w'.ext stObs
          | .error e =>
              ∃ bytes, out = Outcome.halt ∧ stObs.halted = some (.revert, bytes) ∧
                haltError c Γ e bytes ∧ R c Γ κ w stObs

abbrev RuntimeBlockCorrectExts {S E ε : Type} :=
  @RuntimeBlockCorrectExt S E ε

end Lsc.Compiler
