import Lsc.Compiler.Proof.ProgressCoreProof
import YulEvmCompiler.Optimizer.Implementation.MemorySpill

set_option linter.unusedVariables false

/-!
Yul progress for contracts that CALL out: given a memory-blind oracle,
compiled runtime has a halted Yul run.

Paired with EVM determinism this makes "every matching EVM execution"
non-vacuous: the Yul-to-EVM compiler is only forward, so without a run
the universal bytecode statement could hold of nothing.

`NoReentry o ctx.self` is the only assumption about the callee
(reentrancy is not modelled); everything else is adversarial.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

/-- There exists a halted Yul run of the compiled runtime from the starting
EVM state. The CALL oracle is total by construction (`toCalls o`). Without
this, "every matching EVM execution agrees with the model" could hold
vacuously, because the Yul-to-EVM compiler only goes forward from a Yul
run. Reentrancy is not modelled (`NoReentry`); constructors are excluded. -/
theorem yul_progress {S E ε : Type}
    (c : ContractDef) (Γ : ContractSchema S ExtState E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (o : ExtOracle)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : runtimeBlock c = some yul)
    (ctx : Ctx) (w : World S ExtState E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0)
    (hNR : ExtOracle.NoReentry o ctx.self) :
    ∃ st' out, Run (yulD (toCalls o))
      (YulEvmCompiler.Optimizer.MemorySpill.eraseMemoryGuardStmts yul) st0 [] st' out :=
  Proof.yul_progress c Γ hΓ κ hκ o hctor hS2 hlen hbound yul hyul
    ctx w st0 hctx hR hNR

end Lsc.Compiler
