import Lsc.Compiler.Proof.ProgressCoreProof
import YulEvmCompiler.Optimizer.Implementation.MemorySpill

set_option linter.unusedVariables false

/-!
Yul progress for contracts that CALL out: given a total CALL oracle
(every CALL returns some bytes), compiled runtime has a halted Yul run.

Paired with EVM determinism this makes "every matching EVM execution"
non-vacuous: the Yul-to-EVM compiler is only forward, so without a run
the universal bytecode statement could hold of nothing.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

/-- There exists a halted Yul run of the compiled runtime from the starting
EVM state, provided every CALL returns some bytes. Without this, "every
matching EVM execution agrees with the model" could hold vacuously,
because the Yul-to-EVM compiler only goes forward from a Yul run. Bound
tokens must conform; constructors are excluded. -/
theorem yul_progress {I : Interface} {S X E ε : Type}
    (bs : List (BindEnv I S X)) (c : ContractDef) (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (calls : ExternalCalls) (htot : CallsTotal calls)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : runtimeBlock c = some yul)
    (ctx : Ctx) (w : World S X E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0)
    (hconf : BindEnvs.conforms bs ctx.self w.self calls)
    (hBind : BindEnvs.lookupWF c Γ bs)
    (hslot : ∀ f ∈ c.functions, BindEnvs.avoids Γ c bs f.core) :
    ∃ st' o, Run (yulD calls)
      (YulEvmCompiler.Optimizer.MemorySpill.eraseMemoryGuardStmts yul) st0 [] st' o :=
  Proof.yul_progress bs c Γ hΓ κ hκ calls htot hctor hS2 hlen hbound yul hyul
    ctx w st0 hctx hR hconf hBind hslot

end Lsc.Compiler
