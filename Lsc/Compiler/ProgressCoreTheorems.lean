import Lsc.Compiler.Proof.ProgressCoreProof

set_option linter.unusedVariables false

/-!
S2 Yul progress: under `CallsTotal`, compiled S2Frag runtime has a halted
`Run`. Paired with EVM determinism this makes `EvmCallRunExtAll` non-vacuous.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

/-- There exists a halted Yul `Run` of the compiled S2 runtime from the
starting EVM state. The external CALL oracle is total (`CallsTotal`): every
CALL returns some bytes. Without this, powdr `compile_correct` is only
forward (`Yul Run → ∃ EVM Steps`) and the universal `EvmCallRunExtAll`
quantifier could be empty. Assumes S2Frag, `Conforms`, and the usual layout
bounds. -/
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
    ∃ st' o, Run (yulD calls) yul st0 [] st' o :=
  Proof.yul_progress bs c Γ hΓ κ hκ calls htot hctor hS2 hlen hbound yul hyul
    ctx w st0 hctx hR hconf hBind hslot

end Lsc.Compiler
