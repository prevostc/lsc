import Lsc.Compiler.DispatchExtDefs
import Lsc.Compiler.Proof.DispatchExtProof

set_option linter.unusedVariables false

/-!
ABI dispatcher for contracts that CALL out: same size guard and
selector as the call-free dispatcher, but the selected body may CALL.
Unknown selectors still revert with empty data.

`NoReentry o ctx.self` is the only assumption about the callee
(reentrancy is not modelled); everything else is adversarial. This is
the Yul dispatcher that `bytecode_call_correct_ext` lifts to EVM bytecode.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

/-- A compiled runtime that may CALL out agrees with the high-level model
on every calldata: a known selector runs the matching function under
`w.oracle = Oracle.ofExt o`; an unknown selector reverts with storage
unchanged. Reentrancy is not modelled (`NoReentry`); everything else
about the callee is adversarial. This is the Yul dispatcher that
`bytecode_call_correct_ext` lifts to bytecode. -/
theorem runtimeBlock_correct_ext {S E ε : Type}
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
    (hAgr : ExtAgree ctx.self w.ext st0)
    (hOr : w.oracle = Oracle.ofExt o)
    (hNR : ExtOracle.NoReentry o ctx.self) :
    RuntimeBlockCorrectExt c Γ κ o yul ctx w st0 :=
  Proof.runtimeBlock_correct_ext c Γ hΓ κ hκ o hctor hS2 hlen hbound yul hyul
    ctx w st0 hctx hR hAgr hOr hNR

end Lsc.Compiler
