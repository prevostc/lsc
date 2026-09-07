import Lsc.Compiler.DispatchDefs
import Lsc.Compiler.Proof.DispatchProof

/-!
S1 ABI dispatcher: calldata size guard + 4-byte selector `switch`, then the
selected function's Yul. Unknown selectors revert with empty data.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

/-- A compiled call-free runtime block matches `Core.denote` of the selected
function (or reverts like the Lean dispatcher on a bad selector / short
calldata). Assumes every runtime function is `CallFree`, none is a
constructor, and the usual lawful-layout / keccak-separation / word-bound
hypotheses. This is the Yul-level statement that `bytecode_call_correct`
lifts through powdr. -/
theorem runtimeBlock_correct_callFree {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (hcf : ∀ f ∈ c.functions, CallFree f.core)
    (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
    (hlen : c.fields.length < wordBound)
    (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : runtimeBlock c = some yul)
    (ctx : Ctx) (w : World S X E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0) :
    RuntimeBlockCorrectCallFree c Γ κ yul ctx w st0 :=
  Proof.runtimeBlock_correct_callFree c Γ hΓ κ hκ hcf hctor hlen hbound yul hyul ctx w st0 hctx hR

end Lsc.Compiler
