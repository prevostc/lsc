import Lsc.Compiler.DispatchDefs
import Lsc.Compiler.Proof.DispatchProof

/-!
Call-free ABI dispatcher: size guard, 4-byte selector, then the selected
function's Yul. Unknown selectors revert with empty data and storage
unchanged.

This is the Yul-level statement that the call-free bytecode theorem
lifts through the pinned Yul-to-EVM compiler. Every runtime function
must never CALL out; none may be a constructor.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

/-- A compiled call-free runtime agrees with the high-level model on every
calldata: a known selector runs the matching function; an unknown
selector or short calldata reverts with storage unchanged. Every runtime
function must never CALL out and must not be a constructor. This is the
Yul dispatcher that `bytecode_call_correct` lifts to EVM bytecode. -/
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
