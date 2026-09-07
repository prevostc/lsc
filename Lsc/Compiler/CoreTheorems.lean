import Lsc.Compiler.CoreDefs
import Lsc.Compiler.Correctness
import Lsc.Compiler.Proof.CoreProof

/-!
S1 Core → Yul: a call-free function's compiled Yul block matches `Core.denote`
under the layout relation `R`. This is the only compiler theorem this repo
owns for the call-free fragment; Yul → EVM is powdr's `compile_correct`.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

/-- If `f` is a runtime (non-constructor) call-free function and `toYulFn`
succeeds, every `Core.denote` outcome is matched by a committed Yul `Run` of
the emitted block: success agrees on return data and on storage/logs via `R`;
a revert agrees on error bytes and rolls `R` back to the pre-state. Assumes
the storage schema is lawful, keccak is injective on the keys this contract
uses, and field/ABI lengths fit in a word. Counter and Token are instances. -/
theorem toYulFn_correct_callFree {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε)
    (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
    (f : FnDef) (hf : f.kind ≠ .constructor)
    (hM1 : CallFree f.core) (hlen : c.fields.length < wordBound)
    (hbound : 4 + 32 * f.params.length < wordBound)
    (yul : YBlock) (hyul : toYulFn c f = some yul)
    (ctx : Ctx) (w : World S X E) (st0 : EvmState)
    (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0) :
    ToYulFnCorrect c Γ κ f yul ctx w st0 :=
  Proof.toYulFn_correct_callFree c Γ hΓ κ hκ f hf hM1 hlen hbound yul hyul ctx w st0 hctx hR

end Lsc.Compiler
