import Lsc.Compiler.CoreDefs
import Lsc.Compiler.Correctness
import Lsc.Compiler.Proof.CoreProof

/-!
Call-free Core to Yul: if the compiler accepted a runtime function that
never CALLs out, running the emitted Yul has the same effect as the
high-level model.

This is the only Core-to-Yul theorem this repo owns for contracts like
Counter and Token; Yul-to-EVM is the pinned compiler's theorem. Shared
assumptions: lawful storage layout, keccak keys do not collide, and
field and ABI lengths fit in a word. Constructors are excluded.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

/-- If the compiler accepted a runtime function that never CALLs out, every
high-level outcome is matched by a Yul run of the emitted block: a
success agrees on return data, storage, and logs; a revert agrees on
error bytes and rolls storage back. The function must not be a
constructor. Counter and Token are instances; Vault and AMM need the
external-call form. -/
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
