import Examples.Amm.CompileDefs
import Examples.Amm.CompileProof
import Examples.Amm.Contract
import Stdlib.ERC20

/-!
AMM's compiler instance: every runtime function, including swaps and
liquidity that CALL two tokens, compiles to Yul that matches the
high-level pool model.

Shared assumptions: the compiler accepted the function, both tokens
behave like conforming ERC-20s at distinct addresses other than the
pool, and the EVM frame matches the starting world. The constructor
writes the token slots and is out of scope.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc.Stdlib

/-- If the compiler accepted an AMM runtime function, every execution of
the emitted Yul is predicted by the high-level pool model under some
choice of which external calls fail. Both tokens must behave like
conforming ERC-20s, at distinct addresses different from the pool.
Unlike `vault_correct_ext` this is two callees, not one. Constructors
are excluded. -/
theorem amm_correct_ext
    (α : Abs IERC20.Ghost)
    (κ : List UInt8 → U256) (hκ : KeccakSep Amm.contract κ)
    (calls : ExternalCalls)
    (f : FnDef) (hf : f ∈ Amm.contract.functions)
    (_hk : f.kind ≠ .constructor)
    (yul : YBlock) (hyul : toYulFn Amm.contract f = some yul)
    (ctx : Ctx) (w : World Amm.Storage Amm.Ext Amm.Event) (st0 : EvmState)
    (hctx : ctxRel ctx st0)
    (hR : R Amm.contract Amm.schema κ w st0)
    (hRX : RXs (ammBs α) w st0) (hign : α.ignoresLocal)
    (hBindNe : BindEnvs.neSelf (ammBs α) ctx.self w.self)
    (hconf : BindEnvs.conforms (ammBs α) ctx.self w.self calls)
    (hinj : BindEnvs.addrInj (ammBs α) w.self) :
    ToYulFnCorrectExts (ammBs α) Amm.contract Amm.schema κ calls f yul ctx w st0 :=
  Proof.amm_correct_ext α κ hκ calls f hf _hk yul hyul ctx w st0 hctx hR hRX hign hBindNe hconf hinj

end Lsc.Compiler
