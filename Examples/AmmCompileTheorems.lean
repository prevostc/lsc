import Examples.AmmCompileDefs
import Examples.AmmCompileProof
import Examples.Amm
import Lsc.Stdlib.ERC20

/-!
AMM is the two-binding S2 instance: `token0` and `token1` are distinct IERC20
addresses in storage. `toYulFn_correct_ext` is applied to the family
`[token0B, token1B]`.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc.Stdlib

/-- Every AMM runtime function matches `Core.denote` under a fault oracle, with
`RX` for both token bindings. Requires `token0 ≠ token1` at the storage
(`addrInj`), orthogonal ghosts, and `Conforms` for each IERC20. This is the
multi-binding compiler theorem PROOF_CHAIN cites. -/
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
