import Examples.Amm.EndToEnd
import Examples.Amm.CompileTheorems
import Examples.Amm.SecurityTheorems

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Proof of AMM bytecode anti-extraction. Statement lives in `AmmEndToEndTheorems`.
-/

open Lsc Lsc.Compiler Lsc.Security Lsc.Stdlib Amm
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open YulEvmCompiler (compile Instr)

namespace Amm

namespace Proof

theorem amm_bytecode_no_unauthorized_extraction
    (α : Abs IERC20.Ghost) (ext : ExternalCalls)
    (hCalls : CallsRealized ext) (htot : CallsTotal ext)
    (rt : YBlock) (hrt : runtimeBlock Amm.contract = some rt)
    (is : List Instr) (hcomp : compileBlock rt = some is)
    (hκ : KeccakSep Amm.contract evmKeccak)
    (hign : α.ignoresLocal) (hF : α.ofState_foreign)
    (self : Address) (calls : List EvmCall) (w : World Storage Ext Event)
    (a : Address) (σ : U256 → U256) (ξ : Foreign)
    (hw : Inv self w) (hlog : w.log = [])
    (hWF : CallsWF (mkAmmSetup hκ rt hrt is hcomp) self calls)
    (hA : NoAuthAlong Auth a (decodeTrace (mkAmmSetup hκ rt hrt is hcomp) calls) w)
    (hs : storageRel Amm.contract Amm.schema evmKeccak w.self σ)
    (hwf : WorldWF Amm.contract Amm.schema w)
    (ha : Nat.lt a wordBound)
    (hRX0 : RX α token0B w
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hRX1 : RX α token1B w
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hconf : ConfFun self ext α)
    (hBindNe0 : accountKey (BitVec.ofNat 256 (token0B.addr w.self)) ≠
                accountKey (BitVec.ofNat 256 self))
    (hBindNe1 : accountKey (BitVec.ofNat 256 (token1B.addr w.self)) ≠
                accountKey (BitVec.ofNat 256 self))
    (hneq : w.self.token0 ≠ w.self.token1) :
    ∀ σ' ξ', EvmTraceRunExtAll is calls σ ξ σ' ξ' →
      ammClaimRead evmKeccak σ a ≤ ammClaimRead evmKeccak σ' a := by
  intro σ' ξ' hE
  let T := mkAmmSetup hκ rt hrt is hcomp
  let Xpkg := mkAmmBindings hκ rt hrt is hcomp α ext hCalls htot hign hF
  have ⟨w', hs', hwf', _, _, hle⟩ :=
    transport_claim_ext T Xpkg (Inv self) claim Auth self a
      (amm_no_unauth self) (amm_preserves_inv self)
      (fun w fo h => amm_inv_faults self w fo h)
      (fun w log h => amm_inv_log self w log h)
      (fun tr w w' => noAuthAlong_irrel a tr w w')
      calls w σ ξ σ' ξ' hs hlog hwf hWF
      (amm_RXs_of α w _ hRX0 hRX1) (amm_neSelf_of α self w.self hBindNe0 hBindNe1)
      (amm_confs_of α self ext hconf) (amm_inj_of α w.self hneq) hA hw hE
  have hpre := amm_claim_of_rel w.self σ a hs ha (amm_shares_bound w a hwf ha)
  have hpost := amm_claim_of_rel w'.self σ' a hs' ha (amm_shares_bound w' a hwf' ha)
  rw [hpre, hpost]
  exact hle

end Proof

end Amm
