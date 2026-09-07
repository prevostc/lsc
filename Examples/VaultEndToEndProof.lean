import Examples.VaultEndToEnd
import Examples.VaultCompileTheorems
import Examples.VaultSecurityTheorems

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Proofs of Vault bytecode security. Statements live in `VaultEndToEndTheorems`.
-/

open Lsc Lsc.Compiler Lsc.Security Lsc.Stdlib Vault
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open YulEvmCompiler (compile Instr)

namespace Vault

namespace Proof

theorem vault_bytecode_no_unauthorized_extraction
    (α : Abs IERC20.Ghost) (ext : ExternalCalls)
    (hCalls : CallsRealized ext) (htot : CallsTotal ext)
    (rt : YBlock) (hrt : runtimeBlock Vault.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Vault.contract evmKeccak)
    (hign : α.ignoresLocal) (hF : α.ofState_foreign)
    (self : Address) (calls : List EvmCall) (w : World Storage Ext Event)
    (a : Address) (σ : U256 → U256) (ξ : Foreign)
    (hw : Inv self w) (hlog : w.log = [])
    (hWF : CallsWF (mkVaultSetup hκ rt hrt is hcomp) self calls)
    (hA : NoAuthAlong Auth a (decodeTrace (mkVaultSetup hκ rt hrt is hcomp) calls) w)
    (hs : storageRel Vault.contract Vault.schema evmKeccak w.self σ)
    (hwf : WorldWF Vault.contract Vault.schema w)
    (ha : Nat.lt a wordBound)
    (hRX : RX α Vault.assetB w
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hconf : ConfFun self ext α)
    (hBindNe : accountKey (BitVec.ofNat 256 (Vault.assetB.addr w.self)) ≠
                accountKey (BitVec.ofNat 256 self)) :
    ∀ σ' ξ', EvmTraceRunExtAll is calls σ ξ σ' ξ' →
      vaultClaimRead evmKeccak σ a ≤ vaultClaimRead evmKeccak σ' a := by
  intro σ' ξ' hE
  let T := mkVaultSetup hκ rt hrt is hcomp
  let Xpkg := mkVaultBindings hκ rt hrt is hcomp α ext hCalls htot hign hF
  have ⟨w', hs', hwf', _, _, hle⟩ :=
    transport_claim_ext T Xpkg (Inv self) claim Auth self a
      (vault_no_unauth self) (vault_preserves_inv self)
      (fun w fo h => vault_inv_faults self w fo h)
      (fun w log h => vault_inv_log self w log h)
      (fun tr w w' => noAuthAlong_irrel a tr w w')
      calls w σ ξ σ' ξ' hs hlog hwf hWF
      (vault_RXs_of α w _ hRX) (vault_neSelf_of α self w.self hBindNe)
      (vault_confs_of α self ext hconf) (vault_inj_of α w.self) hA hw hE
  have hpre := vault_claim_of_rel w.self σ a hs ha
    (vault_ta_bound w hwf) (vault_ts_bound w hwf) (vault_shares_bound w a hwf ha)
  have hpost := vault_claim_of_rel w'.self σ' a hs' ha
    (vault_ta_bound w' hwf') (vault_ts_bound w' hwf') (vault_shares_bound w' a hwf' ha)
  rw [hpre, hpost]
  exact hle

theorem vault_bytecode_no_unauthorized_extraction_exists
    (α : Abs IERC20.Ghost) (ext : ExternalCalls)
    (hCalls : CallsRealized ext) (htot : CallsTotal ext)
    (rt : YBlock) (hrt : runtimeBlock Vault.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Vault.contract evmKeccak)
    (hign : α.ignoresLocal) (hF : α.ofState_foreign)
    (self : Address) (tr : List (Step spec)) (w : World Storage Ext Event)
    (a : Address) (σ : U256 → U256) (ξ : Foreign)
    (hw : Inv self w) (hW : Wf self tr) (hlog : w.log = [])
    (hA : NoAuthAlong Auth a tr w)
    (hs : storageRel Vault.contract Vault.schema evmKeccak w.self σ)
    (hwf : WorldWF Vault.contract Vault.schema w)
    (hb : EncodeBounded (mkVaultSetup hκ rt hrt is hcomp) tr)
    (ha : Nat.lt a wordBound)
    (hRX : RX α Vault.assetB w
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hconf : ConfFun self ext α)
    (hBindNe : accountKey (BitVec.ofNat 256 (Vault.assetB.addr w.self)) ≠
                accountKey (BitVec.ofNat 256 self)) :
    ∃ σ' ξ', EvmTraceRunExt is
        (encodeCalls (mkVaultSetup hκ rt hrt is hcomp) tr) σ ξ σ' ξ' ∧
      vaultClaimRead evmKeccak σ a ≤ vaultClaimRead evmKeccak σ' a := by
  let T := mkVaultSetup hκ rt hrt is hcomp
  let Xpkg := mkVaultBindings hκ rt hrt is hcomp α ext hCalls htot hign hF
  have hwlog : { w with log := ([] : List Event) } = w := by
    cases w; simp at hlog; subst hlog; rfl
  obtain ⟨σ', ξ', w', hE, hs', hwf', _, _, hle⟩ :=
    transport_exists_claim_ext T Xpkg (Inv self) claim Auth self a
      (vault_no_unauth self) (vault_preserves_inv self)
      (fun w fo h => vault_inv_faults self w fo h)
      (fun w log h => vault_inv_log self w log h)
      (fun tr w w' => noAuthAlong_irrel a tr w w')
      tr w σ ξ hs hwf hb hW hw (vault_noAuthAlong_callsOf a tr w hA)
      (by simpa [hwlog] using vault_RXs_of α w _ hRX)
      (vault_neSelf_of α self w.self hBindNe) (vault_confs_of α self ext hconf)
      (vault_inj_of α w.self)
  refine ⟨σ', ξ', hE, ?_⟩
  have hpre := vault_claim_of_rel w.self σ a hs ha
    (vault_ta_bound w hwf) (vault_ts_bound w hwf) (vault_shares_bound w a hwf ha)
  have hpost := vault_claim_of_rel w'.self σ' a hs' ha
    (vault_ta_bound w' hwf') (vault_ts_bound w' hwf') (vault_shares_bound w' a hwf' ha)
  rw [hpre, hpost]
  exact hle

theorem vault_bytecode_solvent
    (α : Abs IERC20.Ghost) (ext : ExternalCalls)
    (hCalls : CallsRealized ext) (htot : CallsTotal ext)
    (rt : YBlock) (hrt : runtimeBlock Vault.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Vault.contract evmKeccak)
    (hign : α.ignoresLocal) (hF : α.ofState_foreign)
    (self : Address) (calls : List EvmCall) (w : World Storage Ext Event)
    (σ : U256 → U256) (ξ : Foreign)
    (hw : Inv self w) (hlog : w.log = [])
    (hWF : CallsWF (mkVaultSetup hκ rt hrt is hcomp) self calls)
    (hs : storageRel Vault.contract Vault.schema evmKeccak w.self σ)
    (hwf : WorldWF Vault.contract Vault.schema w)
    (hRX : RX α Vault.assetB w
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hconf : ConfFun self ext α)
    (hBindNe : accountKey (BitVec.ofNat 256 (Vault.assetB.addr w.self)) ≠
                accountKey (BitVec.ofNat 256 self)) :
    ∀ σ' ξ', EvmTraceRunExtAll is calls σ ξ σ' ξ' →
      vaultSolventRead α σ' ξ' self (Vault.assetB.addr w.self) := by
  intro σ' ξ' hE
  let T := mkVaultSetup hκ rt hrt is hcomp
  let Xpkg := mkVaultBindings hκ rt hrt is hcomp α ext hCalls htot hign hF
  have ⟨_, w', hs', hwf', hRX', hInv', haddr⟩ :=
    transport_trace_ext T Xpkg self calls w σ ξ σ' ξ' hs hlog hwf hWF
      (vault_RXs_of α w _ hRX) (vault_neSelf_of α self w.self hBindNe)
      (vault_confs_of α self ext hconf) (vault_inj_of α w.self) (Inv self) (vault_preserves_inv self)
      (fun w fo h => vault_inv_faults self w fo h)
      (fun w log h => vault_inv_log self w log h)
      hw hE
  have hsol := vaultSolventRead_of_inv α self w' σ' ξ' hInv' hs' hwf'
    (vault_RX_of α w' _ hRX')
  have haddr' : Vault.assetB.addr w'.self = Vault.assetB.addr w.self :=
    haddr (vaultEnv α) (List.mem_singleton.mpr rfl)
  rw [← haddr']
  exact hsol

theorem vault_bytecode_solvent_exists
    (α : Abs IERC20.Ghost) (ext : ExternalCalls)
    (hCalls : CallsRealized ext) (htot : CallsTotal ext)
    (rt : YBlock) (hrt : runtimeBlock Vault.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Vault.contract evmKeccak)
    (hign : α.ignoresLocal) (hF : α.ofState_foreign)
    (self : Address) (tr : List (Step spec)) (w : World Storage Ext Event)
    (σ : U256 → U256) (ξ : Foreign)
    (hw : Inv self w) (hW : Wf self tr) (hlog : w.log = [])
    (hs : storageRel Vault.contract Vault.schema evmKeccak w.self σ)
    (hwf : WorldWF Vault.contract Vault.schema w)
    (hb : EncodeBounded (mkVaultSetup hκ rt hrt is hcomp) tr)
    (hRX : RX α Vault.assetB w
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hconf : ConfFun self ext α)
    (hBindNe : accountKey (BitVec.ofNat 256 (Vault.assetB.addr w.self)) ≠
                accountKey (BitVec.ofNat 256 self)) :
    ∃ σ' ξ', EvmTraceRunExt is
        (encodeCalls (mkVaultSetup hκ rt hrt is hcomp) tr) σ ξ σ' ξ' ∧
      vaultSolventRead α σ' ξ' self (Vault.assetB.addr w.self) := by
  let T := mkVaultSetup hκ rt hrt is hcomp
  let Xpkg := mkVaultBindings hκ rt hrt is hcomp α ext hCalls htot hign hF
  have hwlog : { w with log := ([] : List Event) } = w := by
    cases w; simp at hlog; subst hlog; rfl
  obtain ⟨σ', ξ', w', hE, hs', hwf', hRX', hInv', haddr⟩ :=
    transport_exists_ext T Xpkg (Inv self) self
      (vault_preserves_inv self)
      (fun w fo h => vault_inv_faults self w fo h)
      (fun w log h => vault_inv_log self w log h)
      tr w σ ξ hs hwf hb hW hw
      (by simpa [hwlog] using vault_RXs_of α w _ hRX)
      (vault_neSelf_of α self w.self hBindNe) (vault_confs_of α self ext hconf)
      (vault_inj_of α w.self)
  refine ⟨σ', ξ', hE, ?_⟩
  have hsol := vaultSolventRead_of_inv α self w' σ' ξ' hInv' hs' hwf'
    (vault_RX_of α w' _ hRX')
  have haddr' : Vault.assetB.addr w'.self = Vault.assetB.addr w.self :=
    haddr (vaultEnv α) (List.mem_singleton.mpr rfl)
  rw [← haddr']
  exact hsol

theorem vault_abs_nonvacuous :
    ∃ α : Abs IERC20.Ghost, α.ignoresLocal ∧ α.ofState_foreign :=
  ⟨vaultAbsSolidity, vaultAbsSolidity_ignoresLocal, vaultAbsSolidity_ofState_foreign⟩

end Proof

end Vault
