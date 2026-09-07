import Examples.VaultEndToEnd
import Examples.VaultEndToEndProof

set_option linter.unusedVariables false

/-!
Vault bytecode security: Core-level anti-extraction and solvency, read
back from compiled S2 runtime storage and the bound ERC-20 ghost.
-/

open Lsc Lsc.Compiler Lsc.Security Lsc.Stdlib Vault
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open YulEvmCompiler (compile Instr)

namespace Vault

/-- Every halted EVM execution of a well-formed Vault call sequence, whose
decoded Core trace never authorised `a`, does not decrease `a`'s share
claim as read from bytecode storage. Assumes `Inv`, `storageRel`, a
`Conforms` ERC-20 at the asset address (`CallsRealized` / `CallsTotal`),
and that the compiler accepted the contract. This is the S2 end-to-end
anti-extraction theorem for a single binding. -/
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
      vaultClaimRead evmKeccak σ a ≤ vaultClaimRead evmKeccak σ' a :=
  Proof.vault_bytecode_no_unauthorized_extraction α ext hCalls htot rt hrt is hcomp
    hκ hign hF self calls w a σ ξ hw hlog hWF hA hs hwf ha hRX hconf hBindNe

/-- Anti-extraction for an encoded Security trace: some EVM run realises
the calls and `a`'s claim slot does not fall. Env steps are dropped by
`callsOf`. -/
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
      vaultClaimRead evmKeccak σ a ≤ vaultClaimRead evmKeccak σ' a :=
  Proof.vault_bytecode_no_unauthorized_extraction_exists α ext hCalls htot rt hrt
    is hcomp hκ hign hF self tr w a σ ξ hw hW hlog hA hs hwf hb ha hRX hconf hBindNe

/-- Every halted EVM execution of a well-formed Vault sequence leaves a
solvent vault: the ERC-20 ghost at the asset address covers the sum of
share claims. Post-world may be a fault-oracle-adjusted fold, not
literally `Security.run`. -/
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
      vaultSolventRead α σ' ξ' self (Vault.assetB.addr w.self) :=
  Proof.vault_bytecode_solvent α ext hCalls htot rt hrt is hcomp hκ hign hF
    self calls w σ ξ hw hlog hWF hs hwf hRX hconf hBindNe

/-- Solvency for an encoded Security trace: some EVM run realises the
calls and the post-ghost covers the claims. -/
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
      vaultSolventRead α σ' ξ' self (Vault.assetB.addr w.self) :=
  Proof.vault_bytecode_solvent_exists α ext hCalls htot rt hrt is hcomp hκ hign hF
    self tr w σ ξ hw hW hlog hs hwf hb hRX hconf hBindNe

/-- A Solidity-layout ERC-20 abstraction (`balances` mapping + `decimals`
slot, `evmKeccak`) is foreign-only and projects from any EVM snapshot.
So the `α` hypothesis of the Vault bytecode theorems is inhabited. -/
theorem vault_abs_nonvacuous :
    ∃ α : Abs IERC20.Ghost, α.ignoresLocal ∧ α.ofState_foreign :=
  Proof.vault_abs_nonvacuous

end Vault
