import Examples.Vault.EndToEnd
import Examples.Vault.EndToEndProof

set_option linter.unusedVariables false

/-!
Vault on compiled runtime bytecode: Alice's redeemable assets, read from
EVM storage, cannot fall unless she withdrew, and the token balance
still covers all claims.

The compiler must have accepted the contract. The asset token must
behave like a conforming ERC-20 at an address other than the vault, and
successful CALLs from us must match that model (no reentrancy into vault
storage). Unknown selectors are ignored. The constructor is out of
scope. The `_exists` variants start from a high-level trace.
-/

open Lsc Lsc.Compiler Lsc.Security Lsc.Stdlib Vault
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open YulEvmCompiler (compile Instr)

namespace Vault

/-- Whatever sequence of calls an adversary sends to the deployed Vault
bytecode, Alice's redeemable assets as stored on chain never fall unless
she authorised a decoded `withdraw` in that sequence. Unknown selectors
and short calldata are ignored. The compiler must have accepted the
contract; the asset token must behave like a conforming ERC-20 at an
address other than the vault; storage keys must not collide. This carries
the spec-level anti-extraction fact down to the bytecode, including the
token CALLs `deposit` and `withdraw` make. -/
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

/-- If Alice never authorised a `withdraw` in a given Vault trace, there is
an EVM execution of the encoded calldata that leaves her on-chain
redeemable assets no lower than they started. Use this when you already
have a high-level call sequence rather than raw calldata;
`vault_bytecode_no_unauthorized_extraction` is the matching fact for
every halted run of arbitrary calldata. Environment steps are dropped
when encoding. Same token-conformance and compiler assumptions. -/
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

/-- After any halted EVM execution of a well-formed Vault call sequence,
the sum of redeemable claims read from bytecode still does not exceed
the vault's token balance as read from the bound ERC-20's storage.
Unknown selectors are ignored. Unlike Token's bytecode solvency theorem
this is observed on chain, not as a high-level post-world: a fault
oracle may adjust which external calls succeed. Same compiler and
conforming-token assumptions as the anti-extraction theorem. -/
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

/-- Given a well-formed Vault trace, some EVM execution of the encoded
calldata ends with on-chain claims still covered by the vault's token
balance. Dual of `vault_bytecode_solvent` when you start from a
high-level trace rather than raw calldata. -/
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

/-- There exists a reading of ERC-20 storage — a balances mapping plus a
decimals slot, hashed as the EVM hashes them — that ignores the vault's
own storage and can be taken from any EVM snapshot. So the Vault
bytecode theorems are not vacuous: the "conforming token" hypothesis
they assume can be instantiated. -/
theorem vault_abs_nonvacuous :
    ∃ α : Abs IERC20.Ghost, α.ignoresLocal ∧ α.ofState_foreign :=
  Proof.vault_abs_nonvacuous

end Vault
