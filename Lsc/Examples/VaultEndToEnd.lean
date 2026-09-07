import Lsc.Compiler.EndToEndExt
import Lsc.Compiler.Proof.Vault
import Lsc.Examples.VaultSecurity
import YulEvmCompiler.Compile
import YulEvmCompiler.LowerDefs

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Bytecode-level Vault theorems. Strongest form S2 supports: Security traces
(already proved) plus Yul-level `bytecode_call_correct_ext` (every `Run` of
the compiled runtime is predicted and has matching EVM `Steps`).
Slot-level claim transport across a Spec trace needs Amount
`core_denote` / `toNat` agreement (open; see `PROOF_CHAIN.md`).
-/

open Lsc Lsc.Compiler Lsc.Security Lsc.Stdlib Vault
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open YulEvmCompiler (compile Instr)

namespace Vault

def vaultClaimRead (κ : List UInt8 → U256) (σ : U256 → U256) (a : Address) : Nat :=
  let ta := (σ (BitVec.ofNat 256 0)).toNat
  let ts := (σ (BitVec.ofNat 256 1)).toNat
  let sh := (σ (mapSlot1 κ 2 a)).toNat
  if ts = 0 then 0 else sh * ta / ts

theorem vault_field_totalAssets :
    Vault.contract.fields[0]? =
      some { name := "totalAssets", kind := .scalar, ty := .uint256 } := by
  simp [Vault.contract]

theorem vault_field_totalShares :
    Vault.contract.fields[1]? =
      some { name := "totalShares", kind := .scalar, ty := .uint256 } := by
  simp [Vault.contract]

theorem vault_field_shares :
    Vault.contract.fields[2]? =
      some { name := "shares", kind := .map1, ty := .uint256 } := by
  simp [Vault.contract]

theorem vault_schema_totalAssets (s : Storage) :
    Vault.schema.st.scalar 0 s = s.totalAssets := rfl

theorem vault_schema_totalShares (s : Storage) :
    Vault.schema.st.scalar 1 s = s.totalShares := rfl

theorem vault_schema_shares (s : Storage) (k : Address) :
    Vault.schema.st.map1 2 s k = s.shares k := rfl

theorem vault_claim_of_rel (s : Storage) (σ : U256 → U256) (a : Address)
    (hs : storageRel Vault.contract Vault.schema evmKeccak s σ)
    (ha : Nat.lt a wordBound)
    (hta : s.totalAssets < wordBound) (hts : s.totalShares < wordBound)
    (hsh : s.shares a < wordBound) :
    vaultClaimRead evmKeccak σ a = claim a s := by
  have h0 : σ (BitVec.ofNat 256 0) = BitVec.ofNat 256 s.totalAssets := by
    simpa [vault_schema_totalAssets] using hs 0 _ vault_field_totalAssets
  have h1 : σ (BitVec.ofNat 256 1) = BitVec.ofNat 256 s.totalShares := by
    simpa [vault_schema_totalShares] using hs 1 _ vault_field_totalShares
  have h2 : σ (mapSlot1 evmKeccak 2 a) = BitVec.ofNat 256 (s.shares a) := by
    simpa [vault_schema_shares] using hs 2 _ vault_field_shares a ha
  simp [vaultClaimRead, claim, h0, h1, h2,
    Lsc.Compiler.toNat_ofNat_of_lt hta, Lsc.Compiler.toNat_ofNat_of_lt hts,
    Lsc.Compiler.toNat_ofNat_of_lt hsh]

/-- Compiled Vault runtime: every Yul `Run` is predicted (`∃ fo`) and has
matching EVM `Steps`. -/
theorem vault_bytecode_call_correct_ext
    (α : Abs IERC20.Ghost) (calls : ExternalCalls) (hCalls : CallsRealized calls)
    (rt : YBlock) (hrt : runtimeBlock Vault.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Vault.contract evmKeccak)
    (hign : α.ignoresLocal)
    (ctx : Ctx) (w : World Storage Ext Event) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0) (hR : R Vault.contract Vault.schema evmKeccak w yst0)
    (hRX : RX α Vault.assetB w yst0)
    (hconf : Conforms IERC20 ctx.self (Vault.assetB.addr w.self) calls α)
    (himm0 : ∀ k, yst0.env.immutable k = 0) :
    BytecodeCallCorrectExt α Vault.assetB Vault.contract Vault.schema evmKeccak
      calls ctx w yst0 rt is :=
  bytecode_call_correct_ext (I := IERC20) α Vault.assetB Vault.contract Vault.schema
    Vault.schema_lawful hκ calls hCalls
    (fun f hf => vault_fn_not_ctor hf) (fun f hf => vault_fn_s2 hf)
    vault_fields_lt (fun f hf => vault_fn_params_bound hf)
    rt hrt is hcomp ctx w yst0 hctx hR hRX hign hconf vault_bindWF
    (fun f hf => vault_hslot hf) himm0

/-- Compiled Vault runtime: a well-formed, no-auth-for-`a` Security trace does
not decrease `a`'s claim, and every Yul run of the compiled dispatcher from a
related start is predicted and has matching EVM `Steps`. Slot-level transport
of `claim` along the trace is the Amount `core_denote` gap. -/
theorem vault_bytecode_no_unauthorized_extraction
    (α : Abs IERC20.Ghost) (calls : ExternalCalls) (hCalls : CallsRealized calls)
    (rt : YBlock) (hrt : runtimeBlock Vault.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Vault.contract evmKeccak)
    (hign : α.ignoresLocal)
    (self : Address) (tr : List (Step spec)) (w : World Storage Ext Event)
    (a : Address) (σ : U256 → U256)
    (hw : Inv self w) (hW : Wf self tr)
    (hRely : RelyAlong (vaultRely self) tr w)
    (hA : NoAuthAlong Auth a tr w)
    (hs : storageRel Vault.contract Vault.schema evmKeccak w.self σ)
    (hwf : WorldWF Vault.contract Vault.schema w)
    (ctx : Ctx) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0)
    (hR : R Vault.contract Vault.schema evmKeccak w yst0)
    (hRX : RX α Vault.assetB w yst0)
    (hconf : Conforms IERC20 ctx.self (Vault.assetB.addr w.self) calls α)
    (himm0 : ∀ k, yst0.env.immutable k = 0) :
    claim a w.self ≤ claim a (run tr w).self ∧
      BytecodeCallCorrectExt α Vault.assetB Vault.contract Vault.schema evmKeccak
        calls ctx w yst0 rt is :=
  ⟨vault_no_unauthorized_extraction self tr w a hw hW hRely hA,
    vault_bytecode_call_correct_ext α calls hCalls rt hrt is hcomp hκ hign
      ctx w yst0 hctx hR hRX hconf himm0⟩

/-- Compiled Vault runtime: a well-formed Security trace stays solvent, and
every Yul run of the compiled dispatcher from a related start is predicted
and has matching EVM `Steps`. -/
theorem vault_bytecode_solvent
    (α : Abs IERC20.Ghost) (calls : ExternalCalls) (hCalls : CallsRealized calls)
    (rt : YBlock) (hrt : runtimeBlock Vault.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
    (hκ : KeccakSep Vault.contract evmKeccak)
    (hign : α.ignoresLocal)
    (self : Address) (tr : List (Step spec)) (w : World Storage Ext Event)
    (σ : U256 → U256)
    (hw : Inv self w) (hW : Wf self tr)
    (hRely : RelyAlong (vaultRely self) tr w)
    (hs : storageRel Vault.contract Vault.schema evmKeccak w.self σ)
    (hwf : WorldWF Vault.contract Vault.schema w)
    (ctx : Ctx) (yst0 : EvmState)
    (hctx : ctxRel ctx yst0)
    (hR : R Vault.contract Vault.schema evmKeccak w yst0)
    (hRX : RX α Vault.assetB w yst0)
    (hconf : Conforms IERC20 ctx.self (Vault.assetB.addr w.self) calls α)
    (himm0 : ∀ k, yst0.env.immutable k = 0) :
    Solvent claim holdings self (run tr w) ∧
      BytecodeCallCorrectExt α Vault.assetB Vault.contract Vault.schema evmKeccak
        calls ctx w yst0 rt is :=
  ⟨vault_solvent self tr w hW hRely hw,
    vault_bytecode_call_correct_ext α calls hCalls rt hrt is hcomp hκ hign
      ctx w yst0 hctx hR hRX hconf himm0⟩

end Vault
