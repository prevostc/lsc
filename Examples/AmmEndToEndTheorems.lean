import Examples.AmmEndToEnd
import Examples.AmmEndToEndProof

set_option linter.unusedVariables false

/-!
AMM bytecode security: LP share anti-extraction on the compiled S2 runtime
with two IERC20 bindings.
-/

open Lsc Lsc.Compiler Lsc.Security Lsc.Stdlib Amm
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open YulEvmCompiler (compile Instr)

namespace Amm

/-- Every halted EVM execution of a well-formed AMM call sequence, whose
decoded Core trace never authorised `a`, does not decrease `a`'s LP share
slot. Assumes `Inv`, `storageRel`, `Conforms` at both token addresses
(`token0 ≠ token1`), `CallsRealized` / `CallsTotal`, and that the compiler
accepted the contract. This is the S2 end-to-end theorem for two
bindings. -/
theorem amm_bytecode_no_unauthorized_extraction
    (α : Abs IERC20.Ghost) (ext : ExternalCalls)
    (hCalls : CallsRealized ext) (htot : CallsTotal ext)
    (rt : YBlock) (hrt : runtimeBlock Amm.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is)
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
      ammClaimRead evmKeccak σ a ≤ ammClaimRead evmKeccak σ' a :=
  Proof.amm_bytecode_no_unauthorized_extraction α ext hCalls htot rt hrt is hcomp
    hκ hign hF self calls w a σ ξ hw hlog hWF hA hs hwf ha hRX0 hRX1 hconf
    hBindNe0 hBindNe1 hneq

end Amm
