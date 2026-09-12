import Examples.Amm.Spec
import Examples.Amm.Proofs.Tx
import Examples.Amm.Proofs.Security
import Examples.Amm.Proofs.Compile
import Examples.Amm.Proofs.EndToEnd
import Examples.Amm.Contract
import Stdlib.ERC20
import Lsc.Compiler.ExtOracle

set_option linter.unusedVariables false

/-!
AMM theorems: spec-level anti-extraction and solvency, the two-binding
S2 compiler instance, and share-count anti-extraction on compiled
runtime bytecode.
-/

open Lsc Lsc.Stdlib Lsc.Security Amm

namespace Amm

/-- After any well-formed sequence of pool calls, each reserve is still
covered by the pool's balance of that token: every LP's pro-rata slice
of token0 (resp. token1) sums to no more than the pool holds. The
starting world must already be solvent in that sense, the two tokens
must remain distinct, and between calls neither balance may fall.
Unlike `amm_no_unauthorized_extraction` this is about redeemable
reserves, not share count; it is not lifted to bytecode. -/
theorem amm_solvent (self : Address) (tr : List (Step spec))
    (w : World Storage Ext Event)
    (hW : Wf self tr) (hR : RelyAlong (ammRely self) tr w) (h : Inv self w) :
    Solvent claim0 holdings0 self (run tr w) ∧
      Solvent claim1 holdings1 self (run tr w) :=
  Proof.amm_solvent self tr w hW hR h

/-- No sequence of calls by other users can reduce Alice's LP share count
without a `removeLiquidity` she signed. Swaps, other LPs adding or
removing, and views cannot burn her shares; she may lose shares only
through her own removals. This does not protect her against impermanent
loss — her redeemable token amounts can move when the pool is traded.
Both tokens must behave like conforming ERC-20s; between calls neither
pool balance may fall. Callers must not be the pool itself. -/
theorem amm_no_unauthorized_extraction (self : Address)
    (tr : List (Step spec)) (w : World Storage Ext Event) (a : Address)
    (hw : Inv self w) (hW : Wf self tr) (hR : RelyAlong (ammRely self) tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  Proof.amm_no_unauthorized_extraction self tr w a hw hW hR hA

end Amm

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

open Lsc Lsc.Compiler Lsc.Security Lsc.Stdlib Amm
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open YulEvmCompiler (compile Instr)

namespace Amm

/-- Whatever sequence of calls an adversary sends to the deployed pool
bytecode, Alice's LP share count in EVM storage never falls unless she
herself called `removeLiquidity` in that sequence. Swaps and other users
adding or removing liquidity cannot burn her shares; unknown selectors
are ignored. Both tokens must behave like conforming ERC-20s, at
distinct addresses different from the pool, and cannot see the pool's
private memory, which is true of the EVM. The compiler must have
accepted the contract (`compileBlock`: erase or powdr spill); storage
keys must not collide. This does not protect Alice against impermanent
loss, and there is no bytecode solvency theorem — coverage of pro-rata
reserves stays at the spec. -/
theorem amm_bytecode_no_unauthorized_extraction
    (α : Abs IERC20.Ghost) (o : ExtOracle)
    (hCalls : CallsRealized (toCalls o))
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
    (hconf : ConfFun self (toCalls o) α)
    (hBindNe0 : accountKey (BitVec.ofNat 256 (token0B.addr w.self)) ≠
                accountKey (BitVec.ofNat 256 self))
    (hBindNe1 : accountKey (BitVec.ofNat 256 (token1B.addr w.self)) ≠
                accountKey (BitVec.ofNat 256 self))
    (hneq : w.self.token0Ref.addr ≠ w.self.token1Ref.addr) :
    ∀ σ' ξ', EvmTraceRunExtAll is calls σ ξ σ' ξ' →
      ammClaimRead evmKeccak σ a ≤ ammClaimRead evmKeccak σ' a :=
  Proof.amm_bytecode_no_unauthorized_extraction α o hCalls rt hrt is hcomp
    hκ hign hF self calls w a σ ξ hw hlog hWF hA hs hwf ha hRX0 hRX1 hconf
    hBindNe0 hBindNe1 hneq

end Amm
