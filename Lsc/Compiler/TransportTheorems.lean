import Lsc.Compiler.Transport.Defs
import Lsc.Compiler.TransportProof
import Lsc.Compiler.Transport.Slots
import Lsc.Compiler.Proof.BindEnvs
import Lsc.Compiler.Proof.CallFreeCongr

/-!
Transport: move a high-level security fact onto compiled bytecode.
Example authors fill in their contract and apply these lemmas.

Call-free contracts (Token) get a full match between EVM storage and
the high-level post-world. Contracts that CALL out (Vault, AMM) get a
post-world under some choice of which external calls fail; bound token
addresses that no entrypoint stores stay fixed.

Shared assumptions: the compiler accepted the contract, storage keys
do not collide, starting storage matches, callers are not the contract.
-/

namespace Lsc.Compiler

open Lsc Lsc.Security
open YulSemantics.EVM
open YulEvmCompiler

/-- Whatever sequence of calls an adversary sends to deployed call-free
bytecode, the storage the EVM ends up with is exactly the storage the
contract's high-level model predicts for the same calls; unknown
selectors and short calldata are simply ignored. Callers must not be
the contract itself; starting storage must match a high-level world
with empty logs. This is the step that carries a Token-style security
proof down to the bytecode. -/
theorem transport_trace (T : TransportSetup S X E ε)
    (hcf : ∀ f ∈ T.c.functions, CallFree f.core)
    (hpc : ∀ (fn : T.spec.Fn) (args : T.spec.Args fn) (ctx : Ctx) (w w' : World S X E),
      w.self = w'.self → w.ext = w'.ext →
        (worldAfter (T.spec.exec fn args) ctx w).self =
          (worldAfter (T.spec.exec fn args) ctx w').self ∧
        (worldAfter (T.spec.exec fn args) ctx w).ext =
          (worldAfter (T.spec.exec fn args) ctx w').ext)
    (self : Address) (calls : List EvmCall)
    (w : World S X E) (σ σ' : U256 → U256)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF T.c T.Γ w)
    (hWF : CallsWF T self calls)
    (hE : EvmTraceRunAll T.is calls σ σ') :
    let tr := decodeTrace T calls
    Wf self tr ∧
      storageRel T.c T.Γ evmKeccak (run tr w).self σ' ∧
      WorldWF T.c T.Γ { run tr w with log := [] } :=
  Proof.transport_trace T hcf hpc self calls w σ σ' hs hlog hwf hWF hE

/-- A function that never CALLs out has post-storage and external ghosts
that depend only on the pre-storage and pre-ghosts, not on logs or on
which external calls would have failed. Transport uses this so it can
ignore those extra world fields when matching EVM storage. -/
theorem worldAfter_callFree_congr {S X E ε} {Γ : ContractSchema S X E ε} {t}
    (core : Core t) (hM1 : CallFree core) (env : List Nat) (ctx : Ctx)
    (w w' : World S X E) (hs : w.self = w'.self) (he : w.ext = w'.ext) :
    (worldAfter (Core.denote Γ core env) ctx w).self =
      (worldAfter (Core.denote Γ core env) ctx w').self ∧
    (worldAfter (Core.denote Γ core env) ctx w).ext =
      (worldAfter (Core.denote Γ core env) ctx w').ext := by
  change
    (Lang.worldAfter (Core.denote Γ core env) ctx w).self =
      (Lang.worldAfter (Core.denote Γ core env) ctx w').self ∧
    (Lang.worldAfter (Core.denote Γ core env) ctx w).ext =
      (Lang.worldAfter (Core.denote Γ core env) ctx w').ext
  exact Proof.worldAfter_callFree_congr core hM1 env ctx w w' hs he

/-- Same independence of logs and faults as `worldAfter_callFree_congr`,
stated at the contract's high-level entrypoints rather than the Core IR.
Call-free contracts get this for free; it is the extra hypothesis
`transport_trace` asks of the spec. -/
theorem post_congr_callFree {S X E ε} (T : TransportSetup S X E ε)
    (hcf : ∀ f ∈ T.c.functions, CallFree f.core)
    (fn : T.spec.Fn) (args : T.spec.Args fn) (ctx : Ctx) (w w' : World S X E)
    (hs : w.self = w'.self) (he : w.ext = w'.ext) :
    (worldAfter (T.spec.exec fn args) ctx w).self =
      (worldAfter (T.spec.exec fn args) ctx w').self ∧
    (worldAfter (T.spec.exec fn args) ctx w).ext =
      (worldAfter (T.spec.exec fn args) ctx w').ext := by
  have h1 := T.codec.core_exec fn args ctx w
  have h2 := T.codec.core_exec fn args ctx w'
  rw [← h1, ← h2]
  exact worldAfter_callFree_congr (T.codec.fnDef fn).core
    (hcf _ (T.codec.mem fn)) (T.codec.encode fn args).reverse ctx w w' hs he

/-- The converse of `transport_trace` for a call-free contract: a high-level
call sequence whose arguments fit the ABI has some EVM execution of the
encoded calldata whose final storage matches running that sequence.
Use this when you start from a security scenario rather than raw
calldata. -/
theorem transport_exists (T : TransportSetup S X E ε)
    (hcf : ∀ f ∈ T.c.functions, CallFree f.core)
    (hpc : ∀ (fn : T.spec.Fn) (args : T.spec.Args fn) (ctx : Ctx) (w w' : World S X E),
      w.self = w'.self → w.ext = w'.ext →
        (worldAfter (T.spec.exec fn args) ctx w).self =
          (worldAfter (T.spec.exec fn args) ctx w').self ∧
        (worldAfter (T.spec.exec fn args) ctx w).ext =
          (worldAfter (T.spec.exec fn args) ctx w').ext)
    (tr : List (Step T.spec)) (w : World S X E) (σ : U256 → U256)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hwf : WorldWF T.c T.Γ w)
    (hb : EncodeBounded T tr) :
    ∃ σ', EvmTraceRun T.is (encodeCalls T tr) σ σ' ∧
      storageRel T.c T.Γ evmKeccak
        (run (decodeTrace T (encodeCalls T tr)) { w with log := [] }).self σ' ∧
      WorldWF T.c T.Γ
        { run (decodeTrace T (encodeCalls T tr)) { w with log := [] } with log := [] } :=
  Proof.transport_exists T hcf hpc tr w σ hs hwf hb

variable {I : Interface}

/-- Whatever sequence of calls an adversary sends to bytecode that CALLs
out, there is a high-level post-world whose storage matches the EVM,
whose bound-token ghosts match those accounts, and which still satisfies
the protocol invariant; bound token addresses are unchanged. Unknown
selectors are ignored. The post-world is chosen so Core and Yul agree on
which external calls failed; it need not be the high-level run under the
starting fault bits. Tokens must conform and must not be this contract. -/
theorem transport_trace_ext (T : TransportSetup S X E ε)
    (Xpkg : TransportBindings S X E ε I T)
    (self : Address) (calls : List EvmCall)
    (w : World S X E) (σ : U256 → U256) (ξ : Foreign)
    (σ' : U256 → U256) (ξ' : Foreign)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF T.c T.Γ w)
    (hWF : CallsWF T self calls)
    (hRX : RXs Xpkg.bs w
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hBindNe : BindEnvs.neSelf Xpkg.bs self w.self)
    (hconf : ∀ (w' : World S X E),
      BindEnvs.conforms Xpkg.bs self w'.self Xpkg.extCalls)
    (hinj : BindEnvs.addrInj Xpkg.bs w.self)
    (Inv : World S X E → Prop)
    (hP : PreservesInvAt T.spec Inv self)
    (hInvF : ∀ w fo, Inv w → Inv { w with faults := fo })
    (hInvL : ∀ w (log : List E), Inv w → Inv { w with log := log })
    (hw : Inv w)
    (hE : EvmTraceRunExtAll T.is calls σ ξ σ' ξ') :
    let tr := decodeTrace T calls
    Wf self tr ∧
      ∃ w' : World S X E,
        storageRel T.c T.Γ evmKeccak w'.self σ' ∧
        WorldWF T.c T.Γ w' ∧
        RXs Xpkg.bs w'
          (mkEvmStateExt ([] : List UInt8) σ' ξ' evmKeccak (dummyCtx self)) ∧
        Inv w' ∧
        (∀ e ∈ Xpkg.bs, e.bind.addr w'.self = e.bind.addr w.self) :=
  Proof.transport_trace_ext T Xpkg self calls w σ ξ σ' ξ' hs hlog hwf hWF hRX
    hBindNe hconf hinj Inv hP hInvF hInvL hw hE

/-- After any halted calldata list against bytecode that CALLs out, an
account's protocol claim as stored on chain is no lower than it started,
provided that account authorised no decoded call and the protocol
never lowers a claim except when authorised. This is the lemma Vault
and AMM bytecode anti-extraction use; unlike `transport_trace` it is
about one account's claim, not the whole storage match. Tokens must
conform. -/
theorem transport_claim_ext (T : TransportSetup S X E ε)
    (Xpkg : TransportBindings S X E ε I T)
    (Inv : World S X E → Prop) (claim : Claim S) (Auth : AuthPred T.spec)
    (self : Address) (a : Address)
    (hN : NoUnauthorizedDecrease T.spec Inv claim Auth)
    (hP : PreservesInvAt T.spec Inv self)
    (hInvF : ∀ w fo, Inv w → Inv { w with faults := fo })
    (hInvL : ∀ w (log : List E), Inv w → Inv { w with log := log })
    (hAirr : ∀ tr w w', NoAuthAlong Auth a tr w ↔ NoAuthAlong Auth a tr w')
    (calls : List EvmCall)
    (w : World S X E) (σ : U256 → U256) (ξ : Foreign)
    (σ' : U256 → U256) (ξ' : Foreign)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hlog : w.log = []) (hwf : WorldWF T.c T.Γ w)
    (hWF : CallsWF T self calls)
    (hRX : RXs Xpkg.bs w
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hBindNe : BindEnvs.neSelf Xpkg.bs self w.self)
    (hconf : ∀ (w' : World S X E),
      BindEnvs.conforms Xpkg.bs self w'.self Xpkg.extCalls)
    (hinj : BindEnvs.addrInj Xpkg.bs w.self)
    (hA : NoAuthAlong Auth a (decodeTrace T calls) w)
    (hw : Inv w)
    (hE : EvmTraceRunExtAll T.is calls σ ξ σ' ξ') :
    ∃ w' : World S X E,
      storageRel T.c T.Γ evmKeccak w'.self σ' ∧
      WorldWF T.c T.Γ w' ∧
      RXs Xpkg.bs w'
        (mkEvmStateExt ([] : List UInt8) σ' ξ' evmKeccak (dummyCtx self)) ∧
      Inv w' ∧
      claim a w.self ≤ claim a w'.self :=
  Proof.transport_claim_ext T Xpkg Inv claim Auth self a hN hP hInvF hInvL hAirr
    calls w σ ξ σ' ξ' hs hlog hwf hWF hRX hBindNe hconf hinj hA hw hE

/-- A well-formed high-level trace against a contract that CALLs out has
some EVM execution of the encoded calldata whose post-storage and
bound-token ghosts match a high-level world that still satisfies the
invariant; bound token addresses are unchanged. Dual of
`transport_trace_ext` when you start from a trace rather than raw
calldata. -/
theorem transport_exists_ext (T : TransportSetup S X E ε)
    (Xpkg : TransportBindings S X E ε I T)
    (Inv : World S X E → Prop)
    (self : Address)
    (hP : PreservesInvAt T.spec Inv self)
    (hInvF : ∀ w fo, Inv w → Inv { w with faults := fo })
    (hInvL : ∀ w (log : List E), Inv w → Inv { w with log := log })
    (tr : List (Step T.spec)) (w : World S X E)
    (σ : U256 → U256) (ξ : Foreign)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hwf : WorldWF T.c T.Γ w)
    (hb : EncodeBounded T tr) (hW : Wf self tr) (hw : Inv w)
    (hRX : RXs Xpkg.bs { w with log := ([] : List E) }
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hBindNe : BindEnvs.neSelf Xpkg.bs self w.self)
    (hconf : ∀ (w' : World S X E),
      BindEnvs.conforms Xpkg.bs self w'.self Xpkg.extCalls)
    (hinj : BindEnvs.addrInj Xpkg.bs w.self) :
    ∃ σ' ξ' w',
      EvmTraceRunExt T.is (encodeCalls T tr) σ ξ σ' ξ' ∧
      storageRel T.c T.Γ evmKeccak w'.self σ' ∧
      WorldWF T.c T.Γ w' ∧
      RXs Xpkg.bs w'
        (mkEvmStateExt ([] : List UInt8) σ' ξ' evmKeccak (dummyCtx self)) ∧
      Inv w' ∧
      (∀ e ∈ Xpkg.bs, e.bind.addr w'.self = e.bind.addr w.self) :=
  Proof.transport_exists_ext T Xpkg Inv self hP hInvF hInvL tr w σ ξ hs hwf hb
    hW hw hRX hBindNe hconf hinj

/-- Encoding a high-level trace and running it on bytecode that CALLs out
cannot decrease an account's claim when that account authorised no call
in the trace. Combines `transport_exists_ext` with claim monotonicity;
Vault's `_exists` bytecode theorems use this. -/
theorem transport_exists_claim_ext (T : TransportSetup S X E ε)
    (Xpkg : TransportBindings S X E ε I T)
    (Inv : World S X E → Prop) (claim : Claim S) (Auth : AuthPred T.spec)
    (self a : Address)
    (hN : NoUnauthorizedDecrease T.spec Inv claim Auth)
    (hP : PreservesInvAt T.spec Inv self)
    (hInvF : ∀ w fo, Inv w → Inv { w with faults := fo })
    (hInvL : ∀ w (log : List E), Inv w → Inv { w with log := log })
    (hAirr : ∀ tr w w', NoAuthAlong Auth a tr w ↔ NoAuthAlong Auth a tr w')
    (tr : List (Step T.spec)) (w : World S X E)
    (σ : U256 → U256) (ξ : Foreign)
    (hs : storageRel T.c T.Γ evmKeccak w.self σ)
    (hwf : WorldWF T.c T.Γ w)
    (hb : EncodeBounded T tr) (hW : Wf self tr) (hw : Inv w)
    (hA : NoAuthAlong Auth a (callsOf tr) w)
    (hRX : RXs Xpkg.bs { w with log := ([] : List E) }
      (mkEvmStateExt ([] : List UInt8) σ ξ evmKeccak (dummyCtx self)))
    (hBindNe : BindEnvs.neSelf Xpkg.bs self w.self)
    (hconf : ∀ (w' : World S X E),
      BindEnvs.conforms Xpkg.bs self w'.self Xpkg.extCalls)
    (hinj : BindEnvs.addrInj Xpkg.bs w.self) :
    ∃ σ' ξ' w',
      EvmTraceRunExt T.is (encodeCalls T tr) σ ξ σ' ξ' ∧
      storageRel T.c T.Γ evmKeccak w'.self σ' ∧
      WorldWF T.c T.Γ w' ∧
      RXs Xpkg.bs w'
        (mkEvmStateExt ([] : List UInt8) σ' ξ' evmKeccak (dummyCtx self)) ∧
      Inv w' ∧
      claim a w.self ≤ claim a w'.self :=
  Proof.transport_exists_claim_ext T Xpkg Inv claim Auth self a hN hP hInvF hInvL
    hAirr tr w σ ξ hs hwf hb hW hw hA hRX hBindNe hconf hinj

/-- When EVM storage matches a high-level world, a scalar slot's EVM word
is that world's field packed as a 256-bit word. Read total supply, owner,
or a bound token address off the bytecode with this. -/
theorem storageRel_scalar {S X E ε}
    {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ : List UInt8 → U256} {s : S} {σ : U256 → U256}
    {slot : Nat} {fd : FieldDef}
    (hs : storageRel c Γ κ s σ)
    (hfd : c.fields[slot]? = some fd)
    (hkind : fd.kind = .scalar) :
    σ (BitVec.ofNat 256 slot) = BitVec.ofNat 256 (Γ.st.scalar slot s) :=
  Proof.storageRel_scalar hs hfd hkind

/-- Same as `storageRel_scalar`, returning a natural number when the stored
value is known to fit in a word. Prefer this when comparing claims that
are amounts, not raw words. -/
theorem storageRel_scalar_toNat {S X E ε}
    {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ : List UInt8 → U256} {s : S} {σ : U256 → U256}
    {slot : Nat} {fd : FieldDef} {v : Nat}
    (hs : storageRel c Γ κ s σ)
    (hfd : c.fields[slot]? = some fd)
    (hkind : fd.kind = .scalar)
    (hval : Γ.st.scalar slot s = v)
    (hv : v < wordBound) :
    (σ (BitVec.ofNat 256 slot)).toNat = v :=
  Proof.storageRel_scalar_toNat hs hfd hkind hval hv

/-- When EVM storage matches a high-level world, a one-key mapping slot
(hashed slot and key) holds that world's mapping value. Token balances
and Vault/AMM shares are this shape. -/
theorem storageRel_map1 {S X E ε}
    {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ : List UInt8 → U256} {s : S} {σ : U256 → U256}
    {slot : Nat} {fd : FieldDef} {a : Address}
    (hs : storageRel c Γ κ s σ)
    (hfd : c.fields[slot]? = some fd)
    (hkind : fd.kind = .map1)
    (ha : Nat.lt a wordBound) :
    σ (mapSlot1 κ slot a) = BitVec.ofNat 256 (Γ.st.map1 slot s a) :=
  Proof.storageRel_map1 hs hfd hkind ha

/-- Same as `storageRel_map1`, returning a natural number when the mapping
value fits in a word. Example authors use this to identify an account's
claim with an EVM mapping slot. -/
theorem storageRel_map1_toNat {S X E ε}
    {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ : List UInt8 → U256} {s : S} {σ : U256 → U256}
    {slot : Nat} {fd : FieldDef} {a : Address} {v : Nat}
    (hs : storageRel c Γ κ s σ)
    (hfd : c.fields[slot]? = some fd)
    (hkind : fd.kind = .map1)
    (hval : Γ.st.map1 slot s a = v)
    (ha : Nat.lt a wordBound) (hv : v < wordBound) :
    (σ (mapSlot1 κ slot a)).toNat = v :=
  Proof.storageRel_map1_toNat hs hfd hkind hval ha hv

end Lsc.Compiler
