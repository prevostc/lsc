import Lsc.Compiler.Transport.Defs
import Lsc.Compiler.TransportProof
import Lsc.Compiler.Transport.Slots
import Lsc.Compiler.Proof.BindEnvs
import Lsc.Compiler.Proof.CallFreeCongr

/-!
Public transport lemmas for example authors. Fill a `TransportSetup` (and
for S2 a `TransportBindings`) from your contract, then apply these to move
a Security fact onto compiled bytecode. `coreAvoids_not_write` and
`BindEnvs.avoids_singleton` are imported from the binding-environment
helpers so a bound token address that no entrypoint stores can be shown
stable.
-/

namespace Lsc.Compiler

open Lsc Lsc.Security
open YulSemantics.EVM
open YulEvmCompiler

/-- Given a `TransportSetup` for a call-free contract, every halted EVM run of
an arbitrary calldata list decodes to a well-formed Security trace whose
`Security.run` storage matches the final EVM storage. Dispatcher rejects
(unknown selector / short calldata) are dropped from the trace. The starting
world must have an empty log, matching how Yul `mkEvmState` starts. -/
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

/-- A call-free Core run's post-`self`/`ext` depend only on the pre-`self`/`ext`
(not log or faults). This is `transport_trace`'s `hpc` hypothesis, free for
every S1 contract. -/
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

/-- `hpc` for a `TransportSetup` whose every runtime function is call-free:
Spec post-worlds agree on `self`/`ext` whenever the pre-worlds do, via
`codec.core_exec` and `worldAfter_callFree_congr`. -/
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

/-- The converse direction of `transport_trace` for a call-free contract: a
Security trace whose calls fit the ABI (`EncodeBounded`) has some EVM run of
the encoded calldata whose final storage is `storageRel` of running that
decoded trace. Use this when you start from a Security scenario and need a
matching bytecode execution. -/
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

/-- S2 analogue of `transport_trace`: each halted EVM call may `CALL` out, so
the theorem also returns a post-world with `RXs` for the binding package and
preserves the invariant and bound addresses. The post-world is the
fault-oracle fold (a Core revert keeps storage) and need not equal
`Security.run` when the EVM-chosen `fo` differs from `w.faults`. -/
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

/-- Lifts a Security `NoUnauthorizedDecrease` fact to EVM storage for an S2
contract. After any halted calldata list, the claim of address `a` on the
final bytecode state is at least the claim on the starting state, provided
`a` was never authorised along the decoded trace and `Auth`/`Inv` ignore
log and faults. This is the lemma Vault/AMM bytecode anti-extraction uses. -/
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

/-- Forward S2 existence: a well-formed Security trace that encodes into
bounded calldata has some EVM run (including foreign storage `ξ`) whose
post-world is related by `storageRel`/`RXs` and still satisfies `Inv`.
Bound callee addresses are unchanged. -/
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

/-- Combines `transport_exists_ext` with claim monotonicity: encoding a
Security trace and running it on the EVM cannot decrease `claim a` when `a`
was unauthorised along `callsOf tr`. The `_exists` bytecode theorems for
Vault use this. -/
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

/-- Under `storageRel`, a scalar field's EVM word is the Lean scalar packed
as a 256-bit word. Read a total-supply, owner, or bound-address slot off
the bytecode state with this. -/
theorem storageRel_scalar {S X E ε}
    {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ : List UInt8 → U256} {s : S} {σ : U256 → U256}
    {slot : Nat} {fd : FieldDef}
    (hs : storageRel c Γ κ s σ)
    (hfd : c.fields[slot]? = some fd)
    (hkind : fd.kind = .scalar) :
    σ (BitVec.ofNat 256 slot) = BitVec.ofNat 256 (Γ.st.scalar slot s) :=
  Proof.storageRel_scalar hs hfd hkind

/-- Same as `storageRel_scalar`, returning a `Nat` when the Lean value is
known to fit in a word. Prefer this when comparing claims that are `Nat`. -/
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

/-- Under `storageRel`, a one-key mapping slot (`keccak` of slot and key) holds
the Lean `map1` value. Token balances and Vault/AMM shares are `map1`s. -/
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

/-- `storageRel_map1` as a `Nat`, when the Lean mapping value fits in a word.
Example authors use this to identify `claim a` with an EVM mapping slot. -/
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
