import Lsc.Security.Invariant
import Lsc.Security.InvariantProof

/-!
Trace induction for protocol invariants. Local `lsc_contract` obligations
prove that each entrypoint and `Rely` preserve `Inv`; these theorems lift
that to an arbitrary well-formed adversary trace.
-/

namespace Lsc.Security

/-- If every contract call preserves `Inv` and every environment step that
obeys `rely` does too, then `Inv` still holds after any well-formed trace
(`sender ≠ self`, calls target `self`). Reverted calls are identity, so they
cannot break `Inv`. This is the induction Token uses to carry
`Σ balances = totalSupply` from a single transaction to a whole attack
trace. -/
theorem inv_run {C : Spec S X E ε} {Inv : World S X E → Prop} {rely : X → X → Prop}
    (hC : PreservesInv C Inv) (hE : PreservesInvEnv C Inv rely)
    {w : World S X E} (hw : Inv w) {self : Address} (tr : List (Step C))
    (hW : Wf self tr) (hR : RelyAlong rely tr w) :
    Inv (run tr w) :=
  Proof.inv_run hC hE hw tr hW hR

/-- Same conclusion as `inv_run` when `Inv` is only known to be preserved by
well-formed calls at `self` (`sender ≠ self`). Required for Vault/AMM, whose
invariants mention `holdings self` and therefore cannot be claimed under an
arbitrary `Call` that is not constrained to this contract. -/
theorem inv_run_at {C : Spec S X E ε} {Inv : World S X E → Prop} {rely : X → X → Prop}
    {self : Address}
    (hC : PreservesInvAt C Inv self) (hE : PreservesInvEnv C Inv rely)
    {w : World S X E} (hw : Inv w) (tr : List (Step C))
    (hW : Wf self tr) (hR : RelyAlong rely tr w) :
    Inv (run tr w) :=
  Proof.inv_run_at hC hE hw tr hW hR

end Lsc.Security
