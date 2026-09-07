import Lsc.Security.Invariant
import Lsc.Security.InvariantProof

/-!
Protocol invariants along an attack trace. If each entrypoint and each
environment step the token model allows preserves the invariant, then
the invariant still holds after any well-formed sequence of such steps.

Token uses the unrestricted form (its invariant is only about its own
storage). Vault and AMM use the form that only assumes preservation on
calls that actually target this contract.
-/

namespace Lsc.Security

/-- If every entrypoint preserves the protocol invariant, and so does every
environment step the token model allows, then the invariant still holds
after any well-formed attack trace. Reverted calls leave the world
unchanged, so they cannot break it. Token uses this to carry "balances
sum to supply" from a single transaction to a whole attack. -/
theorem inv_run {C : Spec S X E ε} {Inv : World S X E → Prop} {rely : X → X → Prop}
    (hC : PreservesInv C Inv) (hE : PreservesInvEnv C Inv rely)
    {w : World S X E} (hw : Inv w) {self : Address} (tr : List (Step C))
    (hW : Wf self tr) (hR : RelyAlong rely tr w) :
    Inv (run tr w) :=
  Proof.inv_run hC hE hw tr hW hR

/-- Same conclusion as `inv_run`, but the invariant is only assumed to
survive calls that target this contract with a distinct sender. Vault and
AMM need this because their invariant mentions this contract's token
balance, which cannot be claimed for a call to some other address. -/
theorem inv_run_at {C : Spec S X E ε} {Inv : World S X E → Prop} {rely : X → X → Prop}
    {self : Address}
    (hC : PreservesInvAt C Inv self) (hE : PreservesInvEnv C Inv rely)
    {w : World S X E} (hw : Inv w) (tr : List (Step C))
    (hW : Wf self tr) (hR : RelyAlong rely tr w) :
    Inv (run tr w) :=
  Proof.inv_run_at hC hE hw tr hW hR

end Lsc.Security
