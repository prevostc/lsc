import Lsc.Security.Wealth
import Lsc.Security.WealthProof

/-!
Generic victim-side wealth theorems over the trace semantics. Contract
instances (Token, Vault, AMM) discharge the local `lsc_contract` hypotheses
and inherit these conclusions.
-/

namespace Lsc.Security

variable {S X E ε : Type} {C : Spec S X E ε}

/-- If `Inv` holds initially and is preserved by every call and every
rely-conformant environment step, and account `a` never authorised a call on
the trace (`NoAuthAlong`, judged in each pre-state so allowances are
state-dependent), then `claim a` does not decrease. This is the victim-side
statement of "no unauthorized extraction": other users may trade, but they
cannot reduce `a`'s protocol claim without `a`'s permission. Reverts are
no-ops; the adversary may interleave `env` steps under `Rely`. -/
theorem no_unauthorized_extraction {Inv : World S X E → Prop} {claim : Claim S}
    {Auth : AuthPred C} {rely : X → X → Prop}
    (hN : NoUnauthorizedDecrease C Inv claim Auth)
    (hP : PreservesInv C Inv) (hE : PreservesInvEnv C Inv rely)
    (self : Address) (tr : List (Step C)) (w : World S X E) (a : Address)
    (hw : Inv w) (_hW : Wf self tr) (hR : RelyAlong rely tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  Proof.no_unauthorized_extraction hN hP hE self tr w a hw _hW hR hA

/-- Same guarantee as `no_unauthorized_extraction` when `Inv` is only preserved
by well-formed calls at `self`. Vault and AMM need this form because their
invariants mention the contract's own external-token balance. -/
theorem no_unauthorized_extraction_at {Inv : World S X E → Prop} {claim : Claim S}
    {Auth : AuthPred C} {rely : X → X → Prop} {self : Address}
    (hN : NoUnauthorizedDecrease C Inv claim Auth)
    (hP : PreservesInvAt C Inv self) (hE : PreservesInvEnv C Inv rely)
    (tr : List (Step C)) (w : World S X E) (a : Address)
    (hw : Inv w) (hW : Wf self tr) (hR : RelyAlong rely tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  Proof.no_unauthorized_extraction_at hN hP hE tr w a hw hW hR hA

/-- If `Inv` already implies finite-support solvency (`Σ claim ≤ holdings`),
then solvency holds after every well-formed rely-trace. Per-step conservation
is not required — Vault's pro-rata `claim` is not conservative under floor
rounding, and solvency is the statement that matters there. -/
theorem solvent_run {Inv : World S X E → Prop} {claim : Claim S}
    {holdings : Holdings S X E} {rely : X → X → Prop}
    (hP : PreservesInv C Inv) (hE : PreservesInvEnv C Inv rely)
    (hS : ∀ self w, Inv w → Solvent claim holdings self w)
    {self : Address} {w : World S X E} (hw : Inv w) (tr : List (Step C))
    (hW : Wf self tr) (hR : RelyAlong rely tr w) :
    Solvent claim holdings self (run tr w) :=
  Proof.solvent_run hP hE hS hw tr hW hR

/-- `solvent_run` when `Inv` is preserved only at `self` (Vault/AMM holdings). -/
theorem solvent_run_at {Inv : World S X E → Prop} {claim : Claim S}
    {holdings : Holdings S X E} {rely : X → X → Prop} {self : Address}
    (hP : PreservesInvAt C Inv self) (hE : PreservesInvEnv C Inv rely)
    (hS : ∀ w, Inv w → Solvent claim holdings self w)
    {w : World S X E} (hw : Inv w) (tr : List (Step C))
    (hW : Wf self tr) (hR : RelyAlong rely tr w) :
    Solvent claim holdings self (run tr w) :=
  Proof.solvent_run_at hP hE hS hw tr hW hR

end Lsc.Security
