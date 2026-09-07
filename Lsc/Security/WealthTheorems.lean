import Lsc.Security.Wealth
import Lsc.Security.WealthProof

/-!
Victim-side wealth, once and for all contracts: nobody can reduce your
protocol claim without your authorisation, and if the invariant already
implies solvency then solvency survives any well-formed attack trace.

Each contract declares what a claim is, who may reduce it, and what
the contract holds. Token, Vault, and AMM discharge the local
obligations and inherit these conclusions. Reverted calls are no-ops;
between our calls the environment may change only as the token model
allows.
-/

namespace Lsc.Security

variable {S X E ε : Type} {C : Spec S X E ε}

/-- If a protocol never lowers an account's claim except when that account
authorised the call, then on any sequence of calls — any senders, any
arguments, interleaved with environment steps the token model allows — an
account that authorised nothing never sees its claim fall. "Authorised" is
whatever the contract declared: typically the victim sent the call, or an
allowance they granted covers it. Reverted calls leave the world unchanged.
The protocol invariant must hold at the start and survive every entrypoint
and those environment steps. Unlike `no_unauthorized_extraction_at`, this
form does not require the caller to differ from the contract, and does not
restrict to calls that target this contract. -/
theorem no_unauthorized_extraction {Inv : World S X E → Prop} {claim : Claim S}
    {Auth : AuthPred C} {rely : X → X → Prop}
    (hN : NoUnauthorizedDecrease C Inv claim Auth)
    (hP : PreservesInv C Inv) (hE : PreservesInvEnv C Inv rely)
    (tr : List (Step C)) (w : World S X E) (a : Address)
    (hw : Inv w) (hR : RelyAlong rely tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  Proof.no_unauthorized_extraction hN hP hE tr w a hw hR hA

/-- Same victim-side guarantee as `no_unauthorized_extraction`, but the
invariant is only assumed to survive calls that actually target this
contract with a distinct sender. Vault and AMM need this form because
their invariant talks about "our" token balance, which would be
meaningless for a call to some other address; well-formedness (caller ≠
contract) is required here, not on `no_unauthorized_extraction`.
Authorisation is still judged in the pre-state of each call, so allowances
can change along the trace. -/
theorem no_unauthorized_extraction_at {Inv : World S X E → Prop} {claim : Claim S}
    {Auth : AuthPred C} {rely : X → X → Prop} {self : Address}
    (hN : NoUnauthorizedDecrease C Inv claim Auth)
    (hP : PreservesInvAt C Inv self) (hE : PreservesInvEnv C Inv rely)
    (tr : List (Step C)) (w : World S X E) (a : Address)
    (hw : Inv w) (hW : Wf self tr) (hR : RelyAlong rely tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  Proof.no_unauthorized_extraction_at hN hP hE tr w a hw hW hR hA

/-- If the protocol invariant already implies the contract does not owe more
than it holds, then after any well-formed attack trace it still doesn't.
Per-step conservation of claims is not required: Vault's floor-rounded
pro-rata shares can leak dust each step, and solvency is the statement
that matters there. The invariant must hold at the start and survive
every entrypoint and every environment step the token model allows. -/
theorem solvent_run {Inv : World S X E → Prop} {claim : Claim S}
    {holdings : Holdings S X E} {rely : X → X → Prop}
    (hP : PreservesInv C Inv) (hE : PreservesInvEnv C Inv rely)
    (hS : ∀ self w, Inv w → Solvent claim holdings self w)
    {self : Address} {w : World S X E} (hw : Inv w) (tr : List (Step C))
    (hW : Wf self tr) (hR : RelyAlong rely tr w) :
    Solvent claim holdings self (run tr w) :=
  Proof.solvent_run hP hE hS hw tr hW hR

/-- Same solvency preservation as `solvent_run`, restricted to traces of
calls that target this contract with a distinct sender. Vault and AMM use
this form because "what the contract holds" is this contract's token
balance, which is only meaningful on calls to this address. -/
theorem solvent_run_at {Inv : World S X E → Prop} {claim : Claim S}
    {holdings : Holdings S X E} {rely : X → X → Prop} {self : Address}
    (hP : PreservesInvAt C Inv self) (hE : PreservesInvEnv C Inv rely)
    (hS : ∀ w, Inv w → Solvent claim holdings self w)
    {w : World S X E} (hw : Inv w) (tr : List (Step C))
    (hW : Wf self tr) (hR : RelyAlong rely tr w) :
    Solvent claim holdings self (run tr w) :=
  Proof.solvent_run_at hP hE hS hw tr hW hR

end Lsc.Security
