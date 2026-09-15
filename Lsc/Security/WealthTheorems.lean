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
and those environment steps. Environment steps must not themselves decrease
the claim (`ClaimMonoEnv`; automatic when `claim` depends only on storage).
Unlike `no_unauthorized_extraction_at`, this form does not require the caller
to differ from the contract, and does not restrict to calls that target this
contract. -/
theorem no_unauthorized_extraction {Inv : World S X E → Prop} {claim : Claim S X E}
    {Auth : AuthPred C} {rely : X → X → Prop}
    (hN : NoUnauthorizedDecrease C Inv claim Auth)
    (hP : PreservesInv C Inv) (hE : PreservesInvEnv C Inv rely)
    (hM : ClaimMonoEnv claim rely)
    (tr : List (Step C)) (w : World S X E) (a : Address)
    (hw : Inv w) (hR : RelyAlong rely tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w ≤ claim a (run tr w) :=
  Proof.no_unauthorized_extraction hN hP hE hM tr w a hw hR hA

/-- Same victim-side guarantee as `no_unauthorized_extraction`, but the
invariant is only assumed to survive calls that actually target this
contract with a distinct sender. Vault and AMM need this form because
their invariant talks about "our" token balance, which would be
meaningless for a call to some other address; well-formedness (caller ≠
contract) is required here, not on `no_unauthorized_extraction`.
Authorisation is still judged in the pre-state of each call, so allowances
can change along the trace. -/
theorem no_unauthorized_extraction_at {Inv : World S X E → Prop} {claim : Claim S X E}
    {Auth : AuthPred C} {rely : X → X → Prop} {self : Address}
    (hN : NoUnauthorizedDecrease C Inv claim Auth)
    (hP : PreservesInvAt C Inv self) (hE : PreservesInvEnv C Inv rely)
    (hM : ClaimMonoEnv claim rely)
    (tr : List (Step C)) (w : World S X E) (a : Address)
    (hw : Inv w) (hW : Wf self tr) (hR : RelyAlong rely tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w ≤ claim a (run tr w) :=
  Proof.no_unauthorized_extraction_at hN hP hE hM tr w a hw hW hR hA

/-- If the protocol invariant already implies the contract does not owe more
than it holds, then after any well-formed attack trace it still doesn't.
Per-step conservation of claims is not required: Vault's floor-rounded
pro-rata shares can leak dust each step, and solvency is the statement
that matters there. The invariant must hold at the start and survive
every entrypoint and every environment step the token model allows. -/
theorem solvent_run {Inv : World S X E → Prop} {claim : Claim S X E}
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
theorem solvent_run_at {Inv : World S X E → Prop} {claim : Claim S X E}
    {holdings : Holdings S X E} {rely : X → X → Prop} {self : Address}
    (hP : PreservesInvAt C Inv self) (hE : PreservesInvEnv C Inv rely)
    (hS : ∀ w, Inv w → Solvent claim holdings self w)
    {w : World S X E} (hw : Inv w) (tr : List (Step C))
    (hW : Wf self tr) (hR : RelyAlong rely tr w) :
    Solvent claim holdings self (run tr w) :=
  Proof.solvent_run_at hP hE hS hw tr hW hR

/-- Updating a member of a finite support replaces its contribution in the sum. -/
theorem sum_update_mem {α : Type} [DecidableEq α] (H : Finset α) (f : α → Nat) {i : α}
    (hi : i ∈ H) (n : Nat) :
    H.sum (Function.update f i n) + f i = H.sum f + n :=
  Proof.sum_update_mem H f hi n

/-- Updating a key outside a finite support does not change the sum. -/
theorem sum_update_not_mem {α : Type} [DecidableEq α] (H : Finset α) (f : α → Nat) {i : α}
    (hi : i ∉ H) (n : Nat) :
    H.sum (Function.update f i n) = H.sum f :=
  Proof.sum_update_not_mem H f hi n

/-- `Claim.ofSelf` ignores `ext` and `log`. -/
theorem Claim.ofSelf_congr (c : Address → S → Nat)
    {w w' : World S X E} {a : Address} (h : w.self = w'.self) :
    Claim.ofSelf (S := S) (X := X) (E := E) c a w =
      Claim.ofSelf (S := S) (X := X) (E := E) c a w' :=
  Proof.Claim.ofSelf_congr c h

/-- Storage-only claims ignore `ext`, so any `rely` is claim-monotone. -/
theorem ClaimMonoEnv.of_self (c : Address → S → Nat) (rely : X → X → Prop) :
    ClaimMonoEnv (Claim.ofSelf (S := S) (X := X) (E := E) c) rely :=
  Proof.ClaimMonoEnv.of_self c rely

/-- `NoUnauthorizedDecrease` follows from the per-entrypoint form, invariance
of `Inv` and `claim` under the incoming-value credit. -/
theorem NoUnauthorizedDecrease.of_fns {Inv : World S X E → Prop}
    {claim : Claim S X E} {Auth : AuthPred C}
    (hcredit : ∀ (w : World S X E) (v : Nat), Inv w → Inv (World.creditValue w v))
    (hclaim : ∀ (w : World S X E) (v : Nat) (a : Address),
      claim a (World.creditValue w v) = claim a w)
    (hauth : ∀ (w : World S X E) (v : Nat) (a : Address) (c : Call C),
      Auth a c (World.creditValue w v) → Auth a c w)
    (h : ∀ fn, NoUnauthorizedDecreaseFn C Inv claim Auth fn) :
    NoUnauthorizedDecrease C Inv claim Auth :=
  Proof.NoUnauthorizedDecrease.of_fns hcredit hclaim hauth h

/-- Reduce `NoUnauthorizedDecreaseFn` to the success path: a revert cannot decrease `claim`. -/
theorem NoUnauthorizedDecreaseFn_of_ok {Inv : World S X E → Prop} {claim : Claim S X E}
    {Auth : AuthPred C} {fn : C.Fn}
    (hok : ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E) (a : Address)
        (ret : C.Ret fn) (w' : World S X E),
      Inv w → Tx.run (C.exec fn args) ctx w = .ok (ret, w') →
      claim a w' < claim a w →
      Auth a (Call.ofCtx ctx fn args) w) :
    NoUnauthorizedDecreaseFn C Inv claim Auth fn :=
  Proof.NoUnauthorizedDecreaseFn_of_ok hok

/-- `Conservation` follows from the per-entrypoint form, invariance of
`Inv` / `claim` / `inflow` under the incoming-value credit. -/
theorem Conservation.of_fns {Inv : World S X E → Prop} {claim : Claim S X E}
    {inflow : Inflow C}
    (hcredit : ∀ (w : World S X E) (v : Nat), Inv w → Inv (World.creditValue w v))
    (hclaim : ∀ (w : World S X E) (v : Nat) (a : Address),
      claim a (World.creditValue w v) = claim a w)
    (hin : ∀ (c : Call C) (w : World S X E),
      inflow c (World.creditValue w c.value) = inflow c w)
    (h : ∀ fn, ConservesFn C Inv claim inflow fn) : Conservation C Inv claim inflow :=
  Proof.Conservation.of_fns hcredit hclaim hin h

/-- Reduce `ConservesFn` to the success path: a revert is conservation with empty touch-set. -/
theorem ConservesFn_of_ok {Inv : World S X E → Prop} {claim : Claim S X E}
    {inflow : Inflow C} {fn : C.Fn}
    (hok : ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E) (ret : C.Ret fn)
        (w' : World S X E),
      Inv w → Tx.run (C.exec fn args) ctx w = .ok (ret, w') →
      ∃ T : Finset Address,
        (∀ a, a ∉ T → claim a w' = claim a w) ∧
        T.sum (fun a => claim a w') ≤
          T.sum (fun a => claim a w) + inflow (Call.ofCtx ctx fn args) w) :
    ConservesFn C Inv claim inflow fn :=
  Proof.ConservesFn_of_ok hok

/-- `Σ ⌊f a * num / den⌋ ≤ num` when `Σ f = den` and `den > 0`. -/
theorem sum_mul_div_le {α : Type} [DecidableEq α] (H : Finset α) (f : α → Nat) (num den : Nat)
    (hsum : H.sum f = den) (hpos : 0 < den) :
    H.sum (fun a => f a * num / den) ≤ num :=
  Proof.sum_mul_div_le H f num den hsum hpos

end Lsc.Security
