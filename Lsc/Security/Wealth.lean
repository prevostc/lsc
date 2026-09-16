import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lsc.Security.Invariant

namespace Lsc.Security

variable {S X E ε : Type} {C : Spec S X E ε}

/-! ### Finite sums over `Address → Nat` (Nat is not a group: avoid `sum − x`) -/

/-- `claim a w` is what the protocol owes `a` in world `w` (ERC20: balance).
A storage-only measure is the special case `fun a w => c a w.self`. -/
abbrev Claim (S X E : Type) := Address → World S X E → Nat

/-- Storage-only claim, as Token uses: `claim a w = c a w.self`. -/
abbrev Claim.ofSelf {S X E : Type} (c : Address → S → Nat) : Claim S X E :=
  fun a w => c a w.self

/-- Permission to decrease `claim a`. Evaluated in the **pre-state**. -/
abbrev AuthPred (C : Spec S X E ε) := Address → Call C → World S X E → Prop

/-- Storage-only authorisation: `Auth a c w = A a c w.self`. -/
abbrev AuthPred.ofSelf (A : Address → Call C → S → Prop) : AuthPred C :=
  fun a c w => A a c w.self

/-- Environment steps allowed by `rely` do not decrease `claim`. Automatic
when `claim` depends only on storage (`ClaimMonoEnv.of_self`). -/
def ClaimMonoEnv (claim : Claim S X E) (rely : X → X → Prop) : Prop :=
  ∀ (w : World S X E) (x' : X) (a : Address),
    rely w.ext x' → claim a w ≤ claim a { w with ext := x' }

/-- A decrease of `claim a` on a call from a world satisfying `Inv` is only possible
when `Auth a` holds in the pre-state. Relative to `Inv`: a pro-rata `claim` is only
monotone under the protocol invariant. -/
def NoUnauthorizedDecrease [HasCreditValue X] (C : Spec S X E ε)
    (Inv : World S X E → Prop)
    (claim : Claim S X E) (Auth : AuthPred C) : Prop :=
  ∀ (c : Call C) (w : World S X E) (a : Address),
    Inv w → claim a (step (.call c) w) < claim a w → Auth a c w

/-- Per-entrypoint form of `NoUnauthorizedDecrease` (unpacked args, no `Call` in the hyp). -/
def NoUnauthorizedDecreaseFn (C : Spec S X E ε) (Inv : World S X E → Prop)
    (claim : Claim S X E) (Auth : AuthPred C) (fn : C.Fn) : Prop :=
  ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E) (a : Address),
    Inv w →
    claim a (worldAfter (C.exec fn args) ctx w) < claim a w →
    Auth a (Call.ofCtx ctx fn args) w

/--
`Auth` is state-dependent (allowance), so the hyp must follow the prefix state.
Environment steps are skipped (`Auth` is only judged at calls).
-/
def NoAuthAlong [HasCreditValue X] (Auth : AuthPred C) (a : Address) :
    List (Step C) → World S X E → Prop
  | [], _ => True
  | .call c :: tr, w => ¬ Auth a c w ∧ NoAuthAlong Auth a tr (step (.call c) w)
  | .env x' :: tr, w => NoAuthAlong Auth a tr { w with ext := x' }

/-! Trace theorems `no_unauthorized_extraction` / `_at` live in `WealthTheorems`. -/

/-! ### Conservation (local) and solvency -/

/-- Actual inflow of claim-units on this call (0 on revert). -/
abbrev Inflow (C : Spec S X E ε) := Call C → World S X E → Nat

/-- ∃ a touched set `T` closed for `claim`, and `T` conserves up to `inflow`.
Stated from worlds satisfying `Inv` (a pro-rata `claim` is only conservative under `Inv`). -/
def Conservation [HasCreditValue X] (C : Spec S X E ε) (Inv : World S X E → Prop)
    (claim : Claim S X E)
    (inflow : Inflow C) : Prop :=
  ∀ (c : Call C) (w : World S X E),
    Inv w →
    ∃ T : Finset Address,
      (∀ a, a ∉ T → claim a (step (.call c) w) = claim a w) ∧
      T.sum (fun a => claim a (step (.call c) w)) ≤
        T.sum (fun a => claim a w) + inflow c w

/-- Per-entrypoint form of `Conservation` (unpacked args). -/
def ConservesFn (C : Spec S X E ε) (Inv : World S X E → Prop) (claim : Claim S X E)
    (inflow : Inflow C) (fn : C.Fn) : Prop :=
  ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E),
    Inv w →
    ∃ T : Finset Address,
      (∀ a, a ∉ T →
        claim a (worldAfter (C.exec fn args) ctx w) = claim a w) ∧
      T.sum (fun a => claim a (worldAfter (C.exec fn args) ctx w)) ≤
        T.sum (fun a => claim a w) + inflow (Call.ofCtx ctx fn args) w

/-- Assets the contract actually controls, read from storage or the world (oracle). -/
abbrev Holdings (S X E : Type) := Address → World S X E → Nat

/-- `∉ H → claim = 0` (finite support) and `∑_H claim ≤ holdings self`. -/
def Solvent (claim : Claim S X E) (holdings : Holdings S X E) (self : Address)
    (w : World S X E) : Prop :=
  ∃ H : Finset Address,
    (∀ a, a ∉ H → claim a w = 0) ∧
    H.sum (fun a => claim a w) ≤ holdings self w

/-! `solvent_run` / `solvent_run_at` live in `WealthTheorems`. -/

end Lsc.Security
