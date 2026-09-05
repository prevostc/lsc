import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lsc.Security.Invariant

namespace Lsc.Security

variable {S X E ε : Type} {C : Spec S X E ε}

/-! ### Finite sums over `Address → Nat` (Nat is not a group: avoid `sum − x`) -/

/-- Updating a member of a finite support replaces its contribution in the sum. -/
theorem sum_update_mem {α : Type} [DecidableEq α] (H : Finset α) (f : α → Nat) {i : α}
    (hi : i ∈ H) (n : Nat) :
    H.sum (Function.update f i n) + f i = H.sum f + n := by
  have hsum := Finset.sum_erase_add (s := H) (f := f) hi
  have hsum' := Finset.sum_erase_add (s := H) (f := Function.update f i n) hi
  have hframe : (H.erase i).sum (Function.update f i n) = (H.erase i).sum f :=
    Finset.sum_congr rfl fun y hy =>
      Function.update_of_ne (Finset.ne_of_mem_erase hy) n f
  rw [← hsum', Function.update_self, hframe, Nat.add_assoc, Nat.add_comm n, ← Nat.add_assoc, hsum]

/-- Updating a key outside a finite support does not change the sum. -/
theorem sum_update_not_mem {α : Type} [DecidableEq α] (H : Finset α) (f : α → Nat) {i : α}
    (hi : i ∉ H) (n : Nat) :
    H.sum (Function.update f i n) = H.sum f :=
  Finset.sum_congr rfl fun y hy =>
    Function.update_of_ne (by intro h; subst h; exact hi hy) n f

/-- `claim a` is what the protocol owes `a` (ERC20: balance). -/
abbrev Claim (S : Type) := Address → S → Nat

/-- Permission to decrease `claim a`. Evaluated in the **pre-state**. -/
abbrev AuthPred (C : Spec S X E ε) := Address → Call C → S → Prop

/-- A decrease of `claim a` on a call is only possible when `Auth a` holds in the pre-state. -/
def NoUnauthorizedDecrease (C : Spec S X E ε) (claim : Claim S) (Auth : AuthPred C) : Prop :=
  ∀ (c : Call C) (w : World S X E) (a : Address),
    claim a (step (.call c) w).self < claim a w.self → Auth a c w.self

/-- Per-entrypoint form of `NoUnauthorizedDecrease` (unpacked args, no `Call` in the hyp). -/
def NoUnauthorizedDecreaseFn (C : Spec S X E ε) (claim : Claim S) (Auth : AuthPred C)
    (fn : C.Fn) : Prop :=
  ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E) (a : Address),
    claim a (worldAfter (C.exec fn args) ctx w).self < claim a w.self →
    Auth a (Call.ofCtx ctx fn args) w.self

theorem NoUnauthorizedDecrease.of_fns {claim : Claim S} {Auth : AuthPred C}
    (h : ∀ fn, NoUnauthorizedDecreaseFn C claim Auth fn) :
    NoUnauthorizedDecrease C claim Auth := by
  intro c w a hlt
  simpa [step, Call.ofCtx_toCtx] using h c.fn c.args c.toCtx w a hlt

/--
`Auth` is state-dependent (allowance), so the hyp must follow the prefix state.
Environment steps are skipped (`Auth` is only judged at calls).
-/
def NoAuthAlong (Auth : AuthPred C) (a : Address) : List (Step C) → World S X E → Prop
  | [], _ => True
  | .call c :: tr, w => ¬ Auth a c w.self ∧ NoAuthAlong Auth a tr (step (.call c) w)
  | .env x' :: tr, w => NoAuthAlong Auth a tr { w with ext := x' }

/-- Victim-side: if `a` never authorised a call along `tr`, `claim a` is non-decreasing. -/
theorem no_unauthorized_extraction {claim : Claim S} {Auth : AuthPred C}
    (hN : NoUnauthorizedDecrease C claim Auth)
    (self : Address) (tr : List (Step C)) (w : World S X E) (a : Address)
    (_hW : Wf self tr)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self := by
  induction tr generalizing w with
  | nil => simp [run]
  | cons s tr ih =>
    match s with
    | .call c =>
      obtain ⟨hna, htl⟩ := hA
      have hle : claim a w.self ≤ claim a (step (.call c) w).self :=
        Nat.le_of_not_lt fun hlt => hna (hN c w a hlt)
      exact Nat.le_trans hle (ih (step (.call c) w) (by exact _hW.2.2) htl)
    | .env x' =>
      simpa [step] using ih { w with ext := x' } _hW hA

/-! ### Conservation (local) and solvency -/

/-- Actual inflow of claim-units on this call (0 on revert). -/
abbrev Inflow (C : Spec S X E ε) := Call C → World S X E → Nat

/-- ∃ a touched set `T` closed for `claim`, and `T` conserves up to `inflow`. -/
def Conservation (C : Spec S X E ε) (claim : Claim S) (inflow : Inflow C) : Prop :=
  ∀ (c : Call C) (w : World S X E),
    ∃ T : Finset Address,
      (∀ a, a ∉ T → claim a (step (.call c) w).self = claim a w.self) ∧
      T.sum (fun a => claim a (step (.call c) w).self) ≤
        T.sum (fun a => claim a w.self) + inflow c w

/-- Per-entrypoint form of `Conservation` (unpacked args). -/
def ConservesFn (C : Spec S X E ε) (claim : Claim S) (inflow : Inflow C) (fn : C.Fn) : Prop :=
  ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E),
    ∃ T : Finset Address,
      (∀ a, a ∉ T →
        claim a (worldAfter (C.exec fn args) ctx w).self = claim a w.self) ∧
      T.sum (fun a => claim a (worldAfter (C.exec fn args) ctx w).self) ≤
        T.sum (fun a => claim a w.self) + inflow (Call.ofCtx ctx fn args) w

theorem Conservation.of_fns {claim : Claim S} {inflow : Inflow C}
    (h : ∀ fn, ConservesFn C claim inflow fn) : Conservation C claim inflow := by
  intro c w
  simpa [step, Call.ofCtx_toCtx] using h c.fn c.args c.toCtx w

/-- Assets the contract actually controls, read from storage or the external-token ghost. -/
abbrev Holdings (S X E : Type) := Address → World S X E → Nat

/-- `∉ H → claim = 0` (finite support) and `∑_H claim ≤ holdings self`. -/
def Solvent (claim : Claim S) (holdings : Holdings S X E) (self : Address)
    (w : World S X E) : Prop :=
  ∃ H : Finset Address,
    (∀ a, a ∉ H → claim a w.self = 0) ∧
    H.sum (fun a => claim a w.self) ≤ holdings self w

/-- `Inv ⇒ Solvent`, transported by `inv_run`. No extra conservation needed. -/
theorem solvent_run {Inv : World S X E → Prop} {claim : Claim S}
    {holdings : Holdings S X E} {rely : X → X → Prop}
    (hP : PreservesInv C Inv) (hE : PreservesInvEnv C Inv rely)
    (hS : ∀ self w, Inv w → Solvent claim holdings self w)
    {self : Address} {w : World S X E} (hw : Inv w) (tr : List (Step C))
    (hW : Wf self tr) (hR : RelyAlong rely tr w) :
    Solvent claim holdings self (run tr w) :=
  hS self _ (inv_run hP hE hw tr hW hR)

end Lsc.Security
