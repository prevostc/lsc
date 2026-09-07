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

/-- A decrease of `claim a` on a call from a world satisfying `Inv` is only possible
when `Auth a` holds in the pre-state. Relative to `Inv`: a pro-rata `claim` is only
monotone under the protocol invariant. -/
def NoUnauthorizedDecrease (C : Spec S X E ε) (Inv : World S X E → Prop)
    (claim : Claim S) (Auth : AuthPred C) : Prop :=
  ∀ (c : Call C) (w : World S X E) (a : Address),
    Inv w → claim a (step (.call c) w).self < claim a w.self → Auth a c w.self

/-- Per-entrypoint form of `NoUnauthorizedDecrease` (unpacked args, no `Call` in the hyp). -/
def NoUnauthorizedDecreaseFn (C : Spec S X E ε) (Inv : World S X E → Prop)
    (claim : Claim S) (Auth : AuthPred C) (fn : C.Fn) : Prop :=
  ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E) (a : Address),
    Inv w →
    claim a (worldAfter (C.exec fn args) ctx w).self < claim a w.self →
    Auth a (Call.ofCtx ctx fn args) w.self

theorem NoUnauthorizedDecrease.of_fns {Inv : World S X E → Prop} {claim : Claim S}
    {Auth : AuthPred C} (h : ∀ fn, NoUnauthorizedDecreaseFn C Inv claim Auth fn) :
    NoUnauthorizedDecrease C Inv claim Auth := by
  intro c w a hInv hlt
  simpa [step, Call.ofCtx_toCtx] using h c.fn c.args c.toCtx w a hInv hlt

/-- Reduce `NoUnauthorizedDecreaseFn` to the success path: a revert cannot decrease `claim`. -/
theorem NoUnauthorizedDecreaseFn_of_ok {Inv : World S X E → Prop} {claim : Claim S}
    {Auth : AuthPred C} {fn : C.Fn}
    (hok : ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E) (a : Address)
        (ret : C.Ret fn) (w' : World S X E),
      Inv w → Tx.run (C.exec fn args) ctx w = .ok (ret, w') →
      claim a w'.self < claim a w.self →
      Auth a (Call.ofCtx ctx fn args) w.self) :
    NoUnauthorizedDecreaseFn C Inv claim Auth fn := by
  intro args ctx w a hInv hdec
  cases h : Tx.run (C.exec fn args) ctx w with
  | error _ => simp [worldAfter, h] at hdec
  | ok p =>
    exact hok args ctx w a p.1 p.2 hInv h (by simpa [worldAfter, h] using hdec)

/--
`Auth` is state-dependent (allowance), so the hyp must follow the prefix state.
Environment steps are skipped (`Auth` is only judged at calls).
-/
def NoAuthAlong (Auth : AuthPred C) (a : Address) : List (Step C) → World S X E → Prop
  | [], _ => True
  | .call c :: tr, w => ¬ Auth a c w.self ∧ NoAuthAlong Auth a tr (step (.call c) w)
  | .env x' :: tr, w => NoAuthAlong Auth a tr { w with ext := x' }

/-! Trace theorems `no_unauthorized_extraction` / `_at` live in `WealthTheorems`. -/

/-! ### Conservation (local) and solvency -/

/-- Actual inflow of claim-units on this call (0 on revert). -/
abbrev Inflow (C : Spec S X E ε) := Call C → World S X E → Nat

/-- ∃ a touched set `T` closed for `claim`, and `T` conserves up to `inflow`.
Stated from worlds satisfying `Inv` (a pro-rata `claim` is only conservative under `Inv`). -/
def Conservation (C : Spec S X E ε) (Inv : World S X E → Prop) (claim : Claim S)
    (inflow : Inflow C) : Prop :=
  ∀ (c : Call C) (w : World S X E),
    Inv w →
    ∃ T : Finset Address,
      (∀ a, a ∉ T → claim a (step (.call c) w).self = claim a w.self) ∧
      T.sum (fun a => claim a (step (.call c) w).self) ≤
        T.sum (fun a => claim a w.self) + inflow c w

/-- Per-entrypoint form of `Conservation` (unpacked args). -/
def ConservesFn (C : Spec S X E ε) (Inv : World S X E → Prop) (claim : Claim S)
    (inflow : Inflow C) (fn : C.Fn) : Prop :=
  ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E),
    Inv w →
    ∃ T : Finset Address,
      (∀ a, a ∉ T →
        claim a (worldAfter (C.exec fn args) ctx w).self = claim a w.self) ∧
      T.sum (fun a => claim a (worldAfter (C.exec fn args) ctx w).self) ≤
        T.sum (fun a => claim a w.self) + inflow (Call.ofCtx ctx fn args) w

theorem Conservation.of_fns {Inv : World S X E → Prop} {claim : Claim S} {inflow : Inflow C}
    (h : ∀ fn, ConservesFn C Inv claim inflow fn) : Conservation C Inv claim inflow := by
  intro c w hInv
  simpa [step, Call.ofCtx_toCtx] using h c.fn c.args c.toCtx w hInv

/-- Reduce `ConservesFn` to the success path: a revert is conservation with empty touch-set. -/
theorem ConservesFn_of_ok {Inv : World S X E → Prop} {claim : Claim S}
    {inflow : Inflow C} {fn : C.Fn}
    (hok : ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E) (ret : C.Ret fn)
        (w' : World S X E),
      Inv w → Tx.run (C.exec fn args) ctx w = .ok (ret, w') →
      ∃ T : Finset Address,
        (∀ a, a ∉ T → claim a w'.self = claim a w.self) ∧
        T.sum (fun a => claim a w'.self) ≤
          T.sum (fun a => claim a w.self) + inflow (Call.ofCtx ctx fn args) w) :
    ConservesFn C Inv claim inflow fn := by
  intro args ctx w hInv
  cases h : Tx.run (C.exec fn args) ctx w with
  | error _ =>
    refine ⟨∅, ?_, ?_⟩
    · intro a _; simp [worldAfter, h]
    · simp [worldAfter, h]
  | ok p =>
    simpa [worldAfter, h] using hok args ctx w p.1 p.2 hInv h

/-- Assets the contract actually controls, read from storage or the external-token ghost. -/
abbrev Holdings (S X E : Type) := Address → World S X E → Nat

/-- `∉ H → claim = 0` (finite support) and `∑_H claim ≤ holdings self`. -/
def Solvent (claim : Claim S) (holdings : Holdings S X E) (self : Address)
    (w : World S X E) : Prop :=
  ∃ H : Finset Address,
    (∀ a, a ∉ H → claim a w.self = 0) ∧
    H.sum (fun a => claim a w.self) ≤ holdings self w

/-! `solvent_run` / `solvent_run_at` live in `WealthTheorems`. -/

/-- `Σ ⌊f a * num / den⌋ ≤ num` when `Σ f = den` and `den > 0`. -/
theorem sum_mul_div_le {α : Type} [DecidableEq α] (H : Finset α) (f : α → Nat) (num den : Nat)
    (hsum : H.sum f = den) (hpos : 0 < den) :
    H.sum (fun a => f a * num / den) ≤ num := by
  have hmul_right : ∀ (s : Finset α) (g : α → Nat) (n : Nat),
      s.sum g * n = s.sum (fun a => g a * n) := by
    intro s g n
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Nat.add_mul, ih]
  have hmul_left : ∀ (s : Finset α) (g : α → Nat) (n : Nat),
      n * s.sum g = s.sum (fun a => n * g a) := by
    intro s g n
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Nat.mul_add, ih]
  have hle : ∀ (s : Finset α) (g h : α → Nat), (∀ a ∈ s, g a ≤ h a) → s.sum g ≤ s.sum h := by
    intro s g h hh
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact Nat.add_le_add (hh a (Finset.mem_insert_self _ _))
        (ih fun x hx => hh x (Finset.mem_insert_of_mem hx))
  have hbound :
      H.sum (fun a => f a * num / den) * den ≤ H.sum (fun a => f a * num) := by
    rw [hmul_right]
    exact hle _ _ _ fun _ _ => Nat.div_mul_le_self _ _
  have hrhs : H.sum (fun a => f a * num) = num * den := by
    have h1 : H.sum (fun a => f a * num) = H.sum (fun a => num * f a) :=
      Finset.sum_congr rfl fun _ _ => Nat.mul_comm _ _
    rw [h1, ← hmul_left, hsum]
  have : H.sum (fun a => f a * num / den) * den ≤ num * den := by
    rw [← hrhs]; exact hbound
  exact Nat.le_of_mul_le_mul_right this hpos

end Lsc.Security
