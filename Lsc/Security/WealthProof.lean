import Lsc.Security.Wealth
import Lsc.Security.InvariantTheorems

/-!
Proofs of the generic extraction and solvency theorems. Statements live in
`WealthTheorems`.
-/

namespace Lsc.Security.Proof

variable {S X E ε : Type} {C : Spec S X E ε}

theorem no_unauthorized_extraction {Inv : World S X E → Prop} {claim : Claim S X E}
    {Auth : AuthPred C} {rely : X → X → Prop}
    (hN : NoUnauthorizedDecrease C Inv claim Auth)
    (hP : PreservesInv C Inv) (hE : PreservesInvEnv C Inv rely)
    (hM : ClaimMonoEnv claim rely)
    (tr : List (Step C)) (w : World S X E) (a : Address)
    (hw : Inv w) (hR : RelyAlong rely tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w ≤ claim a (run tr w) := by
  induction tr generalizing w with
  | nil => simp [run]
  | cons s tr ih =>
    match s with
    | .call c =>
      obtain ⟨hna, htl⟩ := hA
      have hw' : Inv (step (.call c) w) := hP c w hw
      have hle : claim a w ≤ claim a (step (.call c) w) :=
        Nat.le_of_not_lt fun hlt => hna (hN c w a hw hlt)
      exact Nat.le_trans hle (ih (step (.call c) w) hw' hR htl)
    | .env x' =>
      obtain ⟨hr, htl⟩ := hR
      have hw' : Inv { w with ext := x' } := hE w x' hw hr
      have hle : claim a w ≤ claim a { w with ext := x' } := hM w x' a hr
      exact Nat.le_trans hle (ih { w with ext := x' } hw' htl hA)

theorem no_unauthorized_extraction_at {Inv : World S X E → Prop} {claim : Claim S X E}
    {Auth : AuthPred C} {rely : X → X → Prop} {self : Address}
    (hN : NoUnauthorizedDecrease C Inv claim Auth)
    (hP : PreservesInvAt C Inv self) (hE : PreservesInvEnv C Inv rely)
    (hM : ClaimMonoEnv claim rely)
    (tr : List (Step C)) (w : World S X E) (a : Address)
    (hw : Inv w) (hW : Wf self tr) (hR : RelyAlong rely tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w ≤ claim a (run tr w) := by
  induction tr generalizing w with
  | nil => simp [run]
  | cons s tr ih =>
    match s with
    | .call c =>
      obtain ⟨hna, htl⟩ := hA
      have ⟨ht, hs, hWtl⟩ := hW
      have hw' : Inv (step (.call c) w) := hP c w ht hs hw
      have hle : claim a w ≤ claim a (step (.call c) w) :=
        Nat.le_of_not_lt fun hlt => hna (hN c w a hw hlt)
      exact Nat.le_trans hle (ih (step (.call c) w) hw' hWtl hR htl)
    | .env x' =>
      obtain ⟨hr, htl⟩ := hR
      have hw' : Inv { w with ext := x' } := hE w x' hw hr
      have hle : claim a w ≤ claim a { w with ext := x' } := hM w x' a hr
      exact Nat.le_trans hle (ih { w with ext := x' } hw' hW htl hA)

theorem solvent_run {Inv : World S X E → Prop} {claim : Claim S X E}
    {holdings : Holdings S X E} {rely : X → X → Prop}
    (hP : PreservesInv C Inv) (hE : PreservesInvEnv C Inv rely)
    (hS : ∀ self w, Inv w → Solvent claim holdings self w)
    {self : Address} {w : World S X E} (hw : Inv w) (tr : List (Step C))
    (hW : Wf self tr) (hR : RelyAlong rely tr w) :
    Solvent claim holdings self (run tr w) :=
  hS self _ (inv_run hP hE hw tr hW hR)

theorem solvent_run_at {Inv : World S X E → Prop} {claim : Claim S X E}
    {holdings : Holdings S X E} {rely : X → X → Prop} {self : Address}
    (hP : PreservesInvAt C Inv self) (hE : PreservesInvEnv C Inv rely)
    (hS : ∀ w, Inv w → Solvent claim holdings self w)
    {w : World S X E} (hw : Inv w) (tr : List (Step C))
    (hW : Wf self tr) (hR : RelyAlong rely tr w) :
    Solvent claim holdings self (run tr w) :=
  hS _ (inv_run_at hP hE hw tr hW hR)

theorem sum_update_mem {α : Type} [DecidableEq α] (H : Finset α) (f : α → Nat) {i : α}
    (hi : i ∈ H) (n : Nat) :
    H.sum (Function.update f i n) + f i = H.sum f + n := by
  have hsum := Finset.sum_erase_add (s := H) (f := f) hi
  have hsum' := Finset.sum_erase_add (s := H) (f := Function.update f i n) hi
  have hframe : (H.erase i).sum (Function.update f i n) = (H.erase i).sum f :=
    Finset.sum_congr rfl fun y hy =>
      Function.update_of_ne (Finset.ne_of_mem_erase hy) n f
  rw [← hsum', Function.update_self, hframe, Nat.add_assoc, Nat.add_comm n, ← Nat.add_assoc, hsum]

theorem sum_update_not_mem {α : Type} [DecidableEq α] (H : Finset α) (f : α → Nat) {i : α}
    (hi : i ∉ H) (n : Nat) :
    H.sum (Function.update f i n) = H.sum f :=
  Finset.sum_congr rfl fun y hy =>
    Function.update_of_ne (by intro h; subst h; exact hi hy) n f

theorem Claim.ofSelf_congr (c : Address → S → Nat)
    {w w' : World S X E} {a : Address} (h : w.self = w'.self) :
    Claim.ofSelf (S := S) (X := X) (E := E) c a w =
      Claim.ofSelf (S := S) (X := X) (E := E) c a w' := by
  simp [Claim.ofSelf, h]

theorem ClaimMonoEnv.of_self (c : Address → S → Nat) (rely : X → X → Prop) :
    ClaimMonoEnv (Claim.ofSelf (S := S) (X := X) (E := E) c) rely := by
  intro _ _ _ _; exact Nat.le_refl _

theorem NoUnauthorizedDecrease.of_fns {Inv : World S X E → Prop} {claim : Claim S X E}
    {Auth : AuthPred C} (h : ∀ fn, NoUnauthorizedDecreaseFn C Inv claim Auth fn) :
    NoUnauthorizedDecrease C Inv claim Auth := by
  intro c w a hInv hlt
  simpa [step, Call.ofCtx_toCtx] using h c.fn c.args c.toCtx w a hInv hlt

theorem NoUnauthorizedDecreaseFn_of_ok {Inv : World S X E → Prop} {claim : Claim S X E}
    {Auth : AuthPred C} {fn : C.Fn}
    (hok : ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E) (a : Address)
        (ret : C.Ret fn) (w' : World S X E),
      Inv w → Tx.run (C.exec fn args) ctx w = .ok (ret, w') →
      claim a w' < claim a w →
      Auth a (Call.ofCtx ctx fn args) w) :
    NoUnauthorizedDecreaseFn C Inv claim Auth fn := by
  intro args ctx w a hInv hdec
  cases h : Tx.run (C.exec fn args) ctx w with
  | error _ => simp [worldAfter_error h] at hdec
  | ok p =>
    exact hok args ctx w a p.1 p.2 hInv h (by simpa [worldAfter_ok h] using hdec)

theorem Conservation.of_fns {Inv : World S X E → Prop} {claim : Claim S X E} {inflow : Inflow C}
    (h : ∀ fn, ConservesFn C Inv claim inflow fn) : Conservation C Inv claim inflow := by
  intro c w hInv
  simpa [step, Call.ofCtx_toCtx] using h c.fn c.args c.toCtx w hInv

theorem ConservesFn_of_ok {Inv : World S X E → Prop} {claim : Claim S X E}
    {inflow : Inflow C} {fn : C.Fn}
    (hok : ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E) (ret : C.Ret fn)
        (w' : World S X E),
      Inv w → Tx.run (C.exec fn args) ctx w = .ok (ret, w') →
      ∃ T : Finset Address,
        (∀ a, a ∉ T → claim a w' = claim a w) ∧
        T.sum (fun a => claim a w') ≤
          T.sum (fun a => claim a w) + inflow (Call.ofCtx ctx fn args) w) :
    ConservesFn C Inv claim inflow fn := by
  intro args ctx w hInv
  cases h : Tx.run (C.exec fn args) ctx w with
  | error _ =>
    refine ⟨∅, ?_, ?_⟩
    · intro a _; simp [worldAfter_error h]
    · simp [worldAfter_error h]
  | ok p =>
    simpa [worldAfter_ok h] using hok args ctx w p.1 p.2 hInv h

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

end Lsc.Security.Proof
