import Lsc.Security.Wealth
import Lsc.Security.InvariantTheorems

/-!
Proofs of the generic extraction and solvency theorems. Statements live in
`WealthTheorems`.
-/

namespace Lsc.Security.Proof

variable {S X E ε : Type} {C : Spec S X E ε}

theorem no_unauthorized_extraction {Inv : World S X E → Prop} {claim : Claim S}
    {Auth : AuthPred C} {rely : X → X → Prop}
    (hN : NoUnauthorizedDecrease C Inv claim Auth)
    (hP : PreservesInv C Inv) (hE : PreservesInvEnv C Inv rely)
    (tr : List (Step C)) (w : World S X E) (a : Address)
    (hw : Inv w) (hR : RelyAlong rely tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self := by
  induction tr generalizing w with
  | nil => simp [run]
  | cons s tr ih =>
    match s with
    | .call c =>
      obtain ⟨hna, htl⟩ := hA
      have hw' : Inv (step (.call c) w) := hP c w hw
      have hle : claim a w.self ≤ claim a (step (.call c) w).self :=
        Nat.le_of_not_lt fun hlt => hna (hN c w a hw hlt)
      exact Nat.le_trans hle (ih (step (.call c) w) hw' hR htl)
    | .env x' =>
      obtain ⟨hr, htl⟩ := hR
      have hw' : Inv { w with ext := x' } := hE w x' hw hr
      simpa [step] using ih { w with ext := x' } hw' htl hA

theorem no_unauthorized_extraction_at {Inv : World S X E → Prop} {claim : Claim S}
    {Auth : AuthPred C} {rely : X → X → Prop} {self : Address}
    (hN : NoUnauthorizedDecrease C Inv claim Auth)
    (hP : PreservesInvAt C Inv self) (hE : PreservesInvEnv C Inv rely)
    (tr : List (Step C)) (w : World S X E) (a : Address)
    (hw : Inv w) (hW : Wf self tr) (hR : RelyAlong rely tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self := by
  induction tr generalizing w with
  | nil => simp [run]
  | cons s tr ih =>
    match s with
    | .call c =>
      obtain ⟨hna, htl⟩ := hA
      have ⟨ht, hs, hWtl⟩ := hW
      have hw' : Inv (step (.call c) w) := hP c w ht hs hw
      have hle : claim a w.self ≤ claim a (step (.call c) w).self :=
        Nat.le_of_not_lt fun hlt => hna (hN c w a hw hlt)
      exact Nat.le_trans hle (ih (step (.call c) w) hw' hWtl hR htl)
    | .env x' =>
      obtain ⟨hr, htl⟩ := hR
      have hw' : Inv { w with ext := x' } := hE w x' hw hr
      simpa [step] using ih { w with ext := x' } hw' hW htl hA

theorem solvent_run {Inv : World S X E → Prop} {claim : Claim S}
    {holdings : Holdings S X E} {rely : X → X → Prop}
    (hP : PreservesInv C Inv) (hE : PreservesInvEnv C Inv rely)
    (hS : ∀ self w, Inv w → Solvent claim holdings self w)
    {self : Address} {w : World S X E} (hw : Inv w) (tr : List (Step C))
    (hW : Wf self tr) (hR : RelyAlong rely tr w) :
    Solvent claim holdings self (run tr w) :=
  hS self _ (inv_run hP hE hw tr hW hR)

theorem solvent_run_at {Inv : World S X E → Prop} {claim : Claim S}
    {holdings : Holdings S X E} {rely : X → X → Prop} {self : Address}
    (hP : PreservesInvAt C Inv self) (hE : PreservesInvEnv C Inv rely)
    (hS : ∀ w, Inv w → Solvent claim holdings self w)
    {w : World S X E} (hw : Inv w) (tr : List (Step C))
    (hW : Wf self tr) (hR : RelyAlong rely tr w) :
    Solvent claim holdings self (run tr w) :=
  hS _ (inv_run_at hP hE hw tr hW hR)

end Lsc.Security.Proof
