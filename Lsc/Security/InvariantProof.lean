import Lsc.Security.Invariant

/-!
Proofs of trace induction for `Inv`. Statements live in `InvariantTheorems`.
-/

namespace Lsc.Security.Proof

variable {S X E ε : Type}

theorem inv_run {C : Spec S X E ε} {Inv : World S X E → Prop} {rely : X → X → Prop}
    (hC : PreservesInv C Inv) (hE : PreservesInvEnv C Inv rely)
    {w : World S X E} (hw : Inv w) {self : Address} (tr : List (Step C))
    (hW : Wf self tr) (hR : RelyAlong rely tr w) :
    Inv (run tr w) := by
  induction tr generalizing w with
  | nil => simpa using hw
  | cons s tr ih =>
    match s with
    | .call c =>
      have htl : Wf self tr := hW.2.2
      exact ih (hC c w hw) htl hR
    | .env x' =>
      have ⟨hr, htl⟩ := hR
      exact ih (hE w x' hw hr) hW htl

theorem inv_run_at {C : Spec S X E ε} {Inv : World S X E → Prop} {rely : X → X → Prop}
    {self : Address}
    (hC : PreservesInvAt C Inv self) (hE : PreservesInvEnv C Inv rely)
    {w : World S X E} (hw : Inv w) (tr : List (Step C))
    (hW : Wf self tr) (hR : RelyAlong rely tr w) :
    Inv (run tr w) := by
  induction tr generalizing w with
  | nil => simpa using hw
  | cons s tr ih =>
    match s with
    | .call c =>
      have ⟨ht, hs, htl⟩ := hW
      exact ih (hC c w ht hs hw) htl hR
    | .env x' =>
      have ⟨hr, htl⟩ := hR
      exact ih (hE w x' hw hr) hW htl

theorem PreservesInv.of_fns {C : Spec S X E ε} {Inv : World S X E → Prop}
    (hcredit : ∀ (w : World S X E) (v : Nat), Inv w → Inv (World.creditValue w v))
    (h : ∀ fn, PreservesInvFn C Inv fn) : PreservesInv C Inv := by
  intro c w hc
  have hw1 : Inv (World.creditValue w c.value) := hcredit w c.value hc
  have hwa : Inv (worldAfter (C.exec c.fn c.args) c.toCtx (World.creditValue w c.value)) :=
    h c.fn c.args c.toCtx (World.creditValue w c.value) hw1
  rw [step_eq_run]
  cases hrun : C.exec c.fn c.args c.toCtx (World.creditValue w c.value) with
  | error _ => exact hc
  | ok p =>
    simp only [worldAfter, Tx.run, hrun] at hwa
    exact hwa

theorem PreservesInvFn_of_ok {C : Spec S X E ε} {Inv : World S X E → Prop} {fn : C.Fn}
    (hok : ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E) (a : C.Ret fn)
        (w' : World S X E),
      Inv w → Tx.run (C.exec fn args) ctx w = .ok (a, w') → Inv w') :
    PreservesInvFn C Inv fn := by
  intro args ctx w hInv
  exact worldAfter_preserves hInv (fun a w' h => hok args ctx w a w' hInv h)

theorem PreservesInvAt.of_fns {C : Spec S X E ε} {Inv : World S X E → Prop}
    {self : Address}
    (hcredit : ∀ (w : World S X E) (v : Nat), Inv w → Inv (World.creditValue w v))
    (h : ∀ fn, PreservesInvFnAt C Inv self fn) : PreservesInvAt C Inv self := by
  intro c w ht hs hc
  have hw1 : Inv (World.creditValue w c.value) := hcredit w c.value hc
  have hwa : Inv (worldAfter (C.exec c.fn c.args) c.toCtx (World.creditValue w c.value)) :=
    h c.fn c.args c.toCtx (World.creditValue w c.value) ht hs hw1
  rw [step_eq_run]
  cases hrun : C.exec c.fn c.args c.toCtx (World.creditValue w c.value) with
  | error _ => exact hc
  | ok p =>
    simp only [worldAfter, Tx.run, hrun] at hwa
    exact hwa

theorem PreservesInvFnAt_of_ok {C : Spec S X E ε} {Inv : World S X E → Prop}
    {self : Address} {fn : C.Fn}
    (hok : ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E) (a : C.Ret fn)
        (w' : World S X E),
      ctx.self = self → ctx.sender ≠ self → Inv w →
      Tx.run (C.exec fn args) ctx w = .ok (a, w') → Inv w') :
    PreservesInvFnAt C Inv self fn := by
  intro args ctx w hself hsne hInv
  exact worldAfter_preserves hInv
    (fun a w' h => hok args ctx w a w' hself hsne hInv h)

end Lsc.Security.Proof
