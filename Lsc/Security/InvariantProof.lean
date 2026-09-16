import Lsc.Security.Invariant

/-!
Proofs of trace induction for `Inv`. Statements live in `InvariantTheorems`.
-/

namespace Lsc.Security.Proof

variable {S X E ε : Type}

theorem inv_run [HasCreditValue X] {C : Spec S X E ε} [HasPayable C]
    [HasSelfBalance X]
    {Inv : World S X E → Prop} {rely : X → X → Prop}
    (hC : PreservesInv C Inv) (hE : PreservesInvEnv C Inv rely)
    {w : World S X E} (hw : Inv w) {self : Address} (tr : List (Step C))
    (hW : Wf self tr w) (hR : RelyAlong rely tr w) :
    Inv (run tr w) := by
  induction tr generalizing w with
  | nil => simpa using hw
  | cons s tr ih =>
    match s with
    | .call c =>
      have ⟨_, _, _, htl⟩ := hW
      exact ih (hC c w hw) htl hR
    | .env x' =>
      have ⟨hr, htl⟩ := hR
      exact ih (hE w x' hw hr) hW htl

theorem inv_run_at [HasCreditValue X] {C : Spec S X E ε} [HasPayable C]
    [HasSelfBalance X]
    {Inv : World S X E → Prop} {rely : X → X → Prop}
    {self : Address}
    (hC : PreservesInvAt C Inv self) (hE : PreservesInvEnv C Inv rely)
    {w : World S X E} (hw : Inv w) (tr : List (Step C))
    (hW : Wf self tr w) (hR : RelyAlong rely tr w) :
    Inv (run tr w) := by
  induction tr generalizing w with
  | nil => simpa using hw
  | cons s tr ih =>
    match s with
    | .call c =>
      have ⟨ht, hs, _, htl⟩ := hW
      exact ih (hC c w ht hs hw) htl hR
    | .env x' =>
      have ⟨hr, htl⟩ := hR
      exact ih (hE w x' hw hr) hW htl

theorem PreservesInv.of_fns [HasCreditValue X] {C : Spec S X E ε} [HasPayable C]
    {Inv : World S X E → Prop}
    (h : ∀ fn, PreservesInvFn C Inv fn)
    (hnp : ∀ fn, C.payable fn = false := by intro fn; cases fn <;> rfl) :
    PreservesInv C Inv := by
  intro c w hc
  have hp : C.payable c.fn = false := hnp c.fn
  by_cases hv : c.value = 0
  · rw [step_eq_worldAfter_of_not_payable c w hp hv]
    exact h c.fn c.args c.toCtx w hc
  · simpa [step_reject_value hp hv] using hc

theorem PreservesInvFn_of_ok {C : Spec S X E ε} {Inv : World S X E → Prop} {fn : C.Fn}
    (hok : ∀ (args : C.Args fn) (ctx : Ctx) (w : World S X E) (a : C.Ret fn)
        (w' : World S X E),
      Inv w → Tx.run (C.exec fn args) ctx w = .ok (a, w') → Inv w') :
    PreservesInvFn C Inv fn := by
  intro args ctx w hInv
  exact worldAfter_preserves hInv (fun a w' h => hok args ctx w a w' hInv h)

theorem PreservesInvAt.of_fns [HasCreditValue X] {C : Spec S X E ε} [HasPayable C]
    {Inv : World S X E → Prop}
    {self : Address}
    (h : ∀ fn, PreservesInvFnAt C Inv self fn)
    (hnp : ∀ fn, C.payable fn = false := by intro fn; cases fn <;> rfl) :
    PreservesInvAt C Inv self := by
  intro c w ht hs hc
  have hp : C.payable c.fn = false := hnp c.fn
  by_cases hv : c.value = 0
  · rw [step_eq_worldAfter_of_not_payable c w hp hv]
    exact h c.fn c.args c.toCtx w ht hs hc
  · simpa [step_reject_value hp hv] using hc

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

theorem PreservesInv.of_fns_credit [HasCreditValue X] {C : Spec S X E ε}
    [HasPayable C]
    {Inv : World S X E → Prop}
    (h : ∀ fn, PreservesInvCreditFn C Inv fn) :
    PreservesInv C Inv := by
  intro c w hc
  rw [step_eq_run]
  split_ifs with hvo
  · cases hrun : C.exec c.fn c.args c.toCtx (World.creditValue w c.value) with
    | error _ => exact hc
    | ok p => exact h c.fn c.args c.toCtx w p.1 p.2 hvo hc hrun
  · exact hc

theorem PreservesInvAt.of_fns_credit [HasCreditValue X] {C : Spec S X E ε}
    [HasPayable C]
    {Inv : World S X E → Prop} {self : Address}
    (h : ∀ fn, PreservesInvCreditFnAt C Inv self fn) :
    PreservesInvAt C Inv self := by
  intro c w ht hs hc
  rw [step_eq_run]
  split_ifs with hvo
  · cases hrun : C.exec c.fn c.args c.toCtx (World.creditValue w c.value) with
    | error _ => exact hc
    | ok p =>
      have hself : c.toCtx.self = self := by simp [Call.toCtx, ht]
      have hsne : c.toCtx.sender ≠ self := by simp [Call.toCtx, hs]
      exact h c.fn c.args c.toCtx w p.1 p.2 hself hsne hvo hc hrun
  · exact hc

/-- Non-payable `PreservesInvFn` yields the credit form: `valueOk` forces
`value = 0`, so `creditValue` is the identity. -/
theorem PreservesInvCreditFn_of_fn [HasCreditValue X] {C : Spec S X E ε}
    [HasPayable C]
    {Inv : World S X E → Prop} {fn : C.Fn}
    (hp : C.payable fn = false)
    (h : PreservesInvFn C Inv fn) :
    PreservesInvCreditFn C Inv fn := by
  intro args ctx w ret w' hvo hInv hrun
  have hv : ctx.value = 0 := C.value_eq_zero_of_valueOk hp hvo
  rw [hv, World.creditValue_zero] at hrun
  have hw : worldAfter (C.exec fn args) ctx w = w' := worldAfter_ok hrun
  simpa [hw] using h args ctx w hInv

/-- Non-payable `PreservesInvFnAt` yields the credit form. -/
theorem PreservesInvCreditFnAt_of_fn [HasCreditValue X] {C : Spec S X E ε}
    [HasPayable C]
    {Inv : World S X E → Prop} {self : Address} {fn : C.Fn}
    (hp : C.payable fn = false)
    (h : PreservesInvFnAt C Inv self fn) :
    PreservesInvCreditFnAt C Inv self fn := by
  intro args ctx w ret w' hself hsne hvo hInv hrun
  have hv : ctx.value = 0 := C.value_eq_zero_of_valueOk hp hvo
  rw [hv, World.creditValue_zero] at hrun
  have hw : worldAfter (C.exec fn args) ctx w = w' := worldAfter_ok hrun
  simpa [hw] using h args ctx w hself hsne hInv

theorem RelyAlong.append [HasCreditValue X] {C : Spec S X E ε} [HasPayable C]
    {rely : X → X → Prop} {tr₁ tr₂ : List (Step C)} {w : World S X E}
    (h₁ : RelyAlong rely tr₁ w) (h₂ : RelyAlong rely tr₂ (run tr₁ w)) :
    RelyAlong rely (tr₁ ++ tr₂) w := by
  induction tr₁ generalizing w with
  | nil => simpa [run] using h₂
  | cons s rest ih =>
    match s with
    | .call c =>
      exact ih h₁ h₂
    | .env x' =>
      have ⟨hr, htl⟩ := h₁
      exact ⟨hr, ih htl h₂⟩

theorem reachable_run [HasCreditValue X] {C : Spec S X E ε} [HasPayable C]
    [HasSelfBalance X] [HasDeploy C]
    {rely : X → X → Prop} {self : Address} {w : World S X E}
    {tr : List (Step C)}
    (h : Reachable (C := C) rely self w) (hW : Wf self tr w)
    (hR : RelyAlong rely tr w) :
    Reachable (C := C) rely self (run tr w) := by
  obtain ⟨w₀, tr₀, hDep, hW₀, hR₀, rfl⟩ := h
  refine ⟨w₀, tr₀ ++ tr, hDep, Wf.append hW₀ hW, RelyAlong.append hR₀ hR, ?_⟩
  simp [run_append]

theorem inv_of_reachable [HasCreditValue X] {C : Spec S X E ε} [HasPayable C]
    [HasSelfBalance X] [HasDeploy C]
    {Inv : World S X E → Prop} {rely : X → X → Prop} {self : Address}
    {w : World S X E}
    (hD : ∀ w, Deployed C w → Inv w)
    (hP : PreservesInvAt C Inv self)
    (hE : PreservesInvEnv C Inv rely)
    (h : Reachable (C := C) rely self w) :
    Inv w := by
  obtain ⟨w₀, tr, hDep, hW, hR, rfl⟩ := h
  exact inv_run_at hP hE (hD w₀ hDep) tr hW hR

end Lsc.Security.Proof
