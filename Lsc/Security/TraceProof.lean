import Lsc.Security.Trace

/-!
Proofs of `Call` round-trip, `worldAfter`, and `run` lemmas. Statements live
in `TraceTheorems.lean`.
-/

namespace Lsc.Security.Proof

variable {S X E ε α : Type} {C : Spec S X E ε}

theorem Call.toCtx_ofCtx (ctx : Ctx) (fn : C.Fn) (args : C.Args fn) :
    (Call.ofCtx (C := C) ctx fn args).toCtx = ctx :=
  rfl

theorem Call.ofCtx_toCtx (c : Call C) :
    Call.ofCtx c.toCtx c.fn c.args = c :=
  rfl

theorem worldAfter_ok {x : Tx S X E ε α} {ctx w a w'}
    (h : Tx.run x ctx w = .ok (a, w')) : worldAfter x ctx w = w' := by
  simp [worldAfter, h]

theorem worldAfter_error {x : Tx S X E ε α} {ctx w e}
    (h : Tx.run x ctx w = .error e) : worldAfter x ctx w = w := by
  simp [worldAfter, h]

theorem worldAfter_preserves {P : World S X E → Prop} {x : Tx S X E ε α}
    {ctx : Ctx} {w : World S X E}
    (hw : P w) (hok : ∀ a w', Tx.run x ctx w = .ok (a, w') → P w') :
    P (worldAfter x ctx w) := by
  cases h : Tx.run x ctx w with
  | error _ => simpa [worldAfter_error h] using hw
  | ok p => simpa [worldAfter_ok h] using hok p.1 p.2 h

theorem worldAfter_eq_self {x : Tx S X E ε α} {ctx : Ctx} {w : World S X E}
    (hok : ∀ a w', Tx.run x ctx w = .ok (a, w') → w' = w) :
    worldAfter x ctx w = w :=
  worldAfter_preserves (P := fun w' => w' = w) rfl hok

theorem run_nil [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    (w : World S X E) :
    run ([] : List (Step C)) w = w :=
  rfl

theorem run_cons [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    (s : Step C) (tr : List (Step C))
    (w : World S X E) :
    run (s :: tr) w = run tr (step s w) :=
  rfl

theorem run_append [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    (tr₁ tr₂ : List (Step C))
    (w : World S X E) :
    run (tr₁ ++ tr₂) w = run tr₂ (run tr₁ w) := by
  induction tr₁ generalizing w with
  | nil => rfl
  | cons _ _ ih => rw [List.cons_append, run_cons, ih, run_cons]

theorem step_of_revert [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    {c : Call C} {w : World S X E} {e : Err ε}
    (hvo : C.valueOk c.fn c.value = true)
    (h : C.exec c.fn c.args c.toCtx (World.creditValue w c.value) = .error e) :
    step (.call c) w = w := by
  simp only [step, stepCall]
  simp [hvo, h]

theorem step_reject_value [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    {c : Call C} {w : World S X E}
    (hp : C.payable c.fn = false) (hv : c.value ≠ 0) :
    step (.call c) w = w := by
  simp only [step, stepCall]
  simp [Spec.valueOk_false (C := C) hp hv]

theorem step_wrap [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    {c : Call C} {w : World S X E}
    (hp : C.payable c.fn = true) (hw : creditWraps w c.value = true) :
    step (.call c) w = w := by
  have hvo : C.valueOk c.fn c.value = true := Spec.valueOk_of_payable (C := C) hp
  simp only [step, stepCall]
  simp [hvo, hp, hw]

theorem step_eq_run [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    (c : Call C) (w : World S X E) :
    step (.call c) w =
      if C.valueOk c.fn c.value then
        if C.payable c.fn && creditWraps w c.value then w
        else
          match C.exec c.fn c.args c.toCtx (World.creditValue w c.value) with
          | .ok (_, w') => w'
          | .error _ => w
      else w :=
  rfl

theorem step_eq_worldAfter_of_credit_id [HasCreditValue X] [HasPayable C]
    [HasSelfBalance X]
    (c : Call C) (w : World S X E)
    (hvo : C.valueOk c.fn c.value = true)
    (h : World.creditValue w c.value = w)
    (hnw : (C.payable c.fn && creditWraps w c.value) = false) :
    step (.call c) w = worldAfter (C.exec c.fn c.args) c.toCtx w := by
  simp only [step, stepCall]
  simp [hvo, hnw, h]
  cases hrun : C.exec c.fn c.args c.toCtx w with
  | ok p => simp [worldAfter, Tx.run, hrun]
  | error e => simp [worldAfter, Tx.run, hrun]

theorem step_eq_worldAfter_of_not_payable [HasCreditValue X] [HasPayable C]
    [HasSelfBalance X]
    (c : Call C) (w : World S X E)
    (hp : C.payable c.fn = false) (hv : c.value = 0) :
    step (.call c) w = worldAfter (C.exec c.fn c.args) c.toCtx w :=
  step_eq_worldAfter_of_credit_id c w
    (by simp [Spec.valueOk, hp, hv]) (by rw [hv, World.creditValue_zero])
    (by simp [hp])

theorem Wf.nil (self : Address) (w : World S X E) : Wf (C := C) self [] w :=
  trivial

theorem Trace.from_nil (A : Finset Address) : Trace.from (C := C) A [] :=
  trivial

theorem External.append {self : Address} {tr₁ tr₂ : List (Step C)}
    (h₁ : External (C := C) self tr₁) (h₂ : External self tr₂) :
    External self (tr₁ ++ tr₂) := by
  induction tr₁ with
  | nil => simpa using h₂
  | cons s rest ih =>
    match s with
    | .call c =>
      have ⟨ht, hs, htl⟩ := h₁
      exact ⟨ht, hs, ih htl⟩
    | .env _ =>
      exact ih h₁

theorem Wf.append [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    {self : Address} {tr₁ tr₂ : List (Step C)} {w : World S X E}
    (h₁ : Wf self tr₁ w) (h₂ : Wf self tr₂ (run tr₁ w)) :
    Wf self (tr₁ ++ tr₂) w :=
  External.append (C := C) h₁ h₂

/-- Crediting `v` wei does not wrap when the sum fits in a 256-bit word. -/
theorem nativeBalance_creditValue {S E : Type} (w : World S ExtState E) (v : Nat)
    (h : World.nativeBalance w + v < wordBound) :
    World.nativeBalance (World.creditValue w v) = World.nativeBalance w + v := by
  have hlt : w.ext.env.selfBalance.toNat + v < 2 ^ 256 := by
    simpa [World.nativeBalance, wordBound] using h
  change (BitVec.ofNat 256 (w.ext.env.selfBalance.toNat + v)).toNat =
    w.ext.env.selfBalance.toNat + v
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

theorem nativeBalance_lt_wordBound {S E : Type} (w : World S ExtState E) :
    HasSelfBalance.get w.ext < wordBound :=
  w.ext.env.selfBalance.isLt

/-- Wrap-reject is exactly 256-bit overflow of `self`'s native balance. -/
theorem creditWraps_false_lt {S E : Type} (w : World S ExtState E) (v : Nat)
    (h : creditWraps w v = false) :
    World.nativeBalance w + v < wordBound := by
  have hnl : ¬ (BitVec.ofNat 256 (World.nativeBalance w + v)).toNat < v := by
    have : decide
        ((BitVec.ofNat 256 (w.ext.env.selfBalance.toNat + v)).toNat < v) =
          false := by
      simpa [creditWraps, World.creditValue, HasCreditValue.credit,
        ExtState.creditValue, HasSelfBalance.get, World.nativeBalance] using h
    exact of_decide_eq_false this
  have hvle : v ≤ (World.nativeBalance w + v) % 2 ^ 256 := by
    simpa [BitVec.toNat_ofNat] using Nat.not_lt.mp hnl
  have hvlt : v < 2 ^ 256 :=
    Nat.lt_of_le_of_lt hvle (Nat.mod_lt _ (by decide))
  have hbal : World.nativeBalance w < 2 ^ 256 := w.ext.env.selfBalance.isLt
  by_contra hge
  rw [Nat.not_lt, show wordBound = 2 ^ 256 from rfl] at hge
  have hdiv : (World.nativeBalance w + v) / 2 ^ 256 = 1 :=
    Nat.div_eq_of_lt_le (by simpa using hge) (by
      have := Nat.add_lt_add hbal hvlt
      simpa [Nat.two_mul] using this)
  have hmod : (World.nativeBalance w + v) % 2 ^ 256 =
      World.nativeBalance w + v - 2 ^ 256 := by
    rw [Nat.mod_eq_sub_div_mul, hdiv, Nat.one_mul]
  have hwrap : World.nativeBalance w + v - 2 ^ 256 < v := by omega
  exact Nat.not_le_of_gt (hmod ▸ hwrap) hvle

/-- `Wf` ignores the world index. -/
theorem Wf.irrel_extState {S E ε : Type} {C : Spec S ExtState E ε}
    (self : Address) (tr : List (Step C))
    (w w' : World S ExtState E)
    (h : Wf self tr w) : Wf self tr w' :=
  h

theorem step_of_not_accepted [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    {c : Call C} {w : World S X E} (h : accepted c w = false) :
    step (.call c) w = w := by
  unfold accepted at h
  cases hvo : C.valueOk c.fn c.value
  · simp [step, stepCall, hvo]
  · cases hwrap : (C.payable c.fn && creditWraps w c.value)
    · cases hrun : C.exec c.fn c.args c.toCtx (World.creditValue w c.value) with
      | ok p =>
        simp [hvo, hwrap, hrun] at h
      | error e =>
        simp [step, stepCall, hvo, hwrap, hrun]
    · simp [step, stepCall, hvo, hwrap]

theorem accepted_ok [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    {c : Call C} {w : World S X E} (h : accepted c w = true) :
    C.valueOk c.fn c.value = true ∧
      (C.payable c.fn && creditWraps w c.value) = false ∧
      ∃ p, C.exec c.fn c.args c.toCtx (World.creditValue w c.value) = .ok p ∧
        step (.call c) w = p.2 := by
  unfold accepted at h
  if hvo : C.valueOk c.fn c.value = true then
    if hwrap : (C.payable c.fn && creditWraps w c.value) = true then
      simp [hvo, hwrap] at h
    else
      cases hrun : C.exec c.fn c.args c.toCtx (World.creditValue w c.value) with
      | error e =>
        simp [hvo, hwrap, hrun] at h
      | ok p =>
        refine ⟨hvo, Bool.eq_false_iff.mpr hwrap, p, rfl, ?_⟩
        simp [step, stepCall, hvo, hwrap, hrun]
  else
    simp [hvo] at h

end Lsc.Security.Proof
