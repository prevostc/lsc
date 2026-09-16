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

theorem run_nil [HasCreditValue X] [HasPayable C] (w : World S X E) :
    run ([] : List (Step C)) w = w :=
  rfl

theorem run_cons [HasCreditValue X] [HasPayable C] (s : Step C) (tr : List (Step C))
    (w : World S X E) :
    run (s :: tr) w = run tr (step s w) :=
  rfl

theorem run_append [HasCreditValue X] [HasPayable C] (tr₁ tr₂ : List (Step C))
    (w : World S X E) :
    run (tr₁ ++ tr₂) w = run tr₂ (run tr₁ w) := by
  induction tr₁ generalizing w with
  | nil => rfl
  | cons _ _ ih => rw [List.cons_append, run_cons, ih, run_cons]

theorem step_of_revert [HasCreditValue X] [HasPayable C] {c : Call C} {w : World S X E}
    {e : Err ε}
    (hvo : C.valueOk c.fn c.value = true)
    (h : C.exec c.fn c.args c.toCtx (World.creditValue w c.value) = .error e) :
    step (.call c) w = w := by
  simp [step, stepCall, hvo, h]

theorem step_reject_value [HasCreditValue X] [HasPayable C] {c : Call C} {w : World S X E}
    (hp : C.payable c.fn = false) (hv : c.value ≠ 0) :
    step (.call c) w = w := by
  simp [step, stepCall, Spec.valueOk_false (C := C) hp hv]

theorem step_eq_run [HasCreditValue X] [HasPayable C] (c : Call C) (w : World S X E) :
    step (.call c) w =
      if C.valueOk c.fn c.value then
        match C.exec c.fn c.args c.toCtx (World.creditValue w c.value) with
        | .ok (_, w') => w'
        | .error _ => w
      else w :=
  rfl

theorem step_eq_worldAfter_of_credit_id [HasCreditValue X] [HasPayable C]
    (c : Call C) (w : World S X E)
    (hvo : C.valueOk c.fn c.value = true)
    (h : World.creditValue w c.value = w) :
    step (.call c) w = worldAfter (C.exec c.fn c.args) c.toCtx w := by
  rw [step_eq_run, hvo, h]
  cases hrun : C.exec c.fn c.args c.toCtx w with
  | ok p => simp [worldAfter, Tx.run, hrun]
  | error e => simp [worldAfter, Tx.run, hrun]

theorem step_eq_worldAfter_of_not_payable [HasCreditValue X] [HasPayable C]
    (c : Call C) (w : World S X E)
    (hp : C.payable c.fn = false) (hv : c.value = 0) :
    step (.call c) w = worldAfter (C.exec c.fn c.args) c.toCtx w :=
  step_eq_worldAfter_of_credit_id c w
    (by simp [Spec.valueOk, hp, hv]) (by rw [hv, World.creditValue_zero])

theorem Wf.nil [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    (self : Address) (w : World S X E) : Wf (C := C) self [] w :=
  trivial

theorem Trace.from_nil (A : Finset Address) : Trace.from (C := C) A [] :=
  trivial

theorem Wf.append [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    {self : Address} {tr₁ tr₂ : List (Step C)} {w : World S X E}
    (h₁ : Wf self tr₁ w) (h₂ : Wf self tr₂ (run tr₁ w)) :
    Wf self (tr₁ ++ tr₂) w := by
  induction tr₁ generalizing w with
  | nil => simpa [run] using h₂
  | cons s rest ih =>
    match s with
    | .call c =>
      have ⟨ht, hs, hb, htl⟩ := h₁
      exact ⟨ht, hs, hb, ih htl h₂⟩
    | .env x' =>
      exact ih h₁ h₂

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

/-- On `ExtState`, zero-value well-formedness does not depend on the starting
world: every native balance already fits in 256 bits. -/
theorem Wf.irrel_extState {S E ε : Type} {C : Spec S ExtState E ε} [HasPayable C]
    (self : Address) (tr : List (Step C))
    (w w' : World S ExtState E)
    (hz : ∀ (c : Call C), Step.call c ∈ tr → c.value = 0)
    (h : Wf self tr w) : Wf self tr w' := by
  induction tr generalizing w w' with
  | nil => trivial
  | cons s rest ih =>
    match s with
    | .env x =>
      exact ih (w := { w with ext := x }) (w' := { w' with ext := x })
        (fun c hc => hz c (List.mem_cons_of_mem _ hc)) h
    | .call c =>
      rcases h with ⟨ht, hs, _, htl⟩
      have hv : c.value = 0 := hz c (List.mem_cons_self)
      refine ⟨ht, hs, ?bound,
        ih (w := step (.call c) w) (w' := step (.call c) w')
          (fun c' hc => hz c' (List.mem_cons_of_mem _ hc)) htl⟩
      have hlt := nativeBalance_lt_wordBound (S := S) (E := E) w'
      simpa [hv, Nat.add_zero] using hlt

end Lsc.Security.Proof
