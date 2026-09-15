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

theorem run_nil (w : World S X E) : run ([] : List (Step C)) w = w :=
  rfl

theorem run_cons (s : Step C) (tr : List (Step C)) (w : World S X E) :
    run (s :: tr) w = run tr (step s w) :=
  rfl

theorem run_append (tr₁ tr₂ : List (Step C)) (w : World S X E) :
    run (tr₁ ++ tr₂) w = run tr₂ (run tr₁ w) := by
  induction tr₁ generalizing w with
  | nil => rfl
  | cons _ _ ih => rw [List.cons_append, run_cons, ih, run_cons]

theorem step_of_revert [HasCreditValue X] {c : Call C} {w : World S X E} {e : Err ε}
    (h : C.exec c.fn c.args c.toCtx (World.creditValue w c.value) = .error e) :
    step (.call c) w = w := by
  simp [step, stepCall, h]

theorem step_eq_run [HasCreditValue X] (c : Call C) (w : World S X E) :
    step (.call c) w =
      match C.exec c.fn c.args c.toCtx (World.creditValue w c.value) with
      | .ok (_, w') => w'
      | .error _ => w :=
  rfl

theorem step_eq_worldAfter_of_credit_id [HasCreditValue X]
    (c : Call C) (w : World S X E)
    (h : World.creditValue w c.value = w) :
    step (.call c) w = worldAfter (C.exec c.fn c.args) c.toCtx w := by
  rw [step_eq_run, h]
  cases hrun : C.exec c.fn c.args c.toCtx w with
  | ok p => simp [worldAfter, Tx.run, hrun]
  | error e => simp [worldAfter, Tx.run, hrun]

theorem Wf.nil (self : Address) : Wf (C := C) self [] :=
  trivial

theorem Trace.from_nil (A : Finset Address) : Trace.from (C := C) A [] :=
  trivial

end Lsc.Security.Proof
