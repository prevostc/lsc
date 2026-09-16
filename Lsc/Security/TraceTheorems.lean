import Lsc.Security.TraceProof

/-!
`Call` round-trip, `worldAfter` peeling, and `run` / `Wf` lemmas over a
language-level `Lsc.Spec`. A reverted call is a no-op on the world.
-/

namespace Lsc.Security

variable {S X E ε α : Type} {C : Spec S X E ε}

/-- Unpacking `ofCtx` recovers the original context. -/
@[simp] theorem Call.toCtx_ofCtx (ctx : Ctx) (fn : C.Fn) (args : C.Args fn) :
    (Call.ofCtx (C := C) ctx fn args).toCtx = ctx :=
  Proof.Call.toCtx_ofCtx ctx fn args

/-- Packing `toCtx` recovers the original call. -/
@[simp] theorem Call.ofCtx_toCtx (c : Call C) :
    Call.ofCtx c.toCtx c.fn c.args = c :=
  Proof.Call.ofCtx_toCtx c

/-- A successful run's post-world is the returned world. -/
@[simp] theorem worldAfter_ok {x : Tx S X E ε α} {ctx w a w'}
    (h : Tx.run x ctx w = .ok (a, w')) : worldAfter x ctx w = w' :=
  Proof.worldAfter_ok h

/-- A reverting run's post-world is the starting world. -/
@[simp] theorem worldAfter_error {x : Tx S X E ε α} {ctx w e}
    (h : Tx.run x ctx w = .error e) : worldAfter x ctx w = w :=
  Proof.worldAfter_error h

/-- `P` holds after `x` if it holds of the pre-world and of every successful
post-world. Reverts are a no-op. -/
theorem worldAfter_preserves {P : World S X E → Prop} {x : Tx S X E ε α}
    {ctx : Ctx} {w : World S X E}
    (hw : P w) (hok : ∀ a w', Tx.run x ctx w = .ok (a, w') → P w') :
    P (worldAfter x ctx w) :=
  Proof.worldAfter_preserves hw hok

/-- If every success path returns the pre-world, then `worldAfter` is the identity. -/
theorem worldAfter_eq_self {x : Tx S X E ε α} {ctx : Ctx} {w : World S X E}
    (hok : ∀ a w', Tx.run x ctx w = .ok (a, w') → w' = w) :
    worldAfter x ctx w = w :=
  Proof.worldAfter_eq_self hok

/-- The empty trace does not change the world. -/
@[simp] theorem run_nil [HasCreditValue X] [HasPayable C] (w : World S X E) :
    run ([] : List (Step C)) w = w :=
  Proof.run_nil w

/-- `run` of a cons is `run` of the tail after one `step`. -/
@[simp] theorem run_cons [HasCreditValue X] [HasPayable C] (s : Step C)
    (tr : List (Step C)) (w : World S X E) :
    run (s :: tr) w = run tr (step s w) :=
  Proof.run_cons s tr w

/-- `run` of an append is sequential composition. -/
theorem run_append [HasCreditValue X] [HasPayable C] (tr₁ tr₂ : List (Step C))
    (w : World S X E) :
    run (tr₁ ++ tr₂) w = run tr₂ (run tr₁ w) :=
  Proof.run_append tr₁ tr₂ w

/-- A reverting call step leaves the world unchanged. The run is on the
post-transfer (value-credited) world when the call is `valueOk`. -/
theorem step_of_revert [HasCreditValue X] [HasPayable C] {c : Call C}
    {w : World S X E} {e : Err ε}
    (hvo : C.valueOk c.fn c.value = true)
    (h : C.exec c.fn c.args c.toCtx (World.creditValue w c.value) = .error e) :
    step (.call c) w = w :=
  Proof.step_of_revert hvo h

/-- Nonzero value to a non-payable function is a revert step. -/
theorem step_reject_value [HasCreditValue X] [HasPayable C] {c : Call C}
    {w : World S X E}
    (hp : C.payable c.fn = false) (hv : c.value ≠ 0) :
    step (.call c) w = w :=
  Proof.step_reject_value hp hv

/-- A call step is `Tx.run` of the entrypoint on the post-transfer world
when `valueOk`; otherwise it is the identity. -/
theorem step_eq_run [HasCreditValue X] [HasPayable C] (c : Call C)
    (w : World S X E) :
    step (.call c) w =
      if C.valueOk c.fn c.value then
        match C.exec c.fn c.args c.toCtx (World.creditValue w c.value) with
        | .ok (_, w') => w'
        | .error _ => w
      else w :=
  Proof.step_eq_run c w

/-- When `valueOk` and `creditValue` is the identity, a call step is `worldAfter`. -/
theorem step_eq_worldAfter_of_credit_id [HasCreditValue X] [HasPayable C]
    (c : Call C) (w : World S X E)
    (hvo : C.valueOk c.fn c.value = true)
    (h : World.creditValue w c.value = w) :
    step (.call c) w = worldAfter (C.exec c.fn c.args) c.toCtx w :=
  Proof.step_eq_worldAfter_of_credit_id c w hvo h

/-- Non-payable success is `v = 0`, so the call step is `worldAfter`. -/
theorem step_eq_worldAfter_of_not_payable [HasCreditValue X] [HasPayable C]
    (c : Call C) (w : World S X E)
    (hp : C.payable c.fn = false) (hv : c.value = 0) :
    step (.call c) w = worldAfter (C.exec c.fn c.args) c.toCtx w :=
  Proof.step_eq_worldAfter_of_not_payable c w hp hv

/-- The empty trace is well-formed at any `self`. -/
theorem Wf.nil (self : Address) : Wf (C := C) self [] :=
  Proof.Wf.nil self

/-- The empty trace is from any sender set. -/
theorem Trace.from_nil (A : Finset Address) : Trace.from (C := C) A [] :=
  Proof.Trace.from_nil A

end Lsc.Security
