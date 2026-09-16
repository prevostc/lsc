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
@[simp] theorem run_nil [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    (w : World S X E) :
    run ([] : List (Step C)) w = w :=
  Proof.run_nil w

/-- `run` of a cons is `run` of the tail after one `step`. -/
@[simp] theorem run_cons [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    (s : Step C)
    (tr : List (Step C)) (w : World S X E) :
    run (s :: tr) w = run tr (step s w) :=
  Proof.run_cons s tr w

/-- `run` of an append is sequential composition. -/
theorem run_append [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    (tr₁ tr₂ : List (Step C))
    (w : World S X E) :
    run (tr₁ ++ tr₂) w = run tr₂ (run tr₁ w) :=
  Proof.run_append tr₁ tr₂ w

/-- A reverting call step leaves the world unchanged. The run is on the
post-transfer (value-credited) world when the call is `valueOk` and does
not wrap. A wrap-reject is also a no-op. -/
theorem step_of_revert [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    {c : Call C} {w : World S X E} {e : Err ε}
    (hvo : C.valueOk c.fn c.value = true)
    (h : C.exec c.fn c.args c.toCtx (World.creditValue w c.value) = .error e) :
    step (.call c) w = w :=
  Proof.step_of_revert hvo h

/-- Nonzero value to a non-payable function is a revert step. -/
theorem step_reject_value [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    {c : Call C} {w : World S X E}
    (hp : C.payable c.fn = false) (hv : c.value ≠ 0) :
    step (.call c) w = w :=
  Proof.step_reject_value hp hv

/-- Payable call whose credited native balance wraps is a revert step. -/
theorem step_wrap [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    {c : Call C} {w : World S X E}
    (hp : C.payable c.fn = true) (hw : creditWraps w c.value = true) :
    step (.call c) w = w :=
  Proof.step_wrap hp hw

/-- A call step is `Tx.run` of the entrypoint on the post-transfer world
when `valueOk` and the credit does not wrap; otherwise it is the identity. -/
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
  Proof.step_eq_run c w

/-- When `valueOk`, `creditValue` is the identity, and the credit does not
wrap, a call step is `worldAfter`. -/
theorem step_eq_worldAfter_of_credit_id [HasCreditValue X] [HasPayable C]
    [HasSelfBalance X]
    (c : Call C) (w : World S X E)
    (hvo : C.valueOk c.fn c.value = true)
    (h : World.creditValue w c.value = w)
    (hnw : (C.payable c.fn && creditWraps w c.value) = false) :
    step (.call c) w = worldAfter (C.exec c.fn c.args) c.toCtx w :=
  Proof.step_eq_worldAfter_of_credit_id c w hvo h hnw

/-- Non-payable success is `v = 0`, so the call step is `worldAfter`. -/
theorem step_eq_worldAfter_of_not_payable [HasCreditValue X] [HasPayable C]
    [HasSelfBalance X]
    (c : Call C) (w : World S X E)
    (hp : C.payable c.fn = false) (hv : c.value = 0) :
    step (.call c) w = worldAfter (C.exec c.fn c.args) c.toCtx w :=
  Proof.step_eq_worldAfter_of_not_payable c w hp hv

/-- The empty trace is well-formed at any `self` and world. -/
theorem Wf.nil (self : Address) (w : World S X E) : Wf (C := C) self [] w :=
  Proof.Wf.nil self w

/-- The empty trace is from any sender set. -/
theorem Trace.from_nil (A : Finset Address) : Trace.from (C := C) A [] :=
  Proof.Trace.from_nil A

/-- Well-formedness of sequential composition: the suffix is judged in the
world after the prefix. -/
theorem Wf.append [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    {self : Address} {tr₁ tr₂ : List (Step C)} {w : World S X E}
    (h₁ : Wf self tr₁ w) (h₂ : Wf self tr₂ (run tr₁ w)) :
    Wf self (tr₁ ++ tr₂) w :=
  Proof.Wf.append h₁ h₂

/-- On `ExtState`, the native balance always fits in a 256-bit word. -/
theorem nativeBalance_lt_wordBound {S E : Type} (w : World S ExtState E) :
    HasSelfBalance.get w.ext < wordBound :=
  Proof.nativeBalance_lt_wordBound w

/-- Crediting `v` wei does not wrap when the sum fits in a 256-bit word. -/
theorem nativeBalance_creditValue {S E : Type} (w : World S ExtState E) (v : Nat)
    (h : World.nativeBalance w + v < wordBound) :
    World.nativeBalance (World.creditValue w v) = World.nativeBalance w + v :=
  Proof.nativeBalance_creditValue w v h

/-- `Wf` ignores the world index. -/
theorem Wf.irrel_extState {S E ε : Type} {C : Spec S ExtState E ε}
    (self : Address) (tr : List (Step C))
    (w w' : World S ExtState E)
    (h : Wf self tr w) : Wf self tr w' :=
  Proof.Wf.irrel_extState self tr w w' h

/-- A rejected call (value, wrap, or body revert) is a no-op on the world. -/
theorem step_of_not_accepted [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    {c : Call C} {w : World S X E} (h : accepted c w = false) :
    step (.call c) w = w :=
  Proof.step_of_not_accepted h

/-- An accepted call ran the body successfully after the value/wrap guards. -/
theorem accepted_ok [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    {c : Call C} {w : World S X E} (h : accepted c w = true) :
    C.valueOk c.fn c.value = true ∧
      (C.payable c.fn && creditWraps w c.value) = false ∧
      ∃ p, C.exec c.fn c.args c.toCtx (World.creditValue w c.value) = .ok p ∧
        step (.call c) w = p.2 :=
  Proof.accepted_ok h

/-- Wrap-reject is exactly 256-bit overflow of `self`'s native balance. -/
theorem creditWraps_false_lt {S E : Type} (w : World S ExtState E) (v : Nat)
    (h : creditWraps w v = false) :
    World.nativeBalance w + v < wordBound :=
  Proof.creditWraps_false_lt w v h

end Lsc.Security
