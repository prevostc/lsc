import Mathlib.Data.Finset.Basic
import Lsc.Lang.Spec

/-!
Trace semantics of one contract: `Call`, `Step`, `step`, and `run` over a language-level
`Lsc.Spec`. A reverted call is a no-op on the world (EVM atomicity). `env` steps replace
the ghost record; they are constrained by `RelyAlong` in `Invariant.lean`.
-/

namespace Lsc.Security

variable {S X E ε : Type}

/-- One attempted call. `target` is `Ctx.self` (the callee). -/
structure Call (C : Spec S X E ε) where
  sender : Address
  value : Nat := 0
  timestamp : Nat := 0
  blockNumber : Nat := 0
  target : Address := 0
  fn : C.Fn
  args : C.Args fn

/-- Unpack a call into the `Tx` context. -/
def Call.toCtx (c : Call C) : Ctx where
  sender := c.sender
  value := c.value
  timestamp := c.timestamp
  blockNumber := c.blockNumber
  self := c.target

/-- Pack a context and an entrypoint into a call. -/
def Call.ofCtx (ctx : Ctx) (fn : C.Fn) (args : C.Args fn) : Call C where
  sender := ctx.sender
  value := ctx.value
  timestamp := ctx.timestamp
  blockNumber := ctx.blockNumber
  target := ctx.self
  fn := fn
  args := args

@[simp] theorem Call.toCtx_ofCtx (ctx : Ctx) (fn : C.Fn) (args : C.Args fn) :
    (Call.ofCtx (C := C) ctx fn args).toCtx = ctx := rfl

@[simp] theorem Call.ofCtx_toCtx (c : Call C) :
    Call.ofCtx c.toCtx c.fn c.args = c := rfl

/-- Post-world of `x`: success keeps the returned world, revert keeps `w`.
Same function as `Lsc.worldAfter`; kept in this namespace so existing
Security proofs keep their qualified names. -/
abbrev worldAfter {α} (x : Tx S X E ε α) (ctx : Ctx) (w : World S X E) :
    World S X E :=
  Lsc.worldAfter x ctx w

@[simp] theorem worldAfter_ok {x : Tx S X E ε α} {ctx w a w'}
    (h : Tx.run x ctx w = .ok (a, w')) : worldAfter x ctx w = w' :=
  Lsc.worldAfter_ok h

@[simp] theorem worldAfter_error {x : Tx S X E ε α} {ctx w e}
    (h : Tx.run x ctx w = .error e) : worldAfter x ctx w = w :=
  Lsc.worldAfter_error h

/-- `P` holds after `x` if it holds of the pre-world and of every successful post-world.
Reverts are a no-op, so the error branch is `hw`. -/
theorem worldAfter_preserves {P : World S X E → Prop} {x : Tx S X E ε α}
    {ctx : Ctx} {w : World S X E}
    (hw : P w) (hok : ∀ a w', Tx.run x ctx w = .ok (a, w') → P w') :
    P (worldAfter x ctx w) := by
  cases h : Tx.run x ctx w with
  | error _ => simpa [worldAfter, h] using hw
  | ok p => simpa [worldAfter, h] using hok p.1 p.2 h

/-- If every success path returns the pre-world, then `worldAfter` is the identity. -/
theorem worldAfter_eq_self {x : Tx S X E ε α} {ctx : Ctx} {w : World S X E}
    (hok : ∀ a w', Tx.run x ctx w = .ok (a, w') → w' = w) :
    worldAfter x ctx w = w :=
  worldAfter_preserves (P := fun w' => w' = w) rfl hok

variable {C : Spec S X E ε}

/-- One trace step: a contract call, or an environment (ghost) update between our calls. -/
inductive Step (C : Spec S X E ε)
  | call (c : Call C)
  | env (ext' : X)

/-- One step, reverting to the pre-world on a failed call. -/
def step : Step C → World S X E → World S X E
  | .call c, w => worldAfter (C.exec c.fn c.args) c.toCtx w
  | .env x', w => { w with ext := x' }

/-- Left fold: first step first. -/
def run (tr : List (Step C)) (w : World S X E) : World S X E :=
  tr.foldl (fun acc s => step s acc) w

@[simp] theorem run_nil (w : World S X E) : run ([] : List (Step C)) w = w := rfl

@[simp] theorem run_cons (s : Step C) (tr : List (Step C)) (w : World S X E) :
    run (s :: tr) w = run tr (step s w) := rfl

theorem run_append (tr₁ tr₂ : List (Step C)) (w : World S X E) :
    run (tr₁ ++ tr₂) w = run tr₂ (run tr₁ w) := by
  induction tr₁ generalizing w with
  | nil => rfl
  | cons _ _ ih => rw [List.cons_append, run_cons, ih, run_cons]

theorem step_of_revert {c : Call C} {w : World S X E} {e : Err ε}
    (h : Tx.run (C.exec c.fn c.args) c.toCtx w = .error e) :
    step (.call c) w = w := worldAfter_error h

theorem step_eq_worldAfter (c : Call C) (w : World S X E) :
    step (.call c) w = worldAfter (C.exec c.fn c.args) c.toCtx w := rfl

/-- Every call is aimed at `self` and is not a self-call. `env` steps are unrestricted. -/
def Wf (self : Address) : List (Step C) → Prop
  | [] => True
  | .call c :: tr => c.target = self ∧ c.sender ≠ self ∧ Wf self tr
  | .env _ :: tr => Wf self tr

theorem Wf.nil (self : Address) : Wf (C := C) self [] := trivial

/-- Every call in `tr` is sent from `A`. Environment steps are ignored. -/
def Trace.from (A : Finset Address) : List (Step C) → Prop
  | [] => True
  | .call c :: tr => c.sender ∈ A ∧ Trace.from A tr
  | .env _ :: tr => Trace.from A tr

theorem Trace.from_nil (A : Finset Address) : Trace.from (C := C) A [] := trivial

end Lsc.Security
