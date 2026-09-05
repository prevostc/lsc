import Mathlib.Data.Finset.Basic
import Lsc.Lang.Tx

/-!
Trace semantics of one contract: a family of entrypoints over one storage type `S`.
A reverted call is a no-op on the world (EVM atomicity).
-/

namespace Lsc.Security

variable {S E ε : Type}

/-- One ABI entrypoint, with its own argument and return types. -/
structure Entry (S E ε : Type) where
  Args : Type
  Ret : Type
  run : Args → Tx S E ε Ret

/-- A contract as a family of entrypoints. `Fn` is typically a finite inductive. -/
structure Spec (S E ε : Type) where
  Fn : Type
  entry : Fn → Entry S E ε

namespace Spec
variable (C : Spec S E ε)
abbrev Args (fn : C.Fn) : Type := (C.entry fn).Args
abbrev Ret (fn : C.Fn) : Type := (C.entry fn).Ret
/-- Run the body of `fn` on `args`. -/
@[reducible] def exec (fn : C.Fn) (args : C.Args fn) : Tx S E ε (C.Ret fn) := (C.entry fn).run args
end Spec

/-- One attempted call. `target` is `Ctx.self` (the callee). -/
structure Call (C : Spec S E ε) where
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

/-- Post-world of `x`: success keeps the returned world, revert keeps `w`. -/
def worldAfter (x : Tx S E ε α) (ctx : Ctx) (w : World S E) : World S E :=
  match Tx.run x ctx w with
  | .ok (_, w') => w'
  | .error _ => w

@[simp] theorem worldAfter_ok {x : Tx S E ε α} {ctx w a w'}
    (h : Tx.run x ctx w = .ok (a, w')) : worldAfter x ctx w = w' := by
  simp [worldAfter, h]

@[simp] theorem worldAfter_error {x : Tx S E ε α} {ctx w e}
    (h : Tx.run x ctx w = .error e) : worldAfter x ctx w = w := by
  simp [worldAfter, h]

variable {C : Spec S E ε}

/-- One call, reverting to the pre-world on failure. -/
def step (c : Call C) (w : World S E) : World S E :=
  worldAfter (C.exec c.fn c.args) c.toCtx w

/-- Left fold: first call first. -/
def run (tr : List (Call C)) (w : World S E) : World S E :=
  tr.foldl (fun acc c => step c acc) w

@[simp] theorem run_nil (w : World S E) : run ([] : List (Call C)) w = w := rfl

@[simp] theorem run_cons (c : Call C) (tr : List (Call C)) (w : World S E) :
    run (c :: tr) w = run tr (step c w) := rfl

theorem run_append (tr₁ tr₂ : List (Call C)) (w : World S E) :
    run (tr₁ ++ tr₂) w = run tr₂ (run tr₁ w) := by
  induction tr₁ generalizing w with
  | nil => rfl
  | cons _ _ ih => rw [List.cons_append, run_cons, ih, run_cons]

theorem step_of_revert {c : Call C} {w : World S E} {e : Err ε}
    (h : Tx.run (C.exec c.fn c.args) c.toCtx w = .error e) :
    step c w = w := worldAfter_error h

theorem step_eq_worldAfter (c : Call C) (w : World S E) :
    step c w = worldAfter (C.exec c.fn c.args) c.toCtx w := rfl

/-- Every call in `tr` is sent from `A`. -/
def Trace.from (A : Finset Address) (tr : List (Call C)) : Prop :=
  ∀ c ∈ tr, c.sender ∈ A

theorem Trace.from_nil (A : Finset Address) : Trace.from (C := C) A [] := by
  intro _ h; cases h

theorem Trace.from_cons (A : Finset Address) (c : Call C) (tr : List (Call C)) :
    Trace.from A (c :: tr) ↔ c.sender ∈ A ∧ Trace.from A tr := by
  simp [Trace.from]

end Lsc.Security
