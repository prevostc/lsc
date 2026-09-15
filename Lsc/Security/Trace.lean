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

/-- Post-world of `x`: success keeps the returned world, revert keeps `w`. -/
def worldAfter {α} (x : Tx S X E ε α) (ctx : Ctx) (w : World S X E) :
    World S X E :=
  match Tx.run x ctx w with
  | .ok (_, w') => w'
  | .error _ => w

variable {C : Spec S X E ε}

/-- One trace step: a contract call, or an environment (ghost) update between our calls. -/
inductive Step (C : Spec S X E ε)
  | call (c : Call C)
  | env (ext' : X)

/-- Post-world of a call: credit incoming value, run the body, roll back on revert. -/
def stepCall [HasCreditValue X] (c : Call C) (w : World S X E) : World S X E :=
  match C.exec c.fn c.args c.toCtx (World.creditValue w c.value) with
  | .ok (_, w') => w'
  | .error _ => w

/-- One step, reverting to the pre-world on a failed call.

Incoming `c.value` is credited onto `self`'s native balance *before*
`Tx.run` (EVM CALL is post-transfer at the callee). A revert rolls the
credit back with the body (`Tx.run` is unchanged). Non-payable selectors
are `valueOk`-forced to `v = 0` in the compiler, so the credit is a
no-op there. -/
def step [HasCreditValue X] : Step C → World S X E → World S X E
  | .call c, w => stepCall c w
  | .env x', w => { w with ext := x' }

/-- Left fold: first step first. -/
def run (tr : List (Step C)) (w : World S X E) : World S X E :=
  tr.foldl (fun acc s => step s acc) w

/-- Every call is aimed at `self` and is not a self-call. `env` steps are unrestricted. -/
def Wf (self : Address) : List (Step C) → Prop
  | [] => True
  | .call c :: tr => c.target = self ∧ c.sender ≠ self ∧ Wf self tr
  | .env _ :: tr => Wf self tr

/-- Every call in `tr` is sent from `A`. Environment steps are ignored. -/
def Trace.from (A : Finset Address) : List (Step C) → Prop
  | [] => True
  | .call c :: tr => c.sender ∈ A ∧ Trace.from A tr
  | .env _ :: tr => Trace.from A tr

end Lsc.Security
