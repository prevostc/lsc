import Mathlib.Data.Finset.Basic
import Lsc.Lang.Spec

/-!
Trace semantics of one contract: `Call`, `Step`, `step`, and `run` over a language-level
`Lsc.Spec`. A reverted call is a no-op on the world (EVM atomicity). `env` steps replace
the ghost record; they are constrained by `RelyAlong` in `Invariant.lean`. `Wf` is
state-indexed: well-formed traces target `self`, are not self-calls, and never overflow
a 256-bit native balance.
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

/-- Post-world of a call. Incoming value is credited only when the target
is payable (`C.payable`); a revert of that body rolls the credit back.
A nonzero-value call to a non-payable function is a revert step (world
unchanged), matching compiler `valueOk` / `dispatchedFn`. Non-payable
success has `v = 0`, so `creditValue w 0 = w`. -/
def stepCall [HasCreditValue X] [HasPayable C] (c : Call C) (w : World S X E) :
    World S X E :=
  if C.valueOk c.fn c.value then
    match C.exec c.fn c.args c.toCtx (World.creditValue w c.value) with
    | .ok (_, w') => w'
    | .error _ => w
  else
    w

/-- One step, reverting to the pre-world on a failed call.

Incoming `c.value` is credited onto `self`'s native balance *before*
`Tx.run` only for an accepted payable call (EVM CALL is post-transfer
at the callee, and a value-reject reverts the transfer). `Tx.run` is
unchanged. -/
def step [HasCreditValue X] [HasPayable C] : Step C → World S X E → World S X E
  | .call c, w => stepCall c w
  | .env x', w => { w with ext := x' }

/-- Left fold: first step first. -/
def run [HasCreditValue X] [HasPayable C] (tr : List (Step C)) (w : World S X E) :
    World S X E :=
  tr.foldl (fun acc s => step s acc) w

/-- Well-formed traces target `self`, are not self-calls, and never overflow a
256-bit native balance — true on every chain since total native supply <
`2^256`. Incoming `creditValue` still wraps (EVM `BitVec`); this predicate
is what rules wrapping out of attack traces. `env` steps thread the world.
On `ExtState`, `HasSelfBalance.get w.ext` is `World.nativeBalance w`. -/
def Wf [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    (self : Address) : List (Step C) → World S X E → Prop
  | [], _ => True
  | .call c :: tr, w =>
      c.target = self ∧ c.sender ≠ self ∧
      HasSelfBalance.get w.ext + c.value < wordBound ∧
      Wf self tr (step (.call c) w)
  | .env x' :: tr, w =>
      Wf self tr { w with ext := x' }

/-- Every call in `tr` is sent from `A`. Environment steps are ignored. -/
def Trace.from (A : Finset Address) : List (Step C) → Prop
  | [] => True
  | .call c :: tr => c.sender ∈ A ∧ Trace.from A tr
  | .env _ :: tr => Trace.from A tr

end Lsc.Security
