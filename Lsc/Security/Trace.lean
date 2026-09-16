import Mathlib.Data.Finset.Basic
import Lsc.Lang.Spec

/-!
Trace semantics of one contract: `Call`, `Step`, `step`, and `run` over a language-level
`Lsc.Spec`. A reverted call is a no-op on the world (EVM atomicity). `env` steps replace
the ghost record; they are constrained by `RelyAlong` in `Invariant.lean`. `External`
says every call targets this contract and is not a self-call (physically only this
contract's code can emit a message from `self`; nested calls are the oracle's
`nested_lock_reverts`). The 256-bit native wrap is a dispatcher/`stepCall` revert,
not a trace assumption. Public theorems quantify `State` / `Txs` (`State.lean`).
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

/-- After the EVM credits `v`, wrap occurred iff the 256-bit balance is
`< v`. Matches dispatcher `lt(selfbalance(), callvalue())`. -/
def creditWraps [HasCreditValue X] [HasSelfBalance X]
    (w : World S X E) (v : Nat) : Bool :=
  decide (HasSelfBalance.get (World.creditValue w v).ext < v)

/-- Post-world of a call. Incoming value is credited only when the target
is payable (`C.payable`); a revert of that body rolls the credit back.
A nonzero-value call to a non-payable function is a revert step (world
unchanged), matching compiler `valueOk` / `dispatchedFn`. A payable call
whose credited balance wraps the 256-bit word is also a revert step,
matching dispatcher `lt(selfbalance(), callvalue())`. Non-payable
success has `v = 0`, so `creditValue w 0 = w`. -/
def stepCall [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    (c : Call C) (w : World S X E) : World S X E :=
  if C.valueOk c.fn c.value then
    if C.payable c.fn && creditWraps w c.value then
      w
    else
      match C.exec c.fn c.args c.toCtx (World.creditValue w c.value) with
      | .ok (_, w') => w'
      | .error _ => w
  else
    w

/-- One step, reverting to the pre-world on a failed call.

Incoming `c.value` is credited onto `self`'s native balance *before*
`Tx.run` only for an accepted payable call (EVM CALL is post-transfer
at the callee, and a value-reject or wrap-reject reverts the transfer).
`Tx.run` is unchanged. -/
def step [HasCreditValue X] [HasPayable C] [HasSelfBalance X] :
    Step C → World S X E → World S X E
  | .call c, w => stepCall c w
  | .env x', w => { w with ext := x' }

/-- Left fold: first step first. -/
def run [HasCreditValue X] [HasPayable C] [HasSelfBalance X] :
    List (Step C) → World S X E → World S X E
  | [], w => w
  | s :: tr, w => run tr (step s w)

/-- Default rely: this contract's native balance does not fall across an
environment step. Only this contract's code can move its ETH; donations
are allowed. Contracts with `Ref` counterparties (Vault/Cpamm) override
via `HasRely`. -/
def defaultRely [HasSelfBalance X] (x x' : X) : Prop :=
  HasSelfBalance.get x ≤ HasSelfBalance.get x'

/-- Environment-step permission. Default is `defaultRely`. -/
class HasRely (C : Spec S X E ε) [HasSelfBalance X] where
  rely : X → X → Prop := defaultRely

instance (priority := low) {C : Spec S X E ε} [HasSelfBalance X] : HasRely C where
  rely := defaultRely

/-- True iff `stepCall` takes the successful-exec arm. Failed attempts
(value reject, wrap, or body revert) are not counted by `Txs.spent`. -/
def accepted [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
    (c : Call C) (w : World S X E) : Bool :=
  if C.valueOk c.fn c.value then
    if C.payable c.fn && creditWraps w c.value then false
    else
      match C.exec c.fn c.args c.toCtx (World.creditValue w c.value) with
      | .ok _ => true
      | .error _ => false
  else false

/-- Calls in this contract's trace target `self` and are not self-calls.
The native wrap is a dispatcher/`stepCall` revert, not a trace assumption. -/
def External (self : Address) : List (Step C) → Prop
  | [] => True
  | .call c :: tr => c.target = self ∧ c.sender ≠ self ∧ External self tr
  | .env _ :: tr => External self tr

/-- Mechanical name: `Wf` no longer carries a native-balance bound or a
world index. Public theorems use `State` / `Txs`. -/
def Wf (self : Address) (tr : List (Step C)) (_w : World S X E) : Prop :=
  External (C := C) self tr

/-- Every call in `tr` is sent from `A`. Environment steps are ignored. -/
def Trace.from (A : Finset Address) : List (Step C) → Prop
  | [] => True
  | .call c :: tr => c.sender ∈ A ∧ Trace.from A tr
  | .env _ :: tr => Trace.from A tr

end Lsc.Security
