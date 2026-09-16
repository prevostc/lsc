import Lsc.Security.Wealth
import Lsc.Security.State
import Examples.Token.Contract

/-!
Token spec: `claim` is an ERC-20 balance; `Auth` is the victim's own
`transfer`/`burn` or an allowance-backed `transferFrom`. `Inv` is
finite-support conservation of balances against `totalSupply`.
-/

open Lsc Lsc.Security Token

namespace Token

/-- `claim a w` is `a`'s ERC-20 balance. -/
def claim : Claim Storage ExtState Event :=
  Claim.ofSelf fun a s => (s.balances a).raw

/-- Tight permission: mint/approve/views never decrease `claim`, so `Auth` is false.
`transferFrom` is allowance-aware so reverting spam still satisfies `NoAuthAlong`. -/
def Auth : AuthPred spec :=
  AuthPred.ofSelf fun a c s =>
    match c.fn, c.args with
    | .transfer, _ => c.sender = a
    | .burn, _ => c.sender = a
    | .transferFrom, (src, _, amount) => src = a ∧ amount ≤ s.allowances src c.sender
    | _, _ => False

/-- Mint is the only inflow; it is `0` on revert. Storage-only so
`inflow` is unchanged by `World.creditValue`. -/
def inflow (c : Call spec) (w : World) : Nat :=
  match c.fn, c.args with
  | .mint, (dst, amt) =>
    if c.toCtx.sender = w.self.owner ∧
        (w.self.totalSupply + amt).raw < wordBound ∧
        (w.self.balances dst + amt).raw < wordBound
    then amt.raw else 0
  | _, _ => 0

/-- Token holdings are the recorded `totalSupply`. The address is ignored. -/
def holdings (_self : Address) (w : World) : Nat :=
  w.self.totalSupply.raw

/-- Finite support of balances. Used by `inv_of_*`; `Inv` wraps it on a world. -/
def InvStorage (s : Storage) : Prop :=
  ∃ H : Finset Address,
    (∀ a, a ∉ H → s.balances a = 0) ∧
    H.sum (fun a => (s.balances a).raw) = s.totalSupply.raw

def Inv (w : World) : Prop := InvStorage w.self

/-- Empty storage is a valid deployment (no constructor in the runtime spec). -/
instance : HasDeploy spec where
  pred w := w.self = default

instance : HasRely spec where
  rely := defaultRely (X := ExtState)

/-- Amount this accepted call moved out on `a`'s authority. -/
def spentCall (a : Address) (c : Call spec) : Amount tokenAsset :=
  match c.fn, c.args with
  | .transfer, (_, amount) => if c.sender = a then amount else 0
  | .burn, amount => if c.sender = a then amount else 0
  | .transferFrom, (src, _, amount) => if src = a then amount else 0
  | _, _ => 0

instance : HasSpent spec where
  asset := tokenAsset
  spentCall := spentCall

/-- Deployed Token states. -/
abbrev State := Lsc.Security.State spec

end Token
