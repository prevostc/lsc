import Lsc.Security.Wealth
import Examples.WNative.Contract

/-!
WNative spec: `claim` is the wrapped balance; `Auth` is the holder's own
`transfer` / `withdraw` or an allowance-backed `transferFrom`. `Inv` is
finite-support conservation of balances against `totalSupply`.
-/

open Lsc Lsc.Security WNative

namespace WNative

/-- `claim a w` is `a`'s wrapped balance. -/
def claim : Claim Storage ExtState Event :=
  Claim.ofSelf fun a s => (s.balances a).raw

/-- Tight permission: views/`approve`/`deposit` never decrease `claim`. -/
def Auth : AuthPred spec :=
  AuthPred.ofSelf fun a c s =>
    match c.fn, c.args with
    | .transfer, _ => c.sender = a
    | .withdraw, amount => c.sender = a ∧ amount ≤ s.balances a
    | .transferFrom, (src, _, amount) => src = a ∧ amount ≤ s.allowances src c.sender
    | _, _ => False

/-- Deposit is the only inflow; it is `0` on revert. -/
def inflow (c : Call spec) (w : World Storage ExtState Event) : Nat :=
  match c.fn, c.args with
  | .deposit, _ =>
    match Tx.run (@deposit Payable.entrypoint) c.toCtx w with
    | .ok _ => c.toCtx.value
    | .error _ => 0
  | _, _ => 0

/-- Holdings for solvency are recorded `totalSupply` (wrapped tokens).
Native ETH of `self` is `World.nativeBalance`, used by `wnative_backed`. -/
def holdings (_self : Address) (w : World Storage ExtState Event) : Nat :=
  w.self.totalSupply.raw

/-- Finite support of balances. -/
def InvStorage (s : Storage) : Prop :=
  ∃ H : Finset Address,
    (∀ a, a ∉ H → s.balances a = 0) ∧
    H.sum (fun a => (s.balances a).raw) = s.totalSupply.raw

def Inv (w : World Storage ExtState Event) : Prop :=
  InvStorage w.self ∧ w.self.totalSupply.raw ≤ World.nativeBalance w

/-- Environment steps may change `ext` (including native balances).
Storage-only `claim` is automatically monotone. -/
def rely (_x _x' : ExtState) : Prop := True

end WNative
