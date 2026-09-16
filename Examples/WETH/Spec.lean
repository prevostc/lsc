import Lsc.Security.Wealth
import Examples.WETH.Contract

/-!
WETH spec: `claim` is the wrapped balance (redeemable native on `self`'s
books; not a second `ofNative` summand). `Auth` is the holder's own
`transfer` / `withdraw` or an allowance-backed `transferFrom`. Between
our transactions, `rely` lets `ext` change except that this contract's
native balance does not fall. The storage/backing invariant is a proof
device in `Proofs/Security.lean`.
-/

open Lsc Lsc.Security WETH

namespace WETH

/-- `claim a w` is `a`'s wrapped balance. Wrapped tokens are the redeemable
native; do not also use `Claim.ofNative`. -/
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
Native ETH of `self` is `World.nativeBalance`, used by `weth_backed`. -/
def holdings (_self : Address) (w : World Storage ExtState Event) : Nat :=
  w.self.totalSupply.raw

/-- Between our transactions the outside world may change `ext`
arbitrarily, except that this contract's native balance does not fall
(donations are allowed). That is what keeps wrapping backed across
environment steps; `withdraw` is the only native outflow, and it burns
matching wrapped tokens. -/
def rely (x x' : ExtState) : Prop :=
  x.env.selfBalance.toNat ≤ x'.env.selfBalance.toNat

end WETH
