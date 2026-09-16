import Stdlib.ERC20
import Examples.WNative.Spec
import Examples.WNative.Proofs.Tx
import Examples.WNative.Proofs.Implements
import Examples.WNative.Proofs.Security
import Examples.WNative.Contract

/-!
WNative theorems: deposit/withdraw deltas, transfer conservation, and
`IERC20.Exact` conformance.
-/

open Lsc Lsc.Stdlib WNative

namespace WNative

variable (ctx : Ctx) (w : World Storage ExtState Event)

/-- A successful `deposit` credits `ctx.value` to the sender and to
`totalSupply`. `Tx.run` does not credit incoming ETH; the trace `step`
does that before the body. -/
theorem deposit_delta {w' : World Storage ExtState Event}
    (h : Tx.run depositTx ctx w = .ok ((), w')) :
    w'.self.balances ctx.sender =
      w.self.balances ctx.sender + ⟨ctx.value⟩ ∧
    w'.self.totalSupply = w.self.totalSupply + ⟨ctx.value⟩ ∧
    World.nativeBalance w' = World.nativeBalance w :=
  Proof.deposit_delta ctx w h

/-- A successful `withdraw` burns `amount` from the sender and from
`totalSupply`. Native `ext` is the `oracle.send` post-state. -/
theorem withdraw_delta (amount : Amount native)
    {w' : World Storage ExtState Event}
    (h : Tx.run (withdraw amount) ctx w = .ok ((), w')) :
    w'.self.balances ctx.sender + amount = w.self.balances ctx.sender ∧
    w'.self.totalSupply + amount = w.self.totalSupply :=
  Proof.withdraw_delta ctx w amount h

/-- A successful `transfer` leaves the sum of the sender's and recipient's
balances unchanged. -/
theorem transfer_conserves (dst : Address) (amount : Amount native)
    {w' : World Storage ExtState Event}
    (h : Tx.run (transfer dst amount) ctx w = .ok (true, w')) :
    w'.self.balances ctx.sender + w'.self.balances dst =
      w.self.balances ctx.sender + w.self.balances dst :=
  Proof.transfer_conserves ctx w dst amount h

/-- WNative is an exact ERC-20: every promise in `IERC20.Spec` holds of
`WNative.impl`. Vault/Cpamm take this via `.toSpec` with no new proofs. -/
theorem wnative_exact : IERC20.Exact WNative.impl :=
  Proof.wnative_exact

/-- Under `Inv`, wrapped `totalSupply` is backed by `self`'s native balance.
Native extraction is not a Wealth `Claim` (see AUDIT_COVERAGE). -/
theorem wnative_backed {w : World Storage ExtState Event} (h : Inv w) :
    w.self.totalSupply.raw ≤ World.nativeBalance w :=
  Proof.wnative_backed h

end WNative
