import Stdlib.ERC20
import Examples.WETH.Spec
import Examples.WETH.Proofs.Tx
import Examples.WETH.Proofs.Implements
import Examples.WETH.Proofs.Security
import Examples.WETH.Contract

/-!
WETH theorems: deposit/withdraw deltas, transfer conservation,
`IERC20.Exact` conformance, backing, and anti-extraction.
-/

open Lsc Lsc.Stdlib WETH

namespace WETH

variable (msg : Ctx) (w : World)

/-- A successful `deposit` credits `msg.value` to the sender and to
`totalSupply`. `Tx.run` does not credit incoming ETH; the trace `step`
does that before the body. -/
theorem deposit_delta {w' : World}
    (h : Tx.run depositTx msg w = .ok ((), w')) :
    w'.self.balances msg.sender =
      w.self.balances msg.sender + ⟨msg.value⟩ ∧
    w'.self.totalSupply = w.self.totalSupply + ⟨msg.value⟩ ∧
    World.nativeBalance w' = World.nativeBalance w :=
  Proof.deposit_delta msg w h

/-- A successful `withdraw` burns `amount` from the sender and from
`totalSupply`. Native `ext` is the `oracle.send` post-state. -/
theorem withdraw_delta (amount : Amount native)
    {w' : World}
    (h : Tx.run (withdraw amount) msg w = .ok ((), w')) :
    w'.self.balances msg.sender + amount = w.self.balances msg.sender ∧
    w'.self.totalSupply + amount = w.self.totalSupply :=
  Proof.withdraw_delta msg w amount h

/-- A successful `transfer` leaves the sum of the sender's and recipient's
balances unchanged. -/
theorem transfer_conserves (dst : Address) (amount : Amount native)
    {w' : World}
    (h : Tx.run (transfer dst amount) msg w = .ok (true, w')) :
    w'.self.balances msg.sender + w'.self.balances dst =
      w.self.balances msg.sender + w.self.balances dst :=
  Proof.transfer_conserves msg w dst amount h

/-- WETH is an exact ERC-20: every promise in `IERC20.Spec` holds of
`WETH.impl`. Vault/Cpamm take this via `.toSpec` with no new proofs. -/
theorem weth_exact : IERC20.Exact WETH.impl :=
  Proof.weth_exact

end WETH

open Lsc Lsc.Security WETH

namespace WETH

/-- Every wrapped token is backed: in any state the contract can actually
reach, the supply never exceeds the native balance it holds. -/
theorem weth_backed (w : State) :
    w.self.totalSupply ≤ w.nativeBalance :=
  Proof.weth_backed w

/-- No sequence of calls by other parties lowers `a`'s wrapped balance
except by the amount `a` itself authorised: `a`'s own `transfer`/`withdraw`,
or a `transferFrom` of `a`'s tokens. Only accepted calls count. Between
calls the environment may not drop this contract's native balance. -/
theorem weth_no_unauthorized_extraction (w : State) (t : Txs w) (a : Address) :
    w.self.balances a ≤ t.end.self.balances a + t.spent a :=
  Proof.weth_no_unauthorized_extraction w t a

end WETH
