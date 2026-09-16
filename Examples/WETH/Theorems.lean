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

/-- WETH is an exact ERC-20: every promise in `IERC20.Spec` holds of
`WETH.impl`. Vault/Cpamm take this via `.toSpec` with no new proofs. -/
theorem weth_exact : IERC20.Exact WETH.impl :=
  Proof.weth_exact

end WETH

open Lsc Lsc.Security WETH

namespace WETH

/-- Every wrapped token is backed: in any state the contract can actually reach, the supply
never exceeds the native balance it holds. -/
theorem weth_backed {self : Address} {w : World Storage ExtState Event}
    (h : Reachable (C := spec) rely self w) :
    w.self.totalSupply.raw ≤ World.nativeBalance w :=
  Proof.weth_backed h

/-- No sequence of calls by other parties lowers `a`'s balance; the only way `a`'s
claim falls is `a`'s own `transfer` or `withdraw`, or a `transferFrom` within an
allowance `a` granted. Deposit is payable and only credits the caller. Between
calls the environment may not drop this contract's native balance (donations are
allowed). Well-formed traces target this contract, have a distinct caller, and
never overflow a 256-bit native balance. Reverted calls leave every balance
unchanged. -/
theorem weth_no_unauthorized_extraction (self : Address)
    (tr : List (Step spec)) (w : World Storage ExtState Event) (a : Address)
    (h : Reachable (C := spec) rely self w)
    (hW : Wf self tr w) (hR : RelyAlong rely tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w ≤ claim a (run tr w) :=
  Proof.weth_no_unauthorized_extraction self tr w a h hW hR hA

end WETH
