import Stdlib.ERC20
import Examples.Token.Spec
import Examples.Token.Proofs.Tx
import Examples.Token.Proofs.Security
import Examples.Token.Proofs.Implements
import Examples.Token.Contract

/-!
Token theorems: local conservation of `transfer` / `transferFrom`, `approve`
sets allowance, the ERC20 conformance theorem, and spec-level anti-extraction
and solvency.
-/

open Lsc Lsc.Stdlib Token

namespace Token

variable (msg : Ctx) (w : World)

/-- A successful `transfer` leaves the sum of the sender's and recipient's
balances unchanged: no tokens are created or destroyed by the send. This
includes a self-transfer, which is a no-op on those two balances. Success
already implies the sender had the funds and the recipient's balance plus
the amount fit in a 256-bit word. This is the local conservation fact
behind Token's global "balances sum to supply" invariant. -/
theorem transfer_conserves (dst : Address) (amount : Amount tokenAsset)
    {w' : World}
    (h : Tx.run (transfer dst amount) msg w = .ok (true, w')) :
    w'.self.balances msg.sender + w'.self.balances dst =
      w.self.balances msg.sender + w.self.balances dst :=
  Proof.transfer_conserves msg w dst amount h

/-- A successful `transferFrom` leaves the sum of the source's and recipient's
balances unchanged, including a self-transfer. Success already implies the
allowance and balance checks and that the credit fit in a word. -/
theorem transferFrom_conserves (src dst : Address) (amount : Amount tokenAsset)
    {w' : World}
    (h : Tx.run (transferFrom src dst amount) msg w = .ok (true, w')) :
    w'.self.balances src + w'.self.balances dst =
      w.self.balances src + w.self.balances dst :=
  Proof.transferFrom_conserves msg w src dst amount h

/-- A successful `transferFrom` spends exactly `amount` of `src`'s allowance
for the caller: the remaining allowance plus `amount` equals the allowance
before the call. This includes self-spend (`sender = src`); the ERC20 spec
only requires the fact when `sender ≠ src`. -/
theorem transferFrom_allowance (src dst : Address) (amount : Amount tokenAsset)
    {w' : World}
    (h : Tx.run (transferFrom src dst amount) msg w = .ok (true, w')) :
    w'.self.allowances src msg.sender + amount =
      w.self.allowances src msg.sender :=
  Proof.transferFrom_allowance msg w src dst amount h

/-- A successful `approve` writes `amount` as the caller's allowance for
`spender`. -/
theorem approve_sets (spender : Address) (amount : Amount tokenAsset)
    {w' : World}
    (h : Tx.run (approve spender amount) msg w = .ok (true, w')) :
    w'.self.allowances msg.sender spender = amount :=
  Proof.approve_sets msg w spender amount h

/-- Token is a conforming ERC20: every promise in `IERC20.Spec` holds of
`Token.impl`. Named `erc20` because `lsc_contract` already generates the ABI
spec as `Token.spec`. -/
theorem erc20 : IERC20.Spec Token.impl :=
  Proof.erc20

end Token

open Lsc Lsc.Security Token

namespace Token

/-- Recorded balances still sum to total supply on a finite support: every
token is accounted for. Mint raises both sides together; burn lowers both;
Token has no external asset that could drift. The sum uses `.raw` because
`Amount` has no `AddCommMonoid` instance for `Finset.sum`. -/
theorem token_solvent (w : State) :
    ∃ H : Finset Address,
      (∀ a, a ∉ H → w.self.balances a = 0) ∧
      H.sum (fun a => (w.self.balances a).raw) = w.self.totalSupply.raw :=
  Proof.token_solvent w

/-- No sequence of calls by other parties lowers `a`'s balance except by the
amount `a` itself authorised: `a`'s own `transfer`/`burn`, or a
`transferFrom` of `a`'s tokens. Only accepted calls count — a reverting
`transferFrom(a, …, 2^200)` does not vacate the bound. Environment steps
cannot change storage. -/
theorem token_no_unauthorized_extraction (w : State) (t : Txs w) (a : Address) :
    w.self.balances a ≤ t.end.self.balances a + t.spent a :=
  Proof.token_no_unauthorized_extraction w t a

end Token
