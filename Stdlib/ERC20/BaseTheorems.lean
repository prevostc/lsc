import Stdlib.ERC20.Proofs.Base

/-!
Generic ERC20 facts over any lawful `ERC20.Fields` lens triple: conservation,
allowance spend, approve, mint/burn deltas, and `IERC20.Exact`.
-/

open Lsc Lsc.Stdlib

namespace Lsc.Stdlib.ERC20

variable {S X E ε : Type} {a : Asset}
variable [Events E a] [Errors ε]
variable (F : Fields S a)
variable [Fields.Lawful F]
variable (msg : Ctx) (w : World S X E)

/-- A successful `transfer` leaves the sum of the sender's and recipient's
balances unchanged, including a self-transfer. -/
theorem transfer_conserves (to : Address) (amount : Amount a) {w' : World S X E}
    (h : Tx.run (transfer (ε := ε) F to amount) msg w = .ok (true, w')) :
    F.balances.get w'.self msg.sender + F.balances.get w'.self to =
      F.balances.get w.self msg.sender + F.balances.get w.self to :=
  Proof.transfer_conserves F msg w to amount h

/-- A successful `transferFrom` spends exactly `amount` of `src`'s allowance
for the caller. -/
theorem transferFrom_allowance (src to : Address) (amount : Amount a)
    {w' : World S X E}
    (h : Tx.run (transferFrom (ε := ε) F src to amount) msg w = .ok (true, w')) :
    F.allowances.get w'.self src msg.sender + amount =
      F.allowances.get w.self src msg.sender :=
  Proof.transferFrom_allowance F msg w src to amount h

/-- A successful `approve` writes `amount` as the caller's allowance for
`spender`. -/
theorem approve_sets (spender : Address) (amount : Amount a) {w' : World S X E}
    (h : Tx.run (approve (ε := ε) F spender amount) msg w = .ok (true, w')) :
    F.allowances.get w'.self msg.sender spender = amount :=
  Proof.approve_sets F msg w spender amount h

/-- A successful `mint` credits `amount` to `to` and to recorded supply. -/
theorem mint_delta (to : Address) (amount : Amount a) {w' : World S X E}
    (h : Tx.run (mint (ε := ε) F to amount) msg w = .ok ((), w')) :
    F.balances.get w'.self to = F.balances.get w.self to + amount ∧
    F.totalSupply.get w'.self = F.totalSupply.get w.self + amount :=
  Proof.mint_delta F msg w to amount h

/-- A successful `burn` removes `amount` from `src` and from recorded supply. -/
theorem burn_delta (src : Address) (amount : Amount a) {w' : World S X E}
    (h : Tx.run (burn (ε := ε) F src amount) msg w = .ok ((), w')) :
    F.balances.get w'.self src + amount = F.balances.get w.self src ∧
    F.totalSupply.get w'.self + amount = F.totalSupply.get w.self :=
  Proof.burn_delta F msg w src amount h

/-- The six IERC20 methods at `F` keep every `IERC20.Exact` promise.
Requires the three lenses to be lawful and pairwise independent
(`Fields.Lawful F`; `ofParent` of a lawful parent synthesises this). -/
theorem exact : IERC20.Exact (impl (E := E) (X := X) (ε := ε) F) :=
  Proof.exact F

end Lsc.Stdlib.ERC20
