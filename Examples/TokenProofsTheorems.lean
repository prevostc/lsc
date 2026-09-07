import Examples.TokenProofs
import Examples.TokenProofsProof

/-!
ERC-20 transfer conservation at the `Tx.run` layer: the amount leaves the
sender and arrives at a distinct recipient, with no extra tokens created.
-/

open Lsc Token

namespace Token

variable (ctx : Ctx) (w : World Storage Unit Event)

/-- A successful `transfer` to a different address moves `amount` from the
sender to `to` and leaves the sum of those two balances unchanged. Both
parties must be in range (sender has the funds; recipient does not
overflow `2^256`). This is the elementary conservation fact the Token
security development uses when showing the global `claim` sum is
preserved. -/
theorem transfer_conserves (to : Address) (amount : Nat) (hne : ctx.sender ≠ to)
    (hsub : amount ≤ w.self.balances ctx.sender)
    (hadd : w.self.balances to + amount < wordBound) :
    ∃ w', Tx.run (transfer to amount) ctx w = .ok ((), w') ∧
      w'.self.balances ctx.sender + w'.self.balances to =
        w.self.balances ctx.sender + w.self.balances to :=
  Proof.transfer_conserves ctx w to amount hne hsub hadd

end Token
