import Examples.Token.Proofs
import Examples.Token.ProofsProof

/-!
Local conservation for Token `transfer`: a successful send to someone
else moves the amount and creates no extra tokens.

The sender must have the funds; the recipient must not overflow a
256-bit word. This is the one-step fact behind the global supply
invariant, not a security theorem about adversaries.
-/

open Lsc Token

namespace Token

variable (ctx : Ctx) (w : World Storage Unit Event)

/-- A successful `transfer` to a different address moves the amount from the
sender to the recipient and leaves the sum of those two balances unchanged:
no tokens are created or destroyed by the send. The sender must have the
funds, and the recipient's balance plus the amount must fit in a 256-bit
word; a self-transfer is out of scope here. This is the local conservation
fact behind Token's global "balances sum to supply" invariant. -/
theorem transfer_conserves (to : Address) (amount : Nat) (hne : ctx.sender ≠ to)
    (hsub : amount ≤ w.self.balances ctx.sender)
    (hadd : w.self.balances to + amount < wordBound) :
    ∃ w', Tx.run (transfer to amount) ctx w = .ok ((), w') ∧
      w'.self.balances ctx.sender + w'.self.balances to =
        w.self.balances ctx.sender + w.self.balances to :=
  Proof.transfer_conserves ctx w to amount hne hsub hadd

end Token
