import Examples.Token.Proofs

open Lsc Token

/-!
Proof of `Token.transfer_conserves`. Statement lives in `TokenProofsTheorems`.
-/

namespace Token

variable (ctx : Ctx) (w : World Storage Unit Event)

namespace Proof

theorem transfer_conserves (to : Address) (amount : Nat) (hne : ctx.sender ≠ to)
    (hsub : amount ≤ w.self.balances ctx.sender)
    (hadd : w.self.balances to + amount < wordBound) :
    ∃ w', Tx.run (transfer to amount) ctx w = .ok ((), w') ∧
      w'.self.balances ctx.sender + w'.self.balances to =
        w.self.balances ctx.sender + w.self.balances to := by
  refine ⟨_, transfer_ok ctx w to amount hsub (by simpa [debit_other _ hne.symm] using hadd), ?_⟩
  simp [transferPost, credit_other _ hne, debit_other _ hne.symm]
  omega

end Proof

end Token
