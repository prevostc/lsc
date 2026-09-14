import Stdlib.ERC20
import Examples.Token.Spec
import Examples.Token.Proofs.Tx
import Examples.Token.Proofs.Security
import Examples.Token.Proofs.Implements
import Examples.Token.Contract

set_option linter.unusedVariables false

/-!
Token theorems: local conservation of `transfer` / `transferFrom`, `approve`
sets allowance, the ERC20 conformance theorem, and spec-level anti-extraction
and solvency.
-/

open Lsc Lsc.Stdlib Token

namespace Token

variable (ctx : Ctx) (w : World Storage ExtState Event)

/-- A successful `transfer` leaves the sum of the sender's and recipient's
balances unchanged: no tokens are created or destroyed by the send. This
includes a self-transfer, which is a no-op on those two balances. Success
already implies the sender had the funds and the recipient's balance plus
the amount fit in a 256-bit word. This is the local conservation fact
behind Token's global "balances sum to supply" invariant. -/
theorem transfer_conserves (dst : Address) (amount : Amount tokenAsset)
    {w' : World Storage ExtState Event}
    (h : Tx.run (transfer dst amount) ctx w = .ok (true, w')) :
    w'.self.balances ctx.sender + w'.self.balances dst =
      w.self.balances ctx.sender + w.self.balances dst :=
  Proof.transfer_conserves ctx w dst amount h

/-- A successful `transferFrom` leaves the sum of the source's and recipient's
balances unchanged, including a self-transfer. Success already implies the
allowance and balance checks and that the credit fit in a word. -/
theorem transferFrom_conserves (src dst : Address) (amount : Amount tokenAsset)
    {w' : World Storage ExtState Event}
    (h : Tx.run (transferFrom src dst amount) ctx w = .ok (true, w')) :
    w'.self.balances src + w'.self.balances dst =
      w.self.balances src + w.self.balances dst :=
  Proof.transferFrom_conserves ctx w src dst amount h

/-- A successful `transferFrom` spends exactly `amount` of `src`'s allowance
for the caller: the remaining allowance plus `amount` equals the allowance
before the call. This includes self-spend (`sender = src`); the ERC20 spec
only requires the fact when `sender ≠ src`. -/
theorem transferFrom_allowance (src dst : Address) (amount : Amount tokenAsset)
    {w' : World Storage ExtState Event}
    (h : Tx.run (transferFrom src dst amount) ctx w = .ok (true, w')) :
    w'.self.allowances src ctx.sender + amount =
      w.self.allowances src ctx.sender :=
  Proof.transferFrom_allowance ctx w src dst amount h

/-- A successful `approve` writes `amount` as the caller's allowance for
`spender`. -/
theorem approve_sets (spender : Address) (amount : Amount tokenAsset)
    {w' : World Storage ExtState Event}
    (h : Tx.run (approve spender amount) ctx w = .ok (true, w')) :
    w'.self.allowances ctx.sender spender = amount :=
  Proof.approve_sets ctx w spender amount h

/-- Token is a conforming ERC20: every promise in `IERC20.Spec` holds of
`Token.impl`. Named `erc20` because `lsc_contract` already generates the ABI
spec as `Token.spec`. -/
theorem erc20 : IERC20.Spec Token.impl :=
  Proof.erc20

end Token

open Lsc Lsc.Security Token

namespace Token

/-- No sequence of calls can reduce Alice's Token balance unless she authorised
one of them: she sent `transfer` or `burn` herself, or a `transferFrom` spent
an allowance she had granted, judged against the allowance stored at that
moment. Other users may transfer, mint, approve, or burn their own tokens in
any order; those actions cannot debit Alice. Views, `approve`, and `mint`
never decrease an existing balance, and a reverted call leaves every balance
unchanged. The starting balances must already sum to total supply. -/
theorem token_no_unauthorized_extraction
    (tr : List (Step spec)) (w : World Storage ExtState Event) (a : Address)
    (hw : Inv w) (hR : RelyAlong (fun _ _ => True) tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  Proof.token_no_unauthorized_extraction tr w a hw hR hA

/-- After any well-formed sequence of Token calls, recorded balances still
sum to total supply on a finite support: every token is accounted for.
The starting world must already satisfy that equality. Mint raises both
sides together; burn lowers both; Token has no external asset that could
drift. The generic solvency bound (sum of balances ≤ supply) is then
immediate. -/
theorem token_solvent (self : Address) (tr : List (Step spec))
    (w : World Storage ExtState Event)
    (hW : Wf self tr) (hR : RelyAlong (fun _ _ => True) tr w) (h : Inv w) :
    Inv (run tr w) :=
  Proof.token_solvent self tr w hW hR h

end Token
