import Examples.Token.Security
import Examples.Token.SecurityProof

/-!
Token at the spec: nobody can reduce your ERC-20 balance without your
authorisation, and recorded balances never exceed total supply.

Authorisation means you sent `transfer` or `burn`, or a `transferFrom`
spent an allowance you had granted. Any address may call any entrypoint
with any arguments. Token never calls another contract.

Traces must be well-formed (the token is not calling itself). Starting
balances must already sum to supply. Bytecode theorems lift these facts.
-/

open Lsc Lsc.Security Token

namespace Token

/-- No sequence of calls can reduce Alice's Token balance unless she authorised
one of them: she sent `transfer` or `burn` herself, or a `transferFrom` spent
an allowance she had granted, judged against the allowance stored at that
moment. Other users may transfer, mint, approve, or burn their own tokens in
any order; those actions cannot debit Alice. Views, `approve`, and `mint`
never decrease an existing balance, and a reverted call leaves every balance
unchanged. The starting balances must already sum to total supply, and the
token must not be calling itself. -/
theorem token_no_unauthorized_extraction
    (self : Address) (tr : List (Step spec)) (w : World Storage Unit Event) (a : Address)
    (hw : Inv w) (hW : Wf self tr) (hR : RelyAlong (fun _ _ => True) tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  Proof.token_no_unauthorized_extraction self tr w a hw hW hR hA

/-- After any well-formed sequence of Token calls, the sum of balances still
does not exceed total supply: the contract never owes more tokens than it
has recorded. The starting world must already be solvent in that sense.
Mint raises both sides together; burn lowers both; Token has no external
asset that could drift. -/
theorem token_solvent (self : Address) (tr : List (Step spec)) (w : World Storage Unit Event)
    (hW : Wf self tr) (hR : RelyAlong (fun _ _ => True) tr w) (h : Inv w) :
    Solvent claim holdings self (run tr w) :=
  Proof.token_solvent self tr w hW hR h

end Token
