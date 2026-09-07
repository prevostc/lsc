import Examples.Token.Security
import Examples.Token.SecurityProof

/-!
Token instances of the generic wealth theorems: ERC-20 balances as `claim`,
over traces of the Token spec.
-/

open Lsc Lsc.Security Token

namespace Token

/-- If `Inv` holds (balances sum to `totalSupply` on a finite support) and
account `a` never authorised a Token call on the trace, `a`'s ERC-20
balance does not fall. `Auth` treats `transfer`/`burn` as the sender's
act and `transferFrom` as allowed only within the stored allowance;
views, `approve`, and `mint` never decrease `claim`. Environment steps
are trivial (`X := Unit`). This is Token's spec-level anti-extraction
theorem; bytecode glue lifts it in `TokenEndToEndTheorems`. -/
theorem token_no_unauthorized_extraction
    (self : Address) (tr : List (Step spec)) (w : World Storage Unit Event) (a : Address)
    (hw : Inv w) (hW : Wf self tr) (hR : RelyAlong (fun _ _ => True) tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  Proof.token_no_unauthorized_extraction self tr w a hw hW hR hA

/-- `Inv` is preserved by every Token call and every (trivial) env step, so
a solvent starting world stays solvent along any well-formed trace:
the sum of balances never exceeds `totalSupply`. -/
theorem token_solvent (self : Address) (tr : List (Step spec)) (w : World Storage Unit Event)
    (hW : Wf self tr) (hR : RelyAlong (fun _ _ => True) tr w) (h : Inv w) :
    Solvent claim holdings self (run tr w) :=
  Proof.token_solvent self tr w hW hR h

end Token
