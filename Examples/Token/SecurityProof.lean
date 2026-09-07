import Examples.Token.Security
import Lsc.Security.InvariantTheorems

open Lsc Lsc.Security Token

/-!
Proofs of Token's victim-side wealth theorems. Statements live in
`TokenSecurityTheorems`.
-/

namespace Token

namespace Proof

theorem token_no_unauthorized_extraction
    (tr : List (Step spec)) (w : World Storage Unit Event) (a : Address)
    (hw : Inv w) (hR : RelyAlong (fun _ _ => True) tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  no_unauthorized_extraction token_no_unauth token_preserves_inv token_inv_rely
    tr w a hw hR hA

theorem token_solvent (self : Address) (tr : List (Step spec)) (w : World Storage Unit Event)
    (hW : Wf self tr) (hR : RelyAlong (fun _ _ => True) tr w) (h : Inv w) :
    Inv (run tr w) :=
  inv_run token_preserves_inv token_inv_rely h tr hW hR

end Proof

end Token
