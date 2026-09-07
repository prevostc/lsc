import Examples.TokenSecurity

open Lsc Lsc.Security Token

/-!
Proofs of Token's victim-side wealth theorems. Statements live in
`TokenSecurityTheorems`.
-/

namespace Token

namespace Proof

theorem token_no_unauthorized_extraction
    (self : Address) (tr : List (Step spec)) (w : World Storage Unit Event) (a : Address)
    (hw : Inv w) (hW : Wf self tr) (hR : RelyAlong (fun _ _ => True) tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  no_unauthorized_extraction token_no_unauth token_preserves_inv token_inv_rely
    self tr w a hw hW hR hA

theorem token_solvent (self : Address) (tr : List (Step spec)) (w : World Storage Unit Event)
    (hW : Wf self tr) (hR : RelyAlong (fun _ _ => True) tr w) (h : Inv w) :
    Solvent claim holdings self (run tr w) :=
  solvent_run token_preserves_inv token_inv_rely inv_solvent h tr hW hR

end Proof

end Token
