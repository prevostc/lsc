import Examples.AmmSecurity

open Lsc Lsc.Stdlib Lsc.Security Amm

/-!
Proofs of AMM's victim-side wealth theorems. Statements live in
`AmmSecurityTheorems`.
-/

namespace Amm

namespace Proof

theorem amm_solvent (self : Address) (tr : List (Step spec))
    (w : World Storage Ext Event)
    (hW : Wf self tr) (hR : RelyAlong (ammRely self) tr w) (h : Inv self w) :
    Solvent claim0 holdings0 self (run tr w) ∧
      Solvent claim1 holdings1 self (run tr w) :=
  ⟨solvent_run_at (amm_preserves_inv self) (inv_rely self) (inv_solvent0 self) h tr hW hR,
    solvent_run_at (amm_preserves_inv self) (inv_rely self) (inv_solvent1 self) h tr hW hR⟩

theorem amm_no_unauthorized_extraction (self : Address)
    (tr : List (Step spec)) (w : World Storage Ext Event) (a : Address)
    (hw : Inv self w) (hW : Wf self tr) (hR : RelyAlong (ammRely self) tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  no_unauthorized_extraction_at (amm_no_unauth self) (amm_preserves_inv self)
    (inv_rely self) tr w a hw hW hR hA

end Proof

end Amm
