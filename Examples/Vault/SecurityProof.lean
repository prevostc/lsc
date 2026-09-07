import Examples.Vault.Security

open Lsc Lsc.Stdlib Lsc.Security Vault

/-!
Proofs of Vault's victim-side wealth theorems. Statements live in
`VaultSecurityTheorems`.
-/

namespace Vault

namespace Proof

theorem vault_solvent (self : Address) (tr : List (Step spec))
    (w : World Storage Ext Event)
    (hW : Wf self tr) (hR : RelyAlong (vaultRely self) tr w) (h : Inv self w) :
    Solvent claim holdings self (run tr w) :=
  solvent_run_at (vault_preserves_inv self) (inv_rely self) (inv_solvent self) h tr hW hR

theorem vault_no_unauthorized_extraction (self : Address)
    (tr : List (Step spec)) (w : World Storage Ext Event) (a : Address)
    (hw : Inv self w) (hW : Wf self tr) (hR : RelyAlong (vaultRely self) tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  no_unauthorized_extraction_at (vault_no_unauth self) (vault_preserves_inv self)
    (inv_rely self) tr w a hw hW hR hA

end Proof

end Vault
