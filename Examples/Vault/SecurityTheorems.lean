import Examples.Vault.Security
import Examples.Vault.SecurityProof

/-!
Vault instances of the generic wealth theorems: a depositor's pro-rata
share of vault assets as `claim`.
-/

open Lsc Lsc.Stdlib Lsc.Security Vault

namespace Vault

/-- `Inv` (share accounting plus the vault's ERC-20 balance covering
`totalAssets`) is preserved by every vault call and by env steps that
do not steal the vault's token (`vaultRely`). A solvent start therefore
stays solvent: `Σ claim ≤ holdings`. Traces are well-formed for this
vault address (`ctx.self = self`). -/
theorem vault_solvent (self : Address) (tr : List (Step spec))
    (w : World Storage Ext Event)
    (hW : Wf self tr) (hR : RelyAlong (vaultRely self) tr w) (h : Inv self w) :
    Solvent claim holdings self (run tr w) :=
  Proof.vault_solvent self tr w hW hR h

/-- If `a` never authorised a vault call (`deposit`/`withdraw` as the
sender; views and pause/unpause never decrease `claim`), then `a`'s
redeemable assets do not fall. Env steps under `vaultRely` cannot debit
the vault's token. This is the spec-level statement bytecode glue
instantiates for Vault. -/
theorem vault_no_unauthorized_extraction (self : Address)
    (tr : List (Step spec)) (w : World Storage Ext Event) (a : Address)
    (hw : Inv self w) (hW : Wf self tr) (hR : RelyAlong (vaultRely self) tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  Proof.vault_no_unauthorized_extraction self tr w a hw hW hR hA

end Vault
