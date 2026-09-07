import Examples.Vault.Security
import Examples.Vault.SecurityProof

/-!
Vault at the spec: Alice's redeemable assets cannot fall unless she
withdrew, and the vault never owes more than its token balance.

Authorisation is only Alice's own `withdraw`. Any address may deposit,
withdraw their own shares, pause, or unpause. The asset token is assumed
to be a conforming ERC-20: between our calls the vault's token balance
does not fall.

Traces must target this vault with a distinct sender. Starting share
accounting must already be consistent and covered by the token balance.
-/

open Lsc Lsc.Stdlib Lsc.Security Vault

namespace Vault

/-- After any well-formed sequence of Vault calls, the sum of depositors'
redeemable assets still does not exceed the vault's token balance: the
vault never owes more than it holds. The starting world must already be
solvent in that sense, and between calls the asset token must not take
the vault's balance (donations are allowed). Floor rounding can leak dust
per step; solvency, not per-step conservation, is the statement. -/
theorem vault_solvent (self : Address) (tr : List (Step spec))
    (w : World Storage Ext Event)
    (hW : Wf self tr) (hR : RelyAlong (vaultRely self) tr w) (h : Inv self w) :
    Solvent claim holdings self (run tr w) :=
  Proof.vault_solvent self tr w hW hR h

/-- No sequence of calls by other users can reduce Alice's redeemable share
of the vault's assets without a transaction she signed: the only
authorised reduction is her own `withdraw`. Other depositors, the owner
pausing or unpausing, and views cannot debit her; she may lose redeemable
value only through her own withdrawals. Between calls the asset token must
not take the vault's balance. Assumed, not proved: the token behaves like
a conforming ERC-20 (no fee-on-transfer, no down-rebase, no reentrancy).
This is not liveness — pause can block withdrawal without reducing the
recorded claim. -/
theorem vault_no_unauthorized_extraction (self : Address)
    (tr : List (Step spec)) (w : World Storage Ext Event) (a : Address)
    (hw : Inv self w) (hW : Wf self tr) (hR : RelyAlong (vaultRely self) tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  Proof.vault_no_unauthorized_extraction self tr w a hw hW hR hA

end Vault
