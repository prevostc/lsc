import Examples.Vault.Spec
import Examples.Vault.Proofs.Tx
import Examples.Vault.Proofs.Security
import Stdlib.ERC20

/-!
Vault theorems: Tx-level share and holdings deltas, spec-level anti-extraction
and solvency. Assumed of the token: it is a conforming ERC-20 per
`IERC20.Spec`; no reentrancy is modelled.
-/

open Lsc Lsc.Stdlib Lsc.Security Vault

namespace Vault

variable (ctx : Ctx) (w : World Storage ExtState Event)

/-- A successful `deposit` credits the caller with the minted shares and
raises `totalShares` by that amount. Success already implies the pause,
positivity, rounding, and overflow checks. -/
theorem deposit_shares (assets : Amount vaultAsset)
    {minted : Amount vShare} {w' : World Storage ExtState Event}
    (h : Tx.run (deposit assets) ctx w = .ok (minted, w')) :
    w'.self.shares ctx.sender = w.self.shares ctx.sender + minted ∧
      w'.self.totalShares = w.self.totalShares + minted :=
  Proof.deposit_shares h

/-- A successful `deposit` raises the vault's live token balance by `assets`,
when the caller is not the vault. Assumed of the token: it is a conforming
ERC-20 per `IERC20.Spec`; no reentrancy is modelled. Self-deposit is excluded
because a conforming self-`transferFrom` is a no-op on the vault's balance, so
the holdings delta is genuinely false there. -/
theorem deposit_holdings (assets : Amount vaultAsset)
    {minted : Amount vShare} {w' : World Storage ExtState Event}
    (hT : IERC20.Spec (w.self.asset.impl w))
    (hne : ctx.sender ≠ ctx.self)
    (h : Tx.run (deposit assets) ctx w = .ok (minted, w')) :
    holdings ctx.self w' = holdings ctx.self w + assets.raw :=
  Proof.deposit_holdings hT hne h

/-- A successful `withdraw` burns `sharesIn` from the caller and lowers
`totalShares` by the burned shares. -/
theorem withdraw_shares (sharesIn : Amount vShare)
    {paid : Amount vaultAsset} {w' : World Storage ExtState Event}
    (h : Tx.run (withdraw sharesIn) ctx w = .ok (paid, w')) :
    w'.self.shares ctx.sender = w.self.shares ctx.sender - sharesIn ∧
      w'.self.totalShares = w.self.totalShares - sharesIn :=
  Proof.withdraw_shares h

/-- A successful `withdraw` lowers the vault's live token balance by the
assets paid, when the caller is not the vault. Assumed of the token: it is a
conforming ERC-20 per `IERC20.Spec`; no reentrancy is modelled. Self-withdraw
is excluded because a conforming self-`transfer` is a no-op on the vault's
balance, so the holdings delta is genuinely false there. -/
theorem withdraw_holdings (sharesIn : Amount vShare)
    {paid : Amount vaultAsset} {w' : World Storage ExtState Event}
    (hT : IERC20.Spec (w.self.asset.impl w))
    (hne : ctx.sender ≠ ctx.self)
    (h : Tx.run (withdraw sharesIn) ctx w = .ok (paid, w')) :
    holdings ctx.self w' + paid.raw = holdings ctx.self w :=
  Proof.withdraw_holdings hT hne h

/-- After any well-formed sequence of Vault calls, the sum of depositors'
redeemable assets still does not exceed the vault's token balance: the
vault never owes more than it holds. The starting world must already be
solvent in that sense, and between calls the asset token must not take
the vault's balance (donations are allowed). Floor rounding can leak dust
per step; solvency, not per-step conservation, is the statement. Assumed of
the token: it is a conforming ERC-20 per `IERC20.Spec`; no reentrancy is
modelled. -/
theorem vault_solvent (self : Address) (tr : List (Step spec))
    (w : World Storage ExtState Event)
    (hW : Wf self tr)
    (hR : RelyAlong (vaultRely self w.self.asset w.oracle) tr w)
    (hT : IERC20.Spec (w.self.asset.impl w))
    (h : Inv w) :
    Solvent (claim self) holdings self (run tr w) :=
  Proof.vault_solvent self tr w hW hR hT h

/-- No sequence of calls by other users can reduce Alice's redeemable share
of the vault's live assets without a transaction she signed: the only
authorised reduction is her own `withdraw`. Other depositors, the owner
pausing or unpausing, and views cannot debit her; she may lose redeemable
value only through her own withdrawals. Between calls the asset token must
not take the vault's balance. Assumed of the token: it is a conforming
ERC-20 per `IERC20.Spec`; no reentrancy is modelled. This is not liveness —
pause can block withdrawal without reducing the recorded claim. -/
theorem vault_no_unauthorized_extraction (self : Address)
    (tr : List (Step spec)) (w : World Storage ExtState Event) (a : Address)
    (hw : Inv w) (hW : Wf self tr)
    (hR : RelyAlong (vaultRely self w.self.asset w.oracle) tr w)
    (hT : IERC20.Spec (w.self.asset.impl w))
    (hA : NoAuthAlong Auth a tr w) :
    claim self a w ≤ claim self a (run tr w) :=
  Proof.vault_no_unauthorized_extraction self tr w a hw hW hR hT hA

end Vault
