import Examples.Vault.Spec
import Examples.Vault.Proofs.Tx
import Examples.Vault.Proofs.Security
import Stdlib.ERC20
import Stdlib.Shares

/-!
Vault theorems: Tx-level share and holdings deltas, spec-level anti-extraction
and solvency. The honest-counterparty assumption (`IERC20.Spec` of the bound
asset) lives in `State` / `HasDeploy` / `HasRely`. Per-call theorems that
mention the token are over `State` with `msg : Msg w`; share-only deltas stay
over `World` with `msg : Ctx`.
-/

open Lsc Lsc.Stdlib Lsc.Security Vault

namespace Vault

variable (msg : Ctx) (w : World)

/-- A successful `deposit` credits the caller with the minted shares and
raises `totalShares` by that amount. Success already implies the pause,
positivity, rounding, and overflow checks. -/
theorem deposit_shares (assets : Amount vaultAsset)
    {minted : Amount vShare} {w' : World}
    (h : Tx.run (deposit assets) msg w = .ok (minted, w')) :
    w'.self.shares msg.sender = w.self.shares msg.sender + minted ∧
      w'.self.totalShares = w.self.totalShares + minted :=
  Proof.deposit_shares h

/-- A successful `withdraw` burns `sharesIn` from the caller and lowers
`totalShares` by the burned shares. -/
theorem withdraw_shares (sharesIn : Amount vShare)
    {paid : Amount vaultAsset} {w' : World}
    (h : Tx.run (withdraw sharesIn) msg w = .ok (paid, w')) :
    w'.self.shares msg.sender = w.self.shares msg.sender - sharesIn ∧
      w'.self.totalShares = w.self.totalShares - sharesIn :=
  Proof.withdraw_shares h

/-- After a successful `deposit` of `x` assets against live holdings `A` and
share supply `S`, redeeming the minted shares recovers all but at most
`(A + 10^offset) / 10^offset` wei: an inflation donation of size `A` costs
on the order of `10^offset` wei per wei the depositor cannot redeem.
The bound is a Nat product of the virtual offset and the unredeemable dust. -/
theorem deposit_inflation_bounded (assets : Amount vaultAsset)
    {minted : Amount vShare} {w' : World}
    (h : Tx.run (deposit assets) msg w = .ok (minted, w')) :
    let V := Shares.virtualShares (s := vShare) offset
    let A := holdingsAt msg.self w
    let S := w.self.totalShares
    let r := Shares.toAssetsRaw offset minted.raw (A.raw + assets.raw)
      (S.raw + minted.raw)
    V.raw * (assets.raw - r) ≤ A.raw + V.raw :=
  Proof.deposit_inflation_bounded (ctx := msg) (w := w) h

end Vault

namespace Vault

/-- A successful `deposit` raises the vault's holdings of its asset by exactly
`assets`. -/
theorem deposit_holdings (w : State) (msg : Msg w) (assets : Amount vaultAsset)
    {minted : Amount vShare} {w' : World}
    (h : Tx.run (deposit assets) msg w = .ok (minted, w')) :
    holdingsAt w.addr w' = w.holdings + assets :=
  Proof.deposit_holdings w msg assets h

/-- A successful `withdraw` lowers the vault's holdings by exactly what it
paid out. -/
theorem withdraw_holdings (w : State) (msg : Msg w) (sharesIn : Amount vShare)
    {paid : Amount vaultAsset} {w' : World}
    (h : Tx.run (withdraw sharesIn) msg w = .ok (paid, w')) :
    holdingsAt w.addr w' + paid = w.holdings :=
  Proof.withdraw_holdings w msg sharesIn h

/-- The vault can always pay out every share: what all shareholders are owed
never exceeds the assets it holds. -/
theorem vault_solvent (w : State) : w.owed ≤ w.holdings :=
  Proof.vault_solvent w

/-- Between any two moments, a shareholder's shares drop by at most what they
themselves redeemed. -/
theorem vault_no_unauthorized_extraction (w : State) (t : Txs w) (a : Address) :
    w.self.shares a ≤ t.end.self.shares a + t.spent a :=
  Proof.vault_no_unauthorized_extraction w t a

end Vault
