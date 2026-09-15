import Lsc.Lang.Amount
import Lsc.Lang.Inline
import Lsc.Lang.Word

/-!
# Virtual-offset share conversion (ERC-4626)

OpenZeppelin-style mitigation of first-depositor / donation share inflation:
`10^offset` virtual shares and 1 virtual asset are always present, so an
inflation attack costs the attacker on the order of `10^offset` wei per wei
stolen from the victim.

`toShares` / `toAssets` round down (against the user on deposit and redeem).
-/

open Lsc

namespace Lsc.Stdlib
namespace Shares

/-- Virtual-offset share math: `10^offset` virtual shares and 1 virtual asset
are always present, so an inflation attack costs the attacker at least
`10^offset` × the victim's loss (up to one extra virtual-asset wei). -/
structure Offset where
  decimals : Nat
  deriving Repr, DecidableEq

/-- Compiled virtual-share count: `10^6`. Examples use `offset := ⟨6⟩`; the
`*Raw` specs stay generic in `o.decimals`. -/
def virtual6 : Word := 1000000

/-- `10^o.decimals` as a word. The `6` branch is a numeral so reification
certificates close by `rfl` without unfolding `Nat.pow`. -/
def Offset.virtual (o : Offset) : Word :=
  match o.decimals with
  | 6 => 1000000
  | d => Word.scale d

/-- `10^o.decimals` virtual shares. Folds to a literal when `o` is a closed
numeral (`⟨6⟩` → `1000000`). -/
def virtualShares {s : Asset} (o : Offset) : Amount s :=
  ⟨o.virtual⟩

/-- Floor conversion used by `toShares`. -/
def toSharesRaw (o : Offset) (assets totalAssets totalShares : Nat) : Nat :=
  assets * (totalShares + Word.scale o.decimals) / (totalAssets + 1)

/-- Floor conversion used by `toAssets`. -/
def toAssetsRaw (o : Offset) (shares totalAssets totalShares : Nat) : Nat :=
  shares * (totalAssets + 1) / (totalShares + Word.scale o.decimals)

variable {S X E ε : Type} {a s : Asset}

/-- Shares minted for `assets` against live `totalAssets` / `totalShares`.
`⌊(totalShares + 10^offset) · assets / (totalAssets + 1)⌋`. -/
@[lsc_inline]
def toShares (o : Offset) (assets totalAssets : Amount a)
    (totalShares : Amount s) : Tx S X E ε (Amount s) := do
  let ts' ← Amount.add totalShares (virtualShares o)
  let ta' ← Amount.add totalAssets (1 : Amount a)
  Amount.mulDivDown ts' assets ta'

/-- Assets paid for `shares` against live `totalAssets` / `totalShares`.
`⌊(totalAssets + 1) · shares / (totalShares + 10^offset)⌋`. -/
@[lsc_inline]
def toAssets (o : Offset) (shares : Amount s) (totalAssets : Amount a)
    (totalShares : Amount s) : Tx S X E ε (Amount a) := do
  let ta' ← Amount.add totalAssets (1 : Amount a)
  let ts' ← Amount.add totalShares (virtualShares o)
  Amount.mulDivDown ta' shares ts'

@[simp] theorem virtual6_eq : virtual6 = 1000000 := rfl

@[simp] theorem virtual6_scale : virtual6 = Word.scale 6 := rfl

@[simp] theorem virtual_eq_scale (o : Offset) :
    o.virtual = Word.scale o.decimals := by
  dsimp [Offset.virtual]
  split
  · next h => rw [h]; rfl
  · rfl

@[simp] theorem virtualShares_raw {s : Asset} (o : Offset) :
    (virtualShares (s := s) o).raw = Word.scale o.decimals := by
  simp [virtualShares]

@[simp] theorem toSharesRaw_eq (o : Offset)
    (assets totalAssets totalShares : Nat) :
    toSharesRaw o assets totalAssets totalShares =
      assets * (totalShares + Word.scale o.decimals) / (totalAssets + 1) :=
  rfl

@[simp] theorem toAssetsRaw_eq (o : Offset)
    (shares totalAssets totalShares : Nat) :
    toAssetsRaw o shares totalAssets totalShares =
      shares * (totalAssets + 1) / (totalShares + Word.scale o.decimals) :=
  rfl

end Shares
end Lsc.Stdlib
