import Lsc.Lang.Word
import Lsc.Lang.Amount
import Lsc.Lang.Inline

/-!
# Named scales and `Fixed d` helpers

`Wad` / `Ray` / `Bps` are `Fixed d` abbreviations; `WAD` / `RAY` / `BPS` are
the unit constants (`⟨10^d⟩`). `USDC_SCALE`, `Q96`, and `E8` remain ordinary
words. Reify reduces closed numerals with `closedNat?`; they are not Core
primitives.

`x *?↓ r` / `x *?↑ r` scale an amount by a `Fixed d`. `Fixed.divDown` /
`divUp` are `@[lsc_inline]` wrappers over dimensional `Amount.mulDivDown` /
`Up` with numerator `10^d`. `Amount.rescale` re-expresses an amount at a
different decimal count.
-/

namespace Stdlib

open Lsc

/-- 18-decimal fixed-point (DAI, WETH, most ERC20s). -/
abbrev Wad : Type := Fixed 18
/-- 27-decimal fixed-point (Aave/MakerDAO rates). -/
abbrev Ray : Type := Fixed 27
/-- 4-decimal fixed-point (basis points). -/
abbrev Bps : Type := Fixed 4

/-- One unit at 18 decimals. -/
def WAD : Wad := ⟨Word.scale 18⟩
/-- One unit at 27 decimals. -/
def RAY : Ray := ⟨Word.scale 27⟩
/-- One unit at 4 decimals (`10000`). -/
def BPS : Bps := ⟨Word.scale 4⟩

/-- 6 decimals (USDC, USDT), as a word. -/
def USDC_SCALE : Word := Word.scale 6
/-- Uniswap v3 Q64.96 fixed point. -/
def Q96 : Word := (2 ^ 96 : Nat)
/-- 8 decimals (WBTC, Chainlink USD feeds), as a word. -/
def E8 : Word := Word.scale 8

end Stdlib

namespace Lsc

variable {S X E ε : Type} {a : Asset}

namespace Amount

/-- Re-express `x` from `srcDec` decimals to `tgtDec` decimals. `r` must be a
literal so Reify can pick `mulDivDown` vs `mulDivUp`. -/
@[lsc_inline]
def rescale (srcDec tgtDec : Word) (r : Rounding) (x : Amount a) :
    Tx S X E ε (Fixed tgtDec) :=
  ofWord <$> Tx.rescale srcDec tgtDec r x.raw

end Amount

/-! ### `Fixed d` inverse scaling -/

namespace Fixed

/-- `⌊a * 10^d / x⌋`. -/
@[lsc_inline]
def divDown {d : Nat} (a x : Fixed d) : Tx S X E ε (Fixed d) :=
  Amount.mulDivDown a (Amount.ofWord (Word.scale d)) x

/-- `⌈a * 10^d / x⌉`. -/
@[lsc_inline]
def divUp {d : Nat} (a x : Fixed d) : Tx S X E ε (Fixed d) :=
  Amount.mulDivUp a (Amount.ofWord (Word.scale d)) x

end Fixed

end Lsc
