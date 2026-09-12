import Lsc.Lang.Word
import Lsc.Lang.Amount
import Lsc.Lang.Inline

/-!
# Named scales and `Fixed d` helpers

`WAD`, `RAY`, `USDC_SCALE`, `Q96`, and `E8` are ordinary words. Reify reduces
them with `closedNat?`; they are not Core primitives.

`Fixed.mulDown` / `mulUp` / `divDown` / `divUp` are `@[lsc_inline]` wrappers
over dimensional `Amount.mulDivDown` / `Up` with denominator `10^d`.
`Amount.rescale` re-expresses an amount at a different decimal count.
-/

namespace Stdlib

open Lsc

/-- 18 decimals (DAI, WETH, most ERC20s). -/
def WAD : Word := Word.scale 18
/-- 27 decimals (Aave/MakerDAO rates). -/
def RAY : Word := Word.scale 27
/-- 6 decimals (USDC, USDT). -/
def USDC_SCALE : Word := Word.scale 6
/-- Uniswap v3 Q64.96 fixed point. -/
def Q96 : Word := (2 ^ 96 : Nat)
/-- 8 decimals (WBTC, Chainlink USD feeds). -/
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

/-! ### `Fixed d` scaling -/

namespace Fixed

/-- `⌊a * x / 10^d⌋`. -/
@[lsc_inline]
def mulDown {d : Nat} (a x : Fixed d) : Tx S X E ε (Fixed d) :=
  Amount.mulDivDown a x (Amount.ofWord (Word.scale d))

/-- `⌈a * x / 10^d⌉`. -/
@[lsc_inline]
def mulUp {d : Nat} (a x : Fixed d) : Tx S X E ε (Fixed d) :=
  Amount.mulDivUp a x (Amount.ofWord (Word.scale d))

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
