import Lsc.Lang.Amount

/-!
# Named scales and derived `Amount` operations

`WAD`, `RAY`, `USDC_SCALE`, `Q96`, and `E8` are ordinary `Nat` constants. Reify
reduces them with `closedNat?`; they are not Core primitives.

`Amount.mulDown` / `mulUp` / `divDown` / `divUp` / `ratioDown` / `ratioUp` /
`rescale` / `convert` unfold to `Tx.mulDivDown` / `mulDivUp` (Reify's
`isSurfaceOp`). They are not used by `Core.denoteA`. Names stay `Lsc.Amount.*`
so existing Reify matching and `open Lsc` continue to work once this module is
imported.
-/

namespace Stdlib

/-- 18 decimals (DAI, WETH, most ERC20s). -/
def WAD : Nat := 10 ^ 18
/-- 27 decimals (Aave/MakerDAO rates). -/
def RAY : Nat := 10 ^ 27
/-- 6 decimals (USDC, USDT). -/
def USDC_SCALE : Nat := 10 ^ 6
/-- Uniswap v3 Q64.96 fixed point. -/
def Q96 : Nat := 2 ^ 96
/-- 8 decimals (WBTC, Chainlink USD feeds). -/
def E8 : Nat := 10 ^ 8

end Stdlib

namespace Lsc.Amount

open Lsc

variable {τ τ' : Type} {s s' : Nat}
variable {S X E ε : Type}

/-! ### Scaling by a dimensionless factor (`Amount τ s * Fixed s → Amount τ s`) -/

/-- `⌊a * x / s⌋`. `s` is passed as a runtime word. -/
def mulDown (a : Amount τ s) (x : Fixed s) : Tx S X E ε (Amount τ s) :=
  (fun n => ofNat n) <$> Tx.mulDivDown a.toNat x.toNat s
/-- `⌈a * x / s⌉`. -/
def mulUp (a : Amount τ s) (x : Fixed s) : Tx S X E ε (Amount τ s) :=
  (fun n => ofNat n) <$> Tx.mulDivUp a.toNat x.toNat s
/-- `⌊a * s / x⌋`. -/
def divDown (a : Amount τ s) (x : Fixed s) : Tx S X E ε (Amount τ s) :=
  (fun n => ofNat n) <$> Tx.mulDivDown a.toNat s x.toNat
/-- `⌈a * s / x⌉`. -/
def divUp (a : Amount τ s) (x : Fixed s) : Tx S X E ε (Amount τ s) :=
  (fun n => ofNat n) <$> Tx.mulDivUp a.toNat s x.toNat

/-! ### Ratios of two same-unit amounts (dimensionless) -/

/-- `⌊a * s / b⌋ : Fixed s`. -/
def ratioDown (a b : Amount τ s) : Tx S X E ε (Fixed s) :=
  (fun n => ofNat n) <$> Tx.mulDivDown a.toNat s b.toNat
/-- `⌈a * s / b⌉ : Fixed s`. -/
def ratioUp (a b : Amount τ s) : Tx S X E ε (Fixed s) :=
  (fun n => ofNat n) <$> Tx.mulDivUp a.toNat s b.toNat

/-! ### Changing scale and unit -/

/-- Re-express an amount at another scale (`a * tgtScale / srcScale`), rounding as requested.
Both scales are runtime words. -/
def rescale (srcScale tgtScale : Nat) (r : Rounding) (a : Amount τ s) :
    Tx S X E ε (Amount τ s') :=
  match r with
  | .down => (fun n => ofNat n) <$> Tx.mulDivDown a.toNat tgtScale srcScale
  | .up => (fun n => ofNat n) <$> Tx.mulDivUp a.toNat tgtScale srcScale

/-- Convert `τ₁` into `τ₂` at price `p` (`a * p / s`). `s` is a runtime word. -/
def convert {τ₁ τ₂ : Type} (p : Price τ₁ τ₂ s) (scale : Nat) (r : Rounding)
    (a : Amount τ₁ s) : Tx S X E ε (Amount τ₂ s) :=
  match r with
  | .down => (fun n => ofNat n) <$> Tx.mulDivDown a.toNat p.toNat scale
  | .up => (fun n => ofNat n) <$> Tx.mulDivUp a.toNat p.toNat scale

end Lsc.Amount
