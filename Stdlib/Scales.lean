import Lsc.Lang.Amount
import Lsc.Lang.Inline

/-!
# Named scales and derived `Amount` operations

`WAD`, `RAY`, `USDC_SCALE`, `Q96`, and `E8` are ordinary `Nat` constants. Reify
reduces them with `closedNat?`; they are not Core primitives.

`Amount.mulDown` / `mulUp` / `divDown` / `divUp` / `ratioDown` / `ratioUp` /
`rescale` / `convert` are `@[lsc_inline]` do-blocks over `Tx.mulDivDown` /
`mulDivUp`. `rescale` / `convert` still require a literal `.down` / `.up`.
Names stay `Lsc.Amount.*` so existing Reify matching and `open Lsc` continue to
work once this module is imported.
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
@[lsc_inline]
def mulDown (a : Amount τ s) (x : Fixed s) : Tx S X E ε (Amount τ s) := do
  let r ← Tx.mulDivDown a.toNat x.toNat s
  pure (Amount.ofNat r)
/-- `⌈a * x / s⌉`. -/
@[lsc_inline]
def mulUp (a : Amount τ s) (x : Fixed s) : Tx S X E ε (Amount τ s) := do
  let r ← Tx.mulDivUp a.toNat x.toNat s
  pure (Amount.ofNat r)
/-- `⌊a * s / x⌋`. -/
@[lsc_inline]
def divDown (a : Amount τ s) (x : Fixed s) : Tx S X E ε (Amount τ s) := do
  let r ← Tx.mulDivDown a.toNat s x.toNat
  pure (Amount.ofNat r)
/-- `⌈a * s / x⌉`. -/
@[lsc_inline]
def divUp (a : Amount τ s) (x : Fixed s) : Tx S X E ε (Amount τ s) := do
  let r ← Tx.mulDivUp a.toNat s x.toNat
  pure (Amount.ofNat r)

/-! ### Ratios of two same-unit amounts (dimensionless) -/

/-- `⌊a * s / b⌋ : Fixed s`. -/
@[lsc_inline]
def ratioDown (a b : Amount τ s) : Tx S X E ε (Fixed s) := do
  let r ← Tx.mulDivDown a.toNat s b.toNat
  pure (Amount.ofNat r)
/-- `⌈a * s / b⌉ : Fixed s`. -/
@[lsc_inline]
def ratioUp (a b : Amount τ s) : Tx S X E ε (Fixed s) := do
  let r ← Tx.mulDivUp a.toNat s b.toNat
  pure (Amount.ofNat r)

/-! ### Changing scale and unit -/

/-- Re-express an amount at another scale (`a * tgtScale / srcScale`), rounding as requested.
Both scales are runtime words. -/
@[lsc_inline]
def rescale (srcScale tgtScale : Nat) (r : Rounding) (a : Amount τ s) :
    Tx S X E ε (Amount τ s') :=
  match r with
  | .down => do
    let n ← Tx.mulDivDown a.toNat tgtScale srcScale
    pure (Amount.ofNat n)
  | .up => do
    let n ← Tx.mulDivUp a.toNat tgtScale srcScale
    pure (Amount.ofNat n)

/-- Convert `τ₁` into `τ₂` at price `p` (`a * p / s`). `s` is a runtime word. -/
@[lsc_inline]
def convert {τ₁ τ₂ : Type} (p : Price τ₁ τ₂ s) (scale : Nat) (r : Rounding)
    (a : Amount τ₁ s) : Tx S X E ε (Amount τ₂ s) :=
  match r with
  | .down => do
    let n ← Tx.mulDivDown a.toNat p.toNat scale
    pure (Amount.ofNat n)
  | .up => do
    let n ← Tx.mulDivUp a.toNat p.toNat scale
    pure (Amount.ofNat n)

/-! ### Run lemmas (do-notation over `Tx.mulDiv*`) -/

@[simp] theorem run_mulDown (a : Amount τ s) (x : Fixed s) (ctx : Ctx) (w : World S X E) :
    Tx.run (mulDown (S := S) (X := X) (E := E) (ε := ε) a x) ctx w =
      Tx.run ((fun n => ofNat n) <$>
        Tx.mulDivDown (S := S) (X := X) (E := E) (ε := ε) a.toNat x.toNat s) ctx w :=
  rfl

@[simp] theorem run_mulUp (a : Amount τ s) (x : Fixed s) (ctx : Ctx) (w : World S X E) :
    Tx.run (mulUp (S := S) (X := X) (E := E) (ε := ε) a x) ctx w =
      Tx.run ((fun n => ofNat n) <$>
        Tx.mulDivUp (S := S) (X := X) (E := E) (ε := ε) a.toNat x.toNat s) ctx w :=
  rfl

@[simp] theorem run_divDown (a : Amount τ s) (x : Fixed s) (ctx : Ctx) (w : World S X E) :
    Tx.run (divDown (S := S) (X := X) (E := E) (ε := ε) a x) ctx w =
      Tx.run ((fun n => ofNat n) <$>
        Tx.mulDivDown (S := S) (X := X) (E := E) (ε := ε) a.toNat s x.toNat) ctx w :=
  rfl

@[simp] theorem run_divUp (a : Amount τ s) (x : Fixed s) (ctx : Ctx) (w : World S X E) :
    Tx.run (divUp (S := S) (X := X) (E := E) (ε := ε) a x) ctx w =
      Tx.run ((fun n => ofNat n) <$>
        Tx.mulDivUp (S := S) (X := X) (E := E) (ε := ε) a.toNat s x.toNat) ctx w :=
  rfl

@[simp] theorem run_ratioDown (a b : Amount τ s) (ctx : Ctx) (w : World S X E) :
    Tx.run (ratioDown (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      Tx.run ((fun n => ofNat n) <$>
        Tx.mulDivDown (S := S) (X := X) (E := E) (ε := ε) a.toNat s b.toNat) ctx w :=
  rfl

@[simp] theorem run_ratioUp (a b : Amount τ s) (ctx : Ctx) (w : World S X E) :
    Tx.run (ratioUp (S := S) (X := X) (E := E) (ε := ε) a b) ctx w =
      Tx.run ((fun n => ofNat n) <$>
        Tx.mulDivUp (S := S) (X := X) (E := E) (ε := ε) a.toNat s b.toNat) ctx w :=
  rfl

@[simp] theorem run_rescale (srcScale tgtScale : Nat) (r : Rounding) (a : Amount τ s)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (rescale (s' := s') (S := S) (X := X) (E := E) (ε := ε) srcScale tgtScale r a) ctx w =
      match r with
      | .down =>
        Tx.run ((fun n => ofNat n) <$>
          Tx.mulDivDown (S := S) (X := X) (E := E) (ε := ε)
            a.toNat tgtScale srcScale) ctx w
      | .up =>
        Tx.run ((fun n => ofNat n) <$>
          Tx.mulDivUp (S := S) (X := X) (E := E) (ε := ε)
            a.toNat tgtScale srcScale) ctx w := by
  cases r <;> rfl

@[simp] theorem run_convert {τ₁ τ₂ : Type} (p : Price τ₁ τ₂ s) (scale : Nat) (r : Rounding)
    (a : Amount τ₁ s) (ctx : Ctx) (w : World S X E) :
    Tx.run (convert (S := S) (X := X) (E := E) (ε := ε) p scale r a) ctx w =
      match r with
      | .down =>
        Tx.run ((fun n => ofNat n) <$>
          Tx.mulDivDown (S := S) (X := X) (E := E) (ε := ε)
            a.toNat p.toNat scale) ctx w
      | .up =>
        Tx.run ((fun n => ofNat n) <$>
          Tx.mulDivUp (S := S) (X := X) (E := E) (ε := ε)
            a.toNat p.toNat scale) ctx w := by
  cases r <;> rfl

end Lsc.Amount
