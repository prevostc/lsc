import Lsc.Lib.Wad.Syntax
import Lsc.Core.ContractM
import Lsc.Lang.AST

namespace Lsc.Wad

def addChecked (a b : Wad) : Except ArithError Wad :=
  (UInt256.addChecked a.raw b.raw).map Wad.mk

def subChecked (a b : Wad) : Except ArithError Wad :=
  (UInt256.subChecked a.raw b.raw).map Wad.mk

def addCheckedNat (a : Wad) (n : Nat) : Except ArithError Wad :=
  (UInt256.addCheckedNat a.raw n).map Wad.mk

/-- Multiply two `Wad`s with half-up rounding, checked for overflow.

`a.raw * b.raw` is a 36-decimal-place fixed-point product (each operand
already carries 18 decimals of scale); dividing by `WAD` brings the result
back down to 18 decimals. Adding `WAD / 2` before dividing rounds to nearest
(half-up), matching the `wadMulHalfUp` naming used throughout
`docs/extensions/MATH.md`. Surface syntax once wired into `Tx` bodies:
`a ⸢*⸣? b` (per `docs/reference/AMM.md`). -/
def mulHalfUpChecked (a b : Wad) : Except ArithError Wad :=
  let productNat := a.raw.toNat * b.raw.toNat
  let resultNat := (productNat + WAD / 2) / WAD
  if resultNat > (BitVec.allOnes 256).toNat then
    .error .Overflow
  else
    .ok (mkNat resultNat)

/-- Divide two `Wad`s, rounding the quotient down, checked for division by
zero and overflow.

`a.raw` is scaled up by `WAD` before dividing so the quotient keeps 18
decimal places of precision instead of collapsing to an integer. Surface
syntax once wired into `Tx` bodies: `a ⌊/⌋? b` (per `docs/reference/AMM.md`). -/
def divDownChecked (a b : Wad) : Except ArithError Wad :=
  if b.raw == 0 then
    .error .DivisionByZero
  else
    let numerNat := a.raw.toNat * WAD
    let resultNat := numerNat / b.raw.toNat
    if resultNat > (BitVec.allOnes 256).toNat then
      .error .Overflow
    else
      .ok (mkNat resultNat)

/-- `w.canAddNat n` holds iff adding `n` to `w` will not overflow 256 bits. -/
abbrev Wad.canAddNat (w : Wad) (n : Nat) : Prop := w.raw.toNat + n < 2 ^ 256

@[simp]
theorem addCheckedNat_ok (a : Wad) (n : Nat) (h : a.canAddNat n) :
    addCheckedNat a n = .ok ⟨BitVec.ofNat 256 (a.raw.toNat + n)⟩ := by
  simp [addCheckedNat, UInt256.addCheckedNat, h, Except.map]

@[simp]
theorem addCheckedNat_error (a : Wad) (n : Nat) (h : ¬ a.canAddNat n) :
    addCheckedNat a n = .error .Overflow := by
  simp [addCheckedNat, UInt256.addCheckedNat, h, Except.map]

variable {S E Err : Type} [ContractErrors Err] [dsl : ContractDSL S E Err]

/-- `ContractM`-based evaluator for `Wad.Expr`, mirroring `Wei.eval` exactly. -/
def eval
    (e : Expr) (env : LocalEnv) : ContractM S E Err Wad :=
  match e with
  | .lit n => pure (Wad.mkNat n)
  | .var name =>
    match env.lookup name with
    | some ⟨Ty.wad, v⟩ => pure (Val.wadOf v)
    | _ => ContractM.revert .Unauthorized
  | .storageGet field => do
    let st ← ContractM.get
    match dsl.getField Ty.wad field st.storage with
    | some (.wad w) => pure w
    | _ => ContractM.revert .Unauthorized
  | .addChecked a b => do
    let va ← eval a env
    let vb ← eval b env
    match Wad.addChecked va vb with
    | .error ae => ContractM.revertArith ae
    | .ok r => pure r
  | .addCheckedNat a n => do
    let va ← eval a env
    match Wad.addCheckedNat va n with
    | .error ae => ContractM.revertArith ae
    | .ok r => pure r
  | .subChecked a b => do
    let va ← eval a env
    let vb ← eval b env
    match Wad.subChecked va vb with
    | .error ae => ContractM.revertArith ae
    | .ok r => pure r
  | .mulHalfUpChecked a b => do
    let va ← eval a env
    let vb ← eval b env
    match Wad.mulHalfUpChecked va vb with
    | .error ae => ContractM.revertArith ae
    | .ok r => pure r
  | .divDownChecked a b => do
    let va ← eval a env
    let vb ← eval b env
    match Wad.divDownChecked va vb with
    | .error ae => ContractM.revertArith ae
    | .ok r => pure r

attribute [simp] eval

end Lsc.Wad
