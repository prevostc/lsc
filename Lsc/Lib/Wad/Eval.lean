import Lsc.Lib.Wad.Syntax
import Lsc.Core.ContractM
import Lsc.Lang.AST

namespace Lsc.Wad

def addChecked (a b : Wad) : Except ArithError Wad :=
  (UInt256.addChecked a.raw b.raw).map Fixed.mk

def subChecked (a b : Wad) : Except ArithError Wad :=
  (UInt256.subChecked a.raw b.raw).map Fixed.mk

def addCheckedNat (a : Wad) (n : Nat) : Except ArithError Wad :=
  (UInt256.addCheckedNat a.raw n).map Fixed.mk

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
theorem addCheckedNat_ok (a : Wad) (n : Nat) (h : Wad.canAddNat a n) :
    addCheckedNat a n = .ok ⟨BitVec.ofNat 256 (a.raw.toNat + n)⟩ := by
  unfold Wad.canAddNat at h
  simp [addCheckedNat, UInt256.addCheckedNat_ok a.raw n h, Except.map]

@[simp]
theorem addCheckedNat_error (a : Wad) (n : Nat) (h : ¬ Wad.canAddNat a n) :
    addCheckedNat a n = .error .Overflow := by
  unfold Wad.canAddNat at h
  simp [addCheckedNat, UInt256.addCheckedNat_error a.raw n h, Except.map]

/-- `a.raw.toNat + b.raw.toNat < 2 ^ 256` — the two-`Wad` analogue of `canAddNat`, needed for
`addChecked`'s ok/error characterization lemmas below (two real `Wad` operands, not a bare
`Nat`). -/
abbrev canAdd (a b : Wad) : Prop := a.raw.toNat + b.raw.toNat < 2 ^ 256

/-- `Wad.addChecked` in the no-overflow case, stated as a pure-`Nat` sum equality rather than a
raw `BitVec`/`Except` computation, so `rw`/`apply` can use it as a single deterministic rewrite
step. See the module docstring below ("chained checked ops") for why this — used via `rw`, not
handed to `simp` as one more lemma among many — matters for tx bodies that chain more than one
checked arithmetic op. -/
theorem addChecked_eq_ok_of (a b : Wad) (n : Nat)
    (hn : a.raw.toNat + b.raw.toNat = n) (hbound : n < 2 ^ 256) :
    addChecked a b = .ok (mkNat n) := by
  have hlt : a.raw.toNat + b.raw.toNat < 2 ^ 256 := hn ▸ hbound
  have htoNat : (a.raw + b.raw).toNat = a.raw.toNat + b.raw.toNat :=
    BitVec.toNat_add_of_lt hlt
  have heq : a.raw + b.raw = BitVec.ofNat 256 n := by
    apply BitVec.eq_of_toNat_eq
    rw [htoNat, hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound]
  have hnolt : ¬ a.raw + b.raw < a.raw := by
    rw [BitVec.lt_def, htoNat]; omega
  simp only [addChecked, UInt256.addChecked, heq]
  rw [if_neg (heq ▸ hnolt)]
  simp [Except.map, mkNat]

/-- `Wad.addChecked` in the overflow case — the error-case counterpart of
`addChecked_eq_ok_of` above. -/
theorem addChecked_eq_error_of (a b : Wad) (h : a.raw.toNat + b.raw.toNat ≥ 2 ^ 256) :
    addChecked a b = .error .Overflow := by
  have hb : b.raw.toNat < 2 ^ 256 := b.raw.isLt
  have htoNat : (a.raw + b.raw).toNat = (a.raw.toNat + b.raw.toNat) % 2 ^ 256 :=
    BitVec.toNat_add a.raw b.raw
  have hlt : (a.raw + b.raw).toNat < a.raw.toNat := by
    rw [htoNat, Nat.mod_eq_sub_mod h]
    have hlt2 : a.raw.toNat + b.raw.toNat - 2 ^ 256 < 2 ^ 256 := by omega
    rw [Nat.mod_eq_of_lt hlt2]
    omega
  have hlt' : a.raw + b.raw < a.raw := by rw [BitVec.lt_def]; exact hlt
  simp only [addChecked, UInt256.addChecked]
  rw [if_pos hlt']
  rfl

/-- `b.raw.toNat ≤ a.raw.toNat` — the subtraction-side analogue of `canAdd`, needed for
`subChecked`'s ok/error characterization lemmas below (`a -? b` doesn't underflow iff `a ≥ b`). -/
abbrev canSub (a b : Wad) : Prop := b.raw.toNat ≤ a.raw.toNat

/-- `Wad.subChecked` in the no-underflow case, stated as a pure-`Nat` difference equality —
same `rw`-not-`simp` rationale as `addChecked_eq_ok_of` above. -/
theorem subChecked_eq_ok_of (a b : Wad) (n : Nat) (hn : a.raw.toNat = b.raw.toNat + n) :
    subChecked a b = .ok (mkNat n) := by
  have hbound : n < 2 ^ 256 := by have := a.raw.isLt; omega
  have hle : b.raw ≤ a.raw := by rw [BitVec.le_def]; omega
  have hnolt : ¬ a.raw < b.raw := by rw [BitVec.lt_def]; omega
  have htoNat : (a.raw - b.raw).toNat = n := by
    rw [BitVec.toNat_sub_of_le hle]; omega
  have heq : a.raw - b.raw = BitVec.ofNat 256 n := by
    apply BitVec.eq_of_toNat_eq
    rw [htoNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound]
  simp only [subChecked, UInt256.subChecked, heq]
  rw [if_neg hnolt]
  simp [Except.map, mkNat]

/-- `Wad.subChecked` in the underflow case — the error-case counterpart of
`subChecked_eq_ok_of` above. -/
theorem subChecked_eq_error_of (a b : Wad) (h : a.raw.toNat < b.raw.toNat) :
    subChecked a b = .error .Underflow := by
  have hlt : a.raw < b.raw := by rw [BitVec.lt_def]; exact h
  simp only [subChecked, UInt256.subChecked]
  rw [if_pos hlt]
  rfl

/-- `Wad.mulHalfUpChecked` in the no-overflow case, as a pure-`Nat` equality — same rationale
and same `rw`-not-`simp` usage pattern as `addChecked_eq_ok_of` above. -/
theorem mulHalfUpChecked_eq_ok_of (a b : Wad) (n : Nat)
    (hn : (a.raw.toNat * b.raw.toNat + WAD / 2) / WAD = n) (hbound : n < 2 ^ 256) :
    mulHalfUpChecked a b = .ok (mkNat n) := by
  simp only [mulHalfUpChecked, hn]
  rw [if_neg]
  simp only [BitVec.toNat_allOnes]
  omega

/-- `Wad.mulHalfUpChecked` in the overflow case — the error-case counterpart of
`mulHalfUpChecked_eq_ok_of` above. -/
theorem mulHalfUpChecked_eq_error_of (a b : Wad)
    (h : (a.raw.toNat * b.raw.toNat + WAD / 2) / WAD > (BitVec.allOnes 256).toNat) :
    mulHalfUpChecked a b = .error .Overflow := by
  simp only [mulHalfUpChecked]
  rw [if_pos h]

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
  | .mapGet field key => do
    let addr ← match key with
      | .caller => ContractM.caller
      | .var name =>
        match env.lookup name with
        | some ⟨Ty.address, .addr a⟩ => pure a
        | _ => ContractM.revert .Unauthorized
    let st ← ContractM.get
    match dsl.getMapField field addr st.storage with
    | some w => pure w
    | none => ContractM.revert .Unauthorized
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
