import Mathlib.Data.Nat.Sqrt
import Lsc.Lib.Math.SqrtAlgo

/-!
# OpenZeppelin-style integer square root (reference for proofs + codegen)

Pure Lean port of [`Math.sqrt`](https://github.com/OpenZeppelin/openzeppelin-contracts/blob/master/contracts/utils/math/Math.sol):
MSB initial estimate, six Newton steps, floor correction. -/

namespace Lsc.Math.SqrtRef

/-- Canonical executable implementation shared with primitive IR lowering. -/
abbrev sqrtEvm : Nat → Nat := Lsc.Math.SqrtAlgo.sqrtNat

/-- One Newton step: `(xn + a / xn) >> 1`. -/
def sqrtStep (a xn : Nat) : Nat := (xn + a / xn) / 2

/-- MSB scaling thresholds (OZ `Math.sqrt`). Returns `(aa, xn)` after magnitude estimate. -/
def sqrtInit (a : Nat) : Nat × Nat :=
  let rec go (aa xn : Nat) : Nat × Nat :=
    if aa >= 2 ^ 128 then go (aa / 2 ^ 128) (xn * 2 ^ 64)
    else if aa >= 2 ^ 64 then go (aa / 2 ^ 64) (xn * 2 ^ 32)
    else if aa >= 2 ^ 32 then go (aa / 2 ^ 32) (xn * 2 ^ 16)
    else if aa >= 2 ^ 16 then go (aa / 2 ^ 16) (xn * 2 ^ 8)
    else if aa >= 2 ^ 8 then go (aa / 2 ^ 8) (xn * 2 ^ 4)
    else if aa >= 2 ^ 4 then go (aa / 2 ^ 4) (xn * 2 ^ 2)
    else if aa >= 2 ^ 2 then (aa, xn * 2)
    else (aa, xn)
  go a 1

/-- After MSB init and `(3 * xn) >> 1` refinement. -/
def sqrtInitRefined (a : Nat) : Nat :=
  let (_, xn0) := sqrtInit a
  (3 * xn0) / 2

/-- Newton iteration until convergence (same step as `Nat.sqrt.iter`). -/
partial def ozNewtonIter (a xn : Nat) : Nat :=
  let next := sqrtStep a xn
  if next < xn then ozNewtonIter a next else xn

/-- Six Newton iterations, before floor correction (EVM bytecode path). -/
def sqrtPreFix (a : Nat) : Nat :=
  let x0 := sqrtInitRefined a
  sqrtStep a (sqrtStep a (sqrtStep a (sqrtStep a (sqrtStep a (sqrtStep a x0)))))

/-- Floor correction: `xn - (xn > a / xn ? 1 : 0)`. -/
def sqrtFloorFix (a xn : Nat) : Nat :=
  if xn > a / xn then xn - 1 else xn

/-- Apply OZ floor correction to a Newton estimate. -/
def ozSqrtFrom (a estimate : Nat) : Nat :=
  if a ≤ 1 then a else sqrtFloorFix a estimate

/-- OZ `Math.sqrt` with convergence — proved `= Nat.sqrt` in [`Lsc.Math.Proofs`]. -/
def ozSqrtFull (a : Nat) : Nat :=
  ozSqrtFrom a (if a ≤ 1 then a else ozNewtonIter a (sqrtInitRefined a))

/-- EVM-aligned six-step OZ sqrt (exact on `n ≤ 2^256 - 1`). -/
def ozSqrtEvm (a : Nat) : Nat :=
  ozSqrtFrom a (if a ≤ 1 then a else sqrtPreFix a)

/-- Proved OZ reference (`= Nat.sqrt`); use `ozSqrtEvm` for bytecode. -/
abbrev ozSqrt (a : Nat) : Nat := ozSqrtEvm a

/-- Largest EVM word; six Newton steps suffice here (OZ `e ≤ 128`). -/
def evmMaxWord : Nat := 2 ^ 256 - 1

end Lsc.Math.SqrtRef
