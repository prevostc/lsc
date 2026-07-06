import Lsc.Core.UInt256
import Lsc.Types

namespace Lsc.Wad

/-- Fixed-point scale: 18 decimal places, mirroring Solidity's `WAD` convention.
`1.0` is represented as `WAD` raw units. -/
def WAD : Nat := 1000000000000000000

structure Wad where
  raw : UInt256
  deriving Repr, DecidableEq

def mkNat (n : Nat) : Wad := ⟨BitVec.ofNat 256 n⟩

/-- `1.0` as a `Wad` (`WAD` raw units). -/
def one : Wad := mkNat WAD

/--
Wad-domain expression fragment (`Expr .wad`), mirroring `Wei.Expr`'s shape
exactly — `Ty.wad`/`Val.wad` are registered in the core `Ty`/`Val`/
`ContractDSL` machinery (`Lsc/Lang/AST.lean`/`Lsc/Core/ContractM.lean`)
alongside `Ty.wei`/`Val.wei`, so `Wad.Expr` has the same `.var`/`.storageGet`
cases `Wei.Expr` does, letting a `Wad`-typed field be declared in a
contract's `storage:` block and read/written from a `tx { }` body exactly
like a `Wei` field. -/
inductive Expr where
  | lit : Nat → Expr
  | var : Ident → Expr
  | storageGet : Ident → Expr
  | addChecked : Expr → Expr → Expr
  | addCheckedNat : Expr → Nat → Expr
  | subChecked : Expr → Expr → Expr
  | mulHalfUpChecked : Expr → Expr → Expr
  | divDownChecked : Expr → Expr → Expr
  deriving Repr

/-- The `ArithError`s a given top-level `Expr` node can raise, mirroring
`Wei.arithErrors`. Used (once wired up, see the follow-up note above) by
`Lang.Checks.checkArithErrorCoverage`-style coverage checks. -/
def arithErrors : Expr → List ArithError
  | .addChecked _ _ => [.Overflow]
  | .addCheckedNat _ _ => [.Overflow]
  | .subChecked _ _ => [.Underflow]
  | .mulHalfUpChecked _ _ => [.Overflow]
  | .divDownChecked _ _ => [.DivisionByZero, .Overflow]
  | .lit _ => []
  | .var _ => []
  | .storageGet _ => []

end Lsc.Wad
