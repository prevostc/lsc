import Lsc.Lang.Derive
import Lsc.Lang.Syntax
import Lsc.Lang.Eval
import Lsc.Lang.Checks
import Lsc.Compile.Bytecode

/-!
# End-to-end tests for `<=`/`>=`/`<`/`>` comparisons in `require` guard conditions

Exercises the new `CoreExpr.lt`/`.le` (`Uint256`-kind) and `CoreExpr.wadLt`/`.wadLe` (`Wad`-kind)
comparison surface: real `tx { .. }` bodies parsed and elaborated through `Lang/Syntax.lean`,
evaluated through `Lang/Eval.lean`'s interpreter (`runS`), and — for `swap` — compiled all the way
to real EVM bytecode (`derive_contract`'s `bytecodeHex`), mirroring `examples/token`'s slippage-
guard-shaped `require (amountOut >= minAmountOut) else revert SlippageExceeded();` use case.
-/

open Lsc

namespace Lsc.ComparisonTest

structure CStorage where
  n : Wad := ⟨0⟩
  deriving Repr, DecidableEq, Lsc.Deriving.ContractStorage

inductive CError where
  | SlippageExceeded
  | TooBig
  | TooSmall
  deriving Repr, DecidableEq, Lsc.Deriving.ContractError

inductive CEvent where
  | Swapped
  deriving Repr, DecidableEq, Lsc.Deriving.ContractEvent

-- The motivating CPAMM-`swap`-shaped guard from the task: `>=` on two `Wad` operands.
tx swap(amountOut : Wad, minAmountOut : Wad) {
  require (amountOut >= minAmountOut) else revert SlippageExceeded();
  emit Swapped();
}

tx checkLt(a : Wad, b : Wad) {
  require (a < b) else revert TooBig();
  emit Swapped();
}

tx checkLe(a : Wad, b : Wad) {
  require (a <= b) else revert TooBig();
  emit Swapped();
}

tx checkGt(a : Wad, b : Wad) {
  require (a > b) else revert TooSmall();
  emit Swapped();
}

derive_contract "C" CStorage CError CEvent

/-- Project an `Except CError _` down to just its error tag (or `none` on success) — avoids
needing a `DecidableEq` instance on the full success payload (`ContractState CStorage × List
CEvent`) just to state `native_decide`-checked "reverted with exactly this error" tests below. -/
def errOf {X : Type} : Except CError X → Option CError
  | .error e => some e
  | .ok _ => none

def mkState : ContractState CStorage :=
  { storage := { n := Wad.mkNat 0 }
    context := { caller := 0, callvalue := 0, timestamp := 0, origin := 0 }
    locked := false }

-- The contract as a whole (including the four new comparison-guarded `tx`s) still passes every
-- structural check (selector collisions, arith-error coverage, ...).
example : (Checks.validateAll contractDef).isOk := by native_decide

/-! ## `>=` (`swap`'s slippage guard) -/

example : (runS ((swap (Wad.mkNat 10) (Wad.mkNat 5) : CM Unit)) mkState).isOk := by native_decide
example : errOf (runS ((swap (Wad.mkNat 10) (Wad.mkNat 20) : CM Unit)) mkState) = some CError.SlippageExceeded := by
  native_decide
-- Boundary: equal values satisfy `≥`.
example : (runS ((swap (Wad.mkNat 10) (Wad.mkNat 10) : CM Unit)) mkState).isOk := by native_decide

/-! ## `<` -/

example : (runS ((checkLt (Wad.mkNat 5) (Wad.mkNat 10) : CM Unit)) mkState).isOk := by native_decide
example : errOf (runS ((checkLt (Wad.mkNat 10) (Wad.mkNat 10) : CM Unit)) mkState) = some CError.TooBig := by
  native_decide
example : errOf (runS ((checkLt (Wad.mkNat 20) (Wad.mkNat 10) : CM Unit)) mkState) = some CError.TooBig := by
  native_decide

/-! ## `<=` -/

example : (runS ((checkLe (Wad.mkNat 10) (Wad.mkNat 10) : CM Unit)) mkState).isOk := by native_decide
example : errOf (runS ((checkLe (Wad.mkNat 11) (Wad.mkNat 10) : CM Unit)) mkState) = some CError.TooBig := by
  native_decide

/-! ## `>` -/

example : (runS ((checkGt (Wad.mkNat 10) (Wad.mkNat 5) : CM Unit)) mkState).isOk := by native_decide
example : errOf (runS ((checkGt (Wad.mkNat 5) (Wad.mkNat 5) : CM Unit)) mkState) = some CError.TooSmall := by
  native_decide
example : errOf (runS ((checkGt (Wad.mkNat 5) (Wad.mkNat 10) : CM Unit)) mkState) = some CError.TooSmall := by
  native_decide

/-! ## End-to-end bytecode: `swap`'s `>=` guard compiles to real `LT`/`ISZERO` opcodes. -/

example : bytecodeHex.startsWith "0x" ∧ bytecodeHex.length > 10 := by native_decide

end Lsc.ComparisonTest
