import Lsc.Lang.Derive
import Lsc.Lang.Syntax
import Lsc.Lang.Eval
import Lsc.Lang.Checks
import Lsc.Compile.Bytecode

/-!
# End-to-end tests for multi-argument `emit` events

Exercises `emit Swap(sender, amountIn, amountOut);` through elaboration, `ContractM`
interpretation (`runS`), and the real bytecode pipeline (`derive_contract`'s `bytecodeHex`).
-/

open Lsc

namespace Lsc.MultiArgEventTest

structure EStorage where
  n : Wad := ⟨0⟩
  deriving Repr, DecidableEq, Lsc.Deriving.ContractStorage

inductive EError where
  | Bad
  deriving Repr, DecidableEq, Lsc.Deriving.ContractError

inductive EEvent where
  | Swap (sender : Address) (amountIn : Wad) (amountOut : Wad)
  | Transfer (amount : Wad)
  deriving Repr, DecidableEq, Lsc.Deriving.ContractEvent

tx doSwap(sender : Address, amountIn : Wad, amountOut : Wad) {
  emit Swap(sender, amountIn, amountOut);
}

tx doTransfer(amount : Wad) {
  emit Transfer(amount);
}

derive_contract "E" EStorage EError EEvent

def mkState : ContractState EStorage :=
  { storage := {}
    context := { caller := 42, callvalue := 0, timestamp := 0, origin := 0 }
    locked := false }

example : (Checks.validateAll contractDef).isOk := by native_decide

example : (runS ((doSwap 7 (Wad.mkNat 100) (Wad.mkNat 200) : EM Unit)) mkState).isOk := by native_decide

example : (runS ((doTransfer (Wad.mkNat 50) : EM Unit)) mkState).isOk := by native_decide

example : bytecodeHex.startsWith "0x" ∧ bytecodeHex.length > 10 := by native_decide

example : EEvent.buildEvent "Swap"
    [⟨Ty.address, .addr 1⟩, ⟨Ty.wad, .wad (Wad.mkNat 2)⟩, ⟨Ty.wad, .wad (Wad.mkNat 3)⟩] =
      some (.Swap 1 (Wad.mkNat 2) (Wad.mkNat 3)) := by
  native_decide

end Lsc.MultiArgEventTest
