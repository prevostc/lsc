import EvmYul.UInt256

namespace Lsc.Compile.Abi

/-- ABI function selector left-padded to a 256-bit word: EVM `SHL(224, selector)`. -/
def paddedSelector (selector : Nat) : Nat :=
  (BitVec.ofNat 256 (selector <<< 224)).toNat

private theorem selector_shift224_lt_word256 (selector : Nat) (h : selector < 2 ^ 32) :
    selector <<< 224 < 2 ^ 256 := by
  rw [Nat.shiftLeft_eq, show 2 ^ 256 = 2 ^ 32 * 2 ^ 224 from by rw [← Nat.pow_add]]
  exact Nat.mul_lt_mul_of_pos_right h (by decide)

/-- `paddedSelector` is `selector <<< 224` for 4-byte ABI selectors (no 256-bit wrap). -/
theorem paddedSelector_eq_shl224 (selector : Nat) (h : selector < 2 ^ 32) :
    paddedSelector selector = selector <<< 224 := by
  dsimp [paddedSelector]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (selector_shift224_lt_word256 selector h)]

/-- IERC20 `transfer(address,uint256)` selector, ABI-packed at memory offset 0. -/
theorem transfer_selector_padded :
    paddedSelector 0xa9059cbb =
      0xa9059cbb00000000000000000000000000000000000000000000000000000000 := by
  native_decide

end Lsc.Compile.Abi
