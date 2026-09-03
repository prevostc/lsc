import Lsc3.EVM.Lemmas
import EvmYul.UInt256
import EvmYul.EVM.Instr

/-!
# Refinement toward EvmYul

Phase B4: our `Nat`-word machine agrees with EvmYul on the word ring and on opcode decoding.
Per-opcode `step` refinement (gas, account map, `ByteArray` memory) is layered on this; the
subset machine has no gas, so those theorems quantify over “enough gas, no calls”.
-/

namespace Lsc3.EVM.EvmYulRefinement

open Lsc3 Lsc3.EVM
open EvmYul

/-! ## Word ring -/

theorem wordBound_eq_UInt256_size : wordBound = UInt256.size := rfl

@[simp] theorem wrap_eq_toNat_ofNat (n : Nat) :
    wrap n = (UInt256.ofNat n).toNat := by
  unfold wrap UInt256.ofNat UInt256.toNat
  rw [wordBound_eq_UInt256_size]
  simp [Id.run, Fin.val_natCast]

theorem addW_eq_UInt256 (a b : Nat) :
    addW a b = (UInt256.add (UInt256.ofNat a) (UInt256.ofNat b)).toNat := by
  calc
    addW a b = (a + b) % UInt256.size := by
      simp [addW, wrap, wordBound_eq_UInt256_size]
    _ = ((a % UInt256.size) + (b % UInt256.size)) % UInt256.size :=
      Nat.add_mod a b UInt256.size
    _ = (UInt256.add (UInt256.ofNat a) (UInt256.ofNat b)).toNat := by
      simp [UInt256.add, UInt256.ofNat, UInt256.toNat, Id.run, Fin.add_def, Fin.val_natCast]

theorem mulW_eq_UInt256 (a b : Nat) :
    mulW a b = (UInt256.mul (UInt256.ofNat a) (UInt256.ofNat b)).toNat := by
  calc
    mulW a b = (a * b) % UInt256.size := by
      simp [mulW, wrap, wordBound_eq_UInt256_size]
    _ = ((a % UInt256.size) * (b % UInt256.size)) % UInt256.size :=
      Nat.mul_mod a b UInt256.size
    _ = (UInt256.mul (UInt256.ofNat a) (UInt256.ofNat b)).toNat := by
      simp [UInt256.mul, UInt256.ofNat, UInt256.toNat, Id.run, Fin.mul_def, Fin.val_natCast]

/-! ## Decode: our `ofByte` vs EvmYul `parseInstr` on the emitted subset -/

theorem parseInstr_stop : EVM.parseInstr 0x00 = some .STOP := rfl
theorem parseInstr_add : EVM.parseInstr 0x01 = some .ADD := rfl
theorem parseInstr_mul : EVM.parseInstr 0x02 = some .MUL := rfl
theorem parseInstr_sub : EVM.parseInstr 0x03 = some .SUB := rfl
theorem parseInstr_div : EVM.parseInstr 0x04 = some .DIV := rfl
theorem parseInstr_lt : EVM.parseInstr 0x10 = some .LT := rfl
theorem parseInstr_gt : EVM.parseInstr 0x11 = some .GT := rfl
theorem parseInstr_eq : EVM.parseInstr 0x14 = some .EQ := rfl
theorem parseInstr_iszero : EVM.parseInstr 0x15 = some .ISZERO := rfl
theorem parseInstr_shl : EVM.parseInstr 0x1b = some .SHL := rfl
theorem parseInstr_shr : EVM.parseInstr 0x1c = some .SHR := rfl
theorem parseInstr_keccak : EVM.parseInstr 0x20 = some .KECCAK256 := rfl
theorem parseInstr_caller : EVM.parseInstr 0x33 = some .CALLER := rfl
theorem parseInstr_calldataload : EVM.parseInstr 0x35 = some .CALLDATALOAD := rfl
theorem parseInstr_calldatasize : EVM.parseInstr 0x36 = some .CALLDATASIZE := rfl
theorem parseInstr_codecopy : EVM.parseInstr 0x39 = some .CODECOPY := rfl
theorem parseInstr_pop : EVM.parseInstr 0x50 = some .POP := rfl
theorem parseInstr_mload : EVM.parseInstr 0x51 = some .MLOAD := rfl
theorem parseInstr_mstore : EVM.parseInstr 0x52 = some .MSTORE := rfl
theorem parseInstr_sload : EVM.parseInstr 0x54 = some .SLOAD := rfl
theorem parseInstr_sstore : EVM.parseInstr 0x55 = some .SSTORE := rfl
theorem parseInstr_jump : EVM.parseInstr 0x56 = some .JUMP := rfl
theorem parseInstr_jumpi : EVM.parseInstr 0x57 = some .JUMPI := rfl
theorem parseInstr_jumpdest : EVM.parseInstr 0x5b = some .JUMPDEST := rfl
theorem parseInstr_push0 : EVM.parseInstr 0x5f = some .PUSH0 := rfl
theorem parseInstr_push1 : EVM.parseInstr 0x60 = some .PUSH1 := rfl
theorem parseInstr_dup1 : EVM.parseInstr 0x80 = some .DUP1 := rfl
theorem parseInstr_swap1 : EVM.parseInstr 0x90 = some .SWAP1 := rfl
theorem parseInstr_log1 : EVM.parseInstr 0xa1 = some .LOG1 := rfl
theorem parseInstr_return : EVM.parseInstr 0xf3 = some .RETURN := rfl
theorem parseInstr_revert : EVM.parseInstr 0xfd = some .REVERT := rfl
theorem parseInstr_call : EVM.parseInstr 0xf1 = some .CALL := rfl

theorem ofByte_stop : Opcode.ofByte 0x00 = some .STOP := rfl
theorem ofByte_add : Opcode.ofByte 0x01 = some .ADD := rfl
theorem ofByte_push0 : Opcode.ofByte 0x5f = some (.PUSH ⟨0, by decide⟩) := by
  unfold Opcode.ofByte
  simp
theorem ofByte_push1 : Opcode.ofByte 0x60 = some (.PUSH ⟨1, by decide⟩) := by
  unfold Opcode.ofByte
  simp
theorem ofByte_return : Opcode.ofByte 0xf3 = some .RETURN := rfl

/-- Encoding a STOP (resp. ADD, …) is the same byte EvmYul decodes. -/
theorem toByte_stop_parse : EVM.parseInstr (Opcode.toByte .STOP) = some .STOP := rfl
theorem toByte_add_parse : EVM.parseInstr (Opcode.toByte .ADD) = some .ADD := rfl
theorem toByte_return_parse : EVM.parseInstr (Opcode.toByte .RETURN) = some .RETURN := rfl

end Lsc3.EVM.EvmYulRefinement
