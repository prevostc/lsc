import Lsc3.EVM.Lemmas
import Lsc3.Compile.Encode
import Lsc3.Compile.Exec

/-!
# `PUSH2` jump immediates

The compiler emits a fixed-width `PUSH2` for every jump so layout is independent of
the destination and PCs stay below `2^16`. These lemmas are the decode side of
`emitPush2`.
-/

namespace Lsc3.Compile.Jump

open Lsc3 Lsc3.EVM Lsc3.Compile Lsc3.Compile.Exec

private theorem foldl_range_eq {α} (n : Nat) (f g : α → Nat → α)
    (h : ∀ acc i, i < n → f acc i = g acc i) (acc : α) :
    (List.range n).foldl f acc = (List.range n).foldl g acc := by
  induction n generalizing acc with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih (fun acc i hi => h acc i (Nat.lt_succ_of_lt hi))]
    rw [h _ n (Nat.lt_succ_self n)]

private theorem toNat_ofNat_mod256 (t : Nat) :
    (UInt8.ofNat (t % 256)).toNat = t % 256 := by
  change (t % 256) % 256 = t % 256
  rw [Nat.mod_mod]

private theorem packBE_width2 (n : Nat) :
    (List.range 2).foldl (fun acc i => acc * 256 + n / 256 ^ (1 - i) % 256) 0 =
      n % 256 ^ 2 := by
  have hdiv : n / 256 / 256 = n / 65536 := Nat.div_div_eq_div_mul n 256 256
  have heq : 256 * (n / 256 % 256) + n % 256 = n % 65536 := by
    have hdecomp : 65536 * (n / 65536) + (256 * (n / 256 % 256) + n % 256) = n := by
      calc
        65536 * (n / 65536) + (256 * (n / 256 % 256) + n % 256)
            = 256 * (256 * (n / 65536) + n / 256 % 256) + n % 256 := by ring
        _ = 256 * (256 * (n / 256 / 256) + n / 256 % 256) + n % 256 := by rw [hdiv]
        _ = 256 * (n / 256) + n % 256 := by rw [Nat.div_add_mod (n / 256) 256]
        _ = n := Nat.div_add_mod n 256
    have hstd : 65536 * (n / 65536) + n % 65536 = n := Nat.div_add_mod n 65536
    exact Nat.add_left_cancel (hdecomp.trans hstd.symm)
  have hrange : List.range 2 = [0, 1] := rfl
  rw [hrange, List.foldl_cons, List.foldl_cons, List.foldl_nil]
  simp only [Nat.zero_mul, Nat.zero_add]
  have hpow1 : 256 ^ (1 - 0) = 256 := Nat.pow_one 256
  have hpow0 : 256 ^ (1 - 1) = 1 := by rw [Nat.sub_self, Nat.pow_zero]
  rw [hpow1, hpow0, Nat.div_one, Nat.mul_comm, Nat.pow_two]
  exact heq

theorem readImm_push2 (n : Nat) (rest : List UInt8) :
    readImm (emitPush2 n ++ rest) 0 2 = n % 2 ^ 16 := by
  have hlen : ∀ i, i < 2 → 1 + i < (emitPush2 n ++ rest).length := by
    intro i hi
    simp [emitPush2, natToBytesBE_length]; omega
  have hfold :
      (List.range 2).foldl (fun acc i =>
        if 1 + i < (emitPush2 n ++ rest).length then
          acc * 256 + ((emitPush2 n ++ rest)[1 + i]!).toNat
        else acc) 0 =
        (List.range 2).foldl (fun acc i => acc * 256 + n / 256 ^ (1 - i) % 256) 0 := by
    refine foldl_range_eq 2 _ _ ?_ 0
    intro acc i hi
    have hi' := hlen i hi
    simp only [hi', ↓reduceIte]
    rw [Nat.add_comm 1 i]
    have hi2 : i + 1 < (emitPush2 n ++ rest).length := by
      simpa [Nat.add_comm] using hi'
    rw [getElem!_pos (emitPush2 n ++ rest) (i + 1) hi2]
    simp only [emitPush2, List.cons_append]
    rw [List.getElem_cons_succ]
    have hlt : i < (natToBytesBE n 2).length := by simp [natToBytesBE_length]; exact hi
    rw [List.getElem_append_left hlt, natToBytesBE_getElem n 2 i hi, toNat_ofNat_mod256]
  simp only [readImm, Nat.zero_add]
  rw [hfold, packBE_width2]
  have hpow : 256 ^ 2 = 2 ^ 16 := by
    change (2 ^ 8) ^ 2 = 2 ^ 16
    rw [← Nat.pow_mul]
  rw [hpow]
  exact wrap_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))

theorem decodeAt_push2 (n : Nat) (rest : List UInt8) :
    decodeAt (emitPush2 n ++ rest) 0 =
      some ({ op := .PUSH ⟨2, by decide⟩, imm := n % 2 ^ 16 }, 3) := by
  unfold decodeAt
  have hpc : 0 < (emitPush2 n ++ rest).length := by simp [emitPush2, natToBytesBE_length]
  rw [dif_pos hpc]
  have hbyte : (emitPush2 n ++ rest)[0] = Opcode.toByte (.PUSH ⟨2, by decide⟩) := by
    simp [emitPush2]
  rw [hbyte, ofByte_toByte]
  simp [Opcode.immBytes, readImm_push2]

/-- Immediate of `PUSH32 n` is `wrap n`. Does not reduce `n` (Keccak topics stay symbolic). -/
theorem readImm_push32 (n : Nat) (rest : List UInt8) :
    readImm (emitPush32 n ++ rest) 0 32 = wrap n := by
  have hlen : ∀ i, i < 32 → 1 + i < (emitPush32 n ++ rest).length := by
    intro i hi
    simp [emitPush32, natToBytesBE_length]; omega
  have hfold :
      (List.range 32).foldl (fun acc i =>
        if 1 + i < (emitPush32 n ++ rest).length then
          acc * 256 + ((emitPush32 n ++ rest)[1 + i]!).toNat
        else acc) 0 =
        (List.range 32).foldl (fun acc i => acc * 256 + n / 256 ^ (31 - i) % 256) 0 := by
    refine foldl_range_eq 32 _ _ ?_ 0
    intro acc i hi
    have hi' := hlen i hi
    simp only [hi', ↓reduceIte]
    rw [Nat.add_comm 1 i]
    have hi2 : i + 1 < (emitPush32 n ++ rest).length := by
      simpa [Nat.add_comm] using hi'
    rw [getElem!_pos (emitPush32 n ++ rest) (i + 1) hi2]
    simp only [emitPush32, List.cons_append]
    rw [List.getElem_cons_succ]
    have hlt : i < (natToBytesBE n 32).length := by simp [natToBytesBE_length]; exact hi
    rw [List.getElem_append_left hlt, natToBytesBE_getElem n 32 i hi, toNat_ofNat_mod256]
  simp only [readImm, Nat.zero_add]
  rw [hfold, packWord_high n 32 (by decide), Nat.sub_self, Nat.pow_zero, Nat.div_one,
    pow256_32]
  simp [wrap]

theorem decodeAt_push32 (n : Nat) (rest : List UInt8) :
    decodeAt (emitPush32 n ++ rest) 0 =
      some ({ op := .PUSH ⟨32, by decide⟩, imm := wrap n }, 33) := by
  unfold decodeAt
  have hpc : 0 < (emitPush32 n ++ rest).length := by simp [emitPush32, natToBytesBE_length]
  rw [dif_pos hpc]
  have hbyte : (emitPush32 n ++ rest)[0] = Opcode.toByte (.PUSH ⟨32, by decide⟩) := by
    simp [emitPush32]
  rw [hbyte, ofByte_toByte]
  simp [Opcode.immBytes, readImm_push32]

end Lsc3.Compile.Jump
