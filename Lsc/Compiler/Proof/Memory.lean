import Lsc.Compiler.Yul
import Lsc.Compiler.Proof.Words
import YulSemantics.Dialect.EVMExec

/-!
Memory lemmas for `toYulFn_correct` (M1: one aligned `mstore`, Panic overlapping stores).
-/

namespace Lsc.Compiler

open YulSemantics.EVM

theorem storeWord_in (mem : Nat → UInt8) (p : Nat) (v : U256) (a : Nat)
    (h : p ≤ a ∧ a < p + 32) :
    storeWord mem p v a = byteAt v (31 - (a - p)) := by
  simp [storeWord, h]

theorem storeWord_out (mem : Nat → UInt8) (p : Nat) (v : U256) (a : Nat)
    (h : a < p ∨ p + 32 ≤ a) :
    storeWord mem p v a = mem a := by
  simp only [storeWord]
  split_ifs with hif
  · omega
  · rfl

theorem readBytes_storeWord_at (mem : Nat → UInt8) (p : Nat) (v : U256) :
    readBytes (storeWord mem p v) p 32 =
      (List.range 32).map (fun i => byteAt v (31 - i)) := by
  unfold readBytes
  apply List.map_congr_left
  intro i hi
  have : i < 32 := List.mem_range.mp hi
  rw [storeWord_in (h := by omega)]
  simp

theorem readBytes_split (mem : Nat → UInt8) (p n k : Nat) :
    readBytes mem p (n + k) = readBytes mem p n ++ readBytes mem (p + n) k := by
  simp only [readBytes, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _hi
  simp [Nat.add_assoc]

theorem wordBytes_eq_byteAt {n : Nat} (hn : n < wordBound) :
    wordBytes n = (List.range 32).map (fun i => byteAt (BitVec.ofNat 256 n) (31 - i)) := by
  unfold wordBytes
  apply List.map_congr_left
  intro i _hi
  have hto : (BitVec.ofNat 256 n).toNat = n := toNat_ofNat_of_lt hn
  simp only [byteAt, BitVec.toNat_ushiftRight, hto, Nat.shiftRight_eq_div_pow]
  have : (n / 2 ^ (8 * (31 - i))) % 256 = (n / 2 ^ (8 * (31 - i))) % 2 ^ 8 := rfl
  rw [this, UInt8.ofNat_mod_size]

theorem readBytes_storeWord_wordBytes (mem : Nat → UInt8) (p n : Nat) (hn : n < wordBound) :
    readBytes (storeWord mem p (BitVec.ofNat 256 n)) p 32 = wordBytes n := by
  rw [readBytes_storeWord_at, wordBytes_eq_byteAt hn]

private theorem wordToBytesLE_size (w : BitVec 64) :
    (KeccakEngine.wordToBytesLE w).size = 8 := rfl

private theorem foldl_append_size :
    ∀ (l : List (Array UInt8)) (acc : Array UInt8),
      (∀ a ∈ l, a.size = 8) →
        (l.foldl (· ++ ·) acc).size = acc.size + 8 * l.length
  | [], acc, _ => by simp
  | a :: rest, acc, h => by
    simp only [List.foldl_cons]
    have hr := foldl_append_size rest (acc ++ a)
      (fun x hx => h x (List.mem_cons_of_mem a hx))
    have ha : a.size = 8 := h a (by simp)
    rw [hr, Array.size_append, ha, List.length_cons, Nat.mul_succ, Nat.add_assoc,
      Nat.add_comm (8 * rest.length) 8]

private theorem byteArray_mk_size (arr : Array UInt8) :
    ByteArray.size ⟨arr⟩ = Array.size arr := rfl

theorem squeeze_size (state : Array (BitVec 64)) (n : Nat) :
    (KeccakEngine.squeeze state n).size = 8 * (n / 8) := by
  simp only [KeccakEngine.squeeze]
  rw [byteArray_mk_size, foldl_append_size]
  · simp [List.length_map, List.length_range]
  · intro a ha
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha
    exact wordToBytesLE_size _

theorem keccak256_size (input : ByteArray) :
    (KeccakEngine.keccak256 input).size = 32 := by
  simp only [KeccakEngine.keccak256, KeccakEngine.hash_core]
  have h : KeccakEngine.config_keccak256.outputBytes = 32 := rfl
  rw [h]
  exact squeeze_size _ 32

private theorem foldlM_loop_bytes_lt (bs : ByteArray) {stop : Nat}
    (hstop : stop ≤ bs.size) :
    ∀ (i j acc k : Nat), j + i = stop → acc < 256 ^ k →
      Id.run (ByteArray.foldlM.loop (fun a b => pure (a * 256 + b.toNat))
          bs stop hstop i j acc) < 256 ^ (k + i)
  | 0, j, acc, k, hij, hacc => by
    unfold ByteArray.foldlM.loop
    split
    · have : ¬ j < stop := by omega
      contradiction
    · simpa using hacc
  | i + 1, j, acc, k, hij, hacc => by
    unfold ByteArray.foldlM.loop
    have hj : j < stop := by omega
    simp only [hj, ↓reduceDIte]
    have hb : (bs[j]'(Nat.lt_of_lt_of_le hj hstop)).toNat < 256 := UInt8.toNat_lt_size _
    have hacc' : acc * 256 + (bs[j]'(Nat.lt_of_lt_of_le hj hstop)).toNat < 256 ^ (k + 1) := by
      have h1 : acc * 256 + (bs[j]'(Nat.lt_of_lt_of_le hj hstop)).toNat
          < acc * 256 + 256 := Nat.add_lt_add_left hb _
      have h2 : acc * 256 + 256 = (acc + 1) * 256 := by rw [Nat.succ_mul]
      have h3 : (acc + 1) * 256 ≤ 256 ^ k * 256 :=
        Nat.mul_le_mul_right 256 (Nat.succ_le_of_lt hacc)
      have h4 : 256 ^ k * 256 = 256 ^ (k + 1) := (Nat.pow_succ _ _).symm
      omega
    have hij' : j + 1 + i = stop := by omega
    simpa [Nat.add_assoc, Nat.add_comm 1 i] using
      foldlM_loop_bytes_lt bs hstop i (j + 1) _ (k + 1) hij' hacc'

theorem bytesToNat_lt (bs : ByteArray) : bytesToNat bs < 256 ^ bs.size := by
  unfold bytesToNat ByteArray.foldl ByteArray.foldlM
  have h : bs.size ≤ bs.size := Nat.le_refl _
  simp only [h, ↓reduceDIte, Nat.sub_zero]
  simpa using foldlM_loop_bytes_lt bs h bs.size 0 0 0 (by omega) (by decide)

theorem keccakWord_lt (bs : ByteArray) : keccakWord bs < 2 ^ 256 := by
  have hsz : (KeccakEngine.keccak256 bs).size = 32 := keccak256_size _
  have hlt := bytesToNat_lt (KeccakEngine.keccak256 bs)
  have heq : 256 ^ 32 = 2 ^ 256 := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  simp only [keccakWord] at hlt ⊢
  rw [hsz] at hlt
  rwa [heq] at hlt

theorem selectorOf_lt (name : String) (params : List Param) :
    selectorOf name params < 2 ^ 32 := by
  unfold selectorOf
  have hlt : keccakWord (abiSignature name params).toUTF8 < 2 ^ 256 := keccakWord_lt _
  apply Nat.div_lt_of_lt_mul
  have : (2 ^ 224) * (2 ^ 32) = 2 ^ 256 := by rw [← Nat.pow_add]
  rwa [this]

theorem panicSelector_lt : panicSelector < 2 ^ 32 := selectorOf_lt _ _

private theorem two_pow_32_lt_wordBound : (2 : Nat) ^ 32 < wordBound := by
  unfold wordBound
  exact Nat.pow_lt_pow_right (by decide : (1 : Nat) < 2) (by decide : (32 : Nat) < 256)

theorem byteAt_shl_selector (sel i : Nat) (hsel : sel < 2 ^ 32) (hi : i < 4) :
    byteAt (BitVec.ofNat 256 sel <<< 224) (31 - i) =
      UInt8.ofNat ((sel >>> (8 * (3 - i))) % 256) := by
  have hsel' : sel < wordBound := Nat.lt_trans hsel two_pow_32_lt_wordBound
  have hto : (BitVec.ofNat 256 sel).toNat = sel := toNat_ofNat_of_lt hsel'
  have hshl : (BitVec.ofNat 256 sel <<< 224).toNat = sel <<< 224 := by
    rw [BitVec.toNat_shiftLeft, hto, Nat.shiftLeft_eq]
    have : sel * 2 ^ 224 < 2 ^ 256 := by
      have : sel * 2 ^ 224 < 2 ^ 32 * 2 ^ 224 :=
        Nat.mul_lt_mul_of_pos_right hsel (Nat.two_pow_pos 224)
      rwa [← Nat.pow_add] at this
    exact Nat.mod_eq_of_lt this
  simp only [byteAt, BitVec.toNat_ushiftRight, hshl, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hk : 8 * (3 - i) = 24 - 8 * i := by omega
  have hden : 8 * (31 - i) = 248 - 8 * i := by omega
  have hsum : 224 + (24 - 8 * i) = 248 - 8 * i := by omega
  have hdiv : sel * 2 ^ 224 / 2 ^ (8 * (31 - i)) = sel / 2 ^ (8 * (3 - i)) := by
    rw [hden, hk]
    have hpow : 2 ^ (248 - 8 * i) = 2 ^ 224 * 2 ^ (24 - 8 * i) := by
      rw [← Nat.pow_add, hsum]
    rw [hpow, Nat.mul_comm sel, Nat.mul_div_mul_left _ _ (Nat.two_pow_pos 224)]
  rw [hdiv]
  change UInt8.ofNat _ = UInt8.ofNat (_ % 2 ^ 8)
  exact (UInt8.ofNat_mod_size).symm

theorem panicBytes_mem (mem : Nat → UInt8) (code : Nat) (hcode : code < wordBound) :
    readBytes
      (storeWord
        (storeWord mem abiPtr (BitVec.ofNat 256 panicSelector <<< 224))
        abiAfterSel (BitVec.ofNat 256 code))
      abiPtr 36 = panicBytes code := by
  have h36 : (36 : Nat) = 4 + 32 := rfl
  have hptr : abiPtr + 4 = abiAfterSel := rfl
  rw [panicBytes, h36, readBytes_split, hptr,
    readBytes_storeWord_wordBytes (hn := hcode)]
  refine congrArg (fun l => l ++ wordBytes code) ?_
  apply List.map_congr_left
  intro i hi
  have hi' : i < 4 := List.mem_range.mp hi
  have hlo : abiPtr + i < abiAfterSel := by
    simp only [abiPtr, abiAfterSel]
    omega
  have hidx : abiPtr + i - abiPtr = i := Nat.add_sub_cancel_left abiPtr i
  rw [storeWord_out (h := .inl hlo), storeWord_in (h := by
        simp only [abiPtr]
        omega),
    hidx, byteAt_shl_selector panicSelector i panicSelector_lt hi']

theorem selectorBytes_mem (mem : Nat → UInt8) (sel : Nat) (hsel : sel < 2 ^ 32) :
    readBytes (storeWord mem abiPtr (BitVec.ofNat 256 sel <<< 224)) abiPtr 4 =
      selectorBytes sel := by
  unfold readBytes selectorBytes
  apply List.map_congr_left
  intro i hi
  have hi' : i < 4 := List.mem_range.mp hi
  have hidx : abiPtr + i - abiPtr = i := Nat.add_sub_cancel_left abiPtr i
  rw [storeWord_in (h := by
        simp only [abiPtr]
        omega),
    hidx, byteAt_shl_selector sel i hsel hi']

theorem customErrorBytes_nil (c : ContractDef) {err : Nat} {ed : ErrorDef}
    (h : c.errors[err]? = some ed) :
    customErrorBytes c err [] = selectorBytes ed.selector := by
  simp [customErrorBytes, h]

theorem abiBytes_singleton (n : Nat) : abiBytes [n] = wordBytes n := by
  simp [abiBytes]


end Lsc.Compiler
