import Lsc.Compiler.Yul
import YulSemantics.Dialect.EVMOp
import Mathlib.Data.List.Nodup

/-!
Word / identifier lemmas for `toYulFn_correct` (M1: add / ult / `identV` injectivity).
-/

namespace Lsc.Compiler

open YulSemantics.EVM

theorem toNat_ofNat_of_lt {n : Nat} (h : n < wordBound) :
    (BitVec.ofNat 256 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  simpa [wordBound] using h

theorem ofNat_inj_of_lt {a b : Nat} (ha : a < wordBound) (hb : b < wordBound)
    (h : BitVec.ofNat 256 a = BitVec.ofNat 256 b) : a = b := by
  simpa [toNat_ofNat_of_lt ha, toNat_ofNat_of_lt hb] using congrArg BitVec.toNat h

theorem ofNat_eq_iff {a b : Nat} (ha : a < wordBound) (hb : b < wordBound) :
    BitVec.ofNat 256 a = BitVec.ofNat 256 b ↔ a = b :=
  ⟨ofNat_inj_of_lt ha hb, fun h => h ▸ rfl⟩

theorem ofNat_sub_of_le {a b : Nat} (hba : b ≤ a) (ha : a < wordBound) :
    BitVec.ofNat 256 a - BitVec.ofNat 256 b = BitVec.ofNat 256 (a - b) := by
  have hb : b < wordBound := Nat.lt_of_le_of_lt hba ha
  have hab : a - b < wordBound := Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
  apply BitVec.eq_of_toNat_eq
  have ha' := toNat_ofNat_of_lt ha
  have hb' := toNat_ofNat_of_lt hb
  rw [BitVec.toNat_sub, ha', hb', toNat_ofNat_of_lt hab]
  change (2 ^ 256 - b + a) % 2 ^ 256 = a - b
  have hword : (2 : Nat) ^ 256 = wordBound := rfl
  rw [hword]
  have : wordBound - b + a = (a - b) + wordBound := by omega
  rw [this, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt hab

theorem ofNat_add (a b : Nat) :
    BitVec.ofNat 256 a + BitVec.ofNat 256 b = BitVec.ofNat 256 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod]

theorem ult_ofNat {a b : Nat} (ha : a < wordBound) (hb : b < wordBound) :
    (BitVec.ofNat 256 a).ult (BitVec.ofNat 256 b) = decide (a < b) := by
  simp [BitVec.ult, toNat_ofNat_of_lt ha, toNat_ofNat_of_lt hb]

/-- Checked-add overflow guard: `lt(add(a,b), a)` iff `a+b` does not fit in a word. -/
theorem ult_add_overflow {a b : Nat} (ha : a < wordBound) (hb : b < wordBound) :
    (BitVec.ofNat 256 a + BitVec.ofNat 256 b).ult (BitVec.ofNat 256 a) = true ↔
      wordBound ≤ a + b := by
  rw [ofNat_add]
  have hsum : (BitVec.ofNat 256 (a + b)).toNat = (a + b) % wordBound := by
    simp [BitVec.toNat_ofNat, wordBound]
  have ha' : (BitVec.ofNat 256 a).toNat = a := toNat_ofNat_of_lt ha
  simp only [BitVec.ult, decide_eq_true_eq, hsum, ha']
  constructor
  · intro hlt
    by_contra hge
    have : a + b < wordBound := Nat.lt_of_not_ge hge
    rw [Nat.mod_eq_of_lt this] at hlt
    exact Nat.not_lt_of_ge (Nat.le_add_right a b) hlt
  · intro hle
    have hdiv : (a + b) / wordBound = 1 :=
      Nat.div_eq_of_lt_le (by simpa using hle) (by
        have := Nat.add_lt_add ha hb
        simpa [Nat.two_mul] using this)
    rw [Nat.mod_eq_sub_div_mul, hdiv, Nat.one_mul]
    omega

theorem litValue_number (n : Nat) :
    YulSemantics.EVM.litValue (.number n) = BitVec.ofNat 256 n := rfl

theorem b2w_false : b2w false = 0 := rfl
theorem b2w_true : b2w true = 1 := rfl

theorem identV_inj_of_nodup (n : Nat) (h : identsNodup n = true)
    {i j : Nat} (hi : i < n) (hj : j < n) (heq : identV i = identV j) : i = j := by
  have hnd : ((List.range n).map identV).Nodup := (identsNodup_iff n).mp h
  exact List.inj_on_of_nodup_map hnd (List.mem_range.mpr hi) (List.mem_range.mpr hj) heq

theorem identsNodup_mono {m n : Nat} (hmn : m ≤ n) (h : identsNodup n = true) :
    identsNodup m = true := by
  rw [identsNodup_iff] at h ⊢
  have hsub : (List.range m).Sublist (List.range n) := List.range_sublist.mpr hmn
  exact List.Pairwise.sublist (hsub.map identV) h

theorem one_lt_wordBound : (1 : Nat) < wordBound := by
  unfold wordBound
  exact Nat.one_lt_pow (by decide : (256 : Nat) ≠ 0) (by decide : (1 : Nat) < 2)

theorem zero_lt_wordBound : (0 : Nat) < wordBound :=
  Nat.pow_pos_iff.mpr (.inl (by decide : (0 : Nat) < 2))

theorem lt_256_wordBound {n : Nat} (h : n < 256) : n < wordBound :=
  Nat.lt_trans h (by
    unfold wordBound
    exact Nat.pow_lt_pow_right (by decide : (1 : Nat) < 2) (by decide : (8 : Nat) < 256))

theorem b2w_eq_zero {c : Bool} : b2w c = 0 ↔ c = false := by
  cases c <;> simp [b2w]

theorem b2w_ne_zero {c : Bool} : b2w c ≠ 0 ↔ c = true := by
  cases c <;> simp [b2w]

end Lsc.Compiler
