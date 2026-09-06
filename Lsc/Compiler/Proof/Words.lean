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

theorem ofNat_mul (a b : Nat) :
    BitVec.ofNat 256 a * BitVec.ofNat 256 b = BitVec.ofNat 256 (a * b) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_mod]

theorem ofNat_div {a b : Nat} (ha : a < wordBound) (hb : b < wordBound) :
    BitVec.ofNat 256 a / BitVec.ofNat 256 b = BitVec.ofNat 256 (a / b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, toNat_ofNat_of_lt ha, toNat_ofNat_of_lt hb,
    toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self a b) ha)]

theorem ofNat_mod {a b : Nat} (ha : a < wordBound) (hb : b < wordBound) :
    BitVec.ofNat 256 a % BitVec.ofNat 256 b = BitVec.ofNat 256 (a % b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, toNat_ofNat_of_lt ha, toNat_ofNat_of_lt hb,
    toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le a b) ha)]

theorem ofNat_eq_zero {a : Nat} (ha : a < wordBound) :
    BitVec.ofNat 256 a = 0 ↔ a = 0 := by
  constructor
  · intro h
    simpa [toNat_ofNat_of_lt ha] using congrArg BitVec.toNat h
  · rintro rfl; rfl

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

theorem b2w_and (c d : Bool) : b2w c &&& b2w d = b2w (c && d) := by
  cases c <;> cases d <;> simp [b2w]

theorem b2w_or (c d : Bool) : b2w c ||| b2w d = b2w (c || d) := by
  cases c <;> cases d <;> simp [b2w]

theorem ofNat_sub_wrap {a b : Nat} (ha : a < wordBound) (hb : b < wordBound) :
    BitVec.ofNat 256 a - BitVec.ofNat 256 b =
      BitVec.ofNat 256 ((a + wordBound - b) % wordBound) := by
  apply BitVec.eq_of_toNat_eq
  have ha' := toNat_ofNat_of_lt ha
  have hb' := toNat_ofNat_of_lt hb
  rw [BitVec.toNat_sub, ha', hb']
  have hmod : (a + wordBound - b) % wordBound < wordBound :=
    Nat.mod_lt _ (by unfold wordBound; exact Nat.two_pow_pos 256)
  rw [toNat_ofNat_of_lt hmod]
  change (wordBound - b + a) % wordBound = (a + wordBound - b) % wordBound
  rw [Nat.add_comm (wordBound - b), Nat.add_sub_assoc (Nat.le_of_lt hb)]

/-- `or(iszero(a), eq(div(mul(a,b), a), b))` holds iff the product fits in a word. -/
theorem mul_fits_iff {a b : Nat} (ha : a < wordBound) (hb : b < wordBound) :
    a * b < wordBound ↔
      BitVec.ofNat 256 a = 0 ∨
        (BitVec.ofNat 256 a * BitVec.ofNat 256 b) / BitVec.ofNat 256 a =
          BitVec.ofNat 256 b := by
  rw [ofNat_mul]
  constructor
  · intro hfit
    by_cases ha0 : a = 0
    · exact .inl ((ofNat_eq_zero ha).mpr ha0)
    · refine .inr ?_
      rw [ofNat_div hfit ha, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ha0)]
  · intro h
    rcases h with h0 | hdiv
    · have : a = 0 := (ofNat_eq_zero ha).mp h0
      subst this
      simpa using zero_lt_wordBound
    · by_contra hge
      have hle : wordBound ≤ a * b := Nat.le_of_not_gt hge
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact Nat.not_le.mpr zero_lt_wordBound (by simpa using hle)
      have hp : (BitVec.ofNat 256 (a * b)).toNat = (a * b) % wordBound := by
        simp [BitVec.toNat_ofNat, wordBound]
      have hmod : (a * b) % wordBound < wordBound :=
        Nat.mod_lt _ (by unfold wordBound; exact Nat.two_pow_pos 256)
      have hdivN :
          (BitVec.ofNat 256 (a * b) / BitVec.ofNat 256 a).toNat =
            ((a * b) % wordBound) / a := by
        rw [BitVec.toNat_udiv, hp, toNat_ofNat_of_lt ha]
      have hlt : ((a * b) % wordBound) / a < b := by
        refine (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero ha0)).mpr ?_
        rw [Nat.mul_comm b]
        exact Nat.lt_of_lt_of_le hmod hle
      have hne : BitVec.ofNat 256 (a * b) / BitVec.ofNat 256 a ≠ BitVec.ofNat 256 b := by
        intro he
        have := congrArg BitVec.toNat he
        rw [hdivN, toNat_ofNat_of_lt hb] at this
        exact Nat.ne_of_lt hlt this
      exact hne hdiv

/-- EVM `div` / `mod` return 0 on a zero divisor; otherwise they match `Nat`. -/
theorem evm_div_ofNat {a b : Nat} (ha : a < wordBound) (hb : b < wordBound) (hb0 : b ≠ 0) :
    (if BitVec.ofNat 256 b = 0 then 0 else BitVec.ofNat 256 a / BitVec.ofNat 256 b) =
      BitVec.ofNat 256 (a / b) := by
  have : BitVec.ofNat 256 b ≠ 0 := mt (ofNat_eq_zero hb).mp hb0
  rw [if_neg this, ofNat_div ha hb]

theorem evm_mod_ofNat {a b : Nat} (ha : a < wordBound) (hb : b < wordBound) (hb0 : b ≠ 0) :
    (if BitVec.ofNat 256 b = 0 then 0 else BitVec.ofNat 256 a % BitVec.ofNat 256 b) =
      BitVec.ofNat 256 (a % b) := by
  have : BitVec.ofNat 256 b ≠ 0 := mt (ofNat_eq_zero hb).mp hb0
  rw [if_neg this, ofNat_mod ha hb]

/-- Ceil `⌈a*b/c⌉` still fits when the product does. -/
theorem mulDiv_up_lt {a b c : Nat}
    (hfit : a * b < wordBound) (hc0 : c ≠ 0) (hrem : a * b % c ≠ 0) :
    a * b / c + 1 < wordBound := by
  have hc1 : 1 < c := by
    match c with
    | 0 => exact (hc0 rfl).elim
    | 1 =>
      have : a * b % 1 = 0 := Nat.mod_one _
      exact (hrem this).elim
    | n + 2 => omega
  have hpos : 0 < a * b := by
    by_contra h
    have : a * b = 0 := Nat.eq_zero_of_not_pos h
    simp [this] at hrem
  have := Nat.div_lt_self hpos hc1
  omega

end Lsc.Compiler
