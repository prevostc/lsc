import Lsc.Compiler.Correctness
import Lsc.Compiler.Proof.Words
import Lsc.Compiler.Proof.Memory
import Lsc.Compiler.Proof.Env
import YulSemantics.Dialect.EVMExec

set_option linter.unusedSimpArgs false

/-!
Calldata round-trips: `fnCalldata` recovers `decodeArgs` / `calldataSelector`.
-/

namespace Lsc.Compiler

open YulSemantics.EVM

private theorem pow2_8 : (2 : Nat) ^ 8 = 256 := by decide

private theorem pow256_4 : (256 : Nat) ^ 4 = 2 ^ 32 := by
  calc (256 : Nat) ^ 4 = (2 ^ 8) ^ 4 := by rw [pow2_8]
    _ = 2 ^ (8 * 4) := Nat.pow_mul 2 8 4
    _ = 2 ^ 32 := by decide

private theorem pow256_28 : (256 : Nat) ^ 28 = 2 ^ 224 := by
  calc (256 : Nat) ^ 28 = (2 ^ 8) ^ 28 := by rw [pow2_8]
    _ = 2 ^ (8 * 28) := Nat.pow_mul 2 8 28
    _ = 2 ^ 224 := by decide

private theorem pow256_32 : (256 : Nat) ^ 32 = wordBound := by
  calc (256 : Nat) ^ 32 = (2 ^ 8) ^ 32 := by rw [pow2_8]
    _ = 2 ^ (8 * 32) := Nat.pow_mul 2 8 32
    _ = 2 ^ 256 := by decide

theorem foldl_congr {α β} {xs : List α} {f g : β → α → β} {b : β}
    (h : ∀ (b : β) (a : α), a ∈ xs → f b a = g b a) :
    xs.foldl f b = xs.foldl g b := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
    have hx : f b x = g b x := h b x (List.mem_cons.mpr (Or.inl rfl))
    simp only [List.foldl_cons, hx]
    exact ih fun b' a ha => h b' a (List.mem_cons_of_mem _ ha)

theorem byteFrom_getElem (bs : List UInt8) (i : Nat) (h : i < bs.length) :
    byteFrom bs i = bs[i] := by
  simp [byteFrom, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem byteFrom_append_left (pref rest : List UInt8) (i : Nat) (h : i < pref.length) :
    byteFrom (pref ++ rest) i = pref[i] := by
  simp [byteFrom, List.getD_eq_getElem?_getD, List.getElem?_append_left h,
    List.getElem?_eq_getElem h]

theorem byteFrom_append_right (pref rest : List UInt8) (i : Nat) (h : pref.length ≤ i) :
    byteFrom (pref ++ rest) i = byteFrom rest (i - pref.length) := by
  simp [byteFrom, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem wordFrom_append_right (pref rest : List UInt8) (p : Nat) (h : pref.length ≤ p) :
    wordFrom (pref ++ rest) p = wordFrom rest (p - pref.length) := by
  unfold wordFrom
  refine foldl_congr ?_
  intro acc i _hi
  have : pref.length ≤ p + i := Nat.le_trans h (Nat.le_add_right _ _)
  have heq : p + i - pref.length = p - pref.length + i := by omega
  rw [byteFrom_append_right _ _ _ this, heq]

@[simp] theorem length_wordBytes (n : Nat) : (wordBytes n).length = 32 := by
  simp [wordBytes]

@[simp] theorem length_selectorBytes (n : Nat) : (selectorBytes n).length = 4 := by
  simp [selectorBytes]

theorem getElem_wordBytes (n i : Nat) (hi : i < 32) :
    (wordBytes n)[i] = UInt8.ofNat ((n >>> (8 * (31 - i))) % 256) := by
  simp [wordBytes, List.getElem_range]

theorem wordFrom_eq_foldl_bytes (bs : List UInt8) (p : Nat) :
    wordFrom bs p =
      ((List.range 32).map fun i => byteFrom bs (p + i)).foldl
        (fun (acc : U256) (b : UInt8) =>
          (acc <<< (8 : Nat)) ||| BitVec.ofNat 256 b.toNat) 0 := by
  unfold wordFrom
  have hgen : ∀ (n : Nat) (g : Nat → UInt8),
      (List.range n).foldl (fun (acc : U256) i =>
          (acc <<< (8 : Nat)) ||| BitVec.ofNat 256 (g i).toNat) (0 : U256) =
        ((List.range n).map g).foldl
          (fun (acc : U256) (b : UInt8) =>
            (acc <<< (8 : Nat)) ||| BitVec.ofNat 256 b.toNat) (0 : U256) := by
    intro n g
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.map_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil]
      rw [ih]
  exact hgen 32 (fun i => byteFrom bs (p + i))

/-- Copied from powdr `StateRel.bitvec_fold_eq`. -/
private theorem foldl_shift_or_toNat (l : List UInt8) :
    ∀ acc : U256, l.length ≤ 32 → acc.toNat < 256 ^ (32 - l.length) →
      (l.foldl (fun (acc : U256) b =>
          (acc <<< (8 : Nat)) ||| BitVec.ofNat 256 b.toNat) acc).toNat
        = l.foldl (fun (acc : Nat) b => acc * 256 + b.toNat) acc.toNat := by
  induction l with
  | nil => intro acc _ _; rfl
  | cons b l ih =>
    intro acc hlen hacc
    simp only [List.length_cons] at hlen hacc
    have hb : b.toNat < 256 := b.toNat_lt
    have hmul_lt : acc.toNat * 256 + b.toNat < 2 ^ 256 := by
      have h1 : acc.toNat * 256 + b.toNat < (acc.toNat + 1) * 256 := by omega
      have h2 : (acc.toNat + 1) * 256 ≤ 256 ^ (32 - (l.length + 1)) * 256 :=
        Nat.mul_le_mul_right 256 hacc
      have h32 : (256 : Nat) ^ 32 = 2 ^ 256 := pow256_32
      have hpow : 256 ^ (32 - (l.length + 1)) * 256 ≤ 256 ^ 32 := by
        rw [← Nat.pow_succ]
        exact Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hstep :
        ((acc <<< (8 : Nat)) ||| BitVec.ofNat 256 b.toNat).toNat
          = acc.toNat * 256 + b.toNat := by
      rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      rw [Nat.mod_eq_of_lt (show b.toNat < 2 ^ 256 from Nat.lt_trans hb (by decide))]
      rw [Nat.mod_eq_of_lt (show acc.toNat * 2 ^ 8 < 2 ^ 256 from by
        rw [pow2_8]; exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hmul_lt)]
      rw [pow2_8, Nat.mul_comm acc.toNat 256]
      exact (Nat.two_pow_add_eq_or_of_lt (show b.toNat < 2 ^ 8 from by omega) acc.toNat).symm
    rw [List.foldl_cons, ih _ (by omega) (by
      rw [hstep]
      have h1 : acc.toNat * 256 + b.toNat < (acc.toNat + 1) * 256 := by omega
      have hpow : 256 ^ (32 - (l.length + 1)) * 256 = 256 ^ (32 - l.length) := by
        rw [← Nat.pow_succ]
        congr 1
        omega
      have h2 : (acc.toNat + 1) * 256 ≤ 256 ^ (32 - l.length) := by
        rw [← hpow]
        exact Nat.mul_le_mul_right 256 hacc
      exact Nat.lt_of_lt_of_le h1 h2), hstep, List.foldl_cons]

theorem wordFrom_toNat_bytes (bs : List UInt8) (p : Nat) :
    (wordFrom bs p).toNat =
      ((List.range 32).map fun i => byteFrom bs (p + i)).foldl
        (fun acc b => acc * 256 + b.toNat) 0 := by
  rw [wordFrom_eq_foldl_bytes]
  simpa using foldl_shift_or_toNat
    ((List.range 32).map fun i => byteFrom bs (p + i)) 0 (by simp) (by simp)

theorem beFold_range (n k : Nat) (hn : n < 256 ^ k) :
    ((List.range k).map fun i => UInt8.ofNat ((n >>> (8 * (k - 1 - i))) % 256)).foldl
      (fun acc b => acc * 256 + b.toNat) 0 = n := by
  induction k generalizing n with
  | zero =>
    have : n = 0 := Nat.lt_one_iff.mp (by simpa using hn)
    simp [this]
  | succ k ih =>
    have hdiv : n / 256 < 256 ^ k :=
      Nat.div_lt_of_lt_mul (by
        rw [Nat.mul_comm, ← Nat.pow_succ]
        exact hn)
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    have hhead :
        ((List.range k).map fun i =>
            UInt8.ofNat ((n >>> (8 * ((k + 1) - 1 - i))) % 256)) =
          (List.range k).map fun i =>
            UInt8.ofNat (((n / 256) >>> (8 * (k - 1 - i))) % 256) := by
      apply List.map_congr_left
      intro i hi
      have hi' : i < k := List.mem_range.mp hi
      have hk : (k + 1) - 1 - i = k - i := by omega
      have hidx : 8 * (k - i) = 8 * (k - 1 - i) + 8 := by omega
      have : n >>> (8 * ((k + 1) - 1 - i)) = (n / 256) >>> (8 * (k - 1 - i)) := by
        rw [hk, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, hidx, Nat.pow_add,
          Nat.div_div_eq_div_mul, Nat.mul_comm (2 ^ (8 * (k - 1 - i))), pow2_8]
      rw [this]
    have hlast : (n >>> (8 * ((k + 1) - 1 - k))) % 256 = n % 256 := by
      have : (k + 1) - 1 - k = 0 := by omega
      simp [this]
    rw [hhead, ih _ hdiv, hlast]
    have hU : (UInt8.ofNat (n % 256)).toNat = n % 256 := by
      simp [UInt8.toNat_ofNat]
    rw [hU, Nat.mul_comm, Nat.div_add_mod]

theorem wordFrom_wordBytes (n : Nat) (hn : n < wordBound) :
    wordFrom (wordBytes n) 0 = BitVec.ofNat 256 n := by
  apply BitVec.eq_of_toNat_eq
  rw [wordFrom_toNat_bytes, toNat_ofNat_of_lt hn]
  have hfold := beFold_range n 32 (by rwa [pow256_32])
  have hbytes :
      (List.range 32).map (fun i => byteFrom (wordBytes n) (0 + i)) =
        (List.range 32).map fun i => UInt8.ofNat ((n >>> (8 * (31 - i))) % 256) := by
    apply List.map_congr_left
    intro i hi
    have hi' : i < 32 := List.mem_range.mp hi
    simp only [Nat.zero_add]
    rw [byteFrom_getElem _ i (by simpa using hi')]
    exact getElem_wordBytes n i hi'
  rw [hbytes]
  exact hfold

theorem wordFrom_wordBytes_cons (n : Nat) (rest : List UInt8) (hn : n < wordBound) :
    wordFrom (wordBytes n ++ rest) 0 = BitVec.ofNat 256 n := by
  refine Eq.trans ?_ (wordFrom_wordBytes n hn)
  unfold wordFrom
  refine foldl_congr ?_
  intro acc i hi
  have hi' : i < 32 := List.mem_range.mp hi
  have : i < (wordBytes n).length := by simpa using hi'
  simp only [Nat.zero_add]
  rw [byteFrom_append_left (wordBytes n) rest i this, byteFrom_getElem _ i this]

theorem length_flatMap_wordBytes (args : List Nat) :
    (args.flatMap wordBytes).length = 32 * args.length := by
  induction args with
  | nil => simp
  | cons _n rest ih =>
    simp [List.flatMap_cons, ih]
    omega

theorem wordFrom_flatMap_wordBytes (args : List Nat) (i : Nat)
    (hi : i < args.length) (hbound : ∀ n ∈ args, n < wordBound) :
    wordFrom (args.flatMap wordBytes) (32 * i) = BitVec.ofNat 256 args[i] := by
  induction args generalizing i with
  | nil => cases hi
  | cons n rest ih =>
    cases i with
    | zero =>
      simp only [List.flatMap_cons, List.getElem_cons_zero]
      exact wordFrom_wordBytes_cons n _ (hbound n (by simp))
    | succ i =>
      simp only [List.flatMap_cons]
      have hi' : i < rest.length := Nat.succ_lt_succ_iff.mp hi
      have hbound' : ∀ m ∈ rest, m < wordBound := fun m hm => hbound m (by simp [hm])
      rw [wordFrom_append_right (wordBytes n) _ (32 * (i + 1)) (by simp; omega)]
      simp only [length_wordBytes]
      have hsub : 32 * (i + 1) - 32 = 32 * i := by omega
      rw [hsub]
      simpa [List.getElem_cons_succ] using ih i hi' hbound'

theorem decodeArgs_fnCalldata (f : FnDef) (args : List Nat)
    (hk : f.kind ≠ .constructor)
    (hlen : args.length = f.params.length)
    (hbound : ∀ n ∈ args, n < wordBound) :
    decodeArgs f (fnCalldata f args) = args := by
  rw [decodeArgs_runtime hk]
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi _hi'
    simp only [List.getElem_map, List.getElem_range]
    have hiargs : i < args.length := by omega
    unfold fnCalldata
    have hpref : (selectorBytes f.selector).length ≤ 4 + 32 * i := by
      simp [length_selectorBytes]
    rw [wordFrom_append_right (selectorBytes f.selector) _ (4 + 32 * i) hpref]
    simp only [length_selectorBytes]
    have hsub : 4 + 32 * i - 4 = 32 * i := by omega
    rw [hsub, wordFrom_flatMap_wordBytes args i hiargs hbound,
      toNat_ofNat_of_lt (hbound args[i] (List.getElem_mem hiargs))]

theorem length_fnCalldata (f : FnDef) (args : List Nat) :
    (fnCalldata f args).length = 4 + 32 * args.length := by
  simp [fnCalldata, length_flatMap_wordBytes]
  omega

private theorem beFold_shift (xs : List UInt8) (acc : Nat) :
    xs.foldl (fun a x => a * 256 + x.toNat) acc =
      acc * 256 ^ xs.length + xs.foldl (fun a x => a * 256 + x.toNat) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons, Nat.pow_succ, Nat.zero_mul, Nat.zero_add]
    rw [ih (acc * 256 + x.toNat), ih x.toNat, Nat.add_mul, Nat.mul_assoc acc 256,
      Nat.mul_comm (256 : Nat) (256 ^ xs.length), Nat.add_assoc]

private theorem beFold_lt (bs : List UInt8) :
    bs.foldl (fun acc b => acc * 256 + b.toNat) 0 < 256 ^ bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    have hb : b.toNat < 256 := b.toNat_lt
    simp only [List.foldl_cons, List.length_cons, Nat.pow_succ, Nat.zero_mul, Nat.zero_add]
    rw [beFold_shift, Nat.mul_comm (256 ^ bs.length) 256]
    calc
      b.toNat * 256 ^ bs.length + bs.foldl (fun a x => a * 256 + x.toNat) 0
        < b.toNat * 256 ^ bs.length + 256 ^ bs.length := Nat.add_lt_add_left ih _
      _ = (b.toNat + 1) * 256 ^ bs.length := by rw [Nat.succ_mul]
      _ ≤ 256 * 256 ^ bs.length := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hb)

private theorem beFold_append (a b : List UInt8) :
    (a ++ b).foldl (fun acc x => acc * 256 + x.toNat) 0 =
      a.foldl (fun acc x => acc * 256 + x.toNat) 0 * 256 ^ b.length +
        b.foldl (fun acc x => acc * 256 + x.toNat) 0 := by
  rw [List.foldl_append, beFold_shift]

theorem selectorBytes_beFold (sel : Nat) (hsel : sel < 2 ^ 32) :
    (selectorBytes sel).foldl (fun acc b => acc * 256 + b.toNat) 0 = sel := by
  simpa [selectorBytes] using beFold_range sel 4 (by rwa [pow256_4])

theorem selector_fnCalldata (f : FnDef) (args : List Nat) :
    calldataSelector (fnCalldata f args) = f.selector := by
  have hsel : f.selector < 2 ^ 32 := selectorOf_lt f.name f.params
  unfold calldataSelector fnCalldata
  rw [wordFrom_toNat_bytes]
  set rest := args.flatMap wordBytes
  have hmap :
      (List.range 32).map (fun i =>
          byteFrom (selectorBytes f.selector ++ rest) (0 + i)) =
        selectorBytes f.selector ++
          (List.range 28).map fun i => byteFrom rest i := by
    apply List.ext_getElem
    · simp
    · intro i hi _
      have hi' : i < 32 := by simpa using hi
      simp only [List.getElem_map, List.getElem_range, Nat.zero_add]
      by_cases h4 : i < 4
      · rw [byteFrom_append_left _ _ i (by simp [h4]),
          List.getElem_append_left (by simp [h4])]
      · have hge : 4 ≤ i := Nat.le_of_not_gt h4
        rw [byteFrom_append_right _ _ i (by simpa using hge),
          List.getElem_append_right (by simp; omega)]
        simp [length_selectorBytes]
  rw [hmap, beFold_append, selectorBytes_beFold _ hsel]
  set r := ((List.range 28).map fun i => byteFrom rest i).foldl
    (fun acc b => acc * 256 + b.toNat) 0
  have hr : r < 256 ^ 28 := by
    simpa [r] using beFold_lt ((List.range 28).map fun i => byteFrom rest i)
  simp [List.length_map, List.length_range]
  rw [Nat.shiftRight_eq_div_pow, pow256_28]
  have hpos : 0 < 2 ^ 224 := Nat.two_pow_pos 224
  have hr' : r < 2 ^ 224 := by rwa [← pow256_28]
  have hdiv := Nat.add_mul_div_right r f.selector hpos
  have hr0 : r / 2 ^ 224 = 0 := Nat.div_eq_of_lt hr'
  change (f.selector * 2 ^ 224 + r) / 2 ^ 224 = f.selector
  rw [Nat.add_comm, hdiv, hr0, Nat.zero_add]

theorem find?_eq_of_unique {α} {p : α → Bool} {l : List α} {a : α}
    (hmem : a ∈ l) (hp : p a = true)
    (huniq : ∀ x ∈ l, p x = true → x = a) :
    l.find? p = some a := by
  induction l with
  | nil => cases hmem
  | cons x xs ih =>
    simp only [List.find?]
    split
    · next hx =>
      have : x = a := huniq x (by simp) (by simp [hx])
      subst this
      rfl
    · next hx =>
      have hne : x ≠ a := by
        intro h; subst h; simp [hp] at hx
      simp only [List.mem_cons] at hmem
      rcases hmem with hxa | hmem'
      · exact (hne hxa.symm).elim
      · exact ih hmem' fun y hy hy' => huniq y (List.mem_cons_of_mem _ hy) hy'

theorem pairwise_selector_unique {l : List FnDef}
    (h : (l.map FnDef.selector).Pairwise (fun a b => a ≠ b))
    {x y : FnDef} (hx : x ∈ l) (hy : y ∈ l) (heq : x.selector = y.selector) : x = y := by
  induction l with
  | nil => cases hx
  | cons z zs ih =>
    simp only [List.map_cons, List.pairwise_cons] at h
    rcases h with ⟨hne, htail⟩
    simp only [List.mem_cons] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · subst hx; subst hy; rfl
    · subst hx
      have : y.selector ∈ zs.map FnDef.selector := List.mem_map.mpr ⟨y, hy, rfl⟩
      exact absurd heq (hne y.selector this)
    · subst hy
      have : x.selector ∈ zs.map FnDef.selector := List.mem_map.mpr ⟨x, hx, rfl⟩
      exact absurd heq.symm (hne x.selector this)
    · exact ih htail hx hy

theorem selectedFn_fnCalldata (c : ContractDef) (f : FnDef) (args : List Nat)
    (hf : f ∈ c.functions)
    (hnd : selectorsNodup c = true)
    (hlen : args.length = f.params.length) :
    selectedFn c (fnCalldata f args) = some f := by
  have hlen' : ¬ (fnCalldata f args).length < 4 := by
    rw [length_fnCalldata]; omega
  have hsel : calldataSelector (fnCalldata f args) = f.selector := selector_fnCalldata f args
  have hpair := (selectorsNodup_iff c).mp hnd
  have hfind :
      c.functions.find? (fun g => decide (g.selector = calldataSelector (fnCalldata f args))) =
        some f := by
    rw [hsel]
    refine find?_eq_of_unique hf (by simp) ?_
    intro g hg hg'
    exact pairwise_selector_unique hpair hg hf (by simpa using hg')
  have hlong : ¬ (fnCalldata f args).length < 4 + 32 * f.params.length := by
    rw [length_fnCalldata, hlen]; omega
  simp [selectedFn, hlen', hfind, hlong]

end Lsc.Compiler

