import Lsc3.Contract
import Lsc3.EVM.Step
import Mathlib.Tactic.Ring

/-!
# ABI call wrapper around `Lsc3.EVM.run`

Used by end-to-end tests and (later) `bytecode_ok` certificates: pack calldata, run the
machine, decode a single returned word.
-/

namespace Lsc3.Compile.Exec

open Lsc3 Lsc3.EVM

def packWord (n : Nat) : List UInt8 :=
  (List.range 32).map fun i => UInt8.ofNat ((n / (256 ^ (31 - i))) % 256)

def packCall (sel : Nat) (args : List Nat := []) : List UInt8 :=
  let selBytes := (List.range 4).map fun i => UInt8.ofNat ((sel / (256 ^ (3 - i))) % 256)
  selBytes ++ args.flatMap packWord

def decodeWord (data : List UInt8) : Nat :=
  (List.range (min 32 data.length)).foldl (fun acc i => acc * 256 + UInt8.toNat data[i]!) 0

def mkEnv (code calldata : List UInt8) (caller : Nat := 0) : Env :=
  { code := code, calldata := calldata, address := 1, caller := caller, callvalue := 0,
    timestamp := 0, number := 0 }

inductive Outcome
  | stop (storage : Storage)
  | ret (word : Nat) (storage : Storage)
  | revert
  | fail (e : Exception)
  | timeout

def exec (code calldata : List UInt8) (storage : Storage) (caller : Nat := 0)
    (fuel : Nat := 100000) : Outcome :=
  match run fuel (mkEnv code calldata caller) { storage := storage } with
  | none => .timeout
  | some (Halt.stop, s) => .stop s.storage
  | some (Halt.ret data, s) => .ret (decodeWord data) s.storage
  | some (Halt.revert _, _) => .revert
  | some (Halt.exceptional e, _) => .fail e

def slot0 (n : Nat) : Storage := fun k => if k = 0 then n else 0

/-- Run and return the raw halt + state (logs, memory, storage). -/
def execState (code calldata : List UInt8) (storage : Storage) (caller : Nat := 0)
    (fuel : Nat := 100000) : Option (Halt × State) :=
  run fuel (mkEnv code calldata caller) { storage := storage }

/-- Execute creation bytecode; `some runtime` iff the preamble `RETURN`s the payload. -/
def deploy (code : List UInt8) (fuel : Nat := 100000) : Option (List UInt8) :=
  match run fuel (mkEnv code []) { storage := fun _ => 0 } with
  | some (Halt.ret data, _) => some data
  | _ => none

@[simp] theorem decodeWord_nil : decodeWord [] = 0 := rfl

@[simp] theorem packWord_length (n : Nat) : (packWord n).length = 32 := by
  simp [packWord]

theorem length_flatMap_packWord (args : List Nat) :
    (args.flatMap packWord).length = 32 * args.length := by
  induction args with
  | nil => simp
  | cons n ns ih =>
    simp [packWord_length, ih]
    omega

@[simp] theorem packCall_length (sel : Nat) (args : List Nat) :
    (packCall sel args).length = 4 + 32 * args.length := by
  simp only [packCall, List.length_append, List.length_map, List.length_range,
    length_flatMap_packWord]

theorem pow256_32 : 256 ^ 32 = wordBound := by
  change (2 ^ 8) ^ 32 = 2 ^ 256
  rw [← Nat.pow_mul]

theorem packWord_getElem (n i : Nat) (hi : i < 32) :
    (packWord n)[i]'(by simp [packWord_length]; exact hi) =
      UInt8.ofNat ((n / 256 ^ (31 - i)) % 256) := by
  simp [packWord, List.getElem_map, List.getElem_range]

private theorem toNat_ofNat_mod256 (t : Nat) :
    (UInt8.ofNat (t % 256)).toNat = t % 256 := by
  change (t % 256) % 256 = t % 256
  rw [Nat.mod_mod]

private theorem mul_add_mod_mul (a r m b : Nat) (hr : r < b) :
    (a * b + r) % (m * b) = (a % m) * b + r := by
  have hx : a * b + r = (a / m) * (m * b) + ((a % m) * b + r) := by
    have hdiv := Nat.div_add_mod a m
    calc
      a * b + r = (m * (a / m) + a % m) * b + r := by rw [hdiv]
      _ = m * (a / m) * b + (a % m) * b + r := by ring
      _ = (a / m) * (m * b) + ((a % m) * b + r) := by ring
  have hrem : a % m * b + r < m * b ∨ m = 0 := by
    by_cases hm : m = 0
    · exact Or.inr hm
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      have hb : 0 < b := Nat.zero_lt_of_lt hr
      have h1 : a % m ≤ m - 1 := Nat.le_pred_of_lt (Nat.mod_lt a hmpos)
      have h2 : r ≤ b - 1 := Nat.le_pred_of_lt hr
      refine Or.inl ?_
      calc
        a % m * b + r ≤ (m - 1) * b + (b - 1) := Nat.add_le_add (Nat.mul_le_mul_right b h1) h2
        _ = m * b - 1 := by
          cases m with
          | zero => contradiction
          | succ m =>
            cases b with
            | zero => omega
            | succ b =>
              simp [Nat.add_mul, Nat.mul_add]
              omega
        _ < m * b := Nat.sub_lt (Nat.mul_pos hmpos hb) (by decide)
  rw [hx, Nat.add_comm, Nat.add_mul_mod_self_right]
  cases hrem with
  | inl hlt => exact Nat.mod_eq_of_lt hlt
  | inr hm =>
    subst hm
    simp [Nat.mod_zero]

private theorem div256_mod (x m : Nat) :
    x / 256 % m * 256 + x % 256 = x % (m * 256) := by
  calc
    x / 256 % m * 256 + x % 256
        = (x / 256 * 256 + x % 256) % (m * 256) :=
          (mul_add_mod_mul (x / 256) (x % 256) m 256 (Nat.mod_lt x (by decide))).symm
    _ = x % (m * 256) := by rw [Nat.mul_comm (x / 256), Nat.div_add_mod]

theorem packWord_high (n k : Nat) (hk : k ≤ 32) :
    (List.range k).foldl (fun acc i => acc * 256 + n / 256 ^ (31 - i) % 256) 0 =
      n / 256 ^ (32 - k) % 256 ^ k := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    have hk' : k ≤ 32 := Nat.le_of_succ_le hk
    have hk32 : k < 32 := Nat.lt_of_succ_le hk
    rw [List.range_succ, List.foldl_append, ih hk']
    simp only [List.foldl_cons, List.foldl_nil]
    have hpow : 256 ^ (32 - k) = 256 ^ (31 - k) * 256 := by
      have : 32 - k = (31 - k) + 1 := by omega
      rw [this, Nat.pow_succ, Nat.mul_comm]
    have hx : n / 256 ^ (32 - k) = n / 256 ^ (31 - k) / 256 := by
      rw [hpow, Nat.div_div_eq_div_mul]
    calc
      n / 256 ^ (32 - k) % 256 ^ k * 256 + n / 256 ^ (31 - k) % 256
          = n / 256 ^ (31 - k) / 256 % 256 ^ k * 256 + n / 256 ^ (31 - k) % 256 := by
            rw [hx]
      _ = n / 256 ^ (31 - k) % (256 ^ k * 256) := div256_mod _ _
      _ = n / 256 ^ (31 - k) % 256 ^ (k + 1) := by
            rw [Nat.pow_succ, Nat.mul_comm]
      _ = n / 256 ^ (32 - (k + 1)) % 256 ^ (k + 1) := by
            rw [show 32 - (k + 1) = 31 - k from Nat.succ_sub_succ_eq_sub 31 k]

/-- Big-endian 32-byte packing is inverse to `decodeWord`, modulo `2^256`. -/
theorem decodeWord_packWord (n : Nat) : decodeWord (packWord n) = n % wordBound := by
  have hlen : (packWord n).length = 32 := packWord_length n
  have hfold : ∀ k, k ≤ 32 →
      (List.range k).foldl (fun acc i => acc * 256 + UInt8.toNat (packWord n)[i]!) 0 =
        (List.range k).foldl (fun acc i => acc * 256 + n / 256 ^ (31 - i) % 256) 0 := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hk32 : k < 32 := Nat.lt_of_succ_le hk
      have hk' : k ≤ 32 := Nat.le_of_lt hk32
      rw [List.range_succ, List.foldl_append, List.foldl_append, ih hk']
      simp only [List.foldl_cons, List.foldl_nil]
      have hget :
          (packWord n)[k]! = (packWord n)[k]'(by simp [packWord_length]; exact hk32) :=
        getElem!_pos (packWord n) k (by simp [packWord_length]; exact hk32)
      rw [hget, packWord_getElem n k hk32, toNat_ofNat_mod256]
  simp only [decodeWord, hlen, Nat.min_self]
  rw [hfold 32 (by decide), packWord_high n 32 (by decide), Nat.sub_self, Nat.pow_zero,
    Nat.div_one, pow256_32]

theorem decodeWord_packWord_of_lt {n : Nat} (h : n < wordBound) :
    decodeWord (packWord n) = n := by
  rw [decodeWord_packWord, Nat.mod_eq_of_lt h]

@[simp] theorem decodeWord_packWord_zero : decodeWord (packWord 0) = 0 := rfl

@[simp] theorem decodeWord_packWord_one : decodeWord (packWord 1) = 1 := rfl

@[simp] theorem decodeWord_packWord_42 : decodeWord (packWord 42) = 42 := rfl

theorem packSel_high (n k : Nat) (hk : k ≤ 4) :
    (List.range k).foldl (fun acc i => acc * 256 + n / 256 ^ (3 - i) % 256) 0 =
      n / 256 ^ (4 - k) % 256 ^ k := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    have hk' : k ≤ 4 := Nat.le_of_succ_le hk
    have hk4 : k < 4 := Nat.lt_of_succ_le hk
    rw [List.range_succ, List.foldl_append, ih hk']
    simp only [List.foldl_cons, List.foldl_nil]
    have hpow : 256 ^ (4 - k) = 256 ^ (3 - k) * 256 := by
      have : 4 - k = (3 - k) + 1 := by omega
      rw [this, Nat.pow_succ, Nat.mul_comm]
    have hx : n / 256 ^ (4 - k) = n / 256 ^ (3 - k) / 256 := by
      rw [hpow, Nat.div_div_eq_div_mul]
    calc
      n / 256 ^ (4 - k) % 256 ^ k * 256 + n / 256 ^ (3 - k) % 256
          = n / 256 ^ (3 - k) / 256 % 256 ^ k * 256 + n / 256 ^ (3 - k) % 256 := by
            rw [hx]
      _ = n / 256 ^ (3 - k) % (256 ^ k * 256) := div256_mod _ _
      _ = n / 256 ^ (3 - k) % 256 ^ (k + 1) := by
            rw [Nat.pow_succ, Nat.mul_comm]
      _ = n / 256 ^ (4 - (k + 1)) % 256 ^ (k + 1) := by
            rw [show 4 - (k + 1) = 3 - k from Nat.succ_sub_succ_eq_sub 3 k]

private theorem foldl_horner (byte : Nat → Nat) (m acc : Nat) :
    (List.range m).foldl (fun a i => a * 256 + byte i) acc =
      acc * 256 ^ m + (List.range m).foldl (fun a i => a * 256 + byte i) 0 := by
  induction m generalizing acc with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih]
    ring

private theorem foldl_range_add (byte : Nat → Nat) (n m : Nat) :
    (List.range (n + m)).foldl (fun a i => a * 256 + byte i) 0 =
      (List.range n).foldl (fun a i => a * 256 + byte i) 0 * 256 ^ m +
        (List.range m).foldl (fun a i => a * 256 + byte (n + i)) 0 := by
  rw [List.range_add, List.foldl_append, List.foldl_map]
  exact foldl_horner (fun i => byte (n + i)) m _

private theorem mul_add_lt {a b n m : Nat} (ha : a < n) (hb : b < m) :
    a * m + b < n * m := by
  have : a + 1 ≤ n := Nat.succ_le_of_lt ha
  calc
    a * m + b < a * m + m := Nat.add_lt_add_left hb _
    _ = (a + 1) * m := by ring
    _ ≤ n * m := Nat.mul_le_mul_right m this

private theorem fold_lt256 (byte : Nat → Nat) (hbyte : ∀ i, byte i < 256) (k : Nat) :
    (List.range k).foldl (fun acc i => acc * 256 + byte i) 0 < 256 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [Nat.pow_succ]
    exact mul_add_lt ih (hbyte k)

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

private theorem pow256_4 : 256 ^ 4 = 2 ^ 32 := by
  change (2 ^ 8) ^ 4 = 2 ^ 32
  rw [← Nat.pow_mul]

private theorem uint8_toNat_lt (b : UInt8) : b.toNat < 256 :=
  b.toFin.isLt

theorem packCall_prefix (sel : Nat) (args : List Nat) (i : Nat) (hi : i < 4) :
    (packCall sel args)[i]'(by simp [packCall_length]; omega) =
      UInt8.ofNat ((sel / 256 ^ (3 - i)) % 256) := by
  have hleft : i < ((List.range 4).map fun j =>
      UInt8.ofNat ((sel / (256 ^ (3 - j))) % 256)).length := by
    simpa using hi
  simp only [packCall, List.getElem_append_left hleft, List.getElem_map, List.getElem_range]

private theorem pow256_28 : 256 ^ 28 = 2 ^ 224 := by
  change (2 ^ 8) ^ 28 = 2 ^ 224
  rw [← Nat.pow_mul]

/-- The first 32 calldata bytes are `selector || payload`; `SHR 224` recovers the selector. -/
theorem shrW_calldataLoad_packCall (sel : Nat) (args : List Nat) :
    shrW 0xE0 (calldataLoad (packCall sel args) 0) = sel % 2 ^ 32 := by
  set data := packCall sel args with hdata
  let b (i : Nat) : Nat := if i < data.length then (data[i]!).toNat else 0
  have hbnd : ∀ i, b i < 256 := by
    intro i
    by_cases h : i < data.length
    · simp only [b, h, ↓reduceIte]
      rw [getElem!_pos data i h]
      exact uint8_toNat_lt _
    · simp [b, h]
  have hlen4 : 4 ≤ data.length := by
    simp [data, packCall_length]
  have hfold :
      (List.range 32).foldl (fun acc i =>
        acc * 256 + (if 0 + i < data.length then (data[0 + i]!).toNat else 0)) 0 =
        (List.range 32).foldl (fun acc i => acc * 256 + b i) 0 := by
    refine foldl_range_eq 32 _ _ ?_ 0
    intro acc i hi
    simp [b]
  have hlt : (List.range 32).foldl (fun acc i => acc * 256 + b i) 0 < wordBound :=
    Nat.lt_of_lt_of_eq (fold_lt256 b hbnd 32) pow256_32
  have hhigh :
      (List.range 4).foldl (fun acc i => acc * 256 + b i) 0 = sel % 2 ^ 32 := by
    have hbytes :
        (List.range 4).foldl (fun acc i => acc * 256 + b i) 0 =
          (List.range 4).foldl (fun acc i => acc * 256 + sel / 256 ^ (3 - i) % 256) 0 := by
      refine foldl_range_eq 4 _ _ ?_ 0
      intro acc i hi
      have hi' : i < data.length := Nat.lt_of_lt_of_le hi hlen4
      simp only [b, hi', ↓reduceIte]
      rw [getElem!_pos data i hi', packCall_prefix sel args i hi, toNat_ofNat_mod256]
    rw [hbytes, packSel_high sel 4 (by decide), Nat.sub_self, Nat.pow_zero, Nat.div_one,
      pow256_4]
  have hlow :
      (List.range 28).foldl (fun acc i => acc * 256 + b (4 + i)) 0 < 256 ^ 28 :=
    fold_lt256 (fun i => b (4 + i)) (fun i => hbnd (4 + i)) 28
  have hsplit := foldl_range_add b 4 28
  simp only [calldataLoad]
  rw [hfold, wrap_eq_of_lt hlt]
  rw [show List.range 32 = List.range (4 + 28) from rfl, hsplit, hhigh]
  have h224 : ¬ (0xE0 : Nat) ≥ 256 := by decide
  simp only [shrW, h224, ↓reduceIte, Nat.shiftRight_eq_div_pow]
  rw [Nat.add_comm, ← pow256_28, Nat.add_mul_div_right _ _ (by decide : 0 < 256 ^ 28)]
  rw [Nat.div_eq_of_lt hlow, Nat.zero_add]

theorem packCall_arg_getElem (sel arg : Nat) (i : Nat) (hi : i < 32) :
    (packCall sel [arg])[4 + i]'(by simp [packCall_length]; omega) =
      (packWord arg)[i]'(by simp [packWord_length]; exact hi) := by
  simp only [packCall, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hle : ((List.range 4).map fun j =>
      UInt8.ofNat ((sel / (256 ^ (3 - j))) % 256)).length ≤ 4 + i := by
    simp
  rw [List.getElem_append_right hle]
  simp

/-- ABI word at calldata offset 4 of `packCall sel [arg]`. -/
theorem calldataLoad_packCall_arg (sel arg : Nat) :
    calldataLoad (packCall sel [arg]) 4 = wrap arg := by
  set data := packCall sel [arg]
  have hlen : ∀ i, i < 32 → 4 + i < data.length := by
    intro i hi
    simp [data, packCall_length]; omega
  have hfold :
      (List.range 32).foldl (fun acc i =>
        acc * 256 + (if 4 + i < data.length then (data[4 + i]!).toNat else 0)) 0 =
      (List.range 32).foldl (fun acc i => acc * 256 + (packWord arg)[i]!.toNat) 0 := by
    refine foldl_range_eq 32 _ _ ?_ 0
    intro acc i hi
    have hi' := hlen i hi
    simp only [hi', ↓reduceIte]
    rw [getElem!_pos data (4 + i) hi', packCall_arg_getElem sel arg i hi]
    rw [getElem!_pos (packWord arg) i (by simp [packWord_length]; exact hi)]
  have hdecode :
      (List.range 32).foldl (fun acc i => acc * 256 + (packWord arg)[i]!.toNat) 0 =
        arg % wordBound := by
    have hlen32 : (packWord arg).length = 32 := packWord_length arg
    simpa [decodeWord, hlen32, Nat.min_self] using decodeWord_packWord arg
  simp only [calldataLoad]
  rw [hfold, hdecode]
  simp [wrap]

/-- Word-valued `Tx.run` vs machine `Outcome`. Revert/panic both map to a failing outcome. -/
def agreesWord {S E ε} (o : Outcome) (r : Except (Err ε) (Nat × World S E)) : Prop :=
  match o, r with
  | .ret w _, .ok (v, _) => w = v
  | .revert, .error _ => True
  | .fail _, .error (.arith _) => True
  | _, _ => False

/-- Unit-valued `Tx.run` vs machine `Outcome`. -/
def agreesUnit {S E ε} (o : Outcome) (r : Except (Err ε) (Unit × World S E)) : Prop :=
  match o, r with
  | .stop _, .ok _ => True
  | .revert, .error _ => True
  | .fail _, .error (.arith _) => True
  | _, _ => False

end Lsc3.Compile.Exec
