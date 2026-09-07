import Lsc.Compiler.Proof.MemFootprint
import Lsc.Compiler.Proof.Words
import YulEvmCompiler.Optimizer.Spec.MemoryGuard

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-!
`staticSafeOp` of literal pointer/size arguments implies `OpMemorySafe`.
-/

namespace Lsc.Compiler

open Lsc hiding Op Stmt
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer

variable {calls : ExternalCalls} {creates : ExternalCreates}
variable {base reserved : Nat}

local notation "D" => evmWithExternal calls creates ExternalGas.any

/-! ## Literal evaluation -/

theorem evalExpr_lit {funs : FunEnv D} {V : VEnv D} {st : EvmState} {n : Nat}
    {r : EResult D} (h : EvalExpr D funs V st (lit n) r) :
    r = .vals [BitVec.ofNat 256 n] st := by
  cases h
  rfl

theorem evalArgs_cons_vals {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {e : YExpr} {rest : List YExpr} {vs : List U256} {st' : EvmState}
    (h : EvalArgs D funs V st (e :: rest) (.vals vs st')) :
    ∃ restvals st1 v,
      vs = v :: restvals ∧
      EvalArgs D funs V st rest (.vals restvals st1) ∧
      EvalExpr D funs V st1 e (.vals [v] st') := by
  cases h with
  | argsCons hrest hhead => exact ⟨_, _, _, rfl, hrest, hhead⟩

theorem evalArgs_length {funs : FunEnv D} {V : VEnv D} {st st' : EvmState}
    {args : List YExpr} {vs : List U256}
    (h : EvalArgs D funs V st args (.vals vs st')) :
    vs.length = args.length := by
  induction args generalizing st vs st' with
  | nil =>
    cases h
    rfl
  | cons e rest ih =>
    obtain ⟨restvals, st1, v, hvs, hrest, _⟩ := evalArgs_cons_vals h
    subst vs
    simpa using ih hrest

theorem evalArgs_nth_lit {funs : FunEnv D} {V : VEnv D} {st st' : EvmState}
    {args : List YExpr} {vs : List U256} {i n : Nat}
    (hi : args[i]? = some (lit n))
    (h : EvalArgs D funs V st args (.vals vs st')) :
    vs[i]? = some (BitVec.ofNat 256 n) := by
  induction args generalizing i st vs st' with
  | nil => simp at hi
  | cons e rest ih =>
    obtain ⟨restvals, st1, v, hvs, hrest, hhead⟩ := evalArgs_cons_vals h
    subst vs
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero] at hi ⊢
      cases hi
      have hr := evalExpr_lit hhead
      injection hr with hlist _
      injection hlist with hv
      subst hv
      rfl
    | succ i =>
      simpa using ih hi hrest

theorem toNat_ptr {p k : Nat} (hbase : base < wordBound) (h : p + k ≤ base) :
    (BitVec.ofNat 256 p).toNat = p :=
  toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right p k) h) hbase)

theorem toNat_len {p k : Nat} (hbase : base < wordBound) (h : p + k ≤ base) :
    (BitVec.ofNat 256 k).toNat = k :=
  toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left k p) h) hbase)

theorem litNat?_some {e : YExpr} {n : Nat} (h : litNat? e = some n) : e = lit n := by
  cases e with
  | lit l =>
    cases l with
    | number n' =>
      simp [litNat?, lit] at h ⊢
      exact h
    | bool _ => simp [litNat?] at h
    | string _ => simp [litNat?] at h
  | var _ => simp [litNat?] at h
  | builtin _ _ => simp [litNat?] at h
  | call _ _ => simp [litNat?] at h

theorem list_of_length_1 {α} {l : List α} (h : l.length = 1) : ∃ a, l = [a] := by
  cases l with
  | nil => simp at h
  | cons a as =>
    cases as with
    | nil => exact ⟨a, rfl⟩
    | cons _ _ => simp at h

theorem list_of_length_2 {α} {l : List α} (h : l.length = 2) :
    ∃ a b, l = [a, b] := by
  cases l with
  | nil => simp at h
  | cons a as =>
    cases as with
    | nil => simp at h
    | cons b bs =>
      cases bs with
      | nil => exact ⟨a, b, rfl⟩
      | cons _ _ => simp at h

theorem list_of_length_3 {α} {l : List α} (h : l.length = 3) :
    ∃ a b c, l = [a, b, c] := by
  cases l with
  | nil => simp at h
  | cons a as =>
    obtain ⟨b, c, rfl⟩ := list_of_length_2 (by simpa using h)
    exact ⟨a, b, c, rfl⟩

theorem list_of_length_4 {α} {l : List α} (h : l.length = 4) :
    ∃ a b c d, l = [a, b, c, d] := by
  cases l with
  | nil => simp at h
  | cons a as =>
    obtain ⟨b, c, d, rfl⟩ := list_of_length_3 (by simpa using h)
    exact ⟨a, b, c, d, rfl⟩

theorem list_of_length_5 {α} {l : List α} (h : l.length = 5) :
    ∃ a b c d e, l = [a, b, c, d, e] := by
  cases l with
  | nil => simp at h
  | cons a as =>
    obtain ⟨b, c, d, e, rfl⟩ := list_of_length_4 (by simpa using h)
    exact ⟨a, b, c, d, e, rfl⟩

theorem list_of_length_6 {α} {l : List α} (h : l.length = 6) :
    ∃ a b c d e f, l = [a, b, c, d, e, f] := by
  cases l with
  | nil => simp at h
  | cons a as =>
    obtain ⟨b, c, d, e, f, rfl⟩ := list_of_length_5 (by simpa using h)
    exact ⟨a, b, c, d, e, f, rfl⟩

theorem list_of_length_7 {α} {l : List α} (h : l.length = 7) :
    ∃ a b c d e f g, l = [a, b, c, d, e, f, g] := by
  cases l with
  | nil => simp at h
  | cons a as =>
    obtain ⟨b, c, d, e, f, g, rfl⟩ := list_of_length_6 (by simpa using h)
    exact ⟨a, b, c, d, e, f, g, rfl⟩

theorem range_of_two_lits {funs : FunEnv D} {V : VEnv D} {st st' : EvmState}
    {pE nE : YExpr} {p n : U256}
    (hbase : base < wordBound)
    (hs : (match litNat? pE, litNat? nE with
      | some p, some n => rangeBelow base p n
      | _, _ => false) = true)
    (h : EvalArgs D funs V st [pE, nE] (.vals [p, n] st')) :
    RangeOutside base reserved p.toNat n.toNat := by
  cases hp : litNat? pE <;> cases hn : litNat? nE
  · simp [hp, hn] at hs
  · simp [hp, hn] at hs
  · simp [hp, hn] at hs
  · next pn nn =>
    simp [hp, hn, rangeBelow_iff] at hs
    have := litNat?_some hp; subst pE
    have := litNat?_some hn; subst nE
    have h0 := evalArgs_nth_lit (i := 0) rfl h
    have h1 := evalArgs_nth_lit (i := 1) rfl h
    simp at h0 h1
    cases h0; cases h1
    simp [toNat_ptr (k := nn) hbase hs, toNat_len (p := pn) hbase hs]
    exact rangeBelow_outside hs

theorem range_of_mload {funs : FunEnv D} {V : VEnv D} {st st' : EvmState}
    {pE : YExpr} {p : U256} {k : Nat}
    (hbase : base < wordBound)
    (hs : (match litNat? pE with
      | some p => rangeBelow base p k
      | none => false) = true)
    (h : EvalArgs D funs V st [pE] (.vals [p] st')) :
    RangeOutside base reserved p.toNat k := by
  cases hp : litNat? pE
  · simp [hp] at hs
  · next pn =>
    simp [hp, rangeBelow_iff] at hs
    have := litNat?_some hp; subst pE
    have h0 := evalArgs_nth_lit (i := 0) rfl h
    simp at h0; cases h0
    simp [toNat_ptr (k := k) hbase hs]
    exact rangeBelow_outside hs

theorem range_of_mstore {funs : FunEnv D} {V : VEnv D} {st st' : EvmState}
    {pE vE : YExpr} {p v : U256} {k : Nat}
    (hbase : base < wordBound)
    (hs : (match litNat? pE with
      | some p => rangeBelow base p k
      | none => false) = true)
    (h : EvalArgs D funs V st [pE, vE] (.vals [p, v] st')) :
    RangeOutside base reserved p.toNat k := by
  cases hp : litNat? pE
  · simp [hp] at hs
  · next pn =>
    simp [hp, rangeBelow_iff] at hs
    have := litNat?_some hp; subst pE
    have h0 := evalArgs_nth_lit (i := 0) rfl h
    simp at h0; cases h0
    simp [toNat_ptr (k := k) hbase hs]
    exact rangeBelow_outside hs

theorem range_of_log {funs : FunEnv D} {V : VEnv D} {st st' : EvmState}
    {pE nE : YExpr} {rest : List YExpr} {p n : U256} {tail : List U256}
    (hbase : base < wordBound)
    (hs : (match litNat? pE, litNat? nE with
      | some p, some n => rangeBelow base p n
      | _, _ => false) = true)
    (h : EvalArgs D funs V st (pE :: nE :: rest) (.vals (p :: n :: tail) st')) :
    RangeOutside base reserved p.toNat n.toNat := by
  cases hp : litNat? pE <;> cases hn : litNat? nE
  · simp [hp, hn] at hs
  · simp [hp, hn] at hs
  · simp [hp, hn] at hs
  · next pn nn =>
    simp [hp, hn, rangeBelow_iff] at hs
    have := litNat?_some hp; subst pE
    have := litNat?_some hn; subst nE
    have h0 := evalArgs_nth_lit (i := 0) rfl h
    have h1 := evalArgs_nth_lit (i := 1) rfl h
    simp at h0 h1
    cases h0; cases h1
    simp [toNat_ptr (k := nn) hbase hs, toNat_len (p := pn) hbase hs]
    exact rangeBelow_outside hs

theorem range_of_dst_n {funs : FunEnv D} {V : VEnv D} {st st' : EvmState}
    {dstE srcE nE : YExpr} {dst src n : U256}
    (hbase : base < wordBound)
    (hs : (match litNat? dstE, litNat? nE with
      | some d, some k => rangeBelow base d k
      | _, _ => false) = true)
    (h : EvalArgs D funs V st [dstE, srcE, nE] (.vals [dst, src, n] st')) :
    RangeOutside base reserved dst.toNat n.toNat := by
  cases hd : litNat? dstE <;> cases hn : litNat? nE
  · simp [hd, hn] at hs
  · simp [hd, hn] at hs
  · simp [hd, hn] at hs
  · next dsz nsz =>
    simp [hd, hn, rangeBelow_iff] at hs
    have := litNat?_some hd; subst dstE
    have := litNat?_some hn; subst nE
    have h0 := evalArgs_nth_lit (i := 0) rfl h
    have h2 := evalArgs_nth_lit (i := 2) rfl h
    simp at h0 h2
    cases h0; cases h2
    simp [toNat_ptr (k := nsz) hbase hs, toNat_len (p := dsz) hbase hs]
    exact rangeBelow_outside hs

theorem range_of_mcopy {funs : FunEnv D} {V : VEnv D} {st st' : EvmState}
    {dstE srcE nE : YExpr} {dst src n : U256}
    (hbase : base < wordBound)
    (hs : (match litNat? dstE, litNat? srcE, litNat? nE with
      | some d, some s, some k => rangeBelow base d k && rangeBelow base s k
      | _, _, _ => false) = true)
    (h : EvalArgs D funs V st [dstE, srcE, nE] (.vals [dst, src, n] st')) :
    RangeOutside base reserved dst.toNat n.toNat ∧
      RangeOutside base reserved src.toNat n.toNat := by
  cases hd : litNat? dstE
  · simp [hd] at hs
  · cases hs' : litNat? srcE
    · simp [hd, hs'] at hs
    · cases hn : litNat? nE
      · simp [hd, hs', hn] at hs
      · next dsz ssz nsz =>
        simp [hd, hs', hn, rangeBelow_iff, Bool.and_eq_true] at hs
        have := litNat?_some hd; subst dstE
        have := litNat?_some hs'; subst srcE
        have := litNat?_some hn; subst nE
        have h0 := evalArgs_nth_lit (i := 0) rfl h
        have h1 := evalArgs_nth_lit (i := 1) rfl h
        have h2 := evalArgs_nth_lit (i := 2) rfl h
        simp at h0 h1 h2
        cases h0; cases h1; cases h2
        simp [toNat_ptr (k := nsz) hbase hs.1, toNat_len (p := dsz) hbase hs.1,
          toNat_ptr (k := nsz) hbase hs.2, toNat_len (p := ssz) hbase hs.2]
        exact ⟨rangeBelow_outside hs.1, rangeBelow_outside hs.2⟩

theorem range_of_extcodecopy {funs : FunEnv D} {V : VEnv D} {st st' : EvmState}
    {a0 dstE a2 nE : YExpr} {addr dst src n : U256}
    (hbase : base < wordBound)
    (hs : (match litNat? dstE, litNat? nE with
      | some d, some k => rangeBelow base d k
      | _, _ => false) = true)
    (h : EvalArgs D funs V st [a0, dstE, a2, nE] (.vals [addr, dst, src, n] st')) :
    RangeOutside base reserved dst.toNat n.toNat := by
  cases hd : litNat? dstE <;> cases hn : litNat? nE
  · simp [hd, hn] at hs
  · simp [hd, hn] at hs
  · simp [hd, hn] at hs
  · next dsz nsz =>
    simp [hd, hn, rangeBelow_iff] at hs
    have := litNat?_some hd; subst dstE
    have := litNat?_some hn; subst nE
    have h1 := evalArgs_nth_lit (i := 1) rfl h
    have h3 := evalArgs_nth_lit (i := 3) rfl h
    simp at h1 h3
    cases h1; cases h3
    simp [toNat_ptr (k := nsz) hbase hs, toNat_len (p := dsz) hbase hs]
    exact rangeBelow_outside hs

theorem range_of_create {funs : FunEnv D} {V : VEnv D} {st st' : EvmState}
    {a0 pE nE : YExpr} {val p n : U256}
    (hbase : base < wordBound)
    (hs : (match litNat? pE, litNat? nE with
      | some q, some k => rangeBelow base q k
      | _, _ => false) = true)
    (h : EvalArgs D funs V st [a0, pE, nE] (.vals [val, p, n] st')) :
    RangeOutside base reserved p.toNat n.toNat := by
  cases hp : litNat? pE <;> cases hn : litNat? nE
  · simp [hp, hn] at hs
  · simp [hp, hn] at hs
  · simp [hp, hn] at hs
  · next pn nn =>
    simp [hp, hn, rangeBelow_iff] at hs
    have := litNat?_some hp; subst pE
    have := litNat?_some hn; subst nE
    have h1 := evalArgs_nth_lit (i := 1) rfl h
    have h2 := evalArgs_nth_lit (i := 2) rfl h
    simp at h1 h2
    cases h1; cases h2
    simp [toNat_ptr (k := nn) hbase hs, toNat_len (p := pn) hbase hs]
    exact rangeBelow_outside hs

theorem range_of_create2 {funs : FunEnv D} {V : VEnv D} {st st' : EvmState}
    {a0 pE nE a3 : YExpr} {val p n salt : U256}
    (hbase : base < wordBound)
    (hs : (match litNat? pE, litNat? nE with
      | some q, some k => rangeBelow base q k
      | _, _ => false) = true)
    (h : EvalArgs D funs V st [a0, pE, nE, a3] (.vals [val, p, n, salt] st')) :
    RangeOutside base reserved p.toNat n.toNat := by
  cases hp : litNat? pE <;> cases hn : litNat? nE
  · simp [hp, hn] at hs
  · simp [hp, hn] at hs
  · simp [hp, hn] at hs
  · next pn nn =>
    simp [hp, hn, rangeBelow_iff] at hs
    have := litNat?_some hp; subst pE
    have := litNat?_some hn; subst nE
    have h1 := evalArgs_nth_lit (i := 1) rfl h
    have h2 := evalArgs_nth_lit (i := 2) rfl h
    simp at h1 h2
    cases h1; cases h2
    simp [toNat_ptr (k := nn) hbase hs, toNat_len (p := pn) hbase hs]
    exact rangeBelow_outside hs

theorem range_of_call7 {funs : FunEnv D} {V : VEnv D} {st st' : EvmState}
    {a0 a1 a2 inpE inszE outpE outszE : YExpr}
    {g tok val inp insz outp outsz : U256}
    (hbase : base < wordBound)
    (hs : (match litNat? inpE, litNat? inszE, litNat? outpE, litNat? outszE with
      | some ip, some isz, some op, some osz =>
          rangeBelow base ip isz && rangeBelow base op osz
      | _, _, _, _ => false) = true)
    (h : EvalArgs D funs V st [a0, a1, a2, inpE, inszE, outpE, outszE]
      (.vals [g, tok, val, inp, insz, outp, outsz] st')) :
    RangeOutside base reserved inp.toNat insz.toNat ∧
      RangeOutside base reserved outp.toNat outsz.toNat := by
  cases hi : litNat? inpE
  · simp [hi] at hs
  · cases his : litNat? inszE
    · simp [hi, his] at hs
    · cases ho : litNat? outpE
      · simp [hi, his, ho] at hs
      · cases hos : litNat? outszE
        · simp [hi, his, ho, hos] at hs
        · next ip isz opp osz =>
          simp [hi, his, ho, hos, rangeBelow_iff, Bool.and_eq_true] at hs
          have := litNat?_some hi; subst inpE
          have := litNat?_some his; subst inszE
          have := litNat?_some ho; subst outpE
          have := litNat?_some hos; subst outszE
          have h3 := evalArgs_nth_lit (i := 3) rfl h
          have h4 := evalArgs_nth_lit (i := 4) rfl h
          have h5 := evalArgs_nth_lit (i := 5) rfl h
          have h6 := evalArgs_nth_lit (i := 6) rfl h
          simp at h3 h4 h5 h6
          cases h3; cases h4; cases h5; cases h6
          simp [toNat_ptr (k := isz) hbase hs.1, toNat_len (p := ip) hbase hs.1,
            toNat_ptr (k := osz) hbase hs.2, toNat_len (p := opp) hbase hs.2]
          exact ⟨rangeBelow_outside hs.1, rangeBelow_outside hs.2⟩

theorem range_of_dcall {funs : FunEnv D} {V : VEnv D} {st st' : EvmState}
    {a0 a1 inpE inszE outpE outszE : YExpr}
    {g tok inp insz outp outsz : U256}
    (hbase : base < wordBound)
    (hs : (match litNat? inpE, litNat? inszE, litNat? outpE, litNat? outszE with
      | some ip, some isz, some op, some osz =>
          rangeBelow base ip isz && rangeBelow base op osz
      | _, _, _, _ => false) = true)
    (h : EvalArgs D funs V st [a0, a1, inpE, inszE, outpE, outszE]
      (.vals [g, tok, inp, insz, outp, outsz] st')) :
    RangeOutside base reserved inp.toNat insz.toNat ∧
      RangeOutside base reserved outp.toNat outsz.toNat := by
  cases hi : litNat? inpE
  · simp [hi] at hs
  · cases his : litNat? inszE
    · simp [hi, his] at hs
    · cases ho : litNat? outpE
      · simp [hi, his, ho] at hs
      · cases hos : litNat? outszE
        · simp [hi, his, ho, hos] at hs
        · next ip isz opp osz =>
          simp [hi, his, ho, hos, rangeBelow_iff, Bool.and_eq_true] at hs
          have := litNat?_some hi; subst inpE
          have := litNat?_some his; subst inszE
          have := litNat?_some ho; subst outpE
          have := litNat?_some hos; subst outszE
          have h2 := evalArgs_nth_lit (i := 2) rfl h
          have h3 := evalArgs_nth_lit (i := 3) rfl h
          have h4 := evalArgs_nth_lit (i := 4) rfl h
          have h5 := evalArgs_nth_lit (i := 5) rfl h
          simp at h2 h3 h4 h5
          cases h2; cases h3; cases h4; cases h5
          simp [toNat_ptr (k := isz) hbase hs.1, toNat_len (p := ip) hbase hs.1,
            toNat_ptr (k := osz) hbase hs.2, toNat_len (p := opp) hbase hs.2]
          exact ⟨rangeBelow_outside hs.1, rangeBelow_outside hs.2⟩

theorem length_ne_of_eval {funs : FunEnv D} {V : VEnv D} {st st' : EvmState}
    {args : List YExpr} {vs : List U256} {n : Nat}
    (h : EvalArgs D funs V st args (.vals vs st'))
    (hn : args.length ≠ n) : vs.length ≠ n := by
  intro hv
  exact hn ((evalArgs_length h).symm.trans hv)

theorem keccak_ne {vs : List U256} (h : vs.length ≠ 2) :
    OpMemorySafe base reserved YulSemantics.EVM.Op.keccak256 vs := by
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs with
  | nil => exact (h rfl).elim
  | cons _ _ => simp [OpMemorySafe]

theorem mload_ne {vs : List U256} (h : vs.length ≠ 1) :
    OpMemorySafe base reserved YulSemantics.EVM.Op.mload vs := by
  cases vs with
  | nil => simp [OpMemorySafe]
  | cons _ vs =>
    cases vs with
    | nil => exact (h rfl).elim
    | cons _ _ => simp [OpMemorySafe]

theorem mstore_ne {vs : List U256} (h : vs.length ≠ 2) :
    OpMemorySafe base reserved YulSemantics.EVM.Op.mstore vs := by
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs with
  | nil => exact (h rfl).elim
  | cons _ _ => simp [OpMemorySafe]

theorem mstore8_ne {vs : List U256} (h : vs.length ≠ 2) :
    OpMemorySafe base reserved YulSemantics.EVM.Op.mstore8 vs := by
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs with
  | nil => exact (h rfl).elim
  | cons _ _ => simp [OpMemorySafe]

theorem log0_ne {vs : List U256} (h : vs.length ≠ 2) :
    OpMemorySafe base reserved YulSemantics.EVM.Op.log0 vs := by
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs with
  | nil => exact (h rfl).elim
  | cons _ _ => simp [OpMemorySafe]

theorem ret_ne {vs : List U256} (h : vs.length ≠ 2) :
    OpMemorySafe base reserved YulSemantics.EVM.Op.ret vs := by
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs with
  | nil => exact (h rfl).elim
  | cons _ _ => simp [OpMemorySafe]

theorem revert_ne {vs : List U256} (h : vs.length ≠ 2) :
    OpMemorySafe base reserved YulSemantics.EVM.Op.revert vs := by
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs with
  | nil => exact (h rfl).elim
  | cons _ _ => simp [OpMemorySafe]

theorem log1_ne {vs : List U256} (h : vs.length ≠ 3) :
    OpMemorySafe base reserved YulSemantics.EVM.Op.log1 vs := by
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs with
  | nil => exact (h rfl).elim
  | cons _ _ => simp [OpMemorySafe]

theorem log2_ne {vs : List U256} (h : vs.length ≠ 4) :
    OpMemorySafe base reserved YulSemantics.EVM.Op.log2 vs := by
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs with
  | nil => exact (h rfl).elim
  | cons _ _ => simp [OpMemorySafe]

theorem log3_ne {vs : List U256} (h : vs.length ≠ 5) :
    OpMemorySafe base reserved YulSemantics.EVM.Op.log3 vs := by
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs with
  | nil => exact (h rfl).elim
  | cons _ _ => simp [OpMemorySafe]

theorem log4_ne {vs : List U256} (h : vs.length ≠ 6) :
    OpMemorySafe base reserved YulSemantics.EVM.Op.log4 vs := by
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs with
  | nil => exact (h rfl).elim
  | cons _ _ => simp [OpMemorySafe]

theorem calldatacopy_ne {vs : List U256} (h : vs.length ≠ 3) :
    OpMemorySafe base reserved YulSemantics.EVM.Op.calldatacopy vs := by
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs with
  | nil => exact (h rfl).elim
  | cons _ _ => simp [OpMemorySafe]

theorem codecopy_ne {vs : List U256} (h : vs.length ≠ 3) :
    OpMemorySafe base reserved YulSemantics.EVM.Op.codecopy vs := by
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs with
  | nil => exact (h rfl).elim
  | cons _ _ => simp [OpMemorySafe]

theorem returndatacopy_ne {vs : List U256} (h : vs.length ≠ 3) :
    OpMemorySafe base reserved YulSemantics.EVM.Op.returndatacopy vs := by
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs with
  | nil => exact (h rfl).elim
  | cons _ _ => simp [OpMemorySafe]

theorem datacopy_ne {vs : List U256} (h : vs.length ≠ 3) :
    OpMemorySafe base reserved YulSemantics.EVM.Op.datacopy vs := by
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs with
  | nil => exact (h rfl).elim
  | cons _ _ => simp [OpMemorySafe]

theorem mcopy_ne {vs : List U256} (h : vs.length ≠ 3) :
    OpMemorySafe base reserved YulSemantics.EVM.Op.mcopy vs := by
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs with
  | nil => exact (h rfl).elim
  | cons _ _ => simp [OpMemorySafe]

theorem extcodecopy_ne {vs : List U256} (h : vs.length ≠ 4) :
    OpMemorySafe base reserved YulSemantics.EVM.Op.extcodecopy vs := by
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs with
  | nil => exact (h rfl).elim
  | cons _ _ => simp [OpMemorySafe]

theorem create_ne {vs : List U256} (h : vs.length ≠ 3) :
    OpMemorySafe base reserved YulSemantics.EVM.Op.create vs := by
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs with
  | nil => exact (h rfl).elim
  | cons _ _ => simp [OpMemorySafe]

theorem create2_ne {vs : List U256} (h : vs.length ≠ 4) :
    OpMemorySafe base reserved YulSemantics.EVM.Op.create2 vs := by
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs with
  | nil => exact (h rfl).elim
  | cons _ _ => simp [OpMemorySafe]

theorem call_ne {vs : List U256} (h : vs.length ≠ 7) :
    OpMemorySafe base reserved YulSemantics.EVM.Op.call vs := by
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs with
  | nil => exact (h rfl).elim
  | cons _ _ => simp [OpMemorySafe]

theorem callcode_ne {vs : List U256} (h : vs.length ≠ 7) :
    OpMemorySafe base reserved YulSemantics.EVM.Op.callcode vs := by
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs with
  | nil => exact (h rfl).elim
  | cons _ _ => simp [OpMemorySafe]

theorem dcall_ne {vs : List U256} (h : vs.length ≠ 6) :
    OpMemorySafe base reserved YulSemantics.EVM.Op.delegatecall vs := by
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs with
  | nil => exact (h rfl).elim
  | cons _ _ => simp [OpMemorySafe]

theorem scall_ne {vs : List U256} (h : vs.length ≠ 6) :
    OpMemorySafe base reserved YulSemantics.EVM.Op.staticcall vs := by
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs <;> try simp [OpMemorySafe]
  next _ vs =>
  cases vs with
  | nil => exact (h rfl).elim
  | cons _ _ => simp [OpMemorySafe]

theorem staticSafeOp_eval {funs : FunEnv D} {V : VEnv D} {st st' : EvmState}
    {op : YOp} {args : List YExpr} {vs : List U256}
    (hbase : base < wordBound)
    (hs : staticSafeOp base op args = true)
    (h : EvalArgs D funs V st args (.vals vs st')) :
    OpMemorySafe base reserved op vs := by
  cases op with
  | keccak256 =>
    cases vs with
    | nil => exact keccak_ne (by simp [List.length])
    | cons p rest =>
      cases rest with
      | nil => exact keccak_ne (by simp [List.length])
      | cons n rest2 =>
        cases rest2 with
        | nil =>
          have hlen : args.length = 2 := (evalArgs_length h).symm
          obtain ⟨pE, nE, rfl⟩ := list_of_length_2 hlen
          simp [OpMemorySafe]
          exact range_of_two_lits (reserved := reserved) (p := p) (n := n) hbase hs h
        | cons _ _ => exact keccak_ne (by intro hlen; simp [List.length] at hlen)
  | log0 =>
    cases vs with
    | nil => exact log0_ne (by simp [List.length])
    | cons p rest =>
      cases rest with
      | nil => exact log0_ne (by simp [List.length])
      | cons n rest2 =>
        cases rest2 with
        | nil =>
          have hlen : args.length = 2 := (evalArgs_length h).symm
          obtain ⟨pE, nE, rfl⟩ := list_of_length_2 hlen
          simp [OpMemorySafe]
          exact range_of_two_lits (reserved := reserved) (p := p) (n := n) hbase hs h
        | cons _ _ => exact log0_ne (by intro hlen; simp [List.length] at hlen)
  | ret =>
    cases vs with
    | nil => exact ret_ne (by simp [List.length])
    | cons p rest =>
      cases rest with
      | nil => exact ret_ne (by simp [List.length])
      | cons n rest2 =>
        cases rest2 with
        | nil =>
          have hlen : args.length = 2 := (evalArgs_length h).symm
          obtain ⟨pE, nE, rfl⟩ := list_of_length_2 hlen
          simp [OpMemorySafe]
          exact range_of_two_lits (reserved := reserved) (p := p) (n := n) hbase hs h
        | cons _ _ => exact ret_ne (by intro hlen; simp [List.length] at hlen)
  | revert =>
    cases vs with
    | nil => exact revert_ne (by simp [List.length])
    | cons p rest =>
      cases rest with
      | nil => exact revert_ne (by simp [List.length])
      | cons n rest2 =>
        cases rest2 with
        | nil =>
          have hlen : args.length = 2 := (evalArgs_length h).symm
          obtain ⟨pE, nE, rfl⟩ := list_of_length_2 hlen
          simp [OpMemorySafe]
          exact range_of_two_lits (reserved := reserved) (p := p) (n := n) hbase hs h
        | cons _ _ => exact revert_ne (by intro hlen; simp [List.length] at hlen)
  | mload =>
    cases vs with
    | nil => exact mload_ne (by simp [List.length])
    | cons p rest =>
      cases rest with
      | nil =>
        have hlen : args.length = 1 := (evalArgs_length h).symm
        obtain ⟨pE, rfl⟩ := list_of_length_1 hlen
        simp [OpMemorySafe]
        exact range_of_mload (reserved := reserved) (p := p) (k := 32) hbase hs h
      | cons _ _ => exact mload_ne (by intro hlen; simp [List.length] at hlen)
  | mstore =>
    cases vs with
    | nil => exact mstore_ne (by simp [List.length])
    | cons p rest =>
      cases rest with
      | nil => exact mstore_ne (by simp [List.length])
      | cons v rest2 =>
        cases rest2 with
        | nil =>
          have hlen : args.length = 2 := (evalArgs_length h).symm
          obtain ⟨pE, vE, rfl⟩ := list_of_length_2 hlen
          simp [OpMemorySafe]
          exact range_of_mstore (reserved := reserved) (p := p) (v := v) (k := 32) hbase hs h
        | cons _ _ => exact mstore_ne (by intro hlen; simp [List.length] at hlen)
  | mstore8 =>
    cases vs with
    | nil => exact mstore8_ne (by simp [List.length])
    | cons p rest =>
      cases rest with
      | nil => exact mstore8_ne (by simp [List.length])
      | cons v rest2 =>
        cases rest2 with
        | nil =>
          have hlen : args.length = 2 := (evalArgs_length h).symm
          obtain ⟨pE, vE, rfl⟩ := list_of_length_2 hlen
          simp [OpMemorySafe]
          exact range_of_mstore (reserved := reserved) (p := p) (v := v) (k := 1) hbase hs h
        | cons _ _ => exact mstore8_ne (by intro hlen; simp [List.length] at hlen)
  | msize =>
    simp [staticSafeOp] at hs

  | log1 =>
    cases vs with
    | nil => exact log1_ne (by simp [List.length])
    | cons v0 rest0 =>
      cases rest0 with
      | nil => exact log1_ne (by simp [List.length])
      | cons v1 rest1 =>
        cases rest1 with
        | nil => exact log1_ne (by simp [List.length])
        | cons v2 rest2 =>
          cases rest2 with
          | nil =>
            have hlen : args.length = 3 := (evalArgs_length h).symm
            obtain ⟨pE, nE, tE, rfl⟩ := list_of_length_3 hlen
            simp [OpMemorySafe]
            exact range_of_log (reserved := reserved) (p := v0) (n := v1) (rest := [tE]) (tail := [v2]) hbase hs h
          | cons _ _ => exact log1_ne (by intro hlen; simp [List.length] at hlen)
  | log2 =>
    cases vs with
    | nil => exact log2_ne (by simp [List.length])
    | cons v0 rest0 =>
      cases rest0 with
      | nil => exact log2_ne (by simp [List.length])
      | cons v1 rest1 =>
        cases rest1 with
        | nil => exact log2_ne (by simp [List.length])
        | cons v2 rest2 =>
          cases rest2 with
          | nil => exact log2_ne (by simp [List.length])
          | cons v3 rest3 =>
            cases rest3 with
            | nil =>
              have hlen : args.length = 4 := (evalArgs_length h).symm
              obtain ⟨pE, nE, a, b, rfl⟩ := list_of_length_4 hlen
              simp [OpMemorySafe]
              exact range_of_log (reserved := reserved) (p := v0) (n := v1) (rest := [a, b]) (tail := [v2, v3]) hbase hs h
            | cons _ _ => exact log2_ne (by intro hlen; simp [List.length] at hlen)
  | log3 =>
    cases vs with
    | nil => exact log3_ne (by simp [List.length])
    | cons v0 rest0 =>
      cases rest0 with
      | nil => exact log3_ne (by simp [List.length])
      | cons v1 rest1 =>
        cases rest1 with
        | nil => exact log3_ne (by simp [List.length])
        | cons v2 rest2 =>
          cases rest2 with
          | nil => exact log3_ne (by simp [List.length])
          | cons v3 rest3 =>
            cases rest3 with
            | nil => exact log3_ne (by simp [List.length])
            | cons v4 rest4 =>
              cases rest4 with
              | nil =>
                have hlen : args.length = 5 := (evalArgs_length h).symm
                obtain ⟨pE, nE, a, b, c, rfl⟩ := list_of_length_5 hlen
                simp [OpMemorySafe]
                exact range_of_log (reserved := reserved) (p := v0) (n := v1) (rest := [a, b, c]) (tail := [v2, v3, v4]) hbase hs h
              | cons _ _ => exact log3_ne (by intro hlen; simp [List.length] at hlen)
  | log4 =>
    cases vs with
    | nil => exact log4_ne (by simp [List.length])
    | cons v0 rest0 =>
      cases rest0 with
      | nil => exact log4_ne (by simp [List.length])
      | cons v1 rest1 =>
        cases rest1 with
        | nil => exact log4_ne (by simp [List.length])
        | cons v2 rest2 =>
          cases rest2 with
          | nil => exact log4_ne (by simp [List.length])
          | cons v3 rest3 =>
            cases rest3 with
            | nil => exact log4_ne (by simp [List.length])
            | cons v4 rest4 =>
              cases rest4 with
              | nil => exact log4_ne (by simp [List.length])
              | cons v5 rest5 =>
                cases rest5 with
                | nil =>
                  have hlen : args.length = 6 := (evalArgs_length h).symm
                  obtain ⟨pE, nE, a, b, c, d, rfl⟩ := list_of_length_6 hlen
                  simp [OpMemorySafe]
                  exact range_of_log (reserved := reserved) (p := v0) (n := v1) (rest := [a, b, c, d]) (tail := [v2, v3, v4, v5]) hbase hs h
                | cons _ _ => exact log4_ne (by intro hlen; simp [List.length] at hlen)
  | calldatacopy =>
    cases vs with
    | nil => exact calldatacopy_ne (by simp [List.length])
    | cons v0 rest0 =>
      cases rest0 with
      | nil => exact calldatacopy_ne (by simp [List.length])
      | cons v1 rest1 =>
        cases rest1 with
        | nil => exact calldatacopy_ne (by simp [List.length])
        | cons v2 rest2 =>
          cases rest2 with
          | nil =>
            have hlen : args.length = 3 := (evalArgs_length h).symm
            obtain ⟨dstE, srcE, nE, rfl⟩ := list_of_length_3 hlen
            simp [OpMemorySafe]
            exact range_of_dst_n (reserved := reserved) (dst := v0) (src := v1) (n := v2) hbase hs h
          | cons _ _ => exact calldatacopy_ne (by intro hlen; simp [List.length] at hlen)
  | codecopy =>
    cases vs with
    | nil => exact codecopy_ne (by simp [List.length])
    | cons v0 rest0 =>
      cases rest0 with
      | nil => exact codecopy_ne (by simp [List.length])
      | cons v1 rest1 =>
        cases rest1 with
        | nil => exact codecopy_ne (by simp [List.length])
        | cons v2 rest2 =>
          cases rest2 with
          | nil =>
            have hlen : args.length = 3 := (evalArgs_length h).symm
            obtain ⟨dstE, srcE, nE, rfl⟩ := list_of_length_3 hlen
            simp [OpMemorySafe]
            exact range_of_dst_n (reserved := reserved) (dst := v0) (src := v1) (n := v2) hbase hs h
          | cons _ _ => exact codecopy_ne (by intro hlen; simp [List.length] at hlen)
  | returndatacopy =>
    cases vs with
    | nil => exact returndatacopy_ne (by simp [List.length])
    | cons v0 rest0 =>
      cases rest0 with
      | nil => exact returndatacopy_ne (by simp [List.length])
      | cons v1 rest1 =>
        cases rest1 with
        | nil => exact returndatacopy_ne (by simp [List.length])
        | cons v2 rest2 =>
          cases rest2 with
          | nil =>
            have hlen : args.length = 3 := (evalArgs_length h).symm
            obtain ⟨dstE, srcE, nE, rfl⟩ := list_of_length_3 hlen
            simp [OpMemorySafe]
            exact range_of_dst_n (reserved := reserved) (dst := v0) (src := v1) (n := v2) hbase hs h
          | cons _ _ => exact returndatacopy_ne (by intro hlen; simp [List.length] at hlen)
  | datacopy =>
    cases vs with
    | nil => exact datacopy_ne (by simp [List.length])
    | cons v0 rest0 =>
      cases rest0 with
      | nil => exact datacopy_ne (by simp [List.length])
      | cons v1 rest1 =>
        cases rest1 with
        | nil => exact datacopy_ne (by simp [List.length])
        | cons v2 rest2 =>
          cases rest2 with
          | nil =>
            have hlen : args.length = 3 := (evalArgs_length h).symm
            obtain ⟨dstE, srcE, nE, rfl⟩ := list_of_length_3 hlen
            simp [OpMemorySafe]
            exact range_of_dst_n (reserved := reserved) (dst := v0) (src := v1) (n := v2) hbase hs h
          | cons _ _ => exact datacopy_ne (by intro hlen; simp [List.length] at hlen)
  | mcopy =>
    cases vs with
    | nil => exact mcopy_ne (by simp [List.length])
    | cons v0 rest0 =>
      cases rest0 with
      | nil => exact mcopy_ne (by simp [List.length])
      | cons v1 rest1 =>
        cases rest1 with
        | nil => exact mcopy_ne (by simp [List.length])
        | cons v2 rest2 =>
          cases rest2 with
          | nil =>
            have hlen : args.length = 3 := (evalArgs_length h).symm
            obtain ⟨dstE, srcE, nE, rfl⟩ := list_of_length_3 hlen
            simp [OpMemorySafe]
            exact range_of_mcopy (reserved := reserved) (dst := v0) (src := v1) (n := v2) hbase hs h
          | cons _ _ => exact mcopy_ne (by intro hlen; simp [List.length] at hlen)
  | extcodecopy =>
    cases vs with
    | nil => exact extcodecopy_ne (by simp [List.length])
    | cons v0 rest0 =>
      cases rest0 with
      | nil => exact extcodecopy_ne (by simp [List.length])
      | cons v1 rest1 =>
        cases rest1 with
        | nil => exact extcodecopy_ne (by simp [List.length])
        | cons v2 rest2 =>
          cases rest2 with
          | nil => exact extcodecopy_ne (by simp [List.length])
          | cons v3 rest3 =>
            cases rest3 with
            | nil =>
              have hlen : args.length = 4 := (evalArgs_length h).symm
              obtain ⟨a0, dstE, a2, nE, rfl⟩ := list_of_length_4 hlen
              simp [OpMemorySafe]
              exact range_of_extcodecopy (reserved := reserved) (addr := v0) (dst := v1) (src := v2) (n := v3) hbase hs h
            | cons _ _ => exact extcodecopy_ne (by intro hlen; simp [List.length] at hlen)
  | create =>
    cases vs with
    | nil => exact create_ne (by simp [List.length])
    | cons v0 rest0 =>
      cases rest0 with
      | nil => exact create_ne (by simp [List.length])
      | cons v1 rest1 =>
        cases rest1 with
        | nil => exact create_ne (by simp [List.length])
        | cons v2 rest2 =>
          cases rest2 with
          | nil =>
            have hlen : args.length = 3 := (evalArgs_length h).symm
            obtain ⟨a0, pE, nE, rfl⟩ := list_of_length_3 hlen
            simp [OpMemorySafe]
            exact range_of_create (reserved := reserved) (val := v0) (p := v1) (n := v2) hbase hs h
          | cons _ _ => exact create_ne (by intro hlen; simp [List.length] at hlen)
  | create2 =>
    cases vs with
    | nil => exact create2_ne (by simp [List.length])
    | cons v0 rest0 =>
      cases rest0 with
      | nil => exact create2_ne (by simp [List.length])
      | cons v1 rest1 =>
        cases rest1 with
        | nil => exact create2_ne (by simp [List.length])
        | cons v2 rest2 =>
          cases rest2 with
          | nil => exact create2_ne (by simp [List.length])
          | cons v3 rest3 =>
            cases rest3 with
            | nil =>
              have hlen : args.length = 4 := (evalArgs_length h).symm
              obtain ⟨a0, pE, nE, a3, rfl⟩ := list_of_length_4 hlen
              simp [OpMemorySafe]
              exact range_of_create2 (reserved := reserved) (val := v0) (p := v1) (n := v2) (salt := v3) hbase hs h
            | cons _ _ => exact create2_ne (by intro hlen; simp [List.length] at hlen)
  | call =>
    cases vs with
    | nil => exact call_ne (by simp [List.length])
    | cons v0 rest0 =>
      cases rest0 with
      | nil => exact call_ne (by simp [List.length])
      | cons v1 rest1 =>
        cases rest1 with
        | nil => exact call_ne (by simp [List.length])
        | cons v2 rest2 =>
          cases rest2 with
          | nil => exact call_ne (by simp [List.length])
          | cons v3 rest3 =>
            cases rest3 with
            | nil => exact call_ne (by simp [List.length])
            | cons v4 rest4 =>
              cases rest4 with
              | nil => exact call_ne (by simp [List.length])
              | cons v5 rest5 =>
                cases rest5 with
                | nil => exact call_ne (by simp [List.length])
                | cons v6 rest6 =>
                  cases rest6 with
                  | nil =>
                    have hlen : args.length = 7 := (evalArgs_length h).symm
                    obtain ⟨a0, a1, a2, inpE, inszE, outpE, outszE, rfl⟩ := list_of_length_7 hlen
                    simp [OpMemorySafe]
                    exact range_of_call7 (reserved := reserved) (g := v0) (tok := v1) (val := v2) (inp := v3) (insz := v4) (outp := v5) (outsz := v6) hbase hs h
                  | cons _ _ => exact call_ne (by intro hlen; simp [List.length] at hlen)
  | callcode =>
    cases vs with
    | nil => exact callcode_ne (by simp [List.length])
    | cons v0 rest0 =>
      cases rest0 with
      | nil => exact callcode_ne (by simp [List.length])
      | cons v1 rest1 =>
        cases rest1 with
        | nil => exact callcode_ne (by simp [List.length])
        | cons v2 rest2 =>
          cases rest2 with
          | nil => exact callcode_ne (by simp [List.length])
          | cons v3 rest3 =>
            cases rest3 with
            | nil => exact callcode_ne (by simp [List.length])
            | cons v4 rest4 =>
              cases rest4 with
              | nil => exact callcode_ne (by simp [List.length])
              | cons v5 rest5 =>
                cases rest5 with
                | nil => exact callcode_ne (by simp [List.length])
                | cons v6 rest6 =>
                  cases rest6 with
                  | nil =>
                    have hlen : args.length = 7 := (evalArgs_length h).symm
                    obtain ⟨a0, a1, a2, inpE, inszE, outpE, outszE, rfl⟩ := list_of_length_7 hlen
                    simp [OpMemorySafe]
                    exact range_of_call7 (reserved := reserved) (g := v0) (tok := v1) (val := v2) (inp := v3) (insz := v4) (outp := v5) (outsz := v6) hbase hs h
                  | cons _ _ => exact callcode_ne (by intro hlen; simp [List.length] at hlen)
  | delegatecall =>
    cases vs with
    | nil => exact dcall_ne (by simp [List.length])
    | cons v0 rest0 =>
      cases rest0 with
      | nil => exact dcall_ne (by simp [List.length])
      | cons v1 rest1 =>
        cases rest1 with
        | nil => exact dcall_ne (by simp [List.length])
        | cons v2 rest2 =>
          cases rest2 with
          | nil => exact dcall_ne (by simp [List.length])
          | cons v3 rest3 =>
            cases rest3 with
            | nil => exact dcall_ne (by simp [List.length])
            | cons v4 rest4 =>
              cases rest4 with
              | nil => exact dcall_ne (by simp [List.length])
              | cons v5 rest5 =>
                cases rest5 with
                | nil =>
                  have hlen : args.length = 6 := (evalArgs_length h).symm
                  obtain ⟨a0, a1, inpE, inszE, outpE, outszE, rfl⟩ := list_of_length_6 hlen
                  simp [OpMemorySafe]
                  exact range_of_dcall (reserved := reserved) (g := v0) (tok := v1) (inp := v2) (insz := v3) (outp := v4) (outsz := v5) hbase hs h
                | cons _ _ => exact dcall_ne (by intro hlen; simp [List.length] at hlen)
  | staticcall =>
    cases vs with
    | nil => exact scall_ne (by simp [List.length])
    | cons v0 rest0 =>
      cases rest0 with
      | nil => exact scall_ne (by simp [List.length])
      | cons v1 rest1 =>
        cases rest1 with
        | nil => exact scall_ne (by simp [List.length])
        | cons v2 rest2 =>
          cases rest2 with
          | nil => exact scall_ne (by simp [List.length])
          | cons v3 rest3 =>
            cases rest3 with
            | nil => exact scall_ne (by simp [List.length])
            | cons v4 rest4 =>
              cases rest4 with
              | nil => exact scall_ne (by simp [List.length])
              | cons v5 rest5 =>
                cases rest5 with
                | nil =>
                  have hlen : args.length = 6 := (evalArgs_length h).symm
                  obtain ⟨a0, a1, inpE, inszE, outpE, outszE, rfl⟩ := list_of_length_6 hlen
                  simp [OpMemorySafe]
                  exact range_of_dcall (reserved := reserved) (g := v0) (tok := v1) (inp := v2) (insz := v3) (outp := v4) (outsz := v5) hbase hs h
                | cons _ _ => exact scall_ne (by intro hlen; simp [List.length] at hlen)

  | add | sub | mul | div | sdiv | mod | smod | addmod | mulmod | exp | signextend | clz
  | lt | gt | slt | sgt | eq | iszero
  | and | or | xor | not | byte | shl | shr | sar
  | pop | sload | sstore | tload | tstore
  | calldataload | calldatasize | codesize | returndatasize
  | datasize | dataoffset | loadimmutable
  | address | origin | caller | callvalue | gasprice | selfbalance
  | coinbase | timestamp | number | prevrandao | gaslimit | chainid | basefee | blobbasefee
  | balance | extcodesize | extcodehash | blockhash | blobhash
  | gas | selfdestruct | stop | invalid =>
    simp [OpMemorySafe]

end Lsc.Compiler
