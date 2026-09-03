import Lsc.Compile.IR.Eval
import Lsc.Compile.IR.Builder
import Lsc.Compile.IR.WordEval

namespace Lsc.Compile.IR

theorem wordSize_eq : EvmYul.UInt256.size = 2 ^ 256 := by rfl

theorem Word.toNat_ofNat_of_lt (n : Nat) (h : n < EvmYul.UInt256.size) :
    (EvmYul.UInt256.ofNat n).toNat = n := by
  change n % EvmYul.UInt256.size = n
  exact Nat.mod_eq_of_lt h

theorem Word.toNat_add_of_lt (a b : Word)
    (h : a.toNat + b.toNat < EvmYul.UInt256.size) :
    (EvmYul.UInt256.add a b).toNat = a.toNat + b.toNat := by
  change (a.toNat + b.toNat) % EvmYul.UInt256.size = _
  exact Nat.mod_eq_of_lt h

theorem Word.toNat_sub_of_le (a b : Word) (h : b.toNat ≤ a.toNat) :
    (EvmYul.UInt256.sub a b).toNat = a.toNat - b.toNat := by
  change (EvmYul.UInt256.size - b.val.val + a.val.val) % EvmYul.UInt256.size =
    a.val.val - b.val.val
  change b.val.val ≤ a.val.val at h
  have ha := a.val.isLt
  have hb := b.val.isLt
  have heq : EvmYul.UInt256.size - b.val.val + a.val.val =
      EvmYul.UInt256.size + (a.val.val - b.val.val) := by omega
  rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
  have hdiff : a.val.val - b.val.val < EvmYul.UInt256.size := by omega
  simp [Nat.mod_eq_of_lt hdiff]

theorem Word.toNat_mul_of_lt (a b : Word)
    (h : a.toNat * b.toNat < EvmYul.UInt256.size) :
    (EvmYul.UInt256.mul a b).toNat = a.toNat * b.toNat := by
  change (a.toNat * b.toNat) % EvmYul.UInt256.size = _
  exact Nat.mod_eq_of_lt h

theorem Word.toNat_div (a b : Word) :
    (EvmYul.UInt256.div a b).toNat = a.toNat / b.toNat :=
  Fin.div_val a.val b.val

theorem Word.toNat_xor (a b : Word) :
    (EvmYul.UInt256.xor a b).toNat = a.toNat ^^^ b.toNat := by
  change (a.toNat ^^^ b.toNat) % EvmYul.UInt256.size = _
  rw [Nat.mod_eq_of_lt]
  rw [wordSize_eq]
  exact Nat.xor_lt_two_pow (wordSize_eq ▸ a.val.isLt) (wordSize_eq ▸ b.val.isLt)

theorem Word.toNat_shiftRight (value amount : Word) (h : amount.toNat < 256) :
    (EvmYul.UInt256.shiftRight value amount).toNat =
      value.toNat / 2 ^ amount.toNat := by
  change amount.val.val < 256 at h
  simp only [EvmYul.UInt256.shiftRight]
  split
  · next hge =>
    change 256 ≤ amount.val.val at hge
    omega
  · change (value.val >>> amount.val).val = value.val.val / 2 ^ amount.val.val
    simp [Nat.shiftRight_eq_div_pow]

theorem Word.lt_iff_toNat_lt (a b : Word) : a < b ↔ a.toNat < b.toNat := by
  rfl

theorem Word.eq_iff_toNat_eq (a b : Word) : a = b ↔ a.toNat = b.toNat := by
  constructor
  · exact fun h => congrArg EvmYul.UInt256.toNat h
  · intro h
    cases a with
    | mk av =>
      cases b with
      | mk bv =>
        simp only [EvmYul.UInt256.toNat] at h
        simp only [EvmYul.UInt256.mk.injEq]
        exact Fin.eq_of_val_eq h

theorem Word.beq_eq_true (a b : Word) : (a == b) = true ↔ a = b := by
  cases a with
  | mk av =>
    cases b with
    | mk bv =>
      simp only [EvmYul.UInt256.mk.injEq]
      change (av == bv) = true ↔ av = bv
      simp

@[simp] theorem Word.toNat_boolWord (b : Bool) :
    (boolWord b).toNat = if b then 1 else 0 := by
  cases b
  · exact Word.toNat_ofNat_of_lt 0 (by decide)
  · exact Word.toNat_ofNat_of_lt 1 (by decide)

/-- The Nat and word states agree on every source readable by the pure expression evaluator. -/
def WordState.Agrees (nat : IRState) (word : WordState) : Prop :=
  (∀ name, (word.lookupLocal name).toNat = nat.lookupLocal name) ∧
  (∀ slot, (word.slots slot).toNat = nat.lookupSlot slot) ∧
  ∀ offset, (word.calldata offset).toNat = nat.calldata offset

/-- Exact no-wrap conditions for agreement with the unbounded Nat evaluator.

Only literals, addition, multiplication and subtraction require word-bound hypotheses.  Shift
amounts are restricted to `< 256`, which is sufficient for the sqrt lowering and avoids a
separate proof that Nat division is zero for larger EVM shift amounts. -/
def ExprNoWrap (st : IRState) : Expr → Prop
  | .lit n => n < EvmYul.UInt256.size
  | .local _ | .sload _ | .calldataWord _ => True
  | .mapSlot .. | .mapSlot2 .. => False
  | .dynSload slot => ExprNoWrap st slot
  | .add a b =>
      ExprNoWrap st a ∧ ExprNoWrap st b ∧
        evalExpr st a + evalExpr st b < EvmYul.UInt256.size
  | .sub a b =>
      ExprNoWrap st a ∧ ExprNoWrap st b ∧ evalExpr st b ≤ evalExpr st a
  | .mul a b =>
      ExprNoWrap st a ∧ ExprNoWrap st b ∧
        evalExpr st a * evalExpr st b < EvmYul.UInt256.size
  | .div a b | .lt a b | .eq a b | .gt a b | .xor a b =>
      ExprNoWrap st a ∧ ExprNoWrap st b
  | .isZero a => ExprNoWrap st a
  | .shr amount value =>
      ExprNoWrap st amount ∧ ExprNoWrap st value ∧ evalExpr st amount < 256

/-- Kernel-checked expression agreement.  The witness form is convenient for composing
statements; `evalExprWord_toNat` below is its direct observable corollary. -/
theorem evalExprWord_agrees (nat : IRState) (word : WordState) (e : Expr)
    (hst : word.Agrees nat) (hnw : ExprNoWrap nat e) :
    ∃ value, evalExprWord word e = some value ∧ value.toNat = evalExpr nat e := by
  induction e with
  | lit n =>
      exact ⟨.ofNat n, rfl, Word.toNat_ofNat_of_lt n hnw⟩
  | «local» name =>
      exact ⟨word.lookupLocal name, rfl, hst.1 name⟩
  | sload slot =>
      exact ⟨word.slots slot, rfl, hst.2.1 slot⟩
  | mapSlot base key =>
      contradiction
  | mapSlot2 base key1 key2 =>
      contradiction
  | dynSload slot ih =>
      obtain ⟨slotWord, hslot, hslotNat⟩ := ih hnw
      refine ⟨word.slots slotWord.toNat, by simp [evalExprWord, hslot], ?_⟩
      simpa [evalExpr, hslotNat] using hst.2.1 slotWord.toNat
  | calldataWord offset =>
      exact ⟨word.calldata offset, rfl, hst.2.2 offset⟩
  | add a b iha ihb =>
      rcases hnw with ⟨hna, hnb, hbound⟩
      obtain ⟨wa, ha, hta⟩ := iha hna
      obtain ⟨wb, hb, htb⟩ := ihb hnb
      refine ⟨EvmYul.UInt256.add wa wb, by simp [evalExprWord, ha, hb], ?_⟩
      rw [Word.toNat_add_of_lt wa wb (by simpa [hta, htb] using hbound), hta, htb]
      rfl
  | sub a b iha ihb =>
      rcases hnw with ⟨hna, hnb, hle⟩
      obtain ⟨wa, ha, hta⟩ := iha hna
      obtain ⟨wb, hb, htb⟩ := ihb hnb
      refine ⟨EvmYul.UInt256.sub wa wb, by simp [evalExprWord, ha, hb], ?_⟩
      rw [Word.toNat_sub_of_le wa wb (by simpa [hta, htb] using hle), hta, htb]
      rfl
  | mul a b iha ihb =>
      rcases hnw with ⟨hna, hnb, hbound⟩
      obtain ⟨wa, ha, hta⟩ := iha hna
      obtain ⟨wb, hb, htb⟩ := ihb hnb
      refine ⟨EvmYul.UInt256.mul wa wb, by simp [evalExprWord, ha, hb], ?_⟩
      rw [Word.toNat_mul_of_lt wa wb (by simpa [hta, htb] using hbound), hta, htb]
      rfl
  | div a b iha ihb =>
      rcases hnw with ⟨hna, hnb⟩
      obtain ⟨wa, ha, hta⟩ := iha hna
      obtain ⟨wb, hb, htb⟩ := ihb hnb
      refine ⟨EvmYul.UInt256.div wa wb, by simp [evalExprWord, ha, hb], ?_⟩
      rw [Word.toNat_div, hta, htb]
      rfl
  | lt a b iha ihb =>
      rcases hnw with ⟨hna, hnb⟩
      obtain ⟨wa, ha, hta⟩ := iha hna
      obtain ⟨wb, hb, htb⟩ := ihb hnb
      refine ⟨boolWord (wa < wb), by simp [evalExprWord, ha, hb], ?_⟩
      simp only [Word.toNat_boolWord, evalExpr]
      by_cases h : wa < wb
      · have hn : evalExpr nat a < evalExpr nat b := by
          rw [← hta, ← htb]
          exact (Word.lt_iff_toNat_lt wa wb).mp h
        simp [h, hn]
      · have hn : ¬evalExpr nat a < evalExpr nat b := by
          intro hab
          apply h
          apply (Word.lt_iff_toNat_lt wa wb).mpr
          simpa [hta, htb] using hab
        simp [h, hn]
  | eq a b iha ihb =>
      rcases hnw with ⟨hna, hnb⟩
      obtain ⟨wa, ha, hta⟩ := iha hna
      obtain ⟨wb, hb, htb⟩ := ihb hnb
      refine ⟨boolWord (wa == wb), by simp [evalExprWord, ha, hb], ?_⟩
      simp only [Word.toNat_boolWord, evalExpr]
      by_cases h : wa = wb
      · have hn : evalExpr nat a = evalExpr nat b := by rw [← hta, ← htb, h]
        rw [if_pos (beq_iff_eq.mpr hn)]
        exact if_pos ((Word.beq_eq_true wa wb).mpr h)
      · have hn : evalExpr nat a ≠ evalExpr nat b := by
          intro hab
          apply h
          apply (Word.eq_iff_toNat_eq wa wb).mpr
          simpa [hta, htb] using hab
        rw [if_neg (fun heq => hn (beq_iff_eq.mp heq))]
        exact if_neg (fun heq => h ((Word.beq_eq_true wa wb).mp heq))
  | isZero a ih =>
      obtain ⟨wa, ha, hta⟩ := ih hnw
      refine ⟨boolWord (wa == .ofNat 0), by simp [evalExprWord, ha], ?_⟩
      simp only [Word.toNat_boolWord, evalExpr]
      by_cases h : wa = .ofNat 0
      · have hn : evalExpr nat a = 0 := by
          rw [← hta, h, Word.toNat_ofNat_of_lt 0 (by decide)]
        rw [if_pos (beq_iff_eq.mpr hn)]
        exact if_pos ((Word.beq_eq_true wa (.ofNat 0)).mpr h)
      · have hn : evalExpr nat a ≠ 0 := by
          intro ha0
          apply h
          apply (Word.eq_iff_toNat_eq wa (.ofNat 0)).mpr
          rw [Word.toNat_ofNat_of_lt 0 (by decide), hta, ha0]
        rw [if_neg (fun heq => hn (beq_iff_eq.mp heq))]
        exact if_neg (fun heq => h ((Word.beq_eq_true wa (.ofNat 0)).mp heq))
  | gt a b iha ihb =>
      rcases hnw with ⟨hna, hnb⟩
      obtain ⟨wa, ha, hta⟩ := iha hna
      obtain ⟨wb, hb, htb⟩ := ihb hnb
      refine ⟨boolWord (wa > wb), by simp [evalExprWord, ha, hb], ?_⟩
      simp only [Word.toNat_boolWord, evalExpr]
      by_cases h : wb < wa
      · have hn : evalExpr nat b < evalExpr nat a := by
          rw [← htb, ← hta]
          exact (Word.lt_iff_toNat_lt wb wa).mp h
        simp [h, hn]
      · have hn : ¬evalExpr nat b < evalExpr nat a := by
          intro hab
          apply h
          apply (Word.lt_iff_toNat_lt wb wa).mpr
          simpa [hta, htb] using hab
        simp [h, hn]
  | shr amount value ihAmount ihValue =>
      rcases hnw with ⟨hna, hnv, hbound⟩
      obtain ⟨wa, ha, hta⟩ := ihAmount hna
      obtain ⟨wv, hv, htv⟩ := ihValue hnv
      refine ⟨EvmYul.UInt256.shiftRight wv wa, by simp [evalExprWord, ha, hv], ?_⟩
      rw [Word.toNat_shiftRight wv wa (by simpa [hta] using hbound), hta, htv]
      rfl
  | xor a b iha ihb =>
      rcases hnw with ⟨hna, hnb⟩
      obtain ⟨wa, ha, hta⟩ := iha hna
      obtain ⟨wb, hb, htb⟩ := ihb hnb
      refine ⟨EvmYul.UInt256.xor wa wb, by simp [evalExprWord, ha, hb], ?_⟩
      rw [Word.toNat_xor, hta, htb]
      rfl

theorem evalExprWord_toNat (nat : IRState) (word : WordState) (e : Expr)
    (hst : word.Agrees nat) (hnw : ExprNoWrap nat e) :
    Option.map EvmYul.UInt256.toNat (evalExprWord word e) = some (evalExpr nat e) := by
  obtain ⟨value, heval, hvalue⟩ := evalExprWord_agrees nat word e hst hnw
  simp [heval, hvalue]

/-- Return-observing extension of the existing Nat evaluator's state.  Expressions and local
updates are exactly `evalExpr` and `IRState.setLocal`; only halt information is added. -/
inductive NatHalt where
  | running
  | returned (value : Nat)
  | reverted (selector : Nat)
  deriving Repr, DecidableEq

structure NatViewState where
  state : IRState
  halt : NatHalt := .running

/-- Nat semantics for the pure view statement fragment, including returned values. -/
def evalStmtNatView (st : NatViewState) : Stmt → Option NatViewState
  | .skip => some st
  | .seq first rest => do
      let st ← evalStmtNatView st first
      match st.halt with
      | .running => evalStmtNatView st rest
      | _ => some st
  | .letBind name value =>
      some { state := st.state.setLocal name (evalExpr st.state value), halt := st.halt }
  | .ifRevertSelector cond selector =>
      if evalExpr st.state cond = 1 then
        some { st with halt := .reverted selector }
      else some st
  | .revertSelector selector => some { st with halt := .reverted selector }
  | .ret value => some { st with halt := .returned (evalExpr st.state value) }
  | .sstore .. | .sstoreDyn .. | .log ..
  | .checkReentrancyLock .. | .setReentrancyLock ..
  | .externalCall .. | .externalCallBind .. | .staticCall .. | .staticCallBind .. => none

def NatViewState.Agrees (nat : NatViewState) (word : WordState) : Prop :=
  word.Agrees nat.state ∧
    match nat.halt, word.halt with
    | .running, .running => True
    | .returned n, .returned w => w.toNat = n
    | .reverted a, .reverted b => a = b
    | _, _ => False

theorem WordState.Agrees.setLocal (nat : IRState) (word : WordState)
    (hst : word.Agrees nat) (name : Lsc.Ident) (wordValue : Word) (natValue : Nat)
    (hvalue : wordValue.toNat = natValue) :
    (word.setLocal name wordValue).Agrees (nat.setLocal name natValue) := by
  refine ⟨?_, hst.2.1, hst.2.2⟩
  intro other
  by_cases h : other = name
  · subst h
    simp [WordState.lookupLocal, WordState.setLocal, IRState.lookupLocal_setLocal_same, hvalue]
  · have hne : name ≠ other := Ne.symm h
    simp [WordState.lookupLocal, WordState.setLocal,
      IRState.lookupLocal_setLocal_ne nat name other natValue hne, h]
    exact hst.1 other

/-- Dynamic no-wrap predicate for the return-observing pure view statement fragment.  The
continuation is checked in the Nat state produced by the first statement. -/
def StmtNoWrap (st : NatViewState) : Stmt → Prop
  | .skip => True
  | .seq first rest =>
      StmtNoWrap st first ∧
        match evalStmtNatView st first with
        | some next =>
            match next.halt with
            | .running => StmtNoWrap next rest
            | _ => True
        | none => False
  | .letBind _ value => ExprNoWrap st.state value
  | .ifRevertSelector cond _ => ExprNoWrap st.state cond
  | .revertSelector _ => True
  | .ret value => ExprNoWrap st.state value
  | .sstore .. | .sstoreDyn .. | .log ..
  | .checkReentrancyLock .. | .setReentrancyLock ..
  | .externalCall .. | .externalCallBind .. | .staticCall .. | .staticCallBind .. => False

/-- Kernel-checked agreement for `skip`, `let`, `seq`, conditional/direct revert, and `ret`.
Returned words are related to the exact Nat value returned by `evalStmtNatView`. -/
theorem evalStmtWord_agrees (nat : NatViewState) (word : WordState) (stmt : Stmt)
    (hst : nat.Agrees word) (hnw : StmtNoWrap nat stmt) :
    ∃ natResult wordResult,
      evalStmtNatView nat stmt = some natResult ∧
      evalStmtWord word stmt = some wordResult ∧
      natResult.Agrees wordResult := by
  induction stmt generalizing nat word with
  | skip =>
      exact ⟨nat, word, rfl, rfl, hst⟩
  | seq first rest ihFirst ihRest =>
      rcases hnw with ⟨hnwFirst, hnwRest⟩
      obtain ⟨natFirst, wordFirst, hnatFirst, hwordFirst, hagreeFirst⟩ :=
        ihFirst nat word hst hnwFirst
      cases hhalt : natFirst.halt with
      | running =>
          have hwordHalt : wordFirst.halt = .running := by
            cases hw : wordFirst.halt with
            | running => rfl
            | returned w =>
                simp [NatViewState.Agrees, hhalt, hw] at hagreeFirst
            | reverted selector =>
                simp [NatViewState.Agrees, hhalt, hw] at hagreeFirst
          have hnwRest' : StmtNoWrap natFirst rest := by
            simpa [hnatFirst, hhalt] using hnwRest
          obtain ⟨natRest, wordRest, hnatRest, hwordRest, hagreeRest⟩ :=
            ihRest natFirst wordFirst hagreeFirst hnwRest'
          refine ⟨natRest, wordRest, ?_, ?_, hagreeRest⟩
          · simp [evalStmtNatView, hnatFirst, hhalt, hnatRest]
          · simp [evalStmtWord, hwordFirst, hwordHalt, hwordRest]
      | returned n =>
          obtain ⟨wordValue, hwordHalt, hvalue⟩ : ∃ w,
              wordFirst.halt = .returned w ∧ w.toNat = n := by
            cases hw : wordFirst.halt with
            | running =>
                simp [NatViewState.Agrees, hhalt, hw] at hagreeFirst
            | returned w =>
                exact ⟨w, rfl, by simpa [NatViewState.Agrees, hhalt, hw] using hagreeFirst.2⟩
            | reverted selector =>
                simp [NatViewState.Agrees, hhalt, hw] at hagreeFirst
          refine ⟨natFirst, wordFirst, ?_, ?_, hagreeFirst⟩
          · simp [evalStmtNatView, hnatFirst, hhalt]
          · simp [evalStmtWord, hwordFirst, hwordHalt]
      | reverted selector =>
          obtain ⟨wordSelector, hwordHalt, hselector⟩ : ∃ s,
              wordFirst.halt = .reverted s ∧ selector = s := by
            cases hw : wordFirst.halt with
            | running =>
                simp [NatViewState.Agrees, hhalt, hw] at hagreeFirst
            | returned w =>
                simp [NatViewState.Agrees, hhalt, hw] at hagreeFirst
            | reverted s =>
                exact ⟨s, rfl, by simpa [NatViewState.Agrees, hhalt, hw] using hagreeFirst.2⟩
          refine ⟨natFirst, wordFirst, ?_, ?_, hagreeFirst⟩
          · simp [evalStmtNatView, hnatFirst, hhalt]
          · simp [evalStmtWord, hwordFirst, hwordHalt]
  | letBind name value =>
      obtain ⟨wordValue, hwordValue, hvalue⟩ :=
        evalExprWord_agrees nat.state word value hst.1 hnw
      let natResult : NatViewState :=
        { state := nat.state.setLocal name (evalExpr nat.state value), halt := nat.halt }
      let wordResult := word.setLocal name wordValue
      refine ⟨natResult, wordResult, rfl, by simp [evalStmtWord, hwordValue, wordResult], ?_⟩
      refine ⟨WordState.Agrees.setLocal nat.state word hst.1 name wordValue
        (evalExpr nat.state value) hvalue, ?_⟩
      exact hst.2
  | sstore => contradiction
  | sstoreDyn => contradiction
  | ifRevertSelector cond selector =>
      obtain ⟨wordCond, hwordCond, hcond⟩ :=
        evalExprWord_agrees nat.state word cond hst.1 hnw
      by_cases hc : evalExpr nat.state cond = 1
      · have hwc : wordCond = .ofNat 1 := by
          apply (Word.eq_iff_toNat_eq wordCond (.ofNat 1)).mpr
          rw [Word.toNat_ofNat_of_lt 1 (by decide), hcond, hc]
        let natResult : NatViewState := { nat with halt := .reverted selector }
        let wordResult : WordState := { word with halt := .reverted selector }
        refine ⟨natResult, wordResult, by simp [evalStmtNatView, hc, natResult],
          by simp [evalStmtWord, hwordCond, hwc, Word.beq_eq_true, wordResult], ?_⟩
        exact ⟨hst.1, rfl⟩
      · have hwc : wordCond ≠ .ofNat 1 := by
          intro heq
          apply hc
          rw [← hcond, heq, Word.toNat_ofNat_of_lt 1 (by decide)]
        refine ⟨nat, word, by simp [evalStmtNatView, hc],
          by simp [evalStmtWord, hwordCond, Word.beq_eq_true, hwc], hst⟩
  | log => contradiction
  | revertSelector selector =>
      let natResult : NatViewState := { nat with halt := .reverted selector }
      let wordResult : WordState := { word with halt := .reverted selector }
      exact ⟨natResult, wordResult, rfl, rfl, ⟨hst.1, rfl⟩⟩
  | ret value =>
      obtain ⟨wordValue, hwordValue, hvalue⟩ :=
        evalExprWord_agrees nat.state word value hst.1 hnw
      let natResult : NatViewState :=
        { nat with halt := .returned (evalExpr nat.state value) }
      let wordResult : WordState := { word with halt := .returned wordValue }
      exact ⟨natResult, wordResult, rfl, by simp [evalStmtWord, hwordValue, wordResult],
        ⟨hst.1, hvalue⟩⟩
  | checkReentrancyLock => contradiction
  | setReentrancyLock => contradiction
  | externalCall => contradiction
  | externalCallBind => contradiction
  | staticCall => contradiction
  | staticCallBind => contradiction

/-- A canonical builder-generated `let` chain followed by `ret` returns the expression evaluated
in the state obtained from the existing Nat `evalStmt` semantics for those bindings. -/
theorem evalStmtNatView_seqLets_ret (st : IRState) (binds : List (Lsc.Ident × Expr))
    (result : Expr) :
    evalStmtNatView { state := st }
        (Builder.seqLets binds (.ret result)) =
      some {
        state := evalStmt st (Builder.seqLets binds .skip)
        halt := .returned
          (evalExpr (evalStmt st (Builder.seqLets binds .skip)) result) } := by
  induction binds generalizing st with
  | nil => rfl
  | cons bind rest ih =>
      rcases bind with ⟨name, value⟩
      simp only [Builder.seqLets, evalStmtNatView, evalStmt]
      exact ih (st.setLocal name (evalExpr st value))

/-- Direct returned-value theorem for the shape emitted by `Build.finish (.ret result)`. -/
theorem evalStmtWord_seqLets_returns (st : IRState) (word : WordState)
    (binds : List (Lsc.Ident × Expr)) (result : Expr)
    (hst : word.Agrees st) (hhalt : word.halt = .running)
    (hnw : StmtNoWrap { state := st } (Builder.seqLets binds (.ret result))) :
    ∃ wordResult value,
      evalStmtWord word (Builder.seqLets binds (.ret result)) = some wordResult ∧
      wordResult.halt = .returned value ∧
      value.toNat =
        evalExpr (evalStmt st (Builder.seqLets binds .skip)) result := by
  let natResult : NatViewState := {
    state := evalStmt st (Builder.seqLets binds .skip)
    halt := .returned
      (evalExpr (evalStmt st (Builder.seqLets binds .skip)) result) }
  obtain ⟨actualNat, wordResult, hnat, hword, hagree⟩ :=
    evalStmtWord_agrees { state := st } word
      (Builder.seqLets binds (.ret result))
      ⟨hst, by simp [hhalt]⟩ hnw
  have hnatExpected : actualNat = natResult := by
    rw [evalStmtNatView_seqLets_ret st binds result] at hnat
    exact Option.some.inj hnat.symm
  subst actualNat
  cases hw : wordResult.halt with
  | running =>
      simp [NatViewState.Agrees, natResult, hw] at hagree
  | returned value =>
      refine ⟨wordResult, value, hword, hw, ?_⟩
      simpa [NatViewState.Agrees, natResult, hw] using hagree.2
  | reverted selector =>
      simp [NatViewState.Agrees, natResult, hw] at hagree

end Lsc.Compile.IR
