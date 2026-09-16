import Mathlib.Tactic.SplitIfs
import Lsc.Lang.TxTheorems
import Lsc.Lang.AmountTheorems
import Stdlib.ERC20.Base

/-!
Tx-level lemmas for the ERC20 base: exact `Tx.run` post-states, conservation,
and `IERC20.Exact (ERC20.impl F)`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open Lsc Lsc.Stdlib

namespace Lsc.Stdlib.ERC20
namespace Proof

variable {S X E ε : Type} {a : Asset}
variable [Events E a] [Errors ε]
variable (F : Fields S a)
variable [Fields.Lawful F]
variable (ctx : Ctx) (w : World S X E)

/-- `bals` after removing `amount` from `addr`. -/
def debit (bals : Address ↦ Amount a) (addr : Address) (amount : Amount a) :
    Address ↦ Amount a :=
  Function.update bals addr (bals addr - amount)

/-- `bals` after adding `amount` to `addr`. -/
def credit (bals : Address ↦ Amount a) (addr : Address) (amount : Amount a) :
    Address ↦ Amount a :=
  Function.update bals addr (bals addr + amount)

@[simp] theorem debit_self (bals : Address ↦ Amount a) (addr : Address)
    (n : Amount a) : debit bals addr n addr = bals addr - n := by simp [debit]
@[simp] theorem credit_self (bals : Address ↦ Amount a) (addr : Address)
    (n : Amount a) : credit bals addr n addr = bals addr + n := by simp [credit]
theorem debit_other (bals : Address ↦ Amount a) {addr b : Address}
    (h : b ≠ addr) (n : Amount a) : debit bals addr n b = bals b := by
  simp [debit, Function.update_of_ne h]
theorem credit_other (bals : Address ↦ Amount a) {addr b : Address}
    (h : b ≠ addr) (n : Amount a) : credit bals addr n b = bals b := by
  simp [credit, Function.update_of_ne h]

@[simp] theorem debit_apply_raw (bals : Address ↦ Amount a)
    (src to : Address) (amount : Amount a) :
    (debit bals src amount to).raw =
      Function.update (fun i => (bals i).raw) src ((bals src).raw - amount.raw) to := by
  simp [debit, Amount.update_raw_apply, Amount.raw_sub]

@[simp] theorem debit_credit_raw (bals : Address ↦ Amount a)
    (src to : Address) (amount : Amount a) :
    (debit bals src amount to + amount).raw =
      Function.update (fun i => (bals i).raw) src ((bals src).raw - amount.raw) to +
        amount.raw := by
  simp [debit_apply_raw, Amount.raw_add]

/-- `(x - y) + (z + y) = x + z` when `y ≤ x`. -/
private theorem nat_sub_add_add (x y z : Nat) (h : y ≤ x) :
    x - y + (z + y) = x + z := by
  rw [Nat.add_comm z y, ← Nat.add_assoc, Nat.sub_add_cancel h]

private lemma amount_add_comm (x y : Amount a) : x + y = y + x :=
  Amount.ext (Nat.add_comm _ _)

private lemma ge_self_add (x y : Amount a) : x + y ≥ x :=
  Nat.le_add_right x.raw y.raw

private lemma ge_add_add (x y z : Amount a) : x + y + z ≥ x := by
  have hxy : x.raw ≤ x.raw + y.raw := Nat.le_add_right _ _
  have : x.raw ≤ x.raw + y.raw + z.raw :=
    Nat.le_trans hxy (Nat.le_add_right (x.raw + y.raw) z.raw)
  simpa [Amount.raw_add] using this

private lemma sub_add_ge (b al n : Amount a) (hn : n.raw ≤ b.raw) (ha : n.raw ≤ al.raw) :
    b - n + al ≥ b := by
  have : b.raw ≤ b.raw - n.raw + al.raw :=
    calc
      b.raw = b.raw - n.raw + n.raw := (Nat.sub_add_cancel hn).symm
      _ ≤ b.raw - n.raw + al.raw := Nat.add_le_add_left ha _
  simpa [Amount.raw_sub, Amount.raw_add] using this

/-! ### Views -/

theorem balanceOf_returns (who : Address) :
    Tx.run (balanceOf (ε := ε) F who) ctx w =
      .ok (F.balances.get w.self who, w) := by
  simp [balanceOf]

theorem totalSupply_returns :
    Tx.run (totalSupply (ε := ε) F) ctx w =
      .ok (F.totalSupply.get w.self, w) := by
  simp [totalSupply]

theorem allowance_returns (owner spender : Address) :
    Tx.run (allowance (ε := ε) F owner spender) ctx w =
      .ok (F.allowances.get w.self owner spender, w) := by
  simp [allowance]

/-! ### transfer -/

def transferPost (σ : S) (src to : Address) (amount : Amount a) : S :=
  F.balances.set σ (credit (debit (F.balances.get σ) src amount) to amount)

theorem transfer_ok (to : Address) (amount : Amount a)
    (hsub : amount ≤ F.balances.get w.self ctx.sender)
    (hadd : (debit (F.balances.get w.self) ctx.sender amount to + amount).raw <
      wordBound) :
    Tx.run (transfer (ε := ε) F to amount) ctx w =
      .ok (true, { w with
        self := transferPost F w.self ctx.sender to amount
        log := w.log ++ [Events.transfer ctx.sender to amount] }) := by
  have hle : amount.raw ≤ (F.balances.get w.self ctx.sender).raw := hsub
  have hbound :
      Function.update (fun i => (F.balances.get w.self i).raw) ctx.sender
          ((F.balances.get w.self ctx.sender).raw - amount.raw) to +
        amount.raw < wordBound := by
    simpa [debit, Amount.raw_add, Amount.raw_sub, Amount.update_raw_apply] using hadd
  simp [transfer, hle, Field.Lawful.get_set]
  simp [hbound, Amount.raw_add, Amount.update_raw_apply]
  simp [transferPost, debit, credit, Amount.update2_raw,
    Amount.ofWord_update_lookup, Amount.ofWord_raw, Field.Lawful.get_set,
    Field.Lawful.set_set]

theorem transfer_reverts_on_insufficient_balance (to : Address) (amount : Amount a)
    (h : ¬ amount ≤ F.balances.get w.self ctx.sender) :
    Tx.run (transfer (ε := ε) F to amount) ctx w =
      .error (.user Errors.insufficientBalance) := by
  have hle : ¬ amount.raw ≤ (F.balances.get w.self ctx.sender).raw := h
  simp [transfer, hle]

theorem transfer_reverts_on_overflow (to : Address) (amount : Amount a)
    (hsub : amount ≤ F.balances.get w.self ctx.sender)
    (hadd : ¬ (debit (F.balances.get w.self) ctx.sender amount to + amount).raw <
      wordBound) :
    Tx.run (transfer (ε := ε) F to amount) ctx w = .error (.arith .overflow) := by
  have hle : amount.raw ≤ (F.balances.get w.self ctx.sender).raw := hsub
  have hbound :
      ¬ (Function.update (fun i => (F.balances.get w.self i).raw) ctx.sender
          ((F.balances.get w.self ctx.sender).raw - amount.raw) to +
        amount.raw < wordBound) := by
    simpa [debit, Amount.raw_add, Amount.raw_sub, Amount.update_raw_apply] using hadd
  simp [transfer, hle, Field.Lawful.get_set]
  simp [hbound, Amount.raw_add, Amount.update_raw_apply]

theorem transfer_ok_inv (to : Address) (amount : Amount a) {w' : World S X E}
    (h : Tx.run (transfer (ε := ε) F to amount) ctx w = .ok (true, w')) :
    amount ≤ F.balances.get w.self ctx.sender ∧
    (debit (F.balances.get w.self) ctx.sender amount to + amount).raw < wordBound ∧
    w' = { w with
      self := transferPost F w.self ctx.sender to amount
      log := w.log ++ [Events.transfer ctx.sender to amount] } := by
  by_cases hsub : amount ≤ F.balances.get w.self ctx.sender
  · by_cases hadd :
      (debit (F.balances.get w.self) ctx.sender amount to + amount).raw < wordBound
    · rw [transfer_ok F ctx w to amount hsub hadd] at h
      cases h
      exact ⟨hsub, hadd, rfl⟩
    · rw [transfer_reverts_on_overflow F ctx w to amount hsub hadd] at h
      cases h
  · rw [transfer_reverts_on_insufficient_balance F ctx w to amount hsub] at h
    cases h

theorem transfer_conserves (to : Address) (amount : Amount a) {w' : World S X E}
    (h : Tx.run (transfer (ε := ε) F to amount) ctx w = .ok (true, w')) :
    F.balances.get w'.self ctx.sender + F.balances.get w'.self to =
      F.balances.get w.self ctx.sender + F.balances.get w.self to := by
  have ⟨hsub, _, hw'⟩ := transfer_ok_inv F ctx w to amount h
  if hne : ctx.sender = to then
    subst hne
    apply Amount.ext
    have hle : amount.raw ≤ (F.balances.get w.self ctx.sender).raw := hsub
    simp [hw', transferPost, credit_self, debit_self, Amount.raw_add,
      Amount.raw_sub, Field.Lawful.get_set, Nat.sub_add_cancel hle]
  else
    apply Amount.ext
    have hle : amount.raw ≤ (F.balances.get w.self ctx.sender).raw := hsub
    simp [hw', transferPost, credit_other _ hne, debit_other _ (Ne.symm hne),
      Amount.raw_add, Amount.raw_sub, Field.Lawful.get_set]
    exact nat_sub_add_add _ _ _ hle

theorem transfer_credits (to : Address) (amount : Amount a) {w' : World S X E}
    (h : Tx.run (transfer (ε := ε) F to amount) ctx w = .ok (true, w'))
    (hne : ctx.sender ≠ to) :
    F.balances.get w'.self to = F.balances.get w.self to + amount := by
  have ⟨_, _, hw'⟩ := transfer_ok_inv F ctx w to amount h
  simp [hw', transferPost, debit_other _ hne.symm, Field.Lawful.get_set]

theorem transfer_debits (to : Address) (amount : Amount a) {w' : World S X E}
    (h : Tx.run (transfer (ε := ε) F to amount) ctx w = .ok (true, w'))
    (hne : ctx.sender ≠ to) :
    F.balances.get w'.self ctx.sender + amount =
      F.balances.get w.self ctx.sender := by
  have ⟨hsub, _, hw'⟩ := transfer_ok_inv F ctx w to amount h
  apply Amount.ext
  simp [hw', transferPost, debit, credit, Amount.raw_add, Amount.raw_sub,
    Function.update_of_ne hne, Field.Lawful.get_set]
  exact Nat.sub_add_cancel hsub

theorem transfer_self (to : Address) (amount : Amount a) {w' : World S X E}
    (h : Tx.run (transfer (ε := ε) F to amount) ctx w = .ok (true, w'))
    (heq : ctx.sender = to) :
    F.balances.get w'.self ctx.sender = F.balances.get w.self ctx.sender := by
  have ⟨hsub, _, hw'⟩ := transfer_ok_inv F ctx w to amount h
  subst hw' heq
  apply Amount.ext
  simp [transferPost, debit, credit, Amount.raw_add, Amount.raw_sub,
    Field.Lawful.get_set]
  exact Nat.sub_add_cancel hsub

theorem transfer_others (to : Address) (amount : Amount a) {w' : World S X E}
    (h : Tx.run (transfer (ε := ε) F to amount) ctx w = .ok (true, w'))
    (x : Address) (hx1 : x ≠ ctx.sender) (hx2 : x ≠ to) :
    F.balances.get w'.self x = F.balances.get w.self x := by
  have ⟨_, _, hw'⟩ := transfer_ok_inv F ctx w to amount h
  simp [hw', transferPost, credit_other _ hx2, debit_other _ hx1,
    Field.Lawful.get_set]

theorem transfer_preserves_totalSupply (to : Address) (amount : Amount a)
    {w' : World S X E}
    (h : Tx.run (transfer (ε := ε) F to amount) ctx w = .ok (true, w')) :
    F.totalSupply.get w'.self = F.totalSupply.get w.self := by
  have ⟨_, _, hw'⟩ := transfer_ok_inv F ctx w to amount h
  simp [hw', transferPost, Field.Independent.get_set_other]

theorem transfer_preserves_allowances (to : Address) (amount : Amount a)
    {w' : World S X E}
    (h : Tx.run (transfer (ε := ε) F to amount) ctx w = .ok (true, w')) :
    F.allowances.get w'.self = F.allowances.get w.self := by
  have ⟨_, _, hw'⟩ := transfer_ok_inv F ctx w to amount h
  simp [hw', transferPost, Field.Independent.get_set_other]

theorem transfer_returns_true (to : Address) (amount : Amount a)
    {r : Bool} {w' : World S X E}
    (h : Tx.run (transfer (ε := ε) F to amount) ctx w = .ok (r, w')) :
    r = true := by
  by_cases hsub : amount ≤ F.balances.get w.self ctx.sender
  · by_cases hadd :
      (debit (F.balances.get w.self) ctx.sender amount to + amount).raw < wordBound
    · rw [transfer_ok F ctx w to amount hsub hadd] at h
      cases h; rfl
    · rw [transfer_reverts_on_overflow F ctx w to amount hsub hadd] at h
      cases h
  · rw [transfer_reverts_on_insufficient_balance F ctx w to amount hsub] at h
    cases h

/-! ### approve -/

def approvePost (σ : S) (owner spender : Address) (amount : Amount a) : S :=
  F.allowances.set σ (Function.update (F.allowances.get σ) owner
    (Function.update (F.allowances.get σ owner) spender amount))

theorem approve_ok (spender : Address) (amount : Amount a) :
    Tx.run (approve (ε := ε) F spender amount) ctx w =
      .ok (true, { w with
        self := approvePost F w.self ctx.sender spender amount
        log := w.log ++ [Events.approval ctx.sender spender amount] }) := by
  simp [approve, approvePost, Amount.update_nested_raw, Amount.ofWord_raw,
    Field.Lawful.get_set]

theorem approve_sets (spender : Address) (amount : Amount a) {w' : World S X E}
    (h : Tx.run (approve (ε := ε) F spender amount) ctx w = .ok (true, w')) :
    F.allowances.get w'.self ctx.sender spender = amount := by
  rw [approve_ok F ctx w spender amount] at h
  cases h
  simp [approvePost, Field.Lawful.get_set]

theorem approve_preserves_balances (spender : Address) (amount : Amount a)
    {w' : World S X E}
    (h : Tx.run (approve (ε := ε) F spender amount) ctx w = .ok (true, w')) :
    F.balances.get w'.self = F.balances.get w.self := by
  rw [approve_ok F ctx w spender amount] at h
  cases h
  simp [approvePost, Field.Independent.get_set_other]

theorem approve_preserves_totalSupply (spender : Address) (amount : Amount a)
    {w' : World S X E}
    (h : Tx.run (approve (ε := ε) F spender amount) ctx w = .ok (true, w')) :
    F.totalSupply.get w'.self = F.totalSupply.get w.self := by
  rw [approve_ok F ctx w spender amount] at h
  cases h
  simp [approvePost, Field.Independent.get_set_other]

theorem approve_returns_true (spender : Address) (amount : Amount a)
    {r : Bool} {w' : World S X E}
    (h : Tx.run (approve (ε := ε) F spender amount) ctx w = .ok (r, w')) :
    r = true := by
  rw [approve_ok F ctx w spender amount] at h
  cases h; rfl

/-! ### transferFrom -/

def transferFromPost (σ : S) (src spender to : Address) (amount : Amount a) : S :=
  F.balances.set
    (F.allowances.set σ (Function.update (F.allowances.get σ) src
      (Function.update (F.allowances.get σ src) spender
        (F.allowances.get σ src spender - amount))))
    (credit (debit (F.balances.get σ) src amount) to amount)

theorem transferFrom_ok (src to : Address) (amount : Amount a)
    (hallow : amount ≤ F.allowances.get w.self src ctx.sender)
    (hsub : amount ≤ F.balances.get w.self src)
    (hadd : (debit (F.balances.get w.self) src amount to + amount).raw < wordBound) :
    Tx.run (transferFrom (ε := ε) F src to amount) ctx w =
      .ok (true, { w with
        self := transferFromPost F w.self src ctx.sender to amount
        log := w.log ++ [Events.transfer src to amount] }) := by
  have hallow' : amount.raw ≤ (F.allowances.get w.self src ctx.sender).raw := hallow
  have hsub' : amount.raw ≤ (F.balances.get w.self src).raw := hsub
  simp only [debit_credit_raw] at hadd
  have hbound :
      Function.update (fun i => (F.balances.get w.self i).raw) src
          ((F.balances.get w.self src).raw - amount.raw) to +
        amount.raw < wordBound := by
    simpa [debit, Amount.raw_add, Amount.raw_sub, Amount.update_raw_apply] using hadd
  simp [transferFrom, hallow', hsub', Field.Lawful.get_set,
    Field.Independent.get_set_other]
  simp [hbound, Amount.raw_add, Amount.update_raw_apply]
  simp [transferFromPost, debit, credit, Amount.update_nested_raw,
    Amount.update2_raw, Amount.ofWord_update_lookup, Amount.ofWord_raw,
    Field.Lawful.get_set, Field.Independent.get_set_other, Field.Lawful.set_set]

theorem transferFrom_reverts_on_insufficient_allowance (src to : Address)
    (amount : Amount a)
    (h : ¬ amount ≤ F.allowances.get w.self src ctx.sender) :
    Tx.run (transferFrom (ε := ε) F src to amount) ctx w =
      .error (.user Errors.insufficientAllowance) := by
  have hle : ¬ amount.raw ≤ (F.allowances.get w.self src ctx.sender).raw := h
  simp [transferFrom, hle]

theorem transferFrom_reverts_on_insufficient_balance (src to : Address)
    (amount : Amount a)
    (hallow : amount ≤ F.allowances.get w.self src ctx.sender)
    (h : ¬ amount ≤ F.balances.get w.self src) :
    Tx.run (transferFrom (ε := ε) F src to amount) ctx w =
      .error (.user Errors.insufficientBalance) := by
  have hallow' : amount.raw ≤ (F.allowances.get w.self src ctx.sender).raw := hallow
  have hle : ¬ amount.raw ≤ (F.balances.get w.self src).raw := h
  simp [transferFrom, hallow', hle]

theorem transferFrom_reverts_on_overflow (src to : Address) (amount : Amount a)
    (hallow : amount ≤ F.allowances.get w.self src ctx.sender)
    (hsub : amount ≤ F.balances.get w.self src)
    (hadd : ¬ (debit (F.balances.get w.self) src amount to + amount).raw < wordBound) :
    Tx.run (transferFrom (ε := ε) F src to amount) ctx w = .error (.arith .overflow) := by
  have hallow' : amount.raw ≤ (F.allowances.get w.self src ctx.sender).raw := hallow
  have hsub' : amount.raw ≤ (F.balances.get w.self src).raw := hsub
  have hbound :
      ¬ (Function.update (fun i => (F.balances.get w.self i).raw) src
          ((F.balances.get w.self src).raw - amount.raw) to +
        amount.raw < wordBound) := by
    simpa [debit, Amount.raw_add, Amount.raw_sub, Amount.update_raw_apply] using hadd
  simp [transferFrom, hallow', hsub', Field.Lawful.get_set,
    Field.Independent.get_set_other]
  simp [hbound, Amount.raw_add, Amount.update_raw_apply]

theorem transferFrom_ok_inv (src to : Address) (amount : Amount a)
    {w' : World S X E}
    (h : Tx.run (transferFrom (ε := ε) F src to amount) ctx w = .ok (true, w')) :
    amount ≤ F.allowances.get w.self src ctx.sender ∧
    amount ≤ F.balances.get w.self src ∧
    (debit (F.balances.get w.self) src amount to + amount).raw < wordBound ∧
    w' = { w with
      self := transferFromPost F w.self src ctx.sender to amount
      log := w.log ++ [Events.transfer src to amount] } := by
  by_cases hallow : amount ≤ F.allowances.get w.self src ctx.sender
  · by_cases hsub : amount ≤ F.balances.get w.self src
    · by_cases hadd :
        (debit (F.balances.get w.self) src amount to + amount).raw < wordBound
      · rw [transferFrom_ok F ctx w src to amount hallow hsub hadd] at h
        cases h
        exact ⟨hallow, hsub, hadd, rfl⟩
      · rw [transferFrom_reverts_on_overflow F ctx w src to amount hallow hsub hadd] at h
        cases h
    · rw [transferFrom_reverts_on_insufficient_balance F ctx w src to amount hallow hsub] at h
      cases h
  · rw [transferFrom_reverts_on_insufficient_allowance F ctx w src to amount hallow] at h
    cases h

theorem transferFrom_conserves (src to : Address) (amount : Amount a)
    {w' : World S X E}
    (h : Tx.run (transferFrom (ε := ε) F src to amount) ctx w = .ok (true, w')) :
    F.balances.get w'.self src + F.balances.get w'.self to =
      F.balances.get w.self src + F.balances.get w.self to := by
  have ⟨_, hsub, _, hw'⟩ := transferFrom_ok_inv F ctx w src to amount h
  if hne : src = to then
    subst hne
    apply Amount.ext
    have hle : amount.raw ≤ (F.balances.get w.self src).raw := hsub
    simp [hw', transferFromPost, credit_self, debit_self, Amount.raw_add,
      Amount.raw_sub, Field.Lawful.get_set, Field.Independent.get_set_other,
      Nat.sub_add_cancel hle]
  else
    apply Amount.ext
    have hle : amount.raw ≤ (F.balances.get w.self src).raw := hsub
    simp [hw', transferFromPost, credit_other _ hne, debit_other _ (Ne.symm hne),
      Amount.raw_add, Amount.raw_sub, Field.Lawful.get_set,
      Field.Independent.get_set_other]
    exact nat_sub_add_add _ _ _ hle

theorem transferFrom_credits (src to : Address) (amount : Amount a)
    {w' : World S X E}
    (h : Tx.run (transferFrom (ε := ε) F src to amount) ctx w = .ok (true, w'))
    (hne : src ≠ to) :
    F.balances.get w'.self to = F.balances.get w.self to + amount := by
  have ⟨_, _, _, hw'⟩ := transferFrom_ok_inv F ctx w src to amount h
  simp [hw', transferFromPost, debit_other _ hne.symm, Field.Lawful.get_set,
    Field.Independent.get_set_other]

theorem transferFrom_debits (src to : Address) (amount : Amount a)
    {w' : World S X E}
    (h : Tx.run (transferFrom (ε := ε) F src to amount) ctx w = .ok (true, w'))
    (hne : src ≠ to) :
    F.balances.get w'.self src + amount = F.balances.get w.self src := by
  have ⟨_, hsub, _, hw'⟩ := transferFrom_ok_inv F ctx w src to amount h
  apply Amount.ext
  simp [hw', transferFromPost, debit, credit, Amount.raw_add, Amount.raw_sub,
    Function.update_of_ne hne, Field.Lawful.get_set, Field.Independent.get_set_other]
  exact Nat.sub_add_cancel hsub

theorem transferFrom_self (src to : Address) (amount : Amount a)
    {w' : World S X E}
    (h : Tx.run (transferFrom (ε := ε) F src to amount) ctx w = .ok (true, w'))
    (heq : src = to) :
    F.balances.get w'.self src = F.balances.get w.self src := by
  have ⟨_, hsub, _, hw'⟩ := transferFrom_ok_inv F ctx w src to amount h
  subst hw' heq
  apply Amount.ext
  simp [transferFromPost, debit, credit, Amount.raw_add, Amount.raw_sub,
    Field.Lawful.get_set, Field.Independent.get_set_other]
  exact Nat.sub_add_cancel hsub

theorem transferFrom_others (src to : Address) (amount : Amount a)
    {w' : World S X E}
    (h : Tx.run (transferFrom (ε := ε) F src to amount) ctx w = .ok (true, w'))
    (x : Address) (hx1 : x ≠ src) (hx2 : x ≠ to) :
    F.balances.get w'.self x = F.balances.get w.self x := by
  have ⟨_, _, _, hw'⟩ := transferFrom_ok_inv F ctx w src to amount h
  simp [hw', transferFromPost, credit_other _ hx2, debit_other _ hx1,
    Field.Lawful.get_set, Field.Independent.get_set_other]

theorem transferFrom_allowance (src to : Address) (amount : Amount a)
    {w' : World S X E}
    (h : Tx.run (transferFrom (ε := ε) F src to amount) ctx w = .ok (true, w')) :
    F.allowances.get w'.self src ctx.sender + amount =
      F.allowances.get w.self src ctx.sender := by
  have ⟨hallow, _, _, hw'⟩ := transferFrom_ok_inv F ctx w src to amount h
  apply Amount.ext
  have hle : amount.raw ≤ (F.allowances.get w.self src ctx.sender).raw := hallow
  simp [hw', transferFromPost, Amount.raw_add, Amount.raw_sub,
    Field.Lawful.get_set, Field.Independent.get_set_other, Nat.sub_add_cancel hle]

theorem transferFrom_preserves_totalSupply (src to : Address) (amount : Amount a)
    {w' : World S X E}
    (h : Tx.run (transferFrom (ε := ε) F src to amount) ctx w = .ok (true, w')) :
    F.totalSupply.get w'.self = F.totalSupply.get w.self := by
  have ⟨_, _, _, hw'⟩ := transferFrom_ok_inv F ctx w src to amount h
  simp [hw', transferFromPost, Field.Independent.get_set_other]

theorem transferFrom_returns_true (src to : Address) (amount : Amount a)
    {r : Bool} {w' : World S X E}
    (h : Tx.run (transferFrom (ε := ε) F src to amount) ctx w = .ok (r, w')) :
    r = true := by
  by_cases hallow : amount ≤ F.allowances.get w.self src ctx.sender
  · by_cases hsub : amount ≤ F.balances.get w.self src
    · by_cases hadd :
        (debit (F.balances.get w.self) src amount to + amount).raw < wordBound
      · rw [transferFrom_ok F ctx w src to amount hallow hsub hadd] at h
        cases h; rfl
      · rw [transferFrom_reverts_on_overflow F ctx w src to amount hallow hsub hadd] at h
        cases h
    · rw [transferFrom_reverts_on_insufficient_balance F ctx w src to amount hallow hsub] at h
      cases h
  · rw [transferFrom_reverts_on_insufficient_allowance F ctx w src to amount hallow] at h
    cases h

/-! ### mint / burn -/

def mintPost (σ : S) (to : Address) (amount : Amount a) : S :=
  F.balances.set (F.totalSupply.set σ (F.totalSupply.get σ + amount))
    (credit (F.balances.get σ) to amount)

theorem mint_ok (to : Address) (amount : Amount a)
    (hsupply : (F.totalSupply.get w.self + amount).raw < wordBound)
    (hadd : (F.balances.get w.self to + amount).raw < wordBound) :
    Tx.run (mint (ε := ε) F to amount) ctx w =
      .ok ((), { w with
        self := mintPost F w.self to amount
        log := w.log ++ [Events.transfer 0 to amount] }) := by
  simp [Amount.raw_add] at hsupply hadd
  simp [mint, Field.Lawful.get_set, Field.Independent.get_set_other]
  simp [hsupply]
  simp [hadd]
  simp [mintPost, credit, Amount.update_raw, Amount.ofWord_raw,
    Field.Lawful.get_set, Field.Independent.get_set_other]

theorem mint_reverts_on_supply_overflow (to : Address) (amount : Amount a)
    (hsupply : ¬ (F.totalSupply.get w.self + amount).raw < wordBound) :
    Tx.run (mint (ε := ε) F to amount) ctx w = .error (.arith .overflow) := by
  have hs : ¬ (F.totalSupply.get w.self).raw + amount.raw < wordBound := by
    simpa [Amount.raw_add] using hsupply
  simp [mint, hs]

theorem mint_reverts_on_balance_overflow (to : Address) (amount : Amount a)
    (hsupply : (F.totalSupply.get w.self + amount).raw < wordBound)
    (hadd : ¬ (F.balances.get w.self to + amount).raw < wordBound) :
    Tx.run (mint (ε := ε) F to amount) ctx w = .error (.arith .overflow) := by
  have hs : (F.totalSupply.get w.self).raw + amount.raw < wordBound := by
    simpa [Amount.raw_add] using hsupply
  have hb : ¬ (F.balances.get w.self to).raw + amount.raw < wordBound := by
    simpa [Amount.raw_add] using hadd
  simp [mint, Field.Lawful.get_set, Field.Independent.get_set_other]
  simp [hs]
  simp [hb]

theorem mint_ok_inv (to : Address) (amount : Amount a) {w' : World S X E}
    (h : Tx.run (mint (ε := ε) F to amount) ctx w = .ok ((), w')) :
    (F.totalSupply.get w.self + amount).raw < wordBound ∧
    (F.balances.get w.self to + amount).raw < wordBound ∧
    w' = { w with
      self := mintPost F w.self to amount
      log := w.log ++ [Events.transfer 0 to amount] } := by
  by_cases hsupply : (F.totalSupply.get w.self + amount).raw < wordBound
  · by_cases hadd : (F.balances.get w.self to + amount).raw < wordBound
    · rw [mint_ok F ctx w to amount hsupply hadd] at h
      cases h
      exact ⟨hsupply, hadd, rfl⟩
    · rw [mint_reverts_on_balance_overflow F ctx w to amount hsupply hadd] at h
      cases h
  · rw [mint_reverts_on_supply_overflow F ctx w to amount hsupply] at h
    cases h

theorem mint_delta (to : Address) (amount : Amount a) {w' : World S X E}
    (h : Tx.run (mint (ε := ε) F to amount) ctx w = .ok ((), w')) :
    F.balances.get w'.self to = F.balances.get w.self to + amount ∧
    F.totalSupply.get w'.self = F.totalSupply.get w.self + amount := by
  have ⟨_, _, hw'⟩ := mint_ok_inv F ctx w to amount h
  simp [hw', mintPost, credit, Field.Lawful.get_set, Field.Independent.get_set_other]

theorem mint_others (to : Address) (amount : Amount a) {w' : World S X E}
    (h : Tx.run (mint (ε := ε) F to amount) ctx w = .ok ((), w'))
    (x : Address) (hx : x ≠ to) :
    F.balances.get w'.self x = F.balances.get w.self x := by
  have ⟨_, _, hw'⟩ := mint_ok_inv F ctx w to amount h
  simp [hw', mintPost, credit_other _ hx, Field.Lawful.get_set,
    Field.Independent.get_set_other]

def burnPost (σ : S) (src : Address) (amount : Amount a) : S :=
  F.totalSupply.set (F.balances.set σ (debit (F.balances.get σ) src amount))
    (F.totalSupply.get σ - amount)

theorem burn_ok (src : Address) (amount : Amount a)
    (hsub : amount ≤ F.balances.get w.self src)
    (hsupply : amount ≤ F.totalSupply.get w.self) :
    Tx.run (burn (ε := ε) F src amount) ctx w =
      .ok ((), { w with
        self := burnPost F w.self src amount
        log := w.log ++ [Events.transfer src 0 amount] }) := by
  have hle : amount.raw ≤ (F.balances.get w.self src).raw := hsub
  have hsup : amount.raw ≤ (F.totalSupply.get w.self).raw := hsupply
  simp [burn, hle, Field.Lawful.get_set, Field.Independent.get_set_other]
  simp [hsup]
  simp [burnPost, debit, Amount.update_raw, Amount.ofWord_raw,
    Field.Lawful.get_set, Field.Independent.get_set_other]

theorem burn_reverts_on_insufficient_balance (src : Address) (amount : Amount a)
    (h : ¬ amount ≤ F.balances.get w.self src) :
    Tx.run (burn (ε := ε) F src amount) ctx w =
      .error (.user Errors.insufficientBalance) := by
  have hle : ¬ amount.raw ≤ (F.balances.get w.self src).raw := h
  simp [burn, hle]

theorem burn_reverts_on_insufficient_supply (src : Address) (amount : Amount a)
    (hsub : amount ≤ F.balances.get w.self src)
    (hsupply : ¬ amount ≤ F.totalSupply.get w.self) :
    Tx.run (burn (ε := ε) F src amount) ctx w = .error (.arith .underflow) := by
  have hle : amount.raw ≤ (F.balances.get w.self src).raw := hsub
  have hsup : ¬ amount.raw ≤ (F.totalSupply.get w.self).raw := hsupply
  simp [burn, hle, Field.Lawful.get_set, Field.Independent.get_set_other]
  simp [hsup]

theorem burn_ok_inv (src : Address) (amount : Amount a) {w' : World S X E}
    (h : Tx.run (burn (ε := ε) F src amount) ctx w = .ok ((), w')) :
    amount ≤ F.balances.get w.self src ∧
    amount ≤ F.totalSupply.get w.self ∧
    w' = { w with
      self := burnPost F w.self src amount
      log := w.log ++ [Events.transfer src 0 amount] } := by
  by_cases hsub : amount ≤ F.balances.get w.self src
  · by_cases hsupply : amount ≤ F.totalSupply.get w.self
    · rw [burn_ok F ctx w src amount hsub hsupply] at h
      cases h
      exact ⟨hsub, hsupply, rfl⟩
    · rw [burn_reverts_on_insufficient_supply F ctx w src amount hsub hsupply] at h
      cases h
  · rw [burn_reverts_on_insufficient_balance F ctx w src amount hsub] at h
    cases h

theorem burn_delta (src : Address) (amount : Amount a) {w' : World S X E}
    (h : Tx.run (burn (ε := ε) F src amount) ctx w = .ok ((), w')) :
    F.balances.get w'.self src + amount = F.balances.get w.self src ∧
    F.totalSupply.get w'.self + amount = F.totalSupply.get w.self := by
  have ⟨hsub, hsupply, hw'⟩ := burn_ok_inv F ctx w src amount h
  constructor
  · apply Amount.ext
    simp [hw', burnPost, debit_self, Amount.raw_add, Amount.raw_sub,
      Field.Lawful.get_set, Field.Independent.get_set_other]
    exact Nat.sub_add_cancel hsub
  · apply Amount.ext
    simp [hw', burnPost, Amount.raw_add, Amount.raw_sub, Field.Lawful.get_set,
      Field.Independent.get_set_other]
    exact Nat.sub_add_cancel hsupply

theorem burn_others (src : Address) (amount : Amount a) {w' : World S X E}
    (h : Tx.run (burn (ε := ε) F src amount) ctx w = .ok ((), w'))
    (x : Address) (hx : x ≠ src) :
    F.balances.get w'.self x = F.balances.get w.self x := by
  have ⟨_, _, hw'⟩ := burn_ok_inv F ctx w src amount h
  simp [hw', burnPost, debit_other _ hx, Field.Lawful.get_set,
    Field.Independent.get_set_other]

/-! ### `IERC20.Impl` unfolding -/

@[simp] theorem impl_transfer (to : Address) (amount : Amount a) :
    (impl (ε := ε) F).transfer to amount ctx w =
      (Tx.run (transfer (ε := ε) F to amount) ctx w).toOption :=
  rfl

@[simp] theorem impl_transferFrom (src to : Address) (amount : Amount a) :
    (impl (ε := ε) F).transferFrom src to amount ctx w =
      (Tx.run (transferFrom (ε := ε) F src to amount) ctx w).toOption :=
  rfl

@[simp] theorem impl_approve (spender : Address) (amount : Amount a) :
    (impl (ε := ε) F).approve spender amount ctx w =
      (Tx.run (approve (ε := ε) F spender amount) ctx w).toOption :=
  rfl

@[simp] theorem impl_balanceOf (who : Address) (w : World S X E) :
    (impl (ε := ε) (X := X) F).balanceOf who w = F.balances.get w.self who :=
  rfl

@[simp] theorem impl_allowance (owner spender : Address) (w : World S X E) :
    (impl (ε := ε) (X := X) F).allowance owner spender w =
      F.allowances.get w.self owner spender :=
  rfl

@[simp] theorem impl_totalSupply (w : World S X E) :
    (impl (ε := ε) (X := X) F).totalSupply w = F.totalSupply.get w.self :=
  rfl

theorem transfer_balance_protected (to : Address) (amount : Amount a)
    {r : Bool} {w' : World S X E} (x : Address)
    (h : Tx.run (transfer (ε := ε) F to amount) ctx w = .ok (r, w'))
    (hne : ctx.sender ≠ x) :
    F.balances.get w'.self x + F.allowances.get w.self x ctx.sender ≥
      F.balances.get w.self x := by
  have hr := transfer_returns_true F ctx w to amount h
  subst hr
  obtain ⟨_, _, hw'⟩ := transfer_ok_inv F ctx w to amount h
  subst hw'
  if hx : x = to then
    have hne' : ctx.sender ≠ to := hx ▸ hne
    have hb : F.balances.get (transferPost F w.self ctx.sender to amount) to =
        F.balances.get w.self to + amount := by
      simp [transferPost, debit_other _ (Ne.symm hne'), Field.Lawful.get_set]
    rw [hx, hb]
    exact ge_add_add _ _ _
  else
    have hb : F.balances.get (transferPost F w.self ctx.sender to amount) x =
        F.balances.get w.self x := by
      simp [transferPost, credit_other _ hx, debit_other _ (Ne.symm hne),
        Field.Lawful.get_set]
    rw [hb]
    exact ge_self_add _ _

theorem transferFrom_balance_protected (src to : Address) (amount : Amount a)
    {r : Bool} {w' : World S X E} (x : Address)
    (h : Tx.run (transferFrom (ε := ε) F src to amount) ctx w = .ok (r, w'))
    (hne : ctx.sender ≠ x) :
    F.balances.get w'.self x + F.allowances.get w.self x ctx.sender ≥
      F.balances.get w.self x := by
  have hr := transferFrom_returns_true F ctx w src to amount h
  subst hr
  obtain ⟨hallow, hsub, _, hw'⟩ := transferFrom_ok_inv F ctx w src to amount h
  subst hw'
  if hx : x = src then
    if hto : src = to then
      have hle : amount.raw ≤ (F.balances.get w.self src).raw := hsub
      have hb : F.balances.get (transferFromPost F w.self src ctx.sender src amount) src =
          F.balances.get w.self src := by
        apply Amount.ext
        simp [transferFromPost, debit, credit, Function.update_self,
          Amount.raw_add, Amount.raw_sub, Field.Lawful.get_set,
          Field.Independent.get_set_other, Nat.sub_add_cancel hle]
      have hpost : F.balances.get (transferFromPost F w.self src ctx.sender to amount) src =
          F.balances.get w.self src := by
        simpa [hto] using hb
      rw [hx, hpost]
      exact ge_self_add _ _
    else
      have hb : F.balances.get (transferFromPost F w.self src ctx.sender to amount) src =
          F.balances.get w.self src - amount := by
        simp [transferFromPost, credit_other _ hto, Field.Lawful.get_set,
          Field.Independent.get_set_other]
      rw [hx, hb]
      exact sub_add_ge _ _ _ hsub hallow
  else if hxto : x = to then
    have hsrc : to ≠ src := fun h => hx (hxto.trans h)
    have hb : F.balances.get (transferFromPost F w.self src ctx.sender to amount) to =
        F.balances.get w.self to + amount := by
      simp [transferFromPost, debit_other _ hsrc, Field.Lawful.get_set,
        Field.Independent.get_set_other]
    rw [hxto, hb]
    exact ge_add_add _ _ _
  else
    have hb : F.balances.get (transferFromPost F w.self src ctx.sender to amount) x =
        F.balances.get w.self x := by
      simp [transferFromPost, credit_other _ hxto, debit_other _ hx,
        Field.Lawful.get_set, Field.Independent.get_set_other]
    rw [hb]
    exact ge_self_add _ _

theorem approve_balance_protected (spender : Address) (amount : Amount a)
    {r : Bool} {w' : World S X E} (x : Address)
    (h : Tx.run (approve (ε := ε) F spender amount) ctx w = .ok (r, w')) :
    F.balances.get w'.self x + F.allowances.get w.self x ctx.sender ≥
      F.balances.get w.self x := by
  have hr := approve_returns_true F ctx w spender amount h
  subst hr
  have hb := approve_preserves_balances F ctx w spender amount h
  rw [hb]
  exact ge_self_add _ _

/-! ### `IERC20.Exact` -/

theorem exact : IERC20.Exact (impl (E := E) (X := X) (ε := ε) F) where
  transfer_moves := by
    intro to amount ctx w w' h
    have hok := Tx.run_toOption_ok (by simpa [impl_transfer] using h)
    constructor
    · have hc := transfer_conserves F ctx w to amount hok
      rw [amount_add_comm (F.balances.get w'.self ctx.sender),
          amount_add_comm (F.balances.get w.self ctx.sender)] at hc
      simpa [impl_balanceOf] using hc
    · constructor
      · intro hne
        simpa [impl_balanceOf] using transfer_credits F ctx w to amount hok hne
      · intro x hx1 hx2
        simpa [impl_balanceOf] using transfer_others F ctx w to amount hok x hx1 hx2
  transfer_supply := by
    intro to amount ctx w r w' h
    have hok := Tx.run_toOption_ok (by simpa [impl_transfer] using h)
    have hr := transfer_returns_true F ctx w to amount hok
    subst hr
    simpa [impl_totalSupply] using transfer_preserves_totalSupply F ctx w to amount hok
  transferFrom_moves := by
    intro src to amount ctx w w' h
    have hok := Tx.run_toOption_ok (by simpa [impl_transferFrom] using h)
    constructor
    · have hc := transferFrom_conserves F ctx w src to amount hok
      rw [amount_add_comm (F.balances.get w'.self src),
          amount_add_comm (F.balances.get w.self src)] at hc
      simpa [impl_balanceOf] using hc
    · constructor
      · intro hne
        simpa [impl_balanceOf] using transferFrom_credits F ctx w src to amount hok hne
      · intro x hx1 hx2
        simpa [impl_balanceOf] using transferFrom_others F ctx w src to amount hok x hx1 hx2
  transferFrom_allowance := by
    intro src to amount ctx w w' h _hne
    have hok := Tx.run_toOption_ok (by simpa [impl_transferFrom] using h)
    simpa [impl_allowance] using transferFrom_allowance F ctx w src to amount hok
  approve_sets := by
    intro spender amount ctx w w' h
    have hok := Tx.run_toOption_ok (by simpa [impl_approve] using h)
    simpa [impl_allowance] using approve_sets F ctx w spender amount hok
  balance_protected := by
    intro ctx w w' x hstep hne
    rcases hstep with h | h | h | h | h | h
    · rcases h with ⟨to, amount, r, hrun⟩
      simpa [impl_balanceOf, impl_allowance] using
        transfer_balance_protected F ctx w to amount x hrun hne
    · rcases h with ⟨src, to, amount, r, hrun⟩
      simpa [impl_balanceOf, impl_allowance] using
        transferFrom_balance_protected F ctx w src to amount x hrun hne
    · rcases h with ⟨spender, amount, r, hrun⟩
      simpa [impl_balanceOf, impl_allowance] using
        approve_balance_protected F ctx w spender amount x hrun
    · rcases h with ⟨who, r, hrun⟩
      rw [balanceOf_returns (ε := ε) F ctx w who] at hrun
      cases hrun
      simpa [impl_balanceOf, impl_allowance] using ge_self_add
        (F.balances.get w.self x) (F.allowances.get w.self x ctx.sender)
    · rcases h with ⟨owner, spender, r, hrun⟩
      rw [allowance_returns (ε := ε) F ctx w owner spender] at hrun
      cases hrun
      simpa [impl_balanceOf, impl_allowance] using ge_self_add
        (F.balances.get w.self x) (F.allowances.get w.self x ctx.sender)
    · rcases h with ⟨r, hrun⟩
      rw [totalSupply_returns (ε := ε) F ctx w] at hrun
      cases hrun
      simpa [impl_balanceOf, impl_allowance] using ge_self_add
        (F.balances.get w.self x) (F.allowances.get w.self x ctx.sender)
  transfer_exact := by
    intro to amount ctx w w' h
    have hok := Tx.run_toOption_ok (by simpa [impl_transfer] using h)
    constructor
    · intro hne
      constructor
      · simpa [impl_balanceOf] using transfer_debits F ctx w to amount hok hne
      · simpa [impl_balanceOf] using transfer_credits F ctx w to amount hok hne
    · intro heq
      simpa [impl_balanceOf] using transfer_self F ctx w to amount hok heq
  transfer_others := by
    intro to amount ctx w w' h x hx1 hx2
    have hok := Tx.run_toOption_ok (by simpa [impl_transfer] using h)
    simpa [impl_balanceOf] using transfer_others F ctx w to amount hok x hx1 hx2
  transferFrom_exact := by
    intro src to amount ctx w w' h
    have hok := Tx.run_toOption_ok (by simpa [impl_transferFrom] using h)
    constructor
    · intro hne
      constructor
      · simpa [impl_balanceOf] using transferFrom_debits F ctx w src to amount hok hne
      · simpa [impl_balanceOf] using transferFrom_credits F ctx w src to amount hok hne
    · intro heq
      simpa [impl_balanceOf] using transferFrom_self F ctx w src to amount hok heq
  transferFrom_others := by
    intro src to amount ctx w w' h x hx1 hx2
    have hok := Tx.run_toOption_ok (by simpa [impl_transferFrom] using h)
    simpa [impl_balanceOf] using transferFrom_others F ctx w src to amount hok x hx1 hx2
  transfer_supply_constant := by
    intro to amount ctx w r w' h
    have hok := Tx.run_toOption_ok (by simpa [impl_transfer] using h)
    have hr := transfer_returns_true F ctx w to amount hok
    subst hr
    simpa [impl_totalSupply] using transfer_preserves_totalSupply F ctx w to amount hok
  transferFrom_supply_constant := by
    intro src to amount ctx w r w' h
    have hok := Tx.run_toOption_ok (by simpa [impl_transferFrom] using h)
    have hr := transferFrom_returns_true F ctx w src to amount hok
    subst hr
    simpa [impl_totalSupply] using
      transferFrom_preserves_totalSupply F ctx w src to amount hok
  approve_supply_constant := by
    intro spender amount ctx w r w' h
    have hok := Tx.run_toOption_ok (by simpa [impl_approve] using h)
    have hr := approve_returns_true F ctx w spender amount hok
    subst hr
    simpa [impl_totalSupply] using approve_preserves_totalSupply F ctx w spender amount hok

end Proof
end Lsc.Stdlib.ERC20
