import Mathlib.Tactic.SplitIfs
import Examples.Token.Contract

/-!
Token Tx-level lemmas: exact `Tx.run` post-states, revert cases, and
conservation of a successful `transfer`.
-/

open Lsc Token

namespace Token

variable (ctx : Ctx) (w : World Storage Unit Event)

/-- `bals` after removing `amount` from `a`. -/
def debit {α} [Sub α] (bals : Mapping Address α) (a : Address) (amount : α) :
    Mapping Address α :=
  Function.update bals a (bals a - amount)

/-- `bals` after adding `amount` to `a`. -/
def credit {α} [Add α] (bals : Mapping Address α) (a : Address) (amount : α) :
    Mapping Address α :=
  Function.update bals a (bals a + amount)

@[simp] theorem debit_self {α} [Sub α] (bals : Mapping Address α) (a : Address)
    (n : α) : debit bals a n a = bals a - n := by simp [debit]
@[simp] theorem debit_apply_raw (bals : Mapping Address (Amount tokenAsset))
    (src to : Address) (amount : Amount tokenAsset) :
    (debit bals src amount to).raw =
      Function.update (fun i => (bals i).raw) src ((bals src).raw - amount.raw) to := by
  simp [debit, Amount.update_raw_apply, Amount.raw_sub]

@[simp] theorem debit_credit_raw (bals : Mapping Address (Amount tokenAsset))
    (src to : Address) (amount : Amount tokenAsset) :
    (debit bals src amount to + amount).raw =
      Function.update (fun i => (bals i).raw) src ((bals src).raw - amount.raw) to +
        amount.raw := by
  simp [debit_apply_raw, Amount.raw_add]

@[simp] theorem credit_self {α} [Add α] (bals : Mapping Address α) (a : Address)
    (n : α) : credit bals a n a = bals a + n := by simp [credit]
theorem debit_other {α} [Sub α] (bals : Mapping Address α) {a b : Address}
    (h : b ≠ a) (n : α) : debit bals a n b = bals b := by
  simp [debit, Function.update_of_ne h]
theorem credit_other {α} [Add α] (bals : Mapping Address α) {a b : Address}
    (h : b ≠ a) (n : α) : credit bals a n b = bals b := by
  simp [credit, Function.update_of_ne h]

/-- `(x - y) + (z + y) = x + z` when `y ≤ x`. -/
private theorem nat_sub_add_add (x y z : Nat) (h : y ≤ x) :
    x - y + (z + y) = x + z := by
  rw [Nat.add_comm z y, ← Nat.add_assoc, Nat.sub_add_cancel h]

/-! ### Views -/

theorem balanceOf_returns_stored_balance (who : Address) :
    Tx.run (balanceOf who) ctx w = .ok (w.self.balances who, w) := by
  simp [balanceOf]

theorem totalSupply_returns_stored :
    Tx.run totalSupply ctx w = .ok (w.self.totalSupply, w) := by
  simp [totalSupply]

theorem allowance_returns_stored (owner spender : Address) :
    Tx.run (allowance owner spender) ctx w = .ok (w.self.allowances owner spender, w) := by
  simp [allowance]

/-! ### constructor -/

/-- Storage after a successful `constructor`. -/
def ctorPost (σ : Storage) (owner : Address) (supply : Amount tokenAsset) : Storage :=
  Storage.mk owner supply (Function.update σ.balances owner supply) σ.allowances

theorem ctor_ok (owner : Address) (supply : Amount tokenAsset) :
    Tx.run (Token.constructor owner supply) ctx w =
      .ok ((), World.mk (ctorPost w.self owner supply) w.ext
        (w.log ++ [.Transfer 0 owner supply]) w.faults w.ncalls) := by
  simp [Token.constructor, ctorPost, Amount.update_raw, Amount.ofWord_raw]

/-! ### transfer -/

/-- Storage after a successful `transfer`. -/
def transferPost (σ : Storage) (src to : Address) (amount : Amount tokenAsset) : Storage :=
  { σ with balances := credit (debit σ.balances src amount) to amount }

/-- The exact effect of a successful `transfer` (no assumption that `src ≠ to`). -/
theorem transfer_ok (to : Address) (amount : Amount tokenAsset)
    (hsub : amount ≤ w.self.balances ctx.sender)
    (hadd : (debit w.self.balances ctx.sender amount to + amount).raw < wordBound) :
    Tx.run (transfer to amount) ctx w =
      .ok ((), { w with self := transferPost w.self ctx.sender to amount, log := w.log ++ [.Transfer ctx.sender to amount] }) := by
  simp only [debit, Amount.le_iff, Amount.raw_add, Amount.raw_sub, Amount.update_raw_apply] at hsub hadd
  simp [transfer, hsub, hadd]
  simp [transferPost, debit, credit, Amount.update2_raw,
    Amount.ofWord_update_lookup, Amount.ofWord_raw]

theorem transfer_debits_sender (to : Address) (amount : Amount tokenAsset) (hne : ctx.sender ≠ to)
    (hsub : amount ≤ w.self.balances ctx.sender)
    (hadd : (w.self.balances to + amount).raw < wordBound) :
    ∃ w', Tx.run (transfer to amount) ctx w = .ok ((), w') ∧
      w'.self.balances ctx.sender = w.self.balances ctx.sender - amount := by
  refine ⟨_, transfer_ok ctx w to amount hsub (by simpa [debit_other _ hne.symm] using hadd), ?_⟩
  simp [transferPost, credit_other _ hne]

theorem transfer_credits_recipient (to : Address) (amount : Amount tokenAsset) (hne : ctx.sender ≠ to)
    (hsub : amount ≤ w.self.balances ctx.sender)
    (hadd : (w.self.balances to + amount).raw < wordBound) :
    ∃ w', Tx.run (transfer to amount) ctx w = .ok ((), w') ∧
      w'.self.balances to = w.self.balances to + amount := by
  refine ⟨_, transfer_ok ctx w to amount hsub (by simpa [debit_other _ hne.symm] using hadd), ?_⟩
  simp [transferPost, debit_other _ hne.symm]

theorem transfer_preserves_other_balances (to : Address) (amount : Amount tokenAsset) (a : Address)
    (ha1 : a ≠ ctx.sender) (ha2 : a ≠ to)
    (hsub : amount ≤ w.self.balances ctx.sender)
    (hadd : (debit w.self.balances ctx.sender amount to + amount).raw < wordBound) :
    ∃ w', Tx.run (transfer to amount) ctx w = .ok ((), w') ∧
      w'.self.balances a = w.self.balances a :=
  ⟨_, transfer_ok ctx w to amount hsub hadd, by simp [transferPost, credit_other _ ha2, debit_other _ ha1]⟩

theorem transfer_self_transfer_is_noop (amount : Amount tokenAsset)
    (hsub : amount ≤ w.self.balances ctx.sender)
    (hbound : (w.self.balances ctx.sender).raw < wordBound) :
    ∃ w', Tx.run (transfer ctx.sender amount) ctx w = .ok ((), w') ∧
      w'.self.balances = w.self.balances := by
  refine ⟨_, transfer_ok ctx w ctx.sender amount hsub (by
    have hle : amount.raw ≤ (w.self.balances ctx.sender).raw := hsub
    simp [debit, Function.update_self, Amount.raw_add, Amount.raw_sub]
    rw [Nat.sub_add_cancel hle]
    exact hbound), ?_⟩
  funext a
  by_cases h : a = ctx.sender
  · apply Amount.ext
    have hle : amount.raw ≤ (w.self.balances ctx.sender).raw := hsub
    simp [h, transferPost, debit, credit, Function.update_self, Amount.raw_add, Amount.raw_sub]
    exact Nat.sub_add_cancel hle
  · simp [transferPost, credit_other _ h, debit_other _ h]

/-- Frame: `transfer` never touches `totalSupply`, whatever happens. -/
theorem transfer_preserves_totalSupply (to : Address) (amount : Amount tokenAsset) (w' : World Storage Unit Event)
    (h : Tx.run (transfer to amount) ctx w = .ok ((), w')) :
    w'.self.totalSupply = w.self.totalSupply := by
  by_cases hsub : amount ≤ w.self.balances ctx.sender
  · by_cases hadd : (debit w.self.balances ctx.sender amount to + amount).raw < wordBound
    · rw [transfer_ok ctx w to amount hsub hadd] at h
      cases h; rfl
    · have hle : amount.raw ≤ (w.self.balances ctx.sender).raw := hsub
      simp only [debit_credit_raw] at hadd
      simp [transfer, hle, hadd] at h
  · have hle : ¬ amount.raw ≤ (w.self.balances ctx.sender).raw := hsub
    simp [transfer, hle] at h

theorem transfer_reverts_on_insufficient_balance (to : Address) (amount : Amount tokenAsset)
    (h : w.self.balances ctx.sender < amount) :
    Tx.run (transfer to amount) ctx w = .error (.user .InsufficientBalance) := by
  simp [transfer, Amount.not_le_of_gt h]

theorem transfer_reverts_on_overflow (to : Address) (amount : Amount tokenAsset)
    (hsub : amount ≤ w.self.balances ctx.sender)
    (hadd : wordBound ≤ (debit w.self.balances ctx.sender amount to + amount).raw) :
    Tx.run (transfer to amount) ctx w = .error (.arith .overflow) := by
  have hle : amount.raw ≤ (w.self.balances ctx.sender).raw := hsub
  simp only [debit_credit_raw] at hadd
  simp [transfer, hle, Nat.not_lt.mpr hadd]

/-! ### mint -/

def mintPost (σ : Storage) (to : Address) (amount : Amount tokenAsset) : Storage :=
  { σ with totalSupply := σ.totalSupply + amount, balances := credit σ.balances to amount }

theorem mint_ok (to : Address) (amount : Amount tokenAsset) (howner : ctx.sender = w.self.owner)
    (hsupply : (w.self.totalSupply + amount).raw < wordBound)
    (hadd : (w.self.balances to + amount).raw < wordBound) :
    Tx.run (mint to amount) ctx w =
      .ok ((), { w with self := mintPost w.self to amount, log := w.log ++ [.Transfer 0 to amount] }) := by
  simp [Amount.raw_add] at hsupply hadd
  simp [mint, mintPost, credit, howner, hsupply, hadd, Amount.update_raw]

theorem mint_increases_total_supply (to : Address) (amount : Amount tokenAsset) (howner : ctx.sender = w.self.owner)
    (hsupply : (w.self.totalSupply + amount).raw < wordBound)
    (hadd : (w.self.balances to + amount).raw < wordBound) :
    ∃ w', Tx.run (mint to amount) ctx w = .ok ((), w') ∧
      w'.self.totalSupply = w.self.totalSupply + amount :=
  ⟨_, mint_ok ctx w to amount howner hsupply hadd, rfl⟩

theorem mint_increases_recipient_balance (to : Address) (amount : Amount tokenAsset)
    (howner : ctx.sender = w.self.owner)
    (hsupply : (w.self.totalSupply + amount).raw < wordBound)
    (hadd : (w.self.balances to + amount).raw < wordBound) :
    ∃ w', Tx.run (mint to amount) ctx w = .ok ((), w') ∧
      w'.self.balances to = w.self.balances to + amount :=
  ⟨_, mint_ok ctx w to amount howner hsupply hadd, by simp [mintPost]⟩

theorem mint_preserves_other_balances (to : Address) (amount : Amount tokenAsset) (a : Address) (ha : a ≠ to)
    (howner : ctx.sender = w.self.owner)
    (hsupply : (w.self.totalSupply + amount).raw < wordBound)
    (hadd : (w.self.balances to + amount).raw < wordBound) :
    ∃ w', Tx.run (mint to amount) ctx w = .ok ((), w') ∧
      w'.self.balances a = w.self.balances a :=
  ⟨_, mint_ok ctx w to amount howner hsupply hadd, by simp [mintPost, credit_other _ ha]⟩

theorem mint_reverts_for_non_owner (to : Address) (amount : Amount tokenAsset) (h : ctx.sender ≠ w.self.owner) :
    Tx.run (mint to amount) ctx w = .error (.user .NotOwner) := by
  simp [mint, h]

theorem mint_reverts_on_overflow (to : Address) (amount : Amount tokenAsset) (howner : ctx.sender = w.self.owner)
    (h : wordBound ≤ (w.self.totalSupply + amount).raw) :
    Tx.run (mint to amount) ctx w = .error (.arith .overflow) := by
  simp [Amount.raw_add] at h
  simp [mint, howner, Nat.not_lt.mpr h]

theorem mint_reverts_on_balance_overflow (to : Address) (amount : Amount tokenAsset)
    (howner : ctx.sender = w.self.owner)
    (hsupply : (w.self.totalSupply + amount).raw < wordBound)
    (h : wordBound ≤ (w.self.balances to + amount).raw) :
    Tx.run (mint to amount) ctx w = .error (.arith .overflow) := by
  simp [Amount.raw_add] at hsupply h
  simp [mint, howner, hsupply, Nat.not_lt.mpr h]

/-! ### approve -/

def approvePost (σ : Storage) (owner spender : Address) (amount : Amount tokenAsset) : Storage :=
  { σ with allowances :=
      Function.update σ.allowances owner (Function.update (σ.allowances owner) spender amount) }

theorem approve_ok (spender : Address) (amount : Amount tokenAsset) :
    Tx.run (approve spender amount) ctx w =
      .ok ((), { w with self := approvePost w.self ctx.sender spender amount, log := w.log ++ [.Approval ctx.sender spender amount] }) := by
  simp [approve, approvePost, Amount.update_nested_raw, Amount.ofWord_raw]

theorem approve_sets_allowance (spender : Address) (amount : Amount tokenAsset) :
    ∃ w', Tx.run (approve spender amount) ctx w = .ok ((), w') ∧
      w'.self.allowances ctx.sender spender = amount :=
  ⟨_, approve_ok ctx w spender amount, by simp [approvePost]⟩

theorem approve_preserves_other_allowances (spender : Address) (amount : Amount tokenAsset)
    (o s : Address) (h : o ≠ ctx.sender ∨ s ≠ spender) :
    ∃ w', Tx.run (approve spender amount) ctx w = .ok ((), w') ∧
      w'.self.allowances o s = w.self.allowances o s := by
  refine ⟨_, approve_ok ctx w spender amount, ?_⟩
  rcases h with h | h
  · simp [approvePost, Function.update_of_ne h]
  · by_cases ho : o = ctx.sender
    · subst ho; simp [approvePost, Function.update_of_ne h]
    · simp [approvePost, Function.update_of_ne ho]

theorem approve_preserves_balances (spender : Address) (amount : Amount tokenAsset) :
    ∃ w', Tx.run (approve spender amount) ctx w = .ok ((), w') ∧
      w'.self.balances = w.self.balances :=
  ⟨_, approve_ok ctx w spender amount, rfl⟩

/-! ### transferFrom -/

def transferFromPost (σ : Storage) (src spender to : Address) (amount : Amount tokenAsset) : Storage :=
  { σ with
    allowances := Function.update σ.allowances src
      (Function.update (σ.allowances src) spender (σ.allowances src spender - amount))
    balances := credit (debit σ.balances src amount) to amount }

theorem transferFrom_ok (src to : Address) (amount : Amount tokenAsset)
    (hallow : amount ≤ w.self.allowances src ctx.sender)
    (hsub : amount ≤ w.self.balances src)
    (hadd : (debit w.self.balances src amount to + amount).raw < wordBound) :
    Tx.run (transferFrom src to amount) ctx w =
      .ok ((), { w with self := transferFromPost w.self src ctx.sender to amount, log := w.log ++ [.Transfer src to amount] }) := by
  have hallow' : amount.raw ≤ (w.self.allowances src ctx.sender).raw := hallow
  have hsub' : amount.raw ≤ (w.self.balances src).raw := hsub
  simp only [debit_credit_raw] at hadd
  simp [transferFrom, hallow', hsub', hadd]
  simp [transferFromPost, debit, credit, Amount.update_nested_raw,
    Amount.update2_raw, Amount.ofWord_update_lookup, Amount.ofWord_raw]

theorem transferFrom_reverts_on_insufficient_allowance (src to : Address) (amount : Amount tokenAsset)
    (h : w.self.allowances src ctx.sender < amount) :
    Tx.run (transferFrom src to amount) ctx w = .error (.user .InsufficientAllowance) := by
  simp [transferFrom, Amount.not_le_of_gt h]

theorem transferFrom_reverts_on_insufficient_balance (src to : Address) (amount : Amount tokenAsset)
    (hallow : amount ≤ w.self.allowances src ctx.sender) (h : w.self.balances src < amount) :
    Tx.run (transferFrom src to amount) ctx w = .error (.user .InsufficientBalance) := by
  simp [transferFrom, hallow, Amount.not_le_of_gt h]

theorem transferFrom_decrements_allowance (src to : Address) (amount : Amount tokenAsset)
    (hallow : amount ≤ w.self.allowances src ctx.sender)
    (hsub : amount ≤ w.self.balances src)
    (hadd : (debit w.self.balances src amount to + amount).raw < wordBound) :
    ∃ w', Tx.run (transferFrom src to amount) ctx w = .ok ((), w') ∧
      w'.self.allowances src ctx.sender = w.self.allowances src ctx.sender - amount :=
  ⟨_, transferFrom_ok ctx w src to amount hallow hsub hadd, by simp [transferFromPost]⟩

theorem transferFrom_debits_sender (src to : Address) (amount : Amount tokenAsset) (hne : src ≠ to)
    (hallow : amount ≤ w.self.allowances src ctx.sender)
    (hsub : amount ≤ w.self.balances src)
    (hadd : (w.self.balances to + amount).raw < wordBound) :
    ∃ w', Tx.run (transferFrom src to amount) ctx w = .ok ((), w') ∧
      w'.self.balances src = w.self.balances src - amount :=
  ⟨_, transferFrom_ok ctx w src to amount hallow hsub (by simpa [debit_other _ hne.symm] using hadd),
    by simp [transferFromPost, credit_other _ hne]⟩

theorem transferFrom_credits_recipient (src to : Address) (amount : Amount tokenAsset) (hne : src ≠ to)
    (hallow : amount ≤ w.self.allowances src ctx.sender)
    (hsub : amount ≤ w.self.balances src)
    (hadd : (w.self.balances to + amount).raw < wordBound) :
    ∃ w', Tx.run (transferFrom src to amount) ctx w = .ok ((), w') ∧
      w'.self.balances to = w.self.balances to + amount :=
  ⟨_, transferFrom_ok ctx w src to amount hallow hsub (by simpa [debit_other _ hne.symm] using hadd),
    by simp [transferFromPost, debit_other _ hne.symm]⟩

theorem transferFrom_preserves_other_balances (src to : Address) (amount : Amount tokenAsset) (a : Address)
    (ha1 : a ≠ src) (ha2 : a ≠ to)
    (hallow : amount ≤ w.self.allowances src ctx.sender)
    (hsub : amount ≤ w.self.balances src)
    (hadd : (debit w.self.balances src amount to + amount).raw < wordBound) :
    ∃ w', Tx.run (transferFrom src to amount) ctx w = .ok ((), w') ∧
      w'.self.balances a = w.self.balances a :=
  ⟨_, transferFrom_ok ctx w src to amount hallow hsub hadd,
    by simp [transferFromPost, credit_other _ ha2, debit_other _ ha1]⟩

theorem transferFrom_preserves_other_allowances (src to : Address) (amount : Amount tokenAsset)
    (o s : Address) (h : o ≠ src ∨ s ≠ ctx.sender)
    (hallow : amount ≤ w.self.allowances src ctx.sender)
    (hsub : amount ≤ w.self.balances src)
    (hadd : (debit w.self.balances src amount to + amount).raw < wordBound) :
    ∃ w', Tx.run (transferFrom src to amount) ctx w = .ok ((), w') ∧
      w'.self.allowances o s = w.self.allowances o s := by
  refine ⟨_, transferFrom_ok ctx w src to amount hallow hsub hadd, ?_⟩
  rcases h with h | h
  · simp [transferFromPost, Function.update_of_ne h]
  · by_cases ho : o = src
    · subst ho; simp [transferFromPost, Function.update_of_ne h]
    · simp [transferFromPost, Function.update_of_ne ho]

theorem transferFrom_conserves (src to : Address) (amount : Amount tokenAsset) (hne : src ≠ to)
    (hallow : amount ≤ w.self.allowances src ctx.sender)
    (hsub : amount ≤ w.self.balances src)
    (hadd : (w.self.balances to + amount).raw < wordBound) :
    ∃ w', Tx.run (transferFrom src to amount) ctx w = .ok ((), w') ∧
      w'.self.balances src + w'.self.balances to =
        w.self.balances src + w.self.balances to := by
  refine ⟨_, transferFrom_ok ctx w src to amount hallow hsub
    (by simpa [debit_other _ hne.symm] using hadd), ?_⟩
  apply Amount.ext
  have hle : amount.raw ≤ (w.self.balances src).raw := hsub
  simp [transferFromPost, credit_other _ hne, debit_other _ hne.symm,
    Amount.raw_add, Amount.raw_sub]
  exact nat_sub_add_add _ _ _ hle

theorem transferFrom_self_transfer_is_noop (src : Address) (amount : Amount tokenAsset)
    (hallow : amount ≤ w.self.allowances src ctx.sender)
    (hsub : amount ≤ w.self.balances src)
    (hbound : (w.self.balances src).raw < wordBound) :
    ∃ w', Tx.run (transferFrom src src amount) ctx w = .ok ((), w') ∧
      w'.self.balances = w.self.balances := by
  refine ⟨_, transferFrom_ok ctx w src src amount hallow hsub (by
    have hle : amount.raw ≤ (w.self.balances src).raw := hsub
    simp [debit, Function.update_self, Amount.raw_add, Amount.raw_sub]
    rw [Nat.sub_add_cancel hle]
    exact hbound), ?_⟩
  funext a
  by_cases h : a = src
  · apply Amount.ext
    have hle : amount.raw ≤ (w.self.balances src).raw := hsub
    simp [h, transferFromPost, debit, credit, Function.update_self, Amount.raw_add, Amount.raw_sub]
    exact Nat.sub_add_cancel hle
  · simp [transferFromPost, credit_other _ h, debit_other _ h]

theorem transferFrom_reverts_on_overflow (src to : Address) (amount : Amount tokenAsset)
    (hallow : amount ≤ w.self.allowances src ctx.sender)
    (hsub : amount ≤ w.self.balances src)
    (hadd : wordBound ≤ (debit w.self.balances src amount to + amount).raw) :
    Tx.run (transferFrom src to amount) ctx w = .error (.arith .overflow) := by
  have hallow' : amount.raw ≤ (w.self.allowances src ctx.sender).raw := hallow
  have hsub' : amount.raw ≤ (w.self.balances src).raw := hsub
  simp only [debit_credit_raw] at hadd
  simp [transferFrom, hallow', hsub', Nat.not_lt.mpr hadd]

/-! ### burn -/

theorem burn_reverts_on_insufficient_balance (amount : Amount tokenAsset) (h : w.self.balances ctx.sender < amount) :
    Tx.run (burn amount) ctx w = .error (.user .InsufficientBalance) := by
  have hfail : ¬ amount.raw ≤ (w.self.balances ctx.sender).raw := Amount.not_le_of_gt h
  simp [burn, hfail]

def burnPost (σ : Storage) (src : Address) (amount : Amount tokenAsset) : Storage :=
  { σ with totalSupply := σ.totalSupply - amount, balances := debit σ.balances src amount }

theorem burn_ok (amount : Amount tokenAsset)
    (hsub : amount ≤ w.self.balances ctx.sender) (hsupply : amount ≤ w.self.totalSupply) :
    Tx.run (burn amount) ctx w =
      .ok ((), { w with self := burnPost w.self ctx.sender amount, log := w.log ++ [.Transfer ctx.sender 0 amount] }) := by
  have hle : amount.raw ≤ (w.self.balances ctx.sender).raw := hsub
  have hsup : amount.raw ≤ w.self.totalSupply.raw := hsupply
  simp [burn, burnPost, debit, hle, hsup, Amount.update_raw]

theorem burn_decreases_supply (amount : Amount tokenAsset)
    (hsub : amount ≤ w.self.balances ctx.sender) (hsupply : amount ≤ w.self.totalSupply) :
    ∃ w', Tx.run (burn amount) ctx w = .ok ((), w') ∧
      w'.self.totalSupply = w.self.totalSupply - amount ∧
      w'.self.balances ctx.sender = w.self.balances ctx.sender - amount :=
  ⟨_, burn_ok ctx w amount hsub hsupply, rfl, by simp [burnPost]⟩

theorem burn_preserves_other_balances (amount : Amount tokenAsset) (a : Address) (ha : a ≠ ctx.sender)
    (hsub : amount ≤ w.self.balances ctx.sender) (hsupply : amount ≤ w.self.totalSupply) :
    ∃ w', Tx.run (burn amount) ctx w = .ok ((), w') ∧
      w'.self.balances a = w.self.balances a :=
  ⟨_, burn_ok ctx w amount hsub hsupply, by simp [burnPost, debit_other _ ha]⟩

theorem burn_reverts_on_insufficient_supply (amount : Amount tokenAsset)
    (hsub : amount ≤ w.self.balances ctx.sender) (hsupply : w.self.totalSupply < amount) :
    Tx.run (burn amount) ctx w = .error (.arith .underflow) := by
  have hle : amount.raw ≤ (w.self.balances ctx.sender).raw := hsub
  have hns : ¬ amount.raw ≤ w.self.totalSupply.raw := Amount.not_le_of_gt hsupply
  simp [burn, hle, hns]

namespace Proof

/-- A successful `transfer` conserves the sum of the two balances, including
when sender = recipient. Success implies the funds and overflow checks. -/
theorem transfer_conserves (to : Address) (amount : Amount tokenAsset)
    {w' : World Storage Unit Event}
    (h : Tx.run (transfer to amount) ctx w = .ok ((), w')) :
    w'.self.balances ctx.sender + w'.self.balances to =
      w.self.balances ctx.sender + w.self.balances to := by
  by_cases hsub : amount ≤ w.self.balances ctx.sender
  · by_cases hadd : (debit w.self.balances ctx.sender amount to + amount).raw < wordBound
    · rw [transfer_ok ctx w to amount hsub hadd] at h
      cases h
      if hne : ctx.sender = to then
        subst hne
        apply Amount.ext
        have hle : amount.raw ≤ (w.self.balances ctx.sender).raw := hsub
        simp [transferPost, credit_self, debit_self, Amount.raw_add, Amount.raw_sub,
          Nat.sub_add_cancel hle]
      else
        apply Amount.ext
        have hle : amount.raw ≤ (w.self.balances ctx.sender).raw := hsub
        simp [transferPost, credit_other _ hne, debit_other _ (Ne.symm hne),
          Amount.raw_add, Amount.raw_sub]
        exact nat_sub_add_add _ _ _ hle
    · rw [transfer_reverts_on_overflow ctx w to amount hsub (Nat.not_lt.mp hadd)] at h
      cases h
  · have hlt : w.self.balances ctx.sender < amount := Nat.not_le.mp hsub
    rw [transfer_reverts_on_insufficient_balance ctx w to amount hlt] at h
    cases h

end Proof

end Token
