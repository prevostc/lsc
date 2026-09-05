import Mathlib.Tactic.SplitIfs
import Lsc.Examples.Token

/-!
# Token — theorems

Every statement is about `Tx.run (Token.f args) ctx w`: the plain function view of the
program the user wrote, which is also (by `f.core_denote`) the denotation of the `Core`
term the compiler consumes. Proofs are `simp` with the run lemmas plus `omega`; no
`native_decide`, no framework internals in the statements.
-/

open Lsc Token

namespace Token

variable (ctx : Ctx) (w : World Storage Unit Event)

/-- `bals` after removing `amount` from `a`. -/
def debit (bals : Mapping Address Nat) (a : Address) (amount : Nat) : Mapping Address Nat :=
  Function.update bals a (bals a - amount)

/-- `bals` after adding `amount` to `a`. -/
def credit (bals : Mapping Address Nat) (a : Address) (amount : Nat) : Mapping Address Nat :=
  Function.update bals a (bals a + amount)

@[simp] theorem debit_self (bals : Mapping Address Nat) (a : Address) (n : Nat) :
    debit bals a n a = bals a - n := by simp [debit]
@[simp] theorem credit_self (bals : Mapping Address Nat) (a : Address) (n : Nat) :
    credit bals a n a = bals a + n := by simp [credit]
theorem debit_other (bals : Mapping Address Nat) {a b : Address} (h : b ≠ a) (n : Nat) :
    debit bals a n b = bals b := by simp [debit, Function.update_of_ne h]
theorem credit_other (bals : Mapping Address Nat) {a b : Address} (h : b ≠ a) (n : Nat) :
    credit bals a n b = bals b := by simp [credit, Function.update_of_ne h]

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
def ctorPost (σ : Storage) (owner : Address) (supply : Nat) : Storage :=
  Storage.mk owner supply (Function.update σ.balances owner supply) σ.allowances

theorem ctor_ok (owner : Address) (supply : Nat) :
    Tx.run (Token.constructor owner supply) ctx w =
      .ok ((), World.mk (ctorPost w.self owner supply) w.ext
        (w.log ++ [.Transfer 0 owner supply]) w.faults w.ncalls) := by
  simp [Token.constructor, ctorPost]

/-! ### transfer -/

/-- Storage after a successful `transfer`. -/
def transferPost (σ : Storage) (src to : Address) (amount : Nat) : Storage :=
  { σ with balances := credit (debit σ.balances src amount) to amount }

/-- The exact effect of a successful `transfer` (no assumption that `src ≠ to`). -/
theorem transfer_ok (to : Address) (amount : Nat)
    (hsub : amount ≤ w.self.balances ctx.sender)
    (hadd : debit w.self.balances ctx.sender amount to + amount < wordBound) :
    Tx.run (transfer to amount) ctx w =
      .ok ((), { w with self := transferPost w.self ctx.sender to amount, log := w.log ++ [.Transfer ctx.sender to amount] }) := by
  simp only [debit] at hadd
  simp [transfer, transferPost, debit, credit, hsub, hadd]

theorem transfer_debits_sender (to : Address) (amount : Nat) (hne : ctx.sender ≠ to)
    (hsub : amount ≤ w.self.balances ctx.sender)
    (hadd : w.self.balances to + amount < wordBound) :
    ∃ w', Tx.run (transfer to amount) ctx w = .ok ((), w') ∧
      w'.self.balances ctx.sender = w.self.balances ctx.sender - amount := by
  refine ⟨_, transfer_ok ctx w to amount hsub (by simpa [debit_other _ hne.symm] using hadd), ?_⟩
  simp [transferPost, credit_other _ hne]

theorem transfer_credits_recipient (to : Address) (amount : Nat) (hne : ctx.sender ≠ to)
    (hsub : amount ≤ w.self.balances ctx.sender)
    (hadd : w.self.balances to + amount < wordBound) :
    ∃ w', Tx.run (transfer to amount) ctx w = .ok ((), w') ∧
      w'.self.balances to = w.self.balances to + amount := by
  refine ⟨_, transfer_ok ctx w to amount hsub (by simpa [debit_other _ hne.symm] using hadd), ?_⟩
  simp [transferPost, debit_other _ hne.symm]

theorem transfer_preserves_other_balances (to : Address) (amount : Nat) (a : Address)
    (ha1 : a ≠ ctx.sender) (ha2 : a ≠ to)
    (hsub : amount ≤ w.self.balances ctx.sender)
    (hadd : debit w.self.balances ctx.sender amount to + amount < wordBound) :
    ∃ w', Tx.run (transfer to amount) ctx w = .ok ((), w') ∧
      w'.self.balances a = w.self.balances a :=
  ⟨_, transfer_ok ctx w to amount hsub hadd, by simp [transferPost, credit_other _ ha2, debit_other _ ha1]⟩

theorem transfer_self_transfer_is_noop (amount : Nat)
    (hsub : amount ≤ w.self.balances ctx.sender)
    (hbound : w.self.balances ctx.sender < wordBound) :
    ∃ w', Tx.run (transfer ctx.sender amount) ctx w = .ok ((), w') ∧
      w'.self.balances = w.self.balances := by
  refine ⟨_, transfer_ok ctx w ctx.sender amount hsub (by simp; omega), ?_⟩
  funext a
  by_cases h : a = ctx.sender
  · subst h; simp [transferPost]; omega
  · simp [transferPost, credit_other _ h, debit_other _ h]

/-- Frame: `transfer` never touches `totalSupply`, whatever happens. -/
theorem transfer_preserves_totalSupply (to : Address) (amount : Nat) (w' : World Storage Unit Event)
    (h : Tx.run (transfer to amount) ctx w = .ok ((), w')) :
    w'.self.totalSupply = w.self.totalSupply := by
  by_cases hsub : amount ≤ w.self.balances ctx.sender
  · by_cases hadd : debit w.self.balances ctx.sender amount to + amount < wordBound
    · rw [transfer_ok ctx w to amount hsub hadd] at h
      cases h; rfl
    · simp only [debit] at hadd
      simp [transfer, hsub, hadd] at h
  · simp [transfer, hsub] at h

/-- Two-party conservation: the transferred amount moves, nothing is created. -/
theorem transfer_conserves (to : Address) (amount : Nat) (hne : ctx.sender ≠ to)
    (hsub : amount ≤ w.self.balances ctx.sender)
    (hadd : w.self.balances to + amount < wordBound) :
    ∃ w', Tx.run (transfer to amount) ctx w = .ok ((), w') ∧
      w'.self.balances ctx.sender + w'.self.balances to =
        w.self.balances ctx.sender + w.self.balances to := by
  refine ⟨_, transfer_ok ctx w to amount hsub (by simpa [debit_other _ hne.symm] using hadd), ?_⟩
  simp [transferPost, credit_other _ hne, debit_other _ hne.symm]
  omega

theorem transfer_reverts_on_insufficient_balance (to : Address) (amount : Nat)
    (h : w.self.balances ctx.sender < amount) :
    Tx.run (transfer to amount) ctx w = .error (.user .InsufficientBalance) := by
  simp [transfer, Nat.not_le.mpr h]

theorem transfer_reverts_on_overflow (to : Address) (amount : Nat)
    (hsub : amount ≤ w.self.balances ctx.sender)
    (hadd : wordBound ≤ debit w.self.balances ctx.sender amount to + amount) :
    Tx.run (transfer to amount) ctx w = .error (.arith .overflow) := by
  simp only [debit] at hadd
  simp [transfer, hsub, Nat.not_lt.mpr hadd]

/-! ### mint -/

def mintPost (σ : Storage) (to : Address) (amount : Nat) : Storage :=
  { σ with totalSupply := σ.totalSupply + amount, balances := credit σ.balances to amount }

theorem mint_ok (to : Address) (amount : Nat) (howner : ctx.sender = w.self.owner)
    (hsupply : w.self.totalSupply + amount < wordBound)
    (hadd : w.self.balances to + amount < wordBound) :
    Tx.run (mint to amount) ctx w =
      .ok ((), { w with self := mintPost w.self to amount, log := w.log ++ [.Transfer 0 to amount] }) := by
  simp [mint, mintPost, credit, howner, hsupply, hadd]

theorem mint_increases_total_supply (to : Address) (amount : Nat) (howner : ctx.sender = w.self.owner)
    (hsupply : w.self.totalSupply + amount < wordBound)
    (hadd : w.self.balances to + amount < wordBound) :
    ∃ w', Tx.run (mint to amount) ctx w = .ok ((), w') ∧
      w'.self.totalSupply = w.self.totalSupply + amount :=
  ⟨_, mint_ok ctx w to amount howner hsupply hadd, rfl⟩

theorem mint_increases_recipient_balance (to : Address) (amount : Nat)
    (howner : ctx.sender = w.self.owner)
    (hsupply : w.self.totalSupply + amount < wordBound)
    (hadd : w.self.balances to + amount < wordBound) :
    ∃ w', Tx.run (mint to amount) ctx w = .ok ((), w') ∧
      w'.self.balances to = w.self.balances to + amount :=
  ⟨_, mint_ok ctx w to amount howner hsupply hadd, by simp [mintPost]⟩

theorem mint_preserves_other_balances (to : Address) (amount : Nat) (a : Address) (ha : a ≠ to)
    (howner : ctx.sender = w.self.owner)
    (hsupply : w.self.totalSupply + amount < wordBound)
    (hadd : w.self.balances to + amount < wordBound) :
    ∃ w', Tx.run (mint to amount) ctx w = .ok ((), w') ∧
      w'.self.balances a = w.self.balances a :=
  ⟨_, mint_ok ctx w to amount howner hsupply hadd, by simp [mintPost, credit_other _ ha]⟩

theorem mint_reverts_for_non_owner (to : Address) (amount : Nat) (h : ctx.sender ≠ w.self.owner) :
    Tx.run (mint to amount) ctx w = .error (.user .NotOwner) := by
  simp [mint, h]

theorem mint_reverts_on_overflow (to : Address) (amount : Nat) (howner : ctx.sender = w.self.owner)
    (h : wordBound ≤ w.self.totalSupply + amount) :
    Tx.run (mint to amount) ctx w = .error (.arith .overflow) := by
  simp [mint, howner, Nat.not_lt.mpr h]

theorem mint_reverts_on_balance_overflow (to : Address) (amount : Nat)
    (howner : ctx.sender = w.self.owner)
    (hsupply : w.self.totalSupply + amount < wordBound)
    (h : wordBound ≤ w.self.balances to + amount) :
    Tx.run (mint to amount) ctx w = .error (.arith .overflow) := by
  simp [mint, howner, hsupply, Nat.not_lt.mpr h]

/-! ### approve -/

def approvePost (σ : Storage) (owner spender : Address) (amount : Nat) : Storage :=
  { σ with allowances :=
      Function.update σ.allowances owner (Function.update (σ.allowances owner) spender amount) }

theorem approve_ok (spender : Address) (amount : Nat) :
    Tx.run (approve spender amount) ctx w =
      .ok ((), { w with self := approvePost w.self ctx.sender spender amount, log := w.log ++ [.Approval ctx.sender spender amount] }) := by
  simp [approve, approvePost]

theorem approve_sets_allowance (spender : Address) (amount : Nat) :
    ∃ w', Tx.run (approve spender amount) ctx w = .ok ((), w') ∧
      w'.self.allowances ctx.sender spender = amount :=
  ⟨_, approve_ok ctx w spender amount, by simp [approvePost]⟩

theorem approve_preserves_other_allowances (spender : Address) (amount : Nat)
    (o s : Address) (h : o ≠ ctx.sender ∨ s ≠ spender) :
    ∃ w', Tx.run (approve spender amount) ctx w = .ok ((), w') ∧
      w'.self.allowances o s = w.self.allowances o s := by
  refine ⟨_, approve_ok ctx w spender amount, ?_⟩
  rcases h with h | h
  · simp [approvePost, Function.update_of_ne h]
  · by_cases ho : o = ctx.sender
    · subst ho; simp [approvePost, Function.update_of_ne h]
    · simp [approvePost, Function.update_of_ne ho]

theorem approve_preserves_balances (spender : Address) (amount : Nat) :
    ∃ w', Tx.run (approve spender amount) ctx w = .ok ((), w') ∧
      w'.self.balances = w.self.balances :=
  ⟨_, approve_ok ctx w spender amount, rfl⟩

/-! ### transferFrom -/

def transferFromPost (σ : Storage) (src spender to : Address) (amount : Nat) : Storage :=
  { σ with
    allowances := Function.update σ.allowances src
      (Function.update (σ.allowances src) spender (σ.allowances src spender - amount))
    balances := credit (debit σ.balances src amount) to amount }

theorem transferFrom_ok (src to : Address) (amount : Nat)
    (hallow : amount ≤ w.self.allowances src ctx.sender)
    (hsub : amount ≤ w.self.balances src)
    (hadd : debit w.self.balances src amount to + amount < wordBound) :
    Tx.run (transferFrom src to amount) ctx w =
      .ok ((), { w with self := transferFromPost w.self src ctx.sender to amount, log := w.log ++ [.Transfer src to amount] }) := by
  simp only [debit] at hadd
  simp [transferFrom, transferFromPost, debit, credit, hallow, hsub, hadd]

theorem transferFrom_reverts_on_insufficient_allowance (src to : Address) (amount : Nat)
    (h : w.self.allowances src ctx.sender < amount) :
    Tx.run (transferFrom src to amount) ctx w = .error (.user .InsufficientAllowance) := by
  simp [transferFrom, Nat.not_le.mpr h]

theorem transferFrom_reverts_on_insufficient_balance (src to : Address) (amount : Nat)
    (hallow : amount ≤ w.self.allowances src ctx.sender) (h : w.self.balances src < amount) :
    Tx.run (transferFrom src to amount) ctx w = .error (.user .InsufficientBalance) := by
  simp [transferFrom, hallow, Nat.not_le.mpr h]

theorem transferFrom_decrements_allowance (src to : Address) (amount : Nat)
    (hallow : amount ≤ w.self.allowances src ctx.sender)
    (hsub : amount ≤ w.self.balances src)
    (hadd : debit w.self.balances src amount to + amount < wordBound) :
    ∃ w', Tx.run (transferFrom src to amount) ctx w = .ok ((), w') ∧
      w'.self.allowances src ctx.sender = w.self.allowances src ctx.sender - amount :=
  ⟨_, transferFrom_ok ctx w src to amount hallow hsub hadd, by simp [transferFromPost]⟩

theorem transferFrom_debits_sender (src to : Address) (amount : Nat) (hne : src ≠ to)
    (hallow : amount ≤ w.self.allowances src ctx.sender)
    (hsub : amount ≤ w.self.balances src)
    (hadd : w.self.balances to + amount < wordBound) :
    ∃ w', Tx.run (transferFrom src to amount) ctx w = .ok ((), w') ∧
      w'.self.balances src = w.self.balances src - amount :=
  ⟨_, transferFrom_ok ctx w src to amount hallow hsub (by simpa [debit_other _ hne.symm] using hadd),
    by simp [transferFromPost, credit_other _ hne]⟩

theorem transferFrom_credits_recipient (src to : Address) (amount : Nat) (hne : src ≠ to)
    (hallow : amount ≤ w.self.allowances src ctx.sender)
    (hsub : amount ≤ w.self.balances src)
    (hadd : w.self.balances to + amount < wordBound) :
    ∃ w', Tx.run (transferFrom src to amount) ctx w = .ok ((), w') ∧
      w'.self.balances to = w.self.balances to + amount :=
  ⟨_, transferFrom_ok ctx w src to amount hallow hsub (by simpa [debit_other _ hne.symm] using hadd),
    by simp [transferFromPost, debit_other _ hne.symm]⟩

theorem transferFrom_preserves_other_balances (src to : Address) (amount : Nat) (a : Address)
    (ha1 : a ≠ src) (ha2 : a ≠ to)
    (hallow : amount ≤ w.self.allowances src ctx.sender)
    (hsub : amount ≤ w.self.balances src)
    (hadd : debit w.self.balances src amount to + amount < wordBound) :
    ∃ w', Tx.run (transferFrom src to amount) ctx w = .ok ((), w') ∧
      w'.self.balances a = w.self.balances a :=
  ⟨_, transferFrom_ok ctx w src to amount hallow hsub hadd,
    by simp [transferFromPost, credit_other _ ha2, debit_other _ ha1]⟩

theorem transferFrom_preserves_other_allowances (src to : Address) (amount : Nat)
    (o s : Address) (h : o ≠ src ∨ s ≠ ctx.sender)
    (hallow : amount ≤ w.self.allowances src ctx.sender)
    (hsub : amount ≤ w.self.balances src)
    (hadd : debit w.self.balances src amount to + amount < wordBound) :
    ∃ w', Tx.run (transferFrom src to amount) ctx w = .ok ((), w') ∧
      w'.self.allowances o s = w.self.allowances o s := by
  refine ⟨_, transferFrom_ok ctx w src to amount hallow hsub hadd, ?_⟩
  rcases h with h | h
  · simp [transferFromPost, Function.update_of_ne h]
  · by_cases ho : o = src
    · subst ho; simp [transferFromPost, Function.update_of_ne h]
    · simp [transferFromPost, Function.update_of_ne ho]

theorem transferFrom_conserves (src to : Address) (amount : Nat) (hne : src ≠ to)
    (hallow : amount ≤ w.self.allowances src ctx.sender)
    (hsub : amount ≤ w.self.balances src)
    (hadd : w.self.balances to + amount < wordBound) :
    ∃ w', Tx.run (transferFrom src to amount) ctx w = .ok ((), w') ∧
      w'.self.balances src + w'.self.balances to =
        w.self.balances src + w.self.balances to := by
  refine ⟨_, transferFrom_ok ctx w src to amount hallow hsub
    (by simpa [debit_other _ hne.symm] using hadd), ?_⟩
  simp [transferFromPost, credit_other _ hne, debit_other _ hne.symm]
  omega

theorem transferFrom_self_transfer_is_noop (src : Address) (amount : Nat)
    (hallow : amount ≤ w.self.allowances src ctx.sender)
    (hsub : amount ≤ w.self.balances src)
    (hbound : w.self.balances src < wordBound) :
    ∃ w', Tx.run (transferFrom src src amount) ctx w = .ok ((), w') ∧
      w'.self.balances = w.self.balances := by
  refine ⟨_, transferFrom_ok ctx w src src amount hallow hsub (by simp; omega), ?_⟩
  funext a
  by_cases h : a = src
  · subst h; simp [transferFromPost]; omega
  · simp [transferFromPost, credit_other _ h, debit_other _ h]

theorem transferFrom_reverts_on_overflow (src to : Address) (amount : Nat)
    (hallow : amount ≤ w.self.allowances src ctx.sender)
    (hsub : amount ≤ w.self.balances src)
    (hadd : wordBound ≤ debit w.self.balances src amount to + amount) :
    Tx.run (transferFrom src to amount) ctx w = .error (.arith .overflow) := by
  simp only [debit] at hadd
  simp [transferFrom, hallow, hsub, Nat.not_lt.mpr hadd]

/-! ### burn -/

theorem burn_reverts_on_insufficient_balance (amount : Nat) (h : w.self.balances ctx.sender < amount) :
    Tx.run (burn amount) ctx w = .error (.user .InsufficientBalance) := by
  simp [burn, Nat.not_le.mpr h]

def burnPost (σ : Storage) (src : Address) (amount : Nat) : Storage :=
  { σ with totalSupply := σ.totalSupply - amount, balances := debit σ.balances src amount }

theorem burn_ok (amount : Nat)
    (hsub : amount ≤ w.self.balances ctx.sender) (hsupply : amount ≤ w.self.totalSupply) :
    Tx.run (burn amount) ctx w =
      .ok ((), { w with self := burnPost w.self ctx.sender amount, log := w.log ++ [.Transfer ctx.sender 0 amount] }) := by
  simp [burn, burnPost, debit, hsub, hsupply]

theorem burn_decreases_supply (amount : Nat)
    (hsub : amount ≤ w.self.balances ctx.sender) (hsupply : amount ≤ w.self.totalSupply) :
    ∃ w', Tx.run (burn amount) ctx w = .ok ((), w') ∧
      w'.self.totalSupply = w.self.totalSupply - amount ∧
      w'.self.balances ctx.sender = w.self.balances ctx.sender - amount :=
  ⟨_, burn_ok ctx w amount hsub hsupply, rfl, by simp [burnPost]⟩

theorem burn_preserves_other_balances (amount : Nat) (a : Address) (ha : a ≠ ctx.sender)
    (hsub : amount ≤ w.self.balances ctx.sender) (hsupply : amount ≤ w.self.totalSupply) :
    ∃ w', Tx.run (burn amount) ctx w = .ok ((), w') ∧
      w'.self.balances a = w.self.balances a :=
  ⟨_, burn_ok ctx w amount hsub hsupply, by simp [burnPost, debit_other _ ha]⟩

theorem burn_reverts_on_insufficient_supply (amount : Nat)
    (hsub : amount ≤ w.self.balances ctx.sender) (hsupply : w.self.totalSupply < amount) :
    Tx.run (burn amount) ctx w = .error (.arith .underflow) := by
  simp [burn, hsub, Nat.not_le.mpr hsupply]

end Token
