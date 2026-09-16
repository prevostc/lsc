import Mathlib.Tactic.SplitIfs
import Examples.WETH.Contract

/-!
WETH Tx-level lemmas: exact `Tx.run` post-states and conservation.
-/

set_option linter.unusedSimpArgs false

open Lsc WETH

namespace WETH

variable (ctx : Ctx) (w : World)

def depositTx : M Unit := @deposit Payable.entrypoint

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
@[simp] theorem credit_self {α} [Add α] (bals : Mapping Address α) (a : Address)
    (n : α) : credit bals a n a = bals a + n := by simp [credit]
theorem debit_other {α} [Sub α] (bals : Mapping Address α) {a b : Address}
    (h : b ≠ a) (n : α) : debit bals a n b = bals b := by
  simp [debit, Function.update_of_ne h]
theorem credit_other {α} [Add α] (bals : Mapping Address α) {a b : Address}
    (h : b ≠ a) (n : α) : credit bals a n b = bals b := by
  simp [credit, Function.update_of_ne h]

@[simp] theorem debit_apply_raw (bals : Mapping Address (Amount native))
    (src to : Address) (amount : Amount native) :
    (debit bals src amount to).raw =
      Function.update (fun i => (bals i).raw) src ((bals src).raw - amount.raw) to := by
  simp [debit, Amount.update_raw_apply, Amount.raw_sub]

@[simp] theorem debit_credit_raw (bals : Mapping Address (Amount native))
    (src to : Address) (amount : Amount native) :
    (debit bals src amount to + amount).raw =
      Function.update (fun i => (bals i).raw) src ((bals src).raw - amount.raw) to +
        amount.raw := by
  simp [debit_apply_raw, Amount.raw_add]

/-! ### Views -/

theorem balanceOf_returns_stored_balance (who : Address) :
    Tx.run (balanceOf who) ctx w = .ok (w.self.balances who, w) := by
  simp [balanceOf]

theorem totalSupply_returns_stored :
    Tx.run totalSupply ctx w = .ok (w.self.totalSupply, w) := by
  simp [totalSupply]

theorem allowance_returns_stored (owner spender : Address) :
    Tx.run (allowance owner spender) ctx w =
      .ok (w.self.allowances owner spender, w) := by
  simp [allowance]

/-- `(x - y) + (z + y) = x + z` when `y ≤ x`. -/
private theorem nat_sub_add_add (x y z : Nat) (h : y ≤ x) :
    x - y + (z + y) = x + z := by
  rw [Nat.add_comm z y, ← Nat.add_assoc, Nat.sub_add_cancel h]

@[simp] theorem run_txValue {a : Asset} (ctx : Ctx) (w : World) :
    Tx.run (@Tx.value Storage ExtState Event Error Payable.entrypoint a) ctx w =
      .ok (Amount.ofWord ctx.value, w) := by
  simp [Tx.value]

/-! ### deposit -/

def depositPost (σ : Storage) (who : Address) (v : Amount native) : Storage :=
  { σ with
    balances := credit σ.balances who v
    totalSupply := σ.totalSupply + v }

theorem deposit_ok
    (hbal : (w.self.balances ctx.sender + Amount.ofWord ctx.value).raw < wordBound)
    (hsup : (w.self.totalSupply + Amount.ofWord ctx.value).raw < wordBound) :
    Tx.run depositTx ctx w =
      .ok ((), { w with
        self := depositPost w.self ctx.sender ⟨ctx.value⟩
        log := w.log ++ [.Deposit ctx.sender ⟨ctx.value⟩] }) := by
  have hb : (w.self.balances ctx.sender).raw + ctx.value < wordBound := by
    simpa [Amount.raw_add, Amount.ofWord] using hbal
  have hs : w.self.totalSupply.raw + ctx.value < wordBound := by
    simpa [Amount.raw_add, Amount.ofWord] using hsup
  simp [depositTx, deposit, Tx.value, hb, hs, depositPost, credit]
  apply And.intro
  · apply And.intro
    · rw [Amount.update_raw w.self.balances ctx.sender
        ((w.self.balances ctx.sender).raw + ctx.value)]
      apply congrArg (Function.update w.self.balances ctx.sender)
      exact Amount.ofWord_add_left (w.self.balances ctx.sender) ctx.value
    · simp [Amount.ofWord, Amount.raw_add]
  · simp [Amount.ofWord]

theorem deposit_ok_inv {w' : World}
    (h : Tx.run depositTx ctx w = .ok ((), w')) :
    (w.self.balances ctx.sender + Amount.ofWord ctx.value).raw < wordBound ∧
      (w.self.totalSupply + Amount.ofWord ctx.value).raw < wordBound ∧
      w' = { w with
        self := depositPost w.self ctx.sender ⟨ctx.value⟩
        log := w.log ++ [.Deposit ctx.sender ⟨ctx.value⟩] } := by
  by_cases hbal : (w.self.balances ctx.sender + Amount.ofWord ctx.value).raw < wordBound
  · by_cases hsup : (w.self.totalSupply + Amount.ofWord ctx.value).raw < wordBound
    · rw [deposit_ok ctx w hbal hsup] at h
      cases h
      exact ⟨hbal, hsup, rfl⟩
    · have hs : ¬ w.self.totalSupply.raw + ctx.value < wordBound := by
        simpa [Amount.raw_add, Amount.ofWord] using hsup
      have hb : (w.self.balances ctx.sender).raw + ctx.value < wordBound := by
        simpa [Amount.raw_add, Amount.ofWord] using hbal
      simp [depositTx, deposit, Tx.value, hb, hs] at h
  · have hb : ¬ (w.self.balances ctx.sender).raw + ctx.value < wordBound := by
      simpa [Amount.raw_add, Amount.ofWord] using hbal
    simp [depositTx, deposit, Tx.value, hb] at h

theorem deposit_others {w' : World}
    (h : Tx.run depositTx ctx w = .ok ((), w'))
    (x : Address) (hx : x ≠ ctx.sender) :
    w'.self.balances x = w.self.balances x := by
  obtain ⟨_, _, hw'⟩ := deposit_ok_inv ctx w h
  subst hw'
  simp [depositPost, credit_other _ hx]

/-! ### withdraw -/

@[simp] theorem run_native_send {a : Asset} (to : Address) (amount : Amount a)
    (err : Error) (ctx : Ctx) (w : World) :
    Tx.run (Native.send to amount err) ctx w =
      match w.oracle.send to amount.raw w.ext with
      | none => .error (.user err)
      | some x' => .ok ((), { w with ext := x' }) := by
  simp only [Native.send]
  rw [Tx.run_bind (x := Tx.sendRaw to amount.raw)
    (f := fun ok => Tx.require (ok = true) err)]
  erw [Tx.run_sendRaw]
  cases w.oracle.send to amount.raw w.ext <;> simp [Tx.run_require]

def withdrawPost (σ : Storage) (who : Address) (amount : Amount native) : Storage :=
  { σ with
    balances := debit σ.balances who amount
    totalSupply := σ.totalSupply - amount }

theorem withdraw_ok (amount : Amount native) {x' : ExtState}
    (hbal : amount ≤ w.self.balances ctx.sender)
    (hsup : amount ≤ w.self.totalSupply)
    (hsend : w.oracle.send ctx.sender amount.raw w.ext = some x') :
    Tx.run (withdraw amount) ctx w =
      .ok ((), { w with
        self := withdrawPost w.self ctx.sender amount
        ext := x'
        log := w.log ++ [.Withdrawal ctx.sender amount] }) := by
  have hb : amount.raw ≤ (w.self.balances ctx.sender).raw := hbal
  have hs : amount.raw ≤ w.self.totalSupply.raw := hsup
  simp [withdraw, run_native_send, hb, hs, hsend, withdrawPost, debit,
    Amount.update_raw, Amount.ofWord_raw, Amount.raw_sub]

theorem withdraw_ok_inv (amount : Amount native)
    {w' : World}
    (h : Tx.run (withdraw amount) ctx w = .ok ((), w')) :
    amount ≤ w.self.balances ctx.sender ∧
      amount ≤ w.self.totalSupply ∧
      ∃ x', w.oracle.send ctx.sender amount.raw w.ext = some x' ∧
        w' = { w with
          self := withdrawPost w.self ctx.sender amount
          ext := x'
          log := w.log ++ [.Withdrawal ctx.sender amount] } := by
  by_cases hbal : amount ≤ w.self.balances ctx.sender
  · by_cases hsup : amount ≤ w.self.totalSupply
    · cases hsend : w.oracle.send ctx.sender amount.raw w.ext with
      | none =>
        have hb : amount.raw ≤ (w.self.balances ctx.sender).raw := hbal
        have hs : amount.raw ≤ w.self.totalSupply.raw := hsup
        simp [withdraw, run_native_send, hb, hs, hsend] at h
      | some x' =>
        rw [withdraw_ok ctx w amount hbal hsup hsend] at h
        cases h
        exact ⟨hbal, hsup, ⟨x', rfl, rfl⟩⟩
    · have hb : amount.raw ≤ (w.self.balances ctx.sender).raw := hbal
      have hs : ¬ amount.raw ≤ w.self.totalSupply.raw := hsup
      simp [withdraw, hb, hs] at h
  · have hb : ¬ amount.raw ≤ (w.self.balances ctx.sender).raw := hbal
    simp [withdraw, hb] at h

theorem withdraw_others (amount : Amount native)
    {w' : World}
    (h : Tx.run (withdraw amount) ctx w = .ok ((), w'))
    (x : Address) (hx : x ≠ ctx.sender) :
    w'.self.balances x = w.self.balances x := by
  obtain ⟨_, _, _, _, hw'⟩ := withdraw_ok_inv ctx w amount h
  subst hw'
  simp [withdrawPost, debit_other _ hx]

/-! ### transfer -/

def transferPost (σ : Storage) (src to : Address) (amount : Amount native) : Storage :=
  { σ with balances := credit (debit σ.balances src amount) to amount }

theorem transfer_ok (to : Address) (amount : Amount native)
    (hsub : amount ≤ w.self.balances ctx.sender)
    (hadd : (debit w.self.balances ctx.sender amount to + amount).raw < wordBound) :
    Tx.run (transfer to amount) ctx w =
      .ok (true, { w with
        self := transferPost w.self ctx.sender to amount
        log := w.log ++ [.Transfer ctx.sender to amount] }) := by
  simp only [debit, Amount.le_iff, Amount.raw_add, Amount.raw_sub,
    Amount.update_raw_apply] at hsub hadd
  simp [transfer, hsub, hadd]
  simp [transferPost, debit, credit, Amount.update2_raw,
    Amount.ofWord_update_lookup, Amount.ofWord_raw]

theorem transfer_returns_true (to : Address) (amount : Amount native)
    {r : Bool} {w' : World}
    (h : Tx.run (transfer to amount) ctx w = .ok (r, w')) : r = true := by
  by_cases hsub : amount ≤ w.self.balances ctx.sender
  · by_cases hadd : (debit w.self.balances ctx.sender amount to + amount).raw < wordBound
    · rw [transfer_ok ctx w to amount hsub hadd] at h
      cases h; rfl
    · have hle : amount.raw ≤ (w.self.balances ctx.sender).raw := hsub
      simp only [debit_credit_raw] at hadd
      simp [transfer, hle, hadd] at h
  · have hle : ¬ amount.raw ≤ (w.self.balances ctx.sender).raw :=
      hsub
    simp [transfer, hle] at h

theorem transfer_ok_inv (to : Address) (amount : Amount native)
    {w' : World}
    (h : Tx.run (transfer to amount) ctx w = .ok (true, w')) :
    amount ≤ w.self.balances ctx.sender ∧
      w' = { w with
        self := transferPost w.self ctx.sender to amount
        log := w.log ++ [.Transfer ctx.sender to amount] } := by
  by_cases hsub : amount ≤ w.self.balances ctx.sender
  · by_cases hadd : (debit w.self.balances ctx.sender amount to + amount).raw < wordBound
    · rw [transfer_ok ctx w to amount hsub hadd] at h
      cases h
      exact ⟨hsub, rfl⟩
    · have hle : amount.raw ≤ (w.self.balances ctx.sender).raw := hsub
      simp only [debit_credit_raw] at hadd
      simp [transfer, hle, hadd] at h
  · have hle : ¬ amount.raw ≤ (w.self.balances ctx.sender).raw :=
      hsub
    simp [transfer, hle] at h

theorem transfer_credits (to : Address) (amount : Amount native)
    {w' : World}
    (h : Tx.run (transfer to amount) ctx w = .ok (true, w'))
    (hne : ctx.sender ≠ to) :
    w'.self.balances to = w.self.balances to + amount := by
  obtain ⟨_, hw'⟩ := transfer_ok_inv ctx w to amount h
  subst hw'
  simp [transferPost, credit, debit, Function.update_of_ne (Ne.symm hne)]

theorem transfer_debits (to : Address) (amount : Amount native)
    {w' : World}
    (h : Tx.run (transfer to amount) ctx w = .ok (true, w'))
    (hne : ctx.sender ≠ to) :
    w'.self.balances ctx.sender + amount = w.self.balances ctx.sender := by
  obtain ⟨hsub, hw'⟩ := transfer_ok_inv ctx w to amount h
  subst hw'
  apply Amount.ext
  simp [transferPost, debit, credit, Amount.raw_add, Amount.raw_sub,
    Function.update_of_ne hne]
  exact Nat.sub_add_cancel hsub

theorem transfer_self (to : Address) (amount : Amount native)
    {w' : World}
    (h : Tx.run (transfer to amount) ctx w = .ok (true, w'))
    (heq : ctx.sender = to) :
    w'.self.balances ctx.sender = w.self.balances ctx.sender := by
  obtain ⟨hsub, hw'⟩ := transfer_ok_inv ctx w to amount h
  subst hw' heq
  apply Amount.ext
  simp [transferPost, debit, credit, Amount.raw_add, Amount.raw_sub]
  exact Nat.sub_add_cancel hsub

theorem transfer_others (to : Address) (amount : Amount native)
    {w' : World}
    (h : Tx.run (transfer to amount) ctx w = .ok (true, w'))
    (x : Address) (hx1 : x ≠ ctx.sender) (hx2 : x ≠ to) :
    w'.self.balances x = w.self.balances x := by
  obtain ⟨_, hw'⟩ := transfer_ok_inv ctx w to amount h
  subst hw'
  simp [transferPost, credit_other _ hx2, debit_other _ hx1]

theorem transfer_preserves_totalSupply (to : Address) (amount : Amount native)
    {w' : World}
    (h : Tx.run (transfer to amount) ctx w = .ok (true, w')) :
    w'.self.totalSupply = w.self.totalSupply := by
  obtain ⟨_, hw'⟩ := transfer_ok_inv ctx w to amount h
  subst hw'
  rfl

/-! ### approve -/

def approvePost (σ : Storage) (owner spender : Address) (amount : Amount native) : Storage :=
  { σ with allowances :=
      Function.update σ.allowances owner (Function.update (σ.allowances owner) spender amount) }

theorem approve_ok (spender : Address) (amount : Amount native) :
    Tx.run (approve spender amount) ctx w =
      .ok (true, { w with
        self := approvePost w.self ctx.sender spender amount
        log := w.log ++ [.Approval ctx.sender spender amount] }) := by
  simp [approve, approvePost, Amount.update_nested_raw, Amount.ofWord_raw]

theorem approve_sets (spender : Address) (amount : Amount native)
    {w' : World}
    (h : Tx.run (approve spender amount) ctx w = .ok (true, w')) :
    w'.self.allowances ctx.sender spender = amount := by
  rw [approve_ok] at h
  cases h
  simp [approvePost]

theorem approve_preserves_totalSupply (spender : Address) (amount : Amount native)
    {w' : World}
    (h : Tx.run (approve spender amount) ctx w = .ok (true, w')) :
    w'.self.totalSupply = w.self.totalSupply := by
  rw [approve_ok] at h
  cases h
  rfl

/-! ### transferFrom -/

def transferFromPost (σ : Storage) (src spender to : Address)
    (amount : Amount native) : Storage :=
  { σ with
    allowances := Function.update σ.allowances src
      (Function.update (σ.allowances src) spender
        (σ.allowances src spender - amount))
    balances := credit (debit σ.balances src amount) to amount }

theorem transferFrom_ok (src to : Address) (amount : Amount native)
    (hallow : amount ≤ w.self.allowances src ctx.sender)
    (hsub : amount ≤ w.self.balances src)
    (hadd : (debit w.self.balances src amount to + amount).raw < wordBound) :
    Tx.run (transferFrom src to amount) ctx w =
      .ok (true, { w with
        self := transferFromPost w.self src ctx.sender to amount
        log := w.log ++ [.Transfer src to amount] }) := by
  have hallow' : amount.raw ≤ (w.self.allowances src ctx.sender).raw := hallow
  have hsub' : amount.raw ≤ (w.self.balances src).raw := hsub
  simp only [debit, Amount.raw_add, Amount.raw_sub, Amount.update_raw_apply] at hadd
  simp [transferFrom, hallow', hsub', hadd]
  simp [transferFromPost, debit, credit, Amount.update_nested_raw,
    Amount.update2_raw, Amount.ofWord_update_lookup, Amount.ofWord_raw]

theorem transferFrom_ok_inv (src to : Address) (amount : Amount native)
    {w' : World}
    (h : Tx.run (transferFrom src to amount) ctx w = .ok (true, w')) :
    amount ≤ w.self.allowances src ctx.sender ∧
      amount ≤ w.self.balances src ∧
      w' = { w with
        self := transferFromPost w.self src ctx.sender to amount
        log := w.log ++ [.Transfer src to amount] } := by
  by_cases hallow : amount ≤ w.self.allowances src ctx.sender
  · by_cases hsub : amount ≤ w.self.balances src
    · by_cases hadd : (debit w.self.balances src amount to + amount).raw < wordBound
      · rw [transferFrom_ok ctx w src to amount hallow hsub hadd] at h
        cases h
        exact ⟨hallow, hsub, rfl⟩
      · have hle : amount.raw ≤ (w.self.balances src).raw := hsub
        have ha : amount.raw ≤ (w.self.allowances src ctx.sender).raw := hallow
        simp only [debit_credit_raw] at hadd
        simp [transferFrom, ha, hle, hadd] at h
    · have hle : ¬ amount.raw ≤ (w.self.balances src).raw :=
        hsub
      have ha : amount.raw ≤ (w.self.allowances src ctx.sender).raw := hallow
      simp [transferFrom, ha, hle] at h
  · have ha : ¬ amount.raw ≤ (w.self.allowances src ctx.sender).raw :=
      hallow
    simp [transferFrom, ha] at h

theorem transferFrom_returns_true (src to : Address) (amount : Amount native)
    {r : Bool} {w' : World}
    (h : Tx.run (transferFrom src to amount) ctx w = .ok (r, w')) : r = true := by
  by_cases hallow : amount ≤ w.self.allowances src ctx.sender
  · by_cases hsub : amount ≤ w.self.balances src
    · by_cases hadd : (debit w.self.balances src amount to + amount).raw < wordBound
      · rw [transferFrom_ok ctx w src to amount hallow hsub hadd] at h
        cases h; rfl
      · have hle : amount.raw ≤ (w.self.balances src).raw := hsub
        have ha : amount.raw ≤ (w.self.allowances src ctx.sender).raw := hallow
        simp only [debit_credit_raw] at hadd
        simp [transferFrom, ha, hle, hadd] at h
    · have hle : ¬ amount.raw ≤ (w.self.balances src).raw :=
        hsub
      have ha : amount.raw ≤ (w.self.allowances src ctx.sender).raw := hallow
      simp [transferFrom, ha, hle] at h
  · have ha : ¬ amount.raw ≤ (w.self.allowances src ctx.sender).raw :=
      hallow
    simp [transferFrom, ha] at h

theorem transferFrom_conserves (src to : Address) (amount : Amount native)
    {w' : World}
    (h : Tx.run (transferFrom src to amount) ctx w = .ok (true, w')) :
    w'.self.balances src + w'.self.balances to =
      w.self.balances src + w.self.balances to := by
  obtain ⟨_, hsub, hw'⟩ := transferFrom_ok_inv ctx w src to amount h
  subst hw'
  apply Amount.ext
  by_cases hne : src = to
  · subst hne
    have hle : amount.raw ≤ (w.self.balances src).raw := hsub
    simp [transferFromPost, credit_self, debit_self, Amount.raw_add,
      Amount.raw_sub, Nat.sub_add_cancel hle]
  · have hle : amount.raw ≤ (w.self.balances src).raw := hsub
    simp [transferFromPost, credit_other _ hne, debit_other _ (Ne.symm hne),
      Amount.raw_add, Amount.raw_sub]
    exact nat_sub_add_add _ _ _ hle

theorem transferFrom_credits (src to : Address) (amount : Amount native)
    {w' : World}
    (h : Tx.run (transferFrom src to amount) ctx w = .ok (true, w'))
    (hne : src ≠ to) :
    w'.self.balances to = w.self.balances to + amount := by
  obtain ⟨_, _, hw'⟩ := transferFrom_ok_inv ctx w src to amount h
  subst hw'
  simp [transferFromPost, credit, debit, Function.update_of_ne (Ne.symm hne)]

theorem transferFrom_debits (src to : Address) (amount : Amount native)
    {w' : World}
    (h : Tx.run (transferFrom src to amount) ctx w = .ok (true, w'))
    (hne : src ≠ to) :
    w'.self.balances src + amount = w.self.balances src := by
  obtain ⟨_, hsub, hw'⟩ := transferFrom_ok_inv ctx w src to amount h
  subst hw'
  apply Amount.ext
  simp [transferFromPost, debit, credit, Amount.raw_add, Amount.raw_sub,
    Function.update_of_ne hne]
  exact Nat.sub_add_cancel hsub

theorem transferFrom_self (src to : Address) (amount : Amount native)
    {w' : World}
    (h : Tx.run (transferFrom src to amount) ctx w = .ok (true, w'))
    (heq : src = to) :
    w'.self.balances src = w.self.balances src := by
  obtain ⟨_, hsub, hw'⟩ := transferFrom_ok_inv ctx w src to amount h
  subst hw' heq
  apply Amount.ext
  simp [transferFromPost, debit, credit, Amount.raw_add, Amount.raw_sub]
  exact Nat.sub_add_cancel hsub

theorem transferFrom_others (src to : Address) (amount : Amount native)
    {w' : World}
    (h : Tx.run (transferFrom src to amount) ctx w = .ok (true, w'))
    (x : Address) (hx1 : x ≠ src) (hx2 : x ≠ to) :
    w'.self.balances x = w.self.balances x := by
  obtain ⟨_, _, hw'⟩ := transferFrom_ok_inv ctx w src to amount h
  subst hw'
  simp [transferFromPost, credit_other _ hx2, debit_other _ hx1]

theorem transferFrom_allowance (src to : Address) (amount : Amount native)
    {w' : World}
    (h : Tx.run (transferFrom src to amount) ctx w = .ok (true, w')) :
    w'.self.allowances src ctx.sender + amount =
      w.self.allowances src ctx.sender := by
  obtain ⟨hallow, _, hw'⟩ := transferFrom_ok_inv ctx w src to amount h
  subst hw'
  apply Amount.ext
  simp [transferFromPost, Amount.raw_add, Amount.raw_sub]
  exact Nat.sub_add_cancel hallow

theorem transferFrom_preserves_totalSupply (src to : Address)
    (amount : Amount native) {w' : World}
    (h : Tx.run (transferFrom src to amount) ctx w = .ok (true, w')) :
    w'.self.totalSupply = w.self.totalSupply := by
  obtain ⟨_, _, hw'⟩ := transferFrom_ok_inv ctx w src to amount h
  subst hw'
  rfl

namespace Proof

theorem deposit_delta {w' : World}
    (h : Tx.run depositTx ctx w = .ok ((), w')) :
    w'.self.balances ctx.sender =
      w.self.balances ctx.sender + ⟨ctx.value⟩ ∧
    w'.self.totalSupply = w.self.totalSupply + ⟨ctx.value⟩ ∧
    World.nativeBalance w' = World.nativeBalance w := by
  obtain ⟨_, _, hw'⟩ := deposit_ok_inv ctx w h
  subst hw'
  simp [depositPost, credit, World.nativeBalance]

theorem withdraw_delta (amount : Amount native)
    {w' : World}
    (h : Tx.run (withdraw amount) ctx w = .ok ((), w')) :
    w'.self.balances ctx.sender + amount = w.self.balances ctx.sender ∧
    w'.self.totalSupply + amount = w.self.totalSupply := by
  obtain ⟨hbal, hsup, _, _, hw'⟩ := withdraw_ok_inv ctx w amount h
  subst hw'
  apply And.intro
  · apply Amount.ext
    simp [withdrawPost, debit, Amount.raw_add, Amount.raw_sub]
    exact Nat.sub_add_cancel hbal
  · apply Amount.ext
    simp [withdrawPost, Amount.raw_add, Amount.raw_sub]
    exact Nat.sub_add_cancel hsup

theorem transfer_conserves (to : Address) (amount : Amount native)
    {w' : World}
    (h : Tx.run (transfer to amount) ctx w = .ok (true, w')) :
    w'.self.balances ctx.sender + w'.self.balances to =
      w.self.balances ctx.sender + w.self.balances to := by
  obtain ⟨hsub, hw'⟩ := transfer_ok_inv ctx w to amount h
  subst hw'
  apply Amount.ext
  by_cases hne : ctx.sender = to
  · subst hne
    have hle : amount.raw ≤ (w.self.balances ctx.sender).raw := hsub
    simp [transferPost, credit_self, debit_self, Amount.raw_add, Amount.raw_sub,
      Nat.sub_add_cancel hle]
  · have hle : amount.raw ≤ (w.self.balances ctx.sender).raw := hsub
    simp [transferPost, credit_other _ hne, debit_other _ (Ne.symm hne),
      Amount.raw_add, Amount.raw_sub]
    exact nat_sub_add_add _ _ _ hle

end Proof

end WETH

