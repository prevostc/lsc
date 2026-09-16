import Stdlib.ERC20
import Examples.WNative.Proofs.Tx

/-!
`IERC20.Exact WNative.impl`: WNative keeps every ERC20 promise.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Lsc Lsc.Stdlib WNative

namespace WNative

section

variable (ctx : Ctx) (w : World Storage ExtState Event)

@[simp] theorem impl_transfer (to : Address) (amount : Amount native) :
    WNative.impl.transfer to amount ctx w =
      (Tx.run (transfer to amount) ctx w).toOption :=
  rfl

@[simp] theorem impl_transferFrom (src to : Address) (amount : Amount native) :
    WNative.impl.transferFrom src to amount ctx w =
      (Tx.run (transferFrom src to amount) ctx w).toOption :=
  rfl

@[simp] theorem impl_approve (spender : Address) (amount : Amount native) :
    WNative.impl.approve spender amount ctx w =
      (Tx.run (approve spender amount) ctx w).toOption :=
  rfl

@[simp] theorem impl_balanceOf (who : Address) (w : World Storage ExtState Event) :
    WNative.impl.balanceOf who w = w.self.balances who := by
  change (match Tx.run (balanceOf who) { sender := (0 : Address) } w with
    | .ok (v, _) => v
    | .error _ => default) = _
  rw [balanceOf_returns_stored_balance { sender := 0 } w who]

@[simp] theorem impl_allowance (owner spender : Address)
    (w : World Storage ExtState Event) :
    WNative.impl.allowance owner spender w = w.self.allowances owner spender := by
  change (match Tx.run (allowance owner spender) { sender := (0 : Address) } w with
    | .ok (v, _) => v
    | .error _ => default) = _
  rw [allowance_returns_stored { sender := 0 } w owner spender]

@[simp] theorem impl_totalSupply (w : World Storage ExtState Event) :
    WNative.impl.totalSupply w = w.self.totalSupply := by
  change (match Tx.run totalSupply { sender := (0 : Address) } w with
    | .ok (v, _) => v
    | .error _ => default) = _
  rw [totalSupply_returns_stored { sender := 0 } w]

private lemma amount_add_comm (x y : Amount native) : x + y = y + x :=
  Amount.ext (Nat.add_comm _ _)

private lemma ge_self_add (x y : Amount native) : x + y ≥ x :=
  Nat.le_add_right x.raw y.raw

private lemma ge_add_add (x y z : Amount native) : x + y + z ≥ x := by
  have hxy : x.raw ≤ x.raw + y.raw := Nat.le_add_right _ _
  have : x.raw ≤ x.raw + y.raw + z.raw :=
    Nat.le_trans hxy (Nat.le_add_right (x.raw + y.raw) z.raw)
  simpa [Amount.raw_add] using this

private lemma sub_add_ge (b a n : Amount native) (hn : n.raw ≤ b.raw) (ha : n.raw ≤ a.raw) :
    b - n + a ≥ b := by
  have : b.raw ≤ b.raw - n.raw + a.raw :=
    calc
      b.raw = b.raw - n.raw + n.raw := (Nat.sub_add_cancel hn).symm
      _ ≤ b.raw - n.raw + a.raw := Nat.add_le_add_left ha _
  simpa [Amount.raw_sub, Amount.raw_add] using this

theorem transfer_balance_protected (to : Address) (amount : Amount native)
    {r : Bool} {w' : World Storage ExtState Event} (x : Address)
    (h : Tx.run (transfer to amount) ctx w = .ok (r, w'))
    (hne : ctx.sender ≠ x) :
    w'.self.balances x + w.self.allowances x ctx.sender ≥ w.self.balances x := by
  have hr := transfer_returns_true ctx w to amount h
  subst hr
  obtain ⟨_, hw'⟩ := transfer_ok_inv ctx w to amount h
  subst hw'
  if hx : x = to then
    have hne' : ctx.sender ≠ to := hx ▸ hne
    have hb : (transferPost w.self ctx.sender to amount).balances to =
        w.self.balances to + amount := by
      simp [transferPost, debit_other _ (Ne.symm hne')]
    rw [hx, hb]
    exact ge_add_add _ _ _
  else
    have hb : (transferPost w.self ctx.sender to amount).balances x =
        w.self.balances x := by
      simp [transferPost, credit_other _ hx, debit_other _ (Ne.symm hne)]
    rw [hb]
    exact ge_self_add _ _

theorem transferFrom_balance_protected (src to : Address) (amount : Amount native)
    {r : Bool} {w' : World Storage ExtState Event} (x : Address)
    (h : Tx.run (transferFrom src to amount) ctx w = .ok (r, w'))
    (hne : ctx.sender ≠ x) :
    w'.self.balances x + w.self.allowances x ctx.sender ≥ w.self.balances x := by
  have hr := transferFrom_returns_true ctx w src to amount h
  subst hr
  obtain ⟨hallow, hsub, hw'⟩ := transferFrom_ok_inv ctx w src to amount h
  subst hw'
  if hx : x = src then
    if hto : src = to then
      have hle : amount.raw ≤ (w.self.balances src).raw := hsub
      have hb : (transferFromPost w.self src ctx.sender src amount).balances src =
          w.self.balances src := by
        apply Amount.ext
        simp [transferFromPost, debit, credit, Function.update_self,
          Amount.raw_add, Amount.raw_sub, Nat.sub_add_cancel hle]
      have hpost : (transferFromPost w.self src ctx.sender to amount).balances src =
          w.self.balances src := by
        simpa [hto] using hb
      rw [hx, hpost]
      exact ge_self_add _ _
    else
      have hb : (transferFromPost w.self src ctx.sender to amount).balances src =
          w.self.balances src - amount := by
        simp [transferFromPost, credit_other _ hto]
      rw [hx, hb]
      exact sub_add_ge _ _ _ hsub hallow
  else if hxto : x = to then
    have hsrc : to ≠ src := fun h => hx (hxto.trans h)
    have hb : (transferFromPost w.self src ctx.sender to amount).balances to =
        w.self.balances to + amount := by
      simp [transferFromPost, debit_other _ hsrc]
    rw [hxto, hb]
    exact ge_add_add _ _ _
  else
    have hb : (transferFromPost w.self src ctx.sender to amount).balances x =
        w.self.balances x := by
      simp [transferFromPost, credit_other _ hxto, debit_other _ hx]
    rw [hb]
    exact ge_self_add _ _

theorem approve_balance_protected (spender : Address) (amount : Amount native)
    {r : Bool} {w' : World Storage ExtState Event} (x : Address)
    (h : Tx.run (approve spender amount) ctx w = .ok (r, w')) :
    w'.self.balances x + w.self.allowances x ctx.sender ≥ w.self.balances x := by
  rw [approve_ok] at h
  cases h
  exact ge_self_add _ _

theorem deposit_balance_protected {w' : World Storage ExtState Event} (x : Address)
    (h : Tx.run depositTx ctx w = .ok ((), w')) :
    w'.self.balances x + w.self.allowances x ctx.sender ≥ w.self.balances x := by
  by_cases hx : x = ctx.sender
  · rw [hx]
    have ⟨hbal, _, _⟩ := Proof.deposit_delta ctx w h
    simpa [hbal] using ge_add_add (w.self.balances ctx.sender) ⟨ctx.value⟩
      (w.self.allowances ctx.sender ctx.sender)
  · have hb := deposit_others ctx w h x hx
    simp [hb]

theorem withdraw_balance_protected (amount : Amount native)
    {w' : World Storage ExtState Event} (x : Address)
    (h : Tx.run (withdraw amount) ctx w = .ok ((), w'))
    (hne : ctx.sender ≠ x) :
    w'.self.balances x + w.self.allowances x ctx.sender ≥ w.self.balances x := by
  have hb := withdraw_others ctx w amount h x hne.symm
  simp [hb]

end

namespace Proof

theorem wnative_exact : IERC20.Exact WNative.impl where
  transfer_moves := by
    intro to amount ctx w w' h
    have hok := Tx.run_toOption_ok (by simpa [impl_transfer] using h)
    constructor
    · have hc := Proof.transfer_conserves ctx w to amount hok
      rw [amount_add_comm (w'.self.balances ctx.sender),
          amount_add_comm (w.self.balances ctx.sender)] at hc
      simpa [impl_balanceOf] using hc
    · constructor
      · intro hne
        simpa [impl_balanceOf] using transfer_credits ctx w to amount hok hne
      · intro x hx1 hx2
        simpa [impl_balanceOf] using transfer_others ctx w to amount hok x hx1 hx2
  transfer_supply := by
    intro to amount ctx w r w' h
    have hok := Tx.run_toOption_ok (by simpa [impl_transfer] using h)
    have hr := transfer_returns_true ctx w to amount hok
    subst hr
    simpa [impl_totalSupply] using
      transfer_preserves_totalSupply ctx w to amount hok
  transferFrom_moves := by
    intro src to amount ctx w w' h
    have hok := Tx.run_toOption_ok (by simpa [impl_transferFrom] using h)
    constructor
    · have hc := transferFrom_conserves ctx w src to amount hok
      rw [amount_add_comm (w'.self.balances src),
          amount_add_comm (w.self.balances src)] at hc
      simpa [impl_balanceOf] using hc
    · constructor
      · intro hne
        simpa [impl_balanceOf] using transferFrom_credits ctx w src to amount hok hne
      · intro x hx1 hx2
        simpa [impl_balanceOf] using transferFrom_others ctx w src to amount hok x hx1 hx2
  transferFrom_allowance := by
    intro src to amount ctx w w' h _hne
    have hok := Tx.run_toOption_ok (by simpa [impl_transferFrom] using h)
    simpa [impl_allowance] using transferFrom_allowance ctx w src to amount hok
  approve_sets := by
    intro spender amount ctx w w' h
    have hok := Tx.run_toOption_ok (by simpa [impl_approve] using h)
    simpa [impl_allowance] using approve_sets ctx w spender amount hok
  balance_protected := by
    intro ctx w w' x hstep hne
    rcases hstep with ⟨fn, args, r, hrun⟩
    cases fn with
    | transfer =>
      have hrun' : Tx.run (transfer args.1 args.2) ctx w = .ok (r, w') := by
        simpa [Spec.exec, WNative.spec, WNative.entry] using hrun
      simpa [impl_balanceOf, impl_allowance] using
        transfer_balance_protected ctx w args.1 args.2 x hrun' hne
    | transferFrom =>
      have hrun' : Tx.run (transferFrom args.1 args.2.1 args.2.2) ctx w = .ok (r, w') := by
        simpa [Spec.exec, WNative.spec, WNative.entry] using hrun
      simpa [impl_balanceOf, impl_allowance] using
        transferFrom_balance_protected ctx w args.1 args.2.1 args.2.2 x hrun' hne
    | approve =>
      have hrun' : Tx.run (approve args.1 args.2) ctx w = .ok (r, w') := by
        simpa [Spec.exec, WNative.spec, WNative.entry] using hrun
      simpa [impl_balanceOf, impl_allowance] using
        approve_balance_protected ctx w args.1 args.2 x hrun'
    | deposit =>
      have hrun' : Tx.run depositTx ctx w = .ok (r, w') := by
        simpa [Spec.exec, WNative.spec, WNative.entry, depositTx] using hrun
      simpa [impl_balanceOf, impl_allowance] using
        deposit_balance_protected ctx w x hrun'
    | withdraw =>
      have hrun' : Tx.run (withdraw args) ctx w = .ok (r, w') := by
        simpa [Spec.exec, WNative.spec, WNative.entry] using hrun
      simpa [impl_balanceOf, impl_allowance] using
        withdraw_balance_protected ctx w args x hrun' hne
    | balanceOf | allowance | totalSupply =>
      have : w' = w := by
        simp [Spec.exec, WNative.spec, WNative.entry] at hrun
        cases hrun; rfl
      subst this
      exact ge_self_add _ _
  transfer_exact := by
    intro to amount ctx w w' h
    have hok := Tx.run_toOption_ok (by simpa [impl_transfer] using h)
    constructor
    · intro hne
      constructor
      · simpa [impl_balanceOf] using transfer_debits ctx w to amount hok hne
      · simpa [impl_balanceOf] using transfer_credits ctx w to amount hok hne
    · intro heq
      simpa [impl_balanceOf] using transfer_self ctx w to amount hok heq
  transfer_others := by
    intro to amount ctx w w' h x hx1 hx2
    have hok := Tx.run_toOption_ok (by simpa [impl_transfer] using h)
    simpa [impl_balanceOf] using transfer_others ctx w to amount hok x hx1 hx2
  transferFrom_exact := by
    intro src to amount ctx w w' h
    have hok := Tx.run_toOption_ok (by simpa [impl_transferFrom] using h)
    constructor
    · intro hne
      constructor
      · simpa [impl_balanceOf] using transferFrom_debits ctx w src to amount hok hne
      · simpa [impl_balanceOf] using transferFrom_credits ctx w src to amount hok hne
    · intro heq
      simpa [impl_balanceOf] using transferFrom_self ctx w src to amount hok heq
  transferFrom_others := by
    intro src to amount ctx w w' h x hx1 hx2
    have hok := Tx.run_toOption_ok (by simpa [impl_transferFrom] using h)
    simpa [impl_balanceOf] using transferFrom_others ctx w src to amount hok x hx1 hx2
  transfer_supply_constant := by
    intro to amount ctx w r w' h
    have hok := Tx.run_toOption_ok (by simpa [impl_transfer] using h)
    have hr := transfer_returns_true ctx w to amount hok
    subst hr
    simpa [impl_totalSupply] using
      transfer_preserves_totalSupply ctx w to amount hok
  transferFrom_supply_constant := by
    intro src to amount ctx w r w' h
    have hok := Tx.run_toOption_ok (by simpa [impl_transferFrom] using h)
    have hr := transferFrom_returns_true ctx w src to amount hok
    subst hr
    simpa [impl_totalSupply] using
      transferFrom_preserves_totalSupply ctx w src to amount hok
  approve_supply_constant := by
    intro spender amount ctx w r w' h
    have hok := Tx.run_toOption_ok (by simpa [impl_approve] using h)
    rw [approve_ok ctx w spender amount] at hok
    cases hok
    simp [impl_totalSupply, approvePost]

end Proof

end WNative
