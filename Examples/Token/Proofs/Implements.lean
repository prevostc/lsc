import Stdlib.ERC20
import Examples.Token.Proofs.Tx

/-!
`IERC20.Spec Token.impl`: Token keeps every ERC20 promise. Views read stored
balances/allowances/supply; mutators are the corresponding `Tx.run`s.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Lsc Lsc.Stdlib Token

namespace Token

section

variable (ctx : Ctx) (w : World)

@[simp] theorem impl_transfer (to : Address) (amount : Amount tokenAsset) :
    Token.impl.transfer to amount ctx w =
      (Tx.run (transfer to amount) ctx w).toOption :=
  rfl

@[simp] theorem impl_transferFrom (src to : Address) (amount : Amount tokenAsset) :
    Token.impl.transferFrom src to amount ctx w =
      (Tx.run (transferFrom src to amount) ctx w).toOption :=
  rfl

@[simp] theorem impl_approve (spender : Address) (amount : Amount tokenAsset) :
    Token.impl.approve spender amount ctx w =
      (Tx.run (approve spender amount) ctx w).toOption :=
  rfl

@[simp] theorem impl_balanceOf (who : Address) (w : World) :
    Token.impl.balanceOf who w = w.self.balances who := by
  change (match Tx.run (balanceOf who) { sender := (0 : Address) } w with
    | .ok (v, _) => v
    | .error _ => default) = _
  rw [balanceOf_returns_stored_balance { sender := 0 } w who]

@[simp] theorem impl_allowance (owner spender : Address)
    (w : World) :
    Token.impl.allowance owner spender w = w.self.allowances owner spender := by
  change (match Tx.run (allowance owner spender) { sender := (0 : Address) } w with
    | .ok (v, _) => v
    | .error _ => default) = _
  rw [allowance_returns_stored { sender := 0 } w owner spender]

@[simp] theorem impl_totalSupply (w : World) :
    Token.impl.totalSupply w = w.self.totalSupply := by
  change (match Tx.run totalSupply { sender := (0 : Address) } w with
    | .ok (v, _) => v
    | .error _ => default) = _
  rw [totalSupply_returns_stored { sender := 0 } w]

private lemma amount_add_comm (x y : Amount tokenAsset) : x + y = y + x :=
  Amount.ext (Nat.add_comm _ _)

private lemma ge_self_add (x y : Amount tokenAsset) : x + y ≥ x :=
  Nat.le_add_right x.raw y.raw

private lemma ge_add_add (x y z : Amount tokenAsset) : x + y + z ≥ x := by
  have hxy : x.raw ≤ x.raw + y.raw := Nat.le_add_right _ _
  have : x.raw ≤ x.raw + y.raw + z.raw :=
    Nat.le_trans hxy (Nat.le_add_right (x.raw + y.raw) z.raw)
  simpa [Amount.raw_add] using this

private lemma sub_add_ge (b a n : Amount tokenAsset) (hn : n.raw ≤ b.raw) (ha : n.raw ≤ a.raw) :
    b - n + a ≥ b := by
  have : b.raw ≤ b.raw - n.raw + a.raw :=
    calc
      b.raw = b.raw - n.raw + n.raw := (Nat.sub_add_cancel hn).symm
      _ ≤ b.raw - n.raw + a.raw := Nat.add_le_add_left ha _
  simpa [Amount.raw_sub, Amount.raw_add] using this

/-- Caller ≠ `x` ⇒ `transfer` does not drop `x`'s balance. -/
theorem transfer_balance_protected (to : Address) (amount : Amount tokenAsset)
    {r : Bool} {w' : World} (x : Address)
    (h : Tx.run (transfer to amount) ctx w = .ok (r, w'))
    (hne : ctx.sender ≠ x) :
    w'.self.balances x + w.self.allowances x ctx.sender ≥ w.self.balances x := by
  have hr := Proof.transfer_returns_true ctx w to amount h
  subst hr
  obtain ⟨_, _, hw'⟩ := Proof.transfer_ok_inv ctx w to amount h
  subst hw'
  if hx : x = to then
    have hne' : ctx.sender ≠ to := hx ▸ hne
    have hb : (transferPost w.self ctx.sender to amount).balances to =
        w.self.balances to + amount := by
      simp [transferPost, debit_other _ (Ne.symm hne')]
    rw [hx, hb]
    exact ge_add_add _ _ _
  else
    have hb : (transferPost w.self ctx.sender to amount).balances x = w.self.balances x := by
      simp [transferPost, credit_other _ hx, debit_other _ (Ne.symm hne)]
    rw [hb]
    exact ge_self_add _ _

/-- Caller ≠ `x` ⇒ `transferFrom` does not drop `x` below `balance − allowance`. -/
theorem transferFrom_balance_protected (src to : Address) (amount : Amount tokenAsset)
    {r : Bool} {w' : World} (x : Address)
    (h : Tx.run (transferFrom src to amount) ctx w = .ok (r, w'))
    (hne : ctx.sender ≠ x) :
    w'.self.balances x + w.self.allowances x ctx.sender ≥ w.self.balances x := by
  have hr := Proof.transferFrom_returns_true ctx w src to amount h
  subst hr
  obtain ⟨hallow, hsub, _, hw'⟩ := Proof.transferFrom_ok_inv ctx w src to amount h
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

/-- `approve` never changes balances. -/
theorem approve_balance_protected (spender : Address) (amount : Amount tokenAsset)
    {r : Bool} {w' : World} (x : Address)
    (h : Tx.run (approve spender amount) ctx w = .ok (r, w')) :
    w'.self.balances x + w.self.allowances x ctx.sender ≥ w.self.balances x := by
  have hr := Proof.approve_returns_true ctx w spender amount h
  subst hr
  rw [approve_ok ctx w spender amount] at h
  cases h
  exact ge_self_add _ _

/-- `mint` never decreases an existing balance. -/
theorem mint_balance_protected (to : Address) (amount : Amount tokenAsset)
    {r : Unit} {w' : World} (x : Address)
    (h : Tx.run (mint to amount) ctx w = .ok (r, w')) :
    w'.self.balances x + w.self.allowances x ctx.sender ≥ w.self.balances x := by
  cases r
  by_cases howner : ctx.sender = w.self.owner
  · by_cases hsupply : (w.self.totalSupply + amount).raw < wordBound
    · by_cases hadd : (w.self.balances to + amount).raw < wordBound
      · rw [mint_ok ctx w to amount howner hsupply hadd] at h
        cases h
        if hx : x = to then
          have hb : (mintPost w.self to amount).balances to = w.self.balances to + amount := by
            simp [mintPost, credit]
          rw [hx, hb]
          exact ge_add_add _ _ _
        else
          have hb : (mintPost w.self to amount).balances x = w.self.balances x := by
            simp [mintPost, credit_other _ hx]
          rw [hb]
          exact ge_self_add _ _
      · rw [mint_reverts_on_balance_overflow ctx w to amount howner hsupply
          (Nat.not_lt.mp hadd)] at h
        cases h
    · rw [mint_reverts_on_overflow ctx w to amount howner (Nat.not_lt.mp hsupply)] at h
      cases h
  · rw [mint_reverts_for_non_owner ctx w to amount howner] at h
    cases h

/-- Caller ≠ `x` ⇒ `burn` does not touch `x`'s balance. -/
theorem burn_balance_protected (amount : Amount tokenAsset)
    {r : Unit} {w' : World} (x : Address)
    (h : Tx.run (burn amount) ctx w = .ok (r, w'))
    (hne : ctx.sender ≠ x) :
    w'.self.balances x + w.self.allowances x ctx.sender ≥ w.self.balances x := by
  cases r
  by_cases hsub : amount ≤ w.self.balances ctx.sender
  · by_cases hsupply : amount ≤ w.self.totalSupply
    · rw [burn_ok ctx w amount hsub hsupply] at h
      cases h
      have hb : (burnPost w.self ctx.sender amount).balances x = w.self.balances x := by
        simp [burnPost, debit_other _ (Ne.symm hne)]
      rw [hb]
      exact ge_self_add _ _
    · rw [burn_reverts_on_insufficient_supply ctx w amount hsub (Nat.not_le.mp hsupply)] at h
      cases h
  · rw [burn_reverts_on_insufficient_balance ctx w amount (Nat.not_le.mp hsub)] at h
    cases h

/-- Views leave the world unchanged. -/
theorem balanceOf_balance_protected (who : Address)
    {r : Amount tokenAsset} {w' : World} (x : Address)
    (h : Tx.run (balanceOf who) ctx w = .ok (r, w')) :
    w'.self.balances x + w.self.allowances x ctx.sender ≥ w.self.balances x := by
  rw [balanceOf_returns_stored_balance ctx w who] at h
  cases h
  exact ge_self_add _ _

theorem allowance_balance_protected (owner spender : Address)
    {r : Amount tokenAsset} {w' : World} (x : Address)
    (h : Tx.run (allowance owner spender) ctx w = .ok (r, w')) :
    w'.self.balances x + w.self.allowances x ctx.sender ≥ w.self.balances x := by
  rw [allowance_returns_stored ctx w owner spender] at h
  cases h
  exact ge_self_add _ _

theorem totalSupply_balance_protected
    {r : Amount tokenAsset} {w' : World} (x : Address)
    (h : Tx.run totalSupply ctx w = .ok (r, w')) :
    w'.self.balances x + w.self.allowances x ctx.sender ≥ w.self.balances x := by
  rw [totalSupply_returns_stored ctx w] at h
  cases h
  exact ge_self_add _ _

end

namespace Proof

theorem erc20 : IERC20.Spec Token.impl where
  transfer_moves := by
    intro to amount ctx w w' h
    have hok := Tx.run_toOption_ok (by simpa [impl_transfer] using h)
    constructor
    · have hc := transfer_conserves ctx w to amount hok
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
        simpa [Spec.exec, Token.spec, Token.entry] using hrun
      simpa [impl_balanceOf, impl_allowance] using
        transfer_balance_protected ctx w args.1 args.2 x hrun' hne
    | transferFrom =>
      have hrun' : Tx.run (transferFrom args.1 args.2.1 args.2.2) ctx w = .ok (r, w') := by
        simpa [Spec.exec, Token.spec, Token.entry] using hrun
      simpa [impl_balanceOf, impl_allowance] using
        transferFrom_balance_protected ctx w args.1 args.2.1 args.2.2 x hrun' hne
    | approve =>
      have hrun' : Tx.run (approve args.1 args.2) ctx w = .ok (r, w') := by
        simpa [Spec.exec, Token.spec, Token.entry] using hrun
      simpa [impl_balanceOf, impl_allowance] using
        approve_balance_protected ctx w args.1 args.2 x hrun'
    | mint =>
      have hrun' : Tx.run (mint args.1 args.2) ctx w = .ok (r, w') := by
        simpa [Spec.exec, Token.spec, Token.entry] using hrun
      simpa [impl_balanceOf, impl_allowance] using
        mint_balance_protected ctx w args.1 args.2 x hrun'
    | burn =>
      have hrun' : Tx.run (burn args) ctx w = .ok (r, w') := by
        simpa [Spec.exec, Token.spec, Token.entry] using hrun
      simpa [impl_balanceOf, impl_allowance] using
        burn_balance_protected ctx w args x hrun' hne
    | balanceOf =>
      have hrun' : Tx.run (balanceOf args) ctx w = .ok (r, w') := by
        simpa [Spec.exec, Token.spec, Token.entry] using hrun
      simpa [impl_balanceOf, impl_allowance] using
        balanceOf_balance_protected ctx w args x hrun'
    | allowance =>
      have hrun' : Tx.run (allowance args.1 args.2) ctx w = .ok (r, w') := by
        simpa [Spec.exec, Token.spec, Token.entry] using hrun
      simpa [impl_balanceOf, impl_allowance] using
        allowance_balance_protected ctx w args.1 args.2 x hrun'
    | totalSupply =>
      have hrun' : Tx.run totalSupply ctx w = .ok (r, w') := by
        simpa [Spec.exec, Token.spec, Token.entry] using hrun
      simpa [impl_balanceOf, impl_allowance] using
        totalSupply_balance_protected ctx w x hrun'

end Proof

end Token
