import EscrowProofs

/-!
Required `Escrow` theorems (`docs/reference/ESCROW.md`): Tier-A (Escrow-local) and Tier-B
(generic `[HonestERC20 T]` token effects). See ADR 0009. -/

open Lsc Escrow Lsc.Interfaces

/-! ## Tier A — Escrow-local (any `[HonestERC20 T]` callee) -/

section TierA

variable {T : Type} [HonestERC20 T]
variable (recipient escrowAddr : Address) (amount : EscrowAmount)
variable (es : ContractState EscrowStorage) (ts : ContractState T)

/-- **Property:** Only the owner may call `release`. -/
theorem release_rejects_non_owner
    (h : ¬ es.context.caller == es.storage.owner) :
    ContractM.PairM.run (releaseHonest T recipient (Wad.Fixed.retag amount)) es ts =
      .error EscrowError.NotOwner := by
  simp [releaseHonest, requireOwner, ContractM.PairM.run, ContractM.PairM.bind_apply,
    ContractM.PairM.liftCaller_apply, h]

theorem release_rejects_when_already_locked
    (howner : es.context.caller == es.storage.owner) (h : es.locked = true) :
    ContractM.PairM.run (releaseHonest T recipient (Wad.Fixed.retag amount)) es ts =
      .error EscrowError.Reentrant := by
  simp [releaseHonest, requireOwner, bumpReleasedEmit, ContractM.PairM.run,
    ContractM.PairM.bind_apply, ContractM.PairM.liftCaller_apply, ContractM.PairM.exec,
    howner, h, ContractErrors.fromFramework]

theorem release_atomic_on_transfer_failure
    (howner : es.context.caller == es.storage.owner) (hlocked : es.locked = false)
    {e : IERC20Spec.ErrT T}
    (hcall : (IERC20Spec.transferTyped (T := T) recipient (Wad.Fixed.retag amount)) ts =
      .error e) :
    ContractM.PairM.run (releaseHonest T recipient (Wad.Fixed.retag amount)) es ts =
      .error EscrowError.ExternalCallFailed :=
  release_honest_atomic_on_transfer_failure (T := T) recipient (Wad.Fixed.retag amount) es ts
    howner hlocked (e := e) hcall

end TierA

section TierBGeneric

/-! ## Tier B — Token effects (`[HonestERC20 T]`) -/

variable (T : Type) [HonestERC20 T]
variable (recipient escrowAddr : Address) (amount : Wad)
variable (es : ContractState EscrowStorage) (ts : ContractState T)
variable (howner : es.context.caller == es.storage.owner)
variable (hlocked : es.locked = false)
variable (hreleased : es.storage.released.n + amount.n < 2 ^ 256)
variable (hsub : amount.n ≤ (IERC20Spec.getBalance (T := T) ts.storage escrowAddr).n)
variable (hadd : (IERC20Spec.getBalance (T := T) ts.storage recipient).n + amount.n < 2 ^ 256)
variable (htokenCaller : ts.context.caller == escrowAddr)

include howner hlocked hreleased hsub hadd htokenCaller in
theorem release_honest_increases_released :
    ∃ es' ts', ContractM.PairM.run (releaseHonest T recipient amount) es ts =
        .ok ((), es', ts', [EscrowEvent.Released (Wad.Fixed.retag amount)]) ∧
      es'.storage.released.n = es.storage.released.n + amount.n := by
  obtain ⟨es', ts', h, hreleased', _⟩ :=
    runReleaseOkHonest T recipient escrowAddr amount es ts howner hlocked hreleased hsub hadd
      htokenCaller
  exact ⟨es', ts', h, hreleased'⟩

include howner hlocked hreleased hsub hadd htokenCaller in
theorem release_honest_debits_escrow (hne : escrowAddr ≠ recipient) :
    ∃ es' ts', ContractM.PairM.run (releaseHonest T recipient amount) es ts =
        .ok ((), es', ts', [EscrowEvent.Released (Wad.Fixed.retag amount)]) ∧
      IERC20Spec.getBalance (T := T) ts'.storage escrowAddr =
        Wad.mkNat ((IERC20Spec.getBalance (T := T) ts.storage escrowAddr).n - amount.n) := by
  obtain ⟨es', ts', h, _, hbal⟩ :=
    runReleaseOkHonest T recipient escrowAddr amount es ts howner hlocked hreleased hsub hadd
      htokenCaller
  exact ⟨es', ts', h, by simpa [hne] using hbal escrowAddr⟩

include howner hlocked hreleased hsub hadd htokenCaller in
theorem release_honest_credits_recipient (hne : escrowAddr ≠ recipient) :
    ∃ es' ts', ContractM.PairM.run (releaseHonest T recipient amount) es ts =
        .ok ((), es', ts', [EscrowEvent.Released (Wad.Fixed.retag amount)]) ∧
      IERC20Spec.getBalance (T := T) ts'.storage recipient =
        Wad.mkNat ((IERC20Spec.getBalance (T := T) ts.storage recipient).n + amount.n) := by
  obtain ⟨es', ts', h, _, hbal⟩ :=
    runReleaseOkHonest T recipient escrowAddr amount es ts howner hlocked hreleased hsub hadd
      htokenCaller
  exact ⟨es', ts', h, by simpa [hne, Ne.symm hne] using hbal recipient⟩

end TierBGeneric
