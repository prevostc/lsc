import TokenProofs

/-!
Required `Token` theorems (`docs/reference/TOKEN.md`), proven against `Token.lean` — stated here
as universally quantified properties (`∀` over every state/address/amount), derived from the
Tier-1 characterization lemmas in `TokenProofs.lean` (`runTransferOk`/`runMintOk`/...), not as
concrete-witness `native_decide` tests. Every theorem below is a short corollary: its statement,
immediately discharged by instantiating/simplifying the corresponding Tier-1 lemma. -/

open Lsc Token

/-! ## `balanceOf` -/

/-- `balanceOf who` always returns exactly `who`'s stored balance, for every state/address. -/
theorem balanceOf_returns_stored_balance (who : Address) (s : ContractState TokenStorage) :
    Except.map (fun x => Val.wadOf x.1) (runS (Token.balanceOf who) s) =
      .ok (s.storage.balances who) :=
  runBalanceOfOk who s

/-- Corollary: a never-written address's balance is `0` (`Wad.WadMap`'s total-function default). -/
theorem balanceOf_zero_by_default (who : Address) (owner : Address) (totalSupply : Amount) :
    Except.map (fun x => Val.wadOf x.1)
        (runS (Token.balanceOf who) (mkState owner totalSupply zeroBalances)) =
      .ok (Wad.mkNat 0) :=
  runBalanceOfOk who (mkState owner totalSupply zeroBalances)

/-! ## `transfer`

Four separate, plainly-statable claims, exactly mirroring `Escrow`'s
`release_debits_escrow`/`release_credits_recipient`/`release_preserves_other_balances`/
`release_self_release_is_noop` split (`EscrowTheorem.lean`) — this is how a human actually
describes `transfer`: "it debits the caller", "it credits the recipient", "it leaves everyone
else alone", and, as a degenerate edge case, "transferring to yourself is a no-op". All four are
the same `∀ a, ..` fact from `TokenProofs.runTransferOk`, just each instantiated/simplified at the
one address (or address class) it's actually talking about. -/

/-- If the caller doesn't transfer to themselves, `transfer` debits exactly `amount` from the
caller's own balance. -/
theorem transfer_debits_sender (recipient : Address) (amount : Wad) (s : ContractState TokenStorage)
    (hne : s.context.caller ≠ recipient)
    (hsub : amount.n ≤ (s.storage.balances s.context.caller).n)
    (hadd : (s.storage.balances recipient).n + amount.n < 2 ^ 256) :
    ∃ s', runS (transfer recipient amount : TokenM Unit) s =
        .ok ((), s', [TokenEvent.Transfer (Wad.Fixed.retag amount)]) ∧
      s'.storage.balances s.context.caller =
        Wad.mkNat ((s.storage.balances s.context.caller).n - amount.n) := by
  obtain ⟨s', h, hbal⟩ := runTransferOk recipient amount s hsub hadd
  exact ⟨s', h, by simpa [hne] using hbal s.context.caller⟩

/-- If the caller doesn't transfer to themselves, `transfer` credits exactly `amount` to the
recipient's balance. -/
theorem transfer_credits_recipient (recipient : Address) (amount : Wad)
    (s : ContractState TokenStorage) (hne : s.context.caller ≠ recipient)
    (hsub : amount.n ≤ (s.storage.balances s.context.caller).n)
    (hadd : (s.storage.balances recipient).n + amount.n < 2 ^ 256) :
    ∃ s', runS (transfer recipient amount : TokenM Unit) s =
        .ok ((), s', [TokenEvent.Transfer (Wad.Fixed.retag amount)]) ∧
      s'.storage.balances recipient = Wad.mkNat ((s.storage.balances recipient).n + amount.n) := by
  obtain ⟨s', h, hbal⟩ := runTransferOk recipient amount s hsub hadd
  exact ⟨s', h, by simpa [hne, Ne.symm hne] using hbal recipient⟩

/-- `transfer` doesn't touch any balance other than the caller's and the recipient's. -/
theorem transfer_preserves_other_balances (recipient : Address) (amount : Wad)
    (s : ContractState TokenStorage) (a : Address) (ha1 : a ≠ s.context.caller)
    (ha2 : a ≠ recipient)
    (hsub : amount.n ≤ (s.storage.balances s.context.caller).n)
    (hadd : (s.storage.balances recipient).n + amount.n < 2 ^ 256) :
    ∃ s', runS (transfer recipient amount : TokenM Unit) s =
        .ok ((), s', [TokenEvent.Transfer (Wad.Fixed.retag amount)]) ∧
      s'.storage.balances a = s.storage.balances a := by
  obtain ⟨s', h, hbal⟩ := runTransferOk recipient amount s hsub hadd
  exact ⟨s', h, by simpa [ha1, ha2] using hbal a⟩

/-- Degenerate edge case: transferring to yourself leaves your balance unchanged (the debit and
the credit exactly cancel). -/
theorem transfer_self_transfer_is_noop (amount : Wad) (s : ContractState TokenStorage)
    (hsub : amount.n ≤ (s.storage.balances s.context.caller).n)
    (hadd : (s.storage.balances s.context.caller).n + amount.n < 2 ^ 256) :
    ∃ s', runS (transfer s.context.caller amount : TokenM Unit) s =
        .ok ((), s', [TokenEvent.Transfer (Wad.Fixed.retag amount)]) ∧
      s'.storage.balances s.context.caller = s.storage.balances s.context.caller := by
  obtain ⟨s', h, hbal⟩ := runTransferOk s.context.caller amount s hsub hadd
  exact ⟨s', h, by simpa using hbal s.context.caller⟩

/-- `transfer` reverts with `Underflow` whenever the caller's balance is below `amount`. -/
theorem transfer_reverts_on_insufficient_balance (recipient : Address) (amount : Wad)
    (s : ContractState TokenStorage) (h : (s.storage.balances s.context.caller).n < amount.n) :
    runS (transfer recipient amount : TokenM Unit) s = .error TokenError.Underflow :=
  runTransferErr recipient amount s h

/-! ## `mint` -/

/-- `mint` (called by the owner) increases `totalSupply` by exactly `amount`. -/
theorem mint_increases_total_supply (recipient : Address) (amount : Wad)
    (s : ContractState TokenStorage) (howner : s.context.caller == s.storage.owner)
    (hsupply : s.storage.totalSupply.n + amount.n < 2 ^ 256)
    (hadd : (s.storage.balances recipient).n + amount.n < 2 ^ 256) :
    ∃ s', runS (mint recipient amount : TokenM Unit) s =
        .ok ((), s', [TokenEvent.Mint (Wad.Fixed.retag amount)]) ∧
      s'.storage.totalSupply.n = s.storage.totalSupply.n + amount.n := by
  obtain ⟨s', h, hsupply', _, _⟩ := runMintOk recipient amount s howner hsupply hadd
  exact ⟨s', h, hsupply'⟩

/-- `mint` (called by the owner) credits exactly `amount` to the recipient's balance. -/
theorem mint_increases_recipient_balance (recipient : Address) (amount : Wad)
    (s : ContractState TokenStorage) (howner : s.context.caller == s.storage.owner)
    (hsupply : s.storage.totalSupply.n + amount.n < 2 ^ 256)
    (hadd : (s.storage.balances recipient).n + amount.n < 2 ^ 256) :
    ∃ s', runS (mint recipient amount : TokenM Unit) s =
        .ok ((), s', [TokenEvent.Mint (Wad.Fixed.retag amount)]) ∧
      s'.storage.balances recipient = Wad.mkNat ((s.storage.balances recipient).n + amount.n) := by
  obtain ⟨s', h, _, hbal, _⟩ := runMintOk recipient amount s howner hsupply hadd
  exact ⟨s', h, hbal⟩

/-- `mint` doesn't touch any balance other than the recipient's. -/
theorem mint_preserves_other_balances (recipient : Address) (amount : Wad)
    (s : ContractState TokenStorage) (howner : s.context.caller == s.storage.owner)
    (hsupply : s.storage.totalSupply.n + amount.n < 2 ^ 256)
    (hadd : (s.storage.balances recipient).n + amount.n < 2 ^ 256)
    (a : Address) (ha : a ≠ recipient) :
    ∃ s', runS (mint recipient amount : TokenM Unit) s =
        .ok ((), s', [TokenEvent.Mint (Wad.Fixed.retag amount)]) ∧
      s'.storage.balances a = s.storage.balances a := by
  obtain ⟨s', h, _, _, hother⟩ := runMintOk recipient amount s howner hsupply hadd
  exact ⟨s', h, hother a ha⟩

/-- `mint` rejects a non-owner caller with `NotOwner`, before ever touching `totalSupply`/any
balance. -/
theorem mint_reverts_for_non_owner (recipient : Address) (amount : Wad)
    (s : ContractState TokenStorage) (h : ¬ s.context.caller == s.storage.owner) :
    runS (mint recipient amount : TokenM Unit) s = .error TokenError.NotOwner :=
  runMintErrNotOwner recipient amount s h

/-- `mint` (called by the owner) reverts with `Overflow` if bumping `totalSupply` by `amount`
would overflow. -/
theorem mint_reverts_on_overflow (recipient : Address) (amount : Wad)
    (s : ContractState TokenStorage) (howner : s.context.caller == s.storage.owner)
    (h : s.storage.totalSupply.n + amount.n ≥ 2 ^ 256) :
    runS (mint recipient amount : TokenM Unit) s = .error TokenError.Overflow :=
  runMintErrOverflow recipient amount s howner h
