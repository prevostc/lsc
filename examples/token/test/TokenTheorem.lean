import TokenProofs
import Lsc.Lib.Interfaces.IERC20

/-!
Required `Token` theorems (`docs/reference/TOKEN.md`). -/

open Lsc Token Lsc.Interfaces

/-- **Property:** `balanceOf` returns the stored balance for any address. -/
theorem balanceOf_returns_stored_balance (who : Address) (s : ContractState TokenStorage) :
    Except.map (fun x => Val.wadOf x.1) (runS (Token.balanceOf who) s) =
      .ok (s.storage.balances who) :=
  runBalanceOfOk who s

theorem balanceOf_zero_by_default (who : Address) (owner : Address) (totalSupply : Amount) :
    Except.map (fun x => Val.wadOf x.1)
        (runS (Token.balanceOf who) (mkState owner totalSupply zeroBalances)) =
      .ok (Wad.mkNat 0) :=
  runBalanceOfOk who (mkState owner totalSupply zeroBalances)

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

theorem transfer_credits_recipient (recipient : Address) (amount : Wad)
    (s : ContractState TokenStorage) (hne : s.context.caller ≠ recipient)
    (hsub : amount.n ≤ (s.storage.balances s.context.caller).n)
    (hadd : (s.storage.balances recipient).n + amount.n < 2 ^ 256) :
    ∃ s', runS (transfer recipient amount : TokenM Unit) s =
        .ok ((), s', [TokenEvent.Transfer (Wad.Fixed.retag amount)]) ∧
      s'.storage.balances recipient = Wad.mkNat ((s.storage.balances recipient).n + amount.n) := by
  obtain ⟨s', h, hbal⟩ := runTransferOk recipient amount s hsub hadd
  exact ⟨s', h, by simpa [hne, Ne.symm hne] using hbal recipient⟩

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

theorem transfer_self_transfer_is_noop (amount : Wad) (s : ContractState TokenStorage)
    (hsub : amount.n ≤ (s.storage.balances s.context.caller).n)
    (hadd : (s.storage.balances s.context.caller).n + amount.n < 2 ^ 256) :
    ∃ s', runS (transfer s.context.caller amount : TokenM Unit) s =
        .ok ((), s', [TokenEvent.Transfer (Wad.Fixed.retag amount)]) ∧
      s'.storage.balances s.context.caller = s.storage.balances s.context.caller := by
  obtain ⟨s', h, hbal⟩ := runTransferOk s.context.caller amount s hsub hadd
  exact ⟨s', h, by simpa using hbal s.context.caller⟩

theorem transfer_reverts_on_insufficient_balance (recipient : Address) (amount : Wad)
    (s : ContractState TokenStorage) (h : (s.storage.balances s.context.caller).n < amount.n) :
    runS (transfer recipient amount : TokenM Unit) s = .error TokenError.Underflow :=
  runTransferErr recipient amount s h

theorem mint_increases_total_supply (recipient : Address) (amount : Wad)
    (s : ContractState TokenStorage) (howner : s.context.caller == s.storage.owner)
    (hsupply : s.storage.totalSupply.n + amount.n < 2 ^ 256)
    (hadd : (s.storage.balances recipient).n + amount.n < 2 ^ 256) :
    ∃ s', runS (mint recipient amount : TokenM Unit) s =
        .ok ((), s', [TokenEvent.Mint (Wad.Fixed.retag amount)]) ∧
      s'.storage.totalSupply.n = s.storage.totalSupply.n + amount.n := by
  obtain ⟨s', h, hsupply', _, _⟩ := runMintOk recipient amount s howner hsupply hadd
  exact ⟨s', h, hsupply'⟩

theorem mint_increases_recipient_balance (recipient : Address) (amount : Wad)
    (s : ContractState TokenStorage) (howner : s.context.caller == s.storage.owner)
    (hsupply : s.storage.totalSupply.n + amount.n < 2 ^ 256)
    (hadd : (s.storage.balances recipient).n + amount.n < 2 ^ 256) :
    ∃ s', runS (mint recipient amount : TokenM Unit) s =
        .ok ((), s', [TokenEvent.Mint (Wad.Fixed.retag amount)]) ∧
      s'.storage.balances recipient = Wad.mkNat ((s.storage.balances recipient).n + amount.n) := by
  obtain ⟨s', h, _, hbal, _⟩ := runMintOk recipient amount s howner hsupply hadd
  exact ⟨s', h, hbal⟩

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

theorem mint_reverts_for_non_owner (recipient : Address) (amount : Wad)
    (s : ContractState TokenStorage) (h : ¬ s.context.caller == s.storage.owner) :
    runS (mint recipient amount : TokenM Unit) s = .error TokenError.NotOwner :=
  runMintErrNotOwner recipient amount s h

theorem mint_reverts_on_overflow (recipient : Address) (amount : Wad)
    (s : ContractState TokenStorage) (howner : s.context.caller == s.storage.owner)
    (h : s.storage.totalSupply.n + amount.n ≥ 2 ^ 256) :
    runS (mint recipient amount : TokenM Unit) s = .error TokenError.Overflow :=
  runMintErrOverflow recipient amount s howner h

/-! ## Cross-contract interface witness

Escrow's Tier-B theorems assume `[HonestERC20 T]` for an abstract callee `T`. That is an
*assumption*, not a fact about every ERC20. This section shows the assumption is at least
*consistent*: our reference `Token` really does provide a witness.

Reading guide:
* `HonestERC20 TokenStorage` is a **Type** (transfer hook + balance read + conservation proof),
  not a yes/no proposition — so we cannot state `theorem … : HonestERC20 TokenStorage`.
* `Nonempty A` means "there exists at least one value of type `A`".
* `token_honest_erc20` therefore reads as: "some honest-ERC20 package for `TokenStorage` exists."
* The concrete package is `TokenProofs.tokenHonestERC20`; `⟨…⟩` wraps it as the existence proof. -/

/-- At least one [`HonestERC20`](../../../Lsc/Lib/Interfaces/IERC20.lean) witness for `TokenStorage`
exists — Escrow's `[HonestERC20 T]` assumption is satisfiable, not vacuous. See ADR 0009. -/
theorem token_honest_erc20 : Nonempty (HonestERC20 TokenStorage) :=
  -- "Here is one:" the bundled witness built in `TokenProofs`.
  ⟨tokenHonestERC20⟩
