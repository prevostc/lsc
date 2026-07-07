import Token

/-!
Proof machinery backing `TokenTheorem.lean` (the required `Token` theorems,
`docs/reference/TOKEN.md`) — kept in its own file so that file can be read as a clean
statement-of-facts document, same split as `examples/interest/test/InterestProofs.lean`/
`InterestTheorems.lean` and `examples/escrow/test/EscrowProofs.lean`/`EscrowTheorem.lean`.

`transfer`/`mint` each chain a checked `Wad` op (`-?`/`+?`) with a mapping read/write — the exact
same shape `EscrowProofs.runTransferOk` already fully characterizes for `Token.transferTyped`, so
this file just repeats that recipe directly against `Token.transfer`/`Token.mint` themselves
(the real, unqualified public tx surface `TOKEN.md` documents), universally quantified over every
state/address/amount rather than fixed to `native_decide` witnesses. Unlike `Escrow`'s use of
`Token.transferTyped`, `amount` here is already plain `Wad` (`transfer`/`mint`'s real compiled
signature, `#check`ed at the bottom of `Token.lean`) — no `Token.Amount`-to-`Wad` retagging is
needed for it; only `totalSupply` (stored as `Token.Amount`) still needs `Wad.Fixed.retag` to feed
the generic `Wad.addChecked`. -/

open Lsc Token

/-! ## Generic state builder -/

def mkState (owner : Address) (totalSupply : Amount) (balances : Address → Wad) :
    ContractState TokenStorage :=
  { storage := { owner := owner, totalSupply := totalSupply, balances := balances }
    context := { caller := 0, callvalue := 0, timestamp := 0, origin := 0 }
    locked := false }

def zeroBalances : Address → Wad := fun _ => Wad.mkNat 0

/-! ## `WadMap` update lemmas (`balances`) -/

theorem setMapField_balances_at (k : Address) (v : Wad) (s : TokenStorage) :
    (TokenStorage.setMapField "balances" k v s).balances k = v := by
  simp [TokenStorage.setMapField]

theorem setMapField_balances_ne (a k : Address) (v : Wad) (s : TokenStorage) (h : a ≠ k) :
    (TokenStorage.setMapField "balances" k v s).balances a = s.balances a := by
  simp [TokenStorage.setMapField, h]

/-! ## `balanceOf` -/

/-- `balanceOf who` always succeeds and returns exactly the stored balance — it never reverts
(`Wad.WadMap`'s total-function model already gives every address *some* balance, `0` if never
written) and never touches storage. -/
theorem runBalanceOfOk (who : Address) (s : ContractState TokenStorage) :
    Except.map (fun x => Val.wadOf x.1) (runS (Token.balanceOf who) s) =
      .ok (s.storage.balances who) := by
  simp [runS, Token.balanceOf, balanceOfImpl, Stmt.evalView, Stmt.evalWith,
    TokenStorage.getMapField, Except.map]

/-! ## `transfer` — full characterization -/

/-- The exact outcome of `transfer recipient amount` (called by `s.context.caller`), for **every**
address `a` at once — same pointwise-law shape as `EscrowProofs.runTransferOk`, and for the same
reason (`transfer`'s two `mapSet`s run *sequentially*, so a self-transfer's checked-subtract and
checked-add cancel out exactly — see that theorem's docstring). -/
theorem runTransferOk (recipient : Address) (amount : Wad) (s : ContractState TokenStorage)
    (hsub : amount.n ≤ (s.storage.balances s.context.caller).n)
    (hadd : (s.storage.balances recipient).n + amount.n < 2 ^ 256) :
    ∃ s' : ContractState TokenStorage,
      runS (transfer recipient amount : TokenM Unit) s =
        .ok ((), s', [TokenEvent.Transfer (Wad.Fixed.retag amount)]) ∧
      ∀ a : Address,
        s'.storage.balances a =
          if a == s.context.caller && a == recipient then
            s.storage.balances a
          else if a == s.context.caller then
            Wad.mkNat ((s.storage.balances s.context.caller).n - amount.n)
          else if a == recipient then
            Wad.mkNat ((s.storage.balances recipient).n + amount.n)
          else
            s.storage.balances a := by
  have hltS := (s.storage.balances s.context.caller).raw.isLt
  have hsubOk : Wad.subChecked (s.storage.balances s.context.caller) amount =
      .ok (Wad.mkNat ((s.storage.balances s.context.caller).n - amount.n)) := by
    apply Wad.subChecked_eq_ok_of
    unfold Wad.Fixed.n at *; omega
  by_cases hsr : s.context.caller = recipient
  · subst hsr
    have haddOk : Wad.addChecked
        (Wad.mkNat ((s.storage.balances s.context.caller).n - amount.n)) amount =
        .ok (Wad.mkNat (s.storage.balances s.context.caller).n) := by
      apply Wad.addChecked_eq_ok_of
      · unfold Wad.Fixed.n at *
        simp only [Wad.mkNat, BitVec.toNat_ofNat]
        omega
      · exact hltS
    simp only [Wad.mkNat] at haddOk
    set s1 : TokenStorage :=
      TokenStorage.setMapField "balances" s.context.caller
        (Wad.mkNat (s.storage.balances s.context.caller).n)
        (TokenStorage.setMapField "balances" s.context.caller
          (Wad.mkNat ((s.storage.balances s.context.caller).n - amount.n)) s.storage)
      with hts1
    refine ⟨{ s with storage := s1 }, ?_, ?_⟩
    · rw [hts1]
      simp [transfer, transferImpl, Stmt.toContractM, runS, Stmt.evalWith,
        hsubOk, haddOk, TokenStorage.getMapField, TokenStorage.setMapField,
        Wad.Fixed.retag, Wad.mkNat, BitVec.ofNat_toNat, List.mapM, List.mapM.loop]
    · intro a
      rw [hts1]
      by_cases ha : a = s.context.caller
      · subst ha; simp [TokenStorage.setMapField]
      · simp [ha, TokenStorage.setMapField]
  · have hne : s.context.caller ≠ recipient := hsr
    have haddOk : Wad.addChecked (s.storage.balances recipient) amount =
        .ok (Wad.mkNat ((s.storage.balances recipient).n + amount.n)) := by
      apply Wad.addChecked_eq_ok_of
      · rfl
      · exact hadd
    set s2 : TokenStorage :=
      TokenStorage.setMapField "balances" recipient
        (Wad.mkNat ((s.storage.balances recipient).n + amount.n))
        (TokenStorage.setMapField "balances" s.context.caller
          (Wad.mkNat ((s.storage.balances s.context.caller).n - amount.n)) s.storage)
      with hts2
    refine ⟨{ s with storage := s2 }, ?_, ?_⟩
    · rw [hts2]
      simp [transfer, transferImpl, Stmt.toContractM, runS, Stmt.evalWith,
        hsubOk, haddOk, TokenStorage.getMapField, TokenStorage.setMapField,
        Wad.Fixed.retag, Wad.mkNat, BitVec.ofNat_toNat, Ne.symm hne, List.mapM, List.mapM.loop]
    · intro a
      rw [hts2]
      by_cases ha1 : a = s.context.caller
      · subst ha1
        simp [TokenStorage.setMapField, hne]
      · by_cases ha2 : a = recipient
        · subst ha2
          simp [TokenStorage.setMapField, ha1]
        · simp [TokenStorage.setMapField, ha1, ha2]

/-- `transfer` reverts with `Underflow` whenever the caller's balance is below `amount` —
regardless of `recipient`/every other address's balance. -/
theorem runTransferErr (recipient : Address) (amount : Wad) (s : ContractState TokenStorage)
    (h : (s.storage.balances s.context.caller).n < amount.n) :
    runS (transfer recipient amount : TokenM Unit) s = .error TokenError.Underflow := by
  have hsubErr : Wad.subChecked (s.storage.balances s.context.caller) amount =
      .error .Underflow := by
    apply Wad.subChecked_eq_error_of
    unfold Wad.Fixed.n at *; omega
  simp [runS, transfer, transferImpl, Stmt.toContractM, Stmt.evalWith, hsubErr,
    TokenStorage.getMapField, List.mapM, List.mapM.loop, ContractM.revertArith,
    ContractErrors.arith]

/-! ## `mint` — full characterization -/

/-- The exact outcome of `mint recipient amount` (called by `s.context.caller`) when the caller is
the owner — bumps `totalSupply` and `recipient`'s balance by exactly `amount`, and (since `mint`
only ever writes `recipient`'s entry) leaves every other address's balance untouched. -/
theorem runMintOk (recipient : Address) (amount : Wad) (s : ContractState TokenStorage)
    (howner : s.context.caller == s.storage.owner)
    (hsupply : s.storage.totalSupply.n + amount.n < 2 ^ 256)
    (hadd : (s.storage.balances recipient).n + amount.n < 2 ^ 256) :
    ∃ s' : ContractState TokenStorage,
      runS (mint recipient amount : TokenM Unit) s =
        .ok ((), s', [TokenEvent.Mint (Wad.Fixed.retag amount)]) ∧
      s'.storage.totalSupply.n = s.storage.totalSupply.n + amount.n ∧
      s'.storage.balances recipient = Wad.mkNat ((s.storage.balances recipient).n + amount.n) ∧
      ∀ a : Address, a ≠ recipient → s'.storage.balances a = s.storage.balances a := by
  have hsupplyOk : Wad.addChecked (⟨s.storage.totalSupply.raw⟩ : Wad.Wad) amount =
      .ok (Wad.mkNat (s.storage.totalSupply.n + amount.n)) := by
    apply Wad.addChecked_eq_ok_of
    · rfl
    · exact hsupply
  have hbalOk : Wad.addChecked (s.storage.balances recipient) amount =
      .ok (Wad.mkNat ((s.storage.balances recipient).n + amount.n)) := by
    apply Wad.addChecked_eq_ok_of
    · rfl
    · exact hadd
  simp only [Wad.mkNat] at hsupplyOk hbalOk
  set s' : TokenStorage :=
    { TokenStorage.setMapField "balances" recipient
        (Wad.mkNat ((s.storage.balances recipient).n + amount.n)) s.storage with
      totalSupply := Wad.mkNat (s.storage.totalSupply.n + amount.n) }
    with hs'
  refine ⟨{ s with storage := s' }, ?_, ?_, ?_, ?_⟩
  · rw [hs']
    simp [mint, mintImpl, Stmt.toContractM, runS, Stmt.evalWith, howner, hsupplyOk, hbalOk,
      TokenStorage.getField, TokenStorage.setField, TokenStorage.getMapField,
      TokenStorage.setMapField, Wad.Fixed.retag, Wad.mkNat, BitVec.ofNat_toNat, List.mapM,
      List.mapM.loop]
  · rw [hs']; unfold Wad.Fixed.n at *; simp only [Wad.mkNat, BitVec.toNat_ofNat]; omega
  · rw [hs']; simp [TokenStorage.setMapField]
  · intro a ha
    rw [hs']
    simp [TokenStorage.setMapField, ha]

/-- `mint` reverts with `NotOwner` when the caller isn't `s.storage.owner`, before ever touching
`totalSupply`/any balance. -/
theorem runMintErrNotOwner (recipient : Address) (amount : Wad) (s : ContractState TokenStorage)
    (h : ¬ s.context.caller == s.storage.owner) :
    runS (mint recipient amount : TokenM Unit) s = .error TokenError.NotOwner := by
  simp [runS, mint, mintImpl, Stmt.toContractM, Stmt.evalWith, h]

/-- `mint` (called by the owner) reverts with `Overflow` if bumping `totalSupply` by `amount`
would overflow — regardless of `recipient`'s own balance. -/
theorem runMintErrOverflow (recipient : Address) (amount : Wad) (s : ContractState TokenStorage)
    (howner : s.context.caller == s.storage.owner)
    (h : s.storage.totalSupply.n + amount.n ≥ 2 ^ 256) :
    runS (mint recipient amount : TokenM Unit) s = .error TokenError.Overflow := by
  have hsupplyErr : Wad.addChecked (⟨s.storage.totalSupply.raw⟩ : Wad.Wad) amount =
      .error .Overflow := by
    apply Wad.addChecked_eq_error_of
    unfold Wad.Fixed.n at *; omega
  simp [runS, mint, mintImpl, Stmt.toContractM, Stmt.evalWith, howner, hsupplyErr,
    Wad.Fixed.retag, TokenStorage.getField, List.mapM, List.mapM.loop, ContractM.revertArith,
    ContractErrors.arith]
