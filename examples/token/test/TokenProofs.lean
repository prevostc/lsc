import Token

import Lsc.Lib.Interfaces.IERC20
import Aesop

/-!
Proof machinery backing `TokenTheorem.lean` (`docs/reference/TOKEN.md`). -/

open Lsc Token Lsc.Interfaces

def balanceAt (s : TokenStorage) (a : Address) : Wad :=
  Wad.Fixed.retag (s.balances.get a)

theorem balanceAt_def (s : TokenStorage) (a : Address) :
    balanceAt s a = { raw := (s.balances.get a).raw } := by
  unfold balanceAt
  simp [Wad.Fixed.retag]

theorem balanceGet_ret (s : TokenStorage) (a : Address) :
    (Wad.Fixed.retag (s.balances.get a) : Wad) = { raw := (s.balances.get a).raw } := by
  simp [Wad.Fixed.retag]

theorem balanceAt_dot (s : TokenStorage) (a : Address) :
    (s.balances.get a).retag = balanceAt s a := by
  unfold balanceAt
  rfl

@[simp]
theorem TokenEvent_mint_wad (amount : Wad) :
    TokenEvent.Mint (Wad.Fixed.retag amount) = TokenEvent.Mint { raw := amount.raw } := by
  simp [Wad.Fixed.retag]

@[simp]
theorem TokenEvent_transfer_wad (amount : Wad) :
    TokenEvent.Transfer (Wad.Fixed.retag amount) = TokenEvent.Transfer { raw := amount.raw } := by
  simp [Wad.Fixed.retag]

def mkState (owner : Address) (totalSupply : Amount) (balances : Mapping Address Amount) :
    ContractState TokenStorage :=
  { storage := { owner := owner, totalSupply := totalSupply, balances := balances }
    context := { caller := 0, callvalue := 0, timestamp := 0, origin := 0 }
    locked := false }

def zeroBalances : Mapping Address Amount := Mapping.empty

theorem setMapField_balances_body (k : Address) (v : Wad) (s : TokenStorage) :
    TokenStorage.setMapField "balances" k v s =
      { s with balances := s.balances.set k (Wad.Fixed.retag v) } := rfl

theorem setMapField_balances_at (k : Address) (v : Wad) (s : TokenStorage) :
    balanceAt (TokenStorage.setMapField "balances" k v s) k = v := by
  unfold balanceAt TokenStorage.setMapField
  simp [Mapping.get_set_same, Wad.Fixed.retag]

theorem setMapField_balances_ne (a k : Address) (v : Wad) (s : TokenStorage) (h : a ≠ k) :
    balanceAt (TokenStorage.setMapField "balances" k v s) a = balanceAt s a := by
  unfold balanceAt TokenStorage.setMapField
  simp [Mapping.get_set_different, Ne.symm h, Wad.Fixed.retag]

@[simp]
theorem getMapField_balances (a : Address) (s : TokenStorage) :
    TokenStorage.getMapField "balances" a s = some (balanceAt s a) := by
  simp [balanceAt, TokenStorage.getMapField, Wad.Fixed.retag]

theorem balanceAt_setMapField (k : Address) (v : Wad) (s : TokenStorage) (a : Address) :
    balanceAt (TokenStorage.setMapField "balances" k v s) a =
      if a = k then v else balanceAt s a := by
  split_ifs with h
  · subst h; exact setMapField_balances_at a v s
  · exact setMapField_balances_ne a k v s h

theorem balanceAt_setMapField2 (k2 : Address) (v2 : Wad) (k1 : Address) (v1 : Wad)
    (s : TokenStorage) (a : Address) :
    balanceAt (TokenStorage.setMapField "balances" k2 v2
      (TokenStorage.setMapField "balances" k1 v1 s)) a =
      if a = k2 then v2 else if a = k1 then v1 else balanceAt s a := by
  rw [balanceAt_setMapField]
  by_cases h2 : a = k2
  · subst h2; simp
  · by_cases h1 : a = k1
    · subst h1; simp [h2, balanceAt_setMapField, setMapField_balances_at]
    · simp [h2, balanceAt_setMapField, h1, setMapField_balances_ne]

theorem runBalanceOfOk (who : Address) (s : ContractState TokenStorage) :
    Except.map (fun x => Val.wadOf x.1) (runS (Token.balanceOf who) s) =
      .ok (balanceAt s.storage who) := by
  simp [runS, Token.balanceOf, balanceOfImpl, Stmt.evalView, Stmt.evalWith,
    Wad.resolveMapKey, getMapField_balances, Except.map]

theorem runTransferOk (recipient : Address) (amount : Wad) (s : ContractState TokenStorage)
    (hsub : amount.n ≤ (balanceAt s.storage s.context.caller).n)
    (hadd : (balanceAt s.storage recipient).n + amount.n < 2 ^ 256) :
    ∃ s' : ContractState TokenStorage,
      runS (transfer recipient amount : TokenM Unit) s =
        .ok ((), s', [TokenEvent.Transfer (Wad.Fixed.retag amount)]) ∧
      ∀ a : Address,
        balanceAt s'.storage a =
          if a == s.context.caller && a == recipient then
            balanceAt s.storage a
          else if a == s.context.caller then
            Wad.mkNat ((balanceAt s.storage s.context.caller).n - amount.n)
          else if a == recipient then
            Wad.mkNat ((balanceAt s.storage recipient).n + amount.n)
          else
            balanceAt s.storage a := by
  have hltS := (balanceAt s.storage s.context.caller).raw.isLt
  have hsubOk : Wad.subChecked (balanceAt s.storage s.context.caller) amount =
      .ok (Wad.mkNat ((balanceAt s.storage s.context.caller).n - amount.n)) := by
    apply Wad.subChecked_eq_ok_of
    unfold Wad.Fixed.n at *; omega
  have hsubOk' :
      Wad.subChecked (s.storage.balances.get s.context.caller).retag amount =
        .ok (Wad.mkNat ((balanceAt s.storage s.context.caller).n - amount.n)) := by
    simpa [balanceAt_dot, balanceAt_def] using hsubOk
  simp only [Wad.mkNat] at hsubOk'
  by_cases hsr : s.context.caller = recipient
  · subst hsr
    have haddOk : Wad.addChecked
        (Wad.mkNat ((balanceAt s.storage s.context.caller).n - amount.n)) amount =
        .ok (Wad.mkNat (balanceAt s.storage s.context.caller).n) := by
      apply Wad.addChecked_eq_ok_of
      · unfold Wad.Fixed.n at *
        simp only [Wad.mkNat, BitVec.toNat_ofNat]
        omega
      · exact hltS
    simp only [Wad.mkNat] at haddOk
    set s1 : TokenStorage :=
      TokenStorage.setMapField "balances" s.context.caller
        (Wad.mkNat (balanceAt s.storage s.context.caller).n)
        (TokenStorage.setMapField "balances" s.context.caller
          (Wad.mkNat ((balanceAt s.storage s.context.caller).n - amount.n)) s.storage)
      with hts1
    refine ⟨{ s with storage := s1 }, ?_, ?_⟩
    · rw [hts1]
      aesop (add simp [
      Wad.resolveMapKey, ContractM.caller,
        transfer, transferImpl, Stmt.toContractM, runS, Stmt.evalWith, Stmt.eval_def,
        hsubOk', haddOk, TokenStorage.getMapField, TokenStorage.setMapField,
        getMapField_balances, balanceAt_dot, balanceAt_def, Wad.Fixed.retag, Wad.mkNat,
        BitVec.ofNat_toNat, Mapping.get_set_same, setMapField_balances_body,
        TokenEvent_transfer_wad, List.mapM, List.mapM.loop, Stmt.evalWith_mapSet,
        TokenStorageDsl_getMapField, TokenStorageDsl_setMapField])
    · intro a
      rw [hts1, balanceAt_setMapField2]
      by_cases ha : a = s.context.caller
      · subst ha
        simp [Wad.mkNat]
      · simp [ha, Wad.mkNat]
  · have hne : s.context.caller ≠ recipient := hsr
    have haddOk : Wad.addChecked (balanceAt s.storage recipient) amount =
        .ok (Wad.mkNat ((balanceAt s.storage recipient).n + amount.n)) := by
      apply Wad.addChecked_eq_ok_of
      · rfl
      · exact hadd
    have haddOk' :
        Wad.addChecked (s.storage.balances.get recipient).retag amount =
          .ok (Wad.mkNat ((balanceAt s.storage recipient).n + amount.n)) := by
      simpa [balanceAt_dot, balanceAt_def] using haddOk
    simp only [Wad.mkNat] at haddOk'
    set s2 : TokenStorage :=
      TokenStorage.setMapField "balances" recipient
        (Wad.mkNat ((balanceAt s.storage recipient).n + amount.n))
        (TokenStorage.setMapField "balances" s.context.caller
          (Wad.mkNat ((balanceAt s.storage s.context.caller).n - amount.n)) s.storage)
      with hts2
    refine ⟨{ s with storage := s2 }, ?_, ?_⟩
    · rw [hts2]
      aesop (add simp [
      Wad.resolveMapKey, ContractM.caller,
        transfer, transferImpl, Stmt.toContractM, runS, Stmt.evalWith, Stmt.eval_def,
        hsubOk', haddOk', TokenStorage.getMapField, TokenStorage.setMapField,
        getMapField_balances, balanceAt_dot, balanceAt_def, Wad.Fixed.retag, Wad.mkNat,
        BitVec.ofNat_toNat, Mapping.get_set_same, Mapping.get_set_different,
        setMapField_balances_body, TokenEvent_transfer_wad, List.mapM, List.mapM.loop,
        Stmt.evalWith_mapSet, TokenStorageDsl_getMapField, TokenStorageDsl_setMapField])
    · intro a
      rw [hts2, balanceAt_setMapField2]
      by_cases ha1 : a = s.context.caller
      · subst ha1
        simp [hne, Wad.mkNat]
      · by_cases ha2 : a = recipient
        · subst ha2
          simp [ha1, Wad.mkNat]
        · simp [ha1, ha2, Wad.mkNat]

theorem runTransferErr (recipient : Address) (amount : Wad) (s : ContractState TokenStorage)
    (h : (balanceAt s.storage s.context.caller).n < amount.n) :
    runS (transfer recipient amount : TokenM Unit) s = .error TokenError.Underflow := by
  have hsubErr : Wad.subChecked (balanceAt s.storage s.context.caller) amount =
      .error .Underflow := by
    apply Wad.subChecked_eq_error_of
    unfold Wad.Fixed.n at *; omega
  have hsubErr' :
      Wad.subChecked (s.storage.balances.get s.context.caller).retag amount =
        .error .Underflow := by
    simpa [balanceAt_dot, balanceAt_def] using hsubErr
  aesop (add simp [
      Wad.resolveMapKey, ContractM.caller,
    runS, transfer, transferImpl, Stmt.toContractM, Stmt.evalWith, Stmt.eval_def, hsubErr',
    TokenStorage.getMapField, getMapField_balances, balanceAt_dot, balanceAt_def, Wad.eval,
    Stmt.evalWith_mapSet, ContractM.revertArith, runS_revertArith, ContractErrors.arith,
    TokenStorageError_arith_Underflow, List.mapM, List.mapM.loop,
    TokenStorageDsl_getMapField])

theorem runMintOk (recipient : Address) (amount : Wad) (s : ContractState TokenStorage)
    (howner : s.context.caller == s.storage.owner)
    (hsupply : s.storage.totalSupply.n + amount.n < 2 ^ 256)
    (hadd : (balanceAt s.storage recipient).n + amount.n < 2 ^ 256) :
    ∃ s' : ContractState TokenStorage,
      runS (mint recipient amount : TokenM Unit) s =
        .ok ((), s', [TokenEvent.Mint (Wad.Fixed.retag amount)]) ∧
      s'.storage.totalSupply.n = s.storage.totalSupply.n + amount.n ∧
      balanceAt s'.storage recipient = Wad.mkNat ((balanceAt s.storage recipient).n + amount.n) ∧
      ∀ a : Address, a ≠ recipient → balanceAt s'.storage a = balanceAt s.storage a := by
  have hsupplyOk : Wad.addChecked (⟨s.storage.totalSupply.raw⟩ : Wad.Wad) amount =
      .ok (Wad.mkNat (s.storage.totalSupply.n + amount.n)) := by
    apply Wad.addChecked_eq_ok_of
    · rfl
    · exact hsupply
  have hbalOk : Wad.addChecked (balanceAt s.storage recipient) amount =
      .ok (Wad.mkNat ((balanceAt s.storage recipient).n + amount.n)) := by
    apply Wad.addChecked_eq_ok_of
    · rfl
    · exact hadd
  have hbalOk' :
      Wad.addChecked (s.storage.balances.get recipient).retag amount =
        .ok (Wad.mkNat ((balanceAt s.storage recipient).n + amount.n)) := by
    simpa [balanceAt_dot, balanceAt_def] using hbalOk
  simp only [Wad.mkNat] at hsupplyOk hbalOk'
  set s' : TokenStorage :=
    { TokenStorage.setMapField "balances" recipient
        (Wad.mkNat ((balanceAt s.storage recipient).n + amount.n)) s.storage with
      totalSupply := Wad.mkNat (s.storage.totalSupply.n + amount.n) }
    with hs'
  refine ⟨{ s with storage := s' }, ?_, ?_, ?_, ?_⟩
  · rw [hs']
    aesop (add simp [
      Wad.resolveMapKey, ContractM.caller,
      mint, mintImpl, Stmt.toContractM, runS, Stmt.evalWith, Stmt.eval_def, howner, hsupplyOk,
      hbalOk', balanceAt_dot, balanceAt_def, getMapField_balances, TokenStorage.getField,
      TokenStorage.setField, TokenStorage.setMapField, balanceAt, Wad.Fixed.retag, Wad.mkNat,
      BitVec.ofNat_toNat, TokenEvent_mint_wad, List.mapM, List.mapM.loop, Stmt.evalWith_mapSet,
      TokenStorageDsl_getMapField, TokenStorageDsl_setMapField])
  · rw [hs']; unfold Wad.Fixed.n at *; simp only [Wad.mkNat, BitVec.toNat_ofNat]; omega
  · rw [hs']
    unfold balanceAt TokenStorage.setMapField
    simp [Mapping.get_set_same, Wad.Fixed.retag, Wad.mkNat]
  · intro a ha
    rw [hs']
    unfold balanceAt TokenStorage.setMapField
    simp [Mapping.get_set_different, Ne.symm ha, Wad.Fixed.retag]

theorem runMintErrNotOwner (recipient : Address) (amount : Wad) (s : ContractState TokenStorage)
    (h : ¬ s.context.caller == s.storage.owner) :
    runS (mint recipient amount : TokenM Unit) s = .error TokenError.NotOwner := by
  simp [runS, mint, mintImpl, Stmt.toContractM, Stmt.evalWith, h]

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

/-- Restate `runTransferOk` in the shape required by `HonestERC20.transfer_conserves`
(explicit `sender`, existential event log). -/
theorem honestTransferConserves (recipient sender : Address) (amount : Wad)
    (ts : ContractState TokenStorage)
    (hsub : amount.n ≤ (balanceAt ts.storage sender).n)
    (hadd : (balanceAt ts.storage recipient).n + amount.n < 2 ^ 256)
    (hcaller : ts.context.caller = sender) :
    ∃ ts' log,
      runS (transfer recipient amount : TokenM Unit) ts = .ok ((), ts', log) ∧
      ∀ a : Address,
        balanceAt ts'.storage a =
          if a == sender && a == recipient then
            balanceAt ts.storage a
          else if a == sender then
            Wad.mkNat ((balanceAt ts.storage sender).n - amount.n)
          else if a == recipient then
            Wad.mkNat ((balanceAt ts.storage recipient).n + amount.n)
          else
            balanceAt ts.storage a := by
  have hsub' : amount.n ≤ (balanceAt ts.storage ts.context.caller).n := by simpa [hcaller] using hsub
  obtain ⟨ts', hrun, hbal⟩ := runTransferOk recipient amount ts hsub' hadd
  refine ⟨ts', [TokenEvent.Transfer (Wad.Fixed.retag amount)], hrun, ?_⟩
  intro a
  simpa [hcaller] using hbal a

/-! ## Allowances (`approve`/`transferFrom`)

Mirrors the `balanceAt`/`setMapField_balances_*`/`getMapField_balances` machinery above one
level deeper, for the pair-keyed `allowances : Mapping (Address × Address) Amount` field
(`TokenStorage.allowances`'s docstring) — the nested-mapping (`.mapping2`) counterpart of
`balanceAt`, backed by `getMapField2`/`setMapField2` instead of `getMapField`/`setMapField`. -/

def allowanceAt (s : TokenStorage) (owner spender : Address) : Wad :=
  Wad.Fixed.retag (s.allowances.get (owner, spender))

theorem allowanceAt_def (s : TokenStorage) (owner spender : Address) :
    allowanceAt s owner spender = { raw := (s.allowances.get (owner, spender)).raw } := by
  unfold allowanceAt
  simp [Wad.Fixed.retag]

theorem allowanceAt_dot (s : TokenStorage) (owner spender : Address) :
    (s.allowances.get (owner, spender)).retag = allowanceAt s owner spender := by
  unfold allowanceAt
  rfl

@[simp]
theorem TokenEvent_approval_wad (amount : Wad) :
    TokenEvent.Approval (Wad.Fixed.retag amount) = TokenEvent.Approval { raw := amount.raw } := by
  simp [Wad.Fixed.retag]

theorem setMapField2_allowances_body (k1 k2 : Address) (v : Wad) (s : TokenStorage) :
    TokenStorage.setMapField2 "allowances" k1 k2 v s =
      { s with allowances := s.allowances.set (k1, k2) (Wad.Fixed.retag v) } := rfl

theorem setMapField2_allowances_at (k1 k2 : Address) (v : Wad) (s : TokenStorage) :
    allowanceAt (TokenStorage.setMapField2 "allowances" k1 k2 v s) k1 k2 = v := by
  unfold allowanceAt TokenStorage.setMapField2
  simp [Mapping.get_set_same, Wad.Fixed.retag]

theorem setMapField2_allowances_ne (k1 k2 a1 a2 : Address) (v : Wad) (s : TokenStorage)
    (h : (a1, a2) ≠ (k1, k2)) :
    allowanceAt (TokenStorage.setMapField2 "allowances" k1 k2 v s) a1 a2 = allowanceAt s a1 a2 := by
  unfold allowanceAt TokenStorage.setMapField2
  simp [Ne.symm h, Wad.Fixed.retag]

@[simp]
theorem getMapField2_allowances (a1 a2 : Address) (s : TokenStorage) :
    TokenStorage.getMapField2 "allowances" a1 a2 s = some (allowanceAt s a1 a2) := by
  simp [allowanceAt, TokenStorage.getMapField2, Wad.Fixed.retag]

/-- `setMapField2 "allowances"` never touches `balances` — the two `Mapping` storage fields are
independent struct fields. -/
theorem balanceAt_setMapField2_allowances (k1 k2 : Address) (v : Wad) (s : TokenStorage) (a : Address) :
    balanceAt (TokenStorage.setMapField2 "allowances" k1 k2 v s) a = balanceAt s a := by
  unfold balanceAt TokenStorage.setMapField2
  rfl

/-- `setMapField "balances"` never touches `allowances` — the converse of
`balanceAt_setMapField2_allowances`. -/
theorem allowanceAt_setMapField_balances (k : Address) (v : Wad) (s : TokenStorage)
    (a1 a2 : Address) :
    allowanceAt (TokenStorage.setMapField "balances" k v s) a1 a2 = allowanceAt s a1 a2 := by
  unfold allowanceAt TokenStorage.setMapField
  rfl

theorem runApproveOk (spender : Address) (amount : Wad) (s : ContractState TokenStorage) :
    ∃ s' : ContractState TokenStorage,
      runS (approve spender amount : TokenM Unit) s =
        .ok ((), s', [TokenEvent.Approval (Wad.Fixed.retag amount)]) ∧
      allowanceAt s'.storage s.context.caller spender = amount ∧
      (∀ a1 a2 : Address, (a1, a2) ≠ (s.context.caller, spender) →
        allowanceAt s'.storage a1 a2 = allowanceAt s.storage a1 a2) ∧
      (∀ a : Address, balanceAt s'.storage a = balanceAt s.storage a) := by
  set s' : TokenStorage := TokenStorage.setMapField2 "allowances" s.context.caller spender amount s.storage
    with hs'
  refine ⟨{ s with storage := s' }, ?_, ?_, ?_, ?_⟩
  · rw [hs']
    aesop (add simp [
      Wad.resolveMapKey, ContractM.caller,
      approve, approveImpl, Stmt.toContractM, runS, Stmt.evalWith, Stmt.eval_def,
      Wad.Fixed.retag, List.mapM, List.mapM.loop, Stmt.evalWith_mapSet2,
      TokenStorageDsl_setMapField2])
  · rw [hs']; simp [setMapField2_allowances_at]
  · intro a1 a2 h
    rw [hs']
    exact setMapField2_allowances_ne s.context.caller spender a1 a2 amount s.storage h
  · intro a
    rw [hs']
    exact balanceAt_setMapField2_allowances s.context.caller spender amount s.storage a

theorem approve_sets_allowance (spender : Address) (amount : Wad) (s : ContractState TokenStorage) :
    ∃ s' : ContractState TokenStorage,
      runS (approve spender amount : TokenM Unit) s =
        .ok ((), s', [TokenEvent.Approval (Wad.Fixed.retag amount)]) ∧
      allowanceAt s'.storage s.context.caller spender = amount :=
  let ⟨s', hrun, hallow, _, _⟩ := runApproveOk spender amount s
  ⟨s', hrun, hallow⟩

theorem transferFrom_requires_sufficient_allowance (sender recipient : Address) (amount : Wad)
    (s : ContractState TokenStorage)
    (h : (allowanceAt s.storage sender s.context.caller).n < amount.n) :
    runS (transferFrom sender recipient amount : TokenM Unit) s = .error TokenError.Underflow := by
  have hsubErr : Wad.subChecked (allowanceAt s.storage sender s.context.caller) amount =
      .error .Underflow := by
    apply Wad.subChecked_eq_error_of
    unfold Wad.Fixed.n at *; omega
  have hsubErr' :
      Wad.subChecked (s.storage.allowances.get (sender, s.context.caller)).retag amount =
        .error .Underflow := by
    simpa [allowanceAt_dot, allowanceAt_def] using hsubErr
  aesop (add simp [
      Wad.resolveMapKey, ContractM.caller,
    runS, transferFrom, transferFromImpl, Stmt.toContractM, Stmt.evalWith, Stmt.eval_def,
    hsubErr', TokenStorage.getMapField2, getMapField2_allowances, allowanceAt_dot,
    allowanceAt_def, Wad.eval, Stmt.evalWith_mapSet2, ContractM.revertArith,
    runS_revertArith, ContractErrors.arith, TokenStorageError_arith_Underflow,
    List.mapM, List.mapM.loop, TokenStorageDsl_getMapField2])

theorem runTransferFromOk (sender recipient : Address) (amount : Wad)
    (s : ContractState TokenStorage)
    (hallow : amount.n ≤ (allowanceAt s.storage sender s.context.caller).n)
    (hsub : amount.n ≤ (balanceAt s.storage sender).n)
    (hadd : (balanceAt s.storage recipient).n + amount.n < 2 ^ 256)
    (hne : sender ≠ recipient) :
    ∃ s' : ContractState TokenStorage,
      runS (transferFrom sender recipient amount : TokenM Unit) s =
        .ok ((), s', [TokenEvent.Transfer (Wad.Fixed.retag amount)]) ∧
      allowanceAt s'.storage sender s.context.caller =
        Wad.mkNat ((allowanceAt s.storage sender s.context.caller).n - amount.n) ∧
      balanceAt s'.storage sender = Wad.mkNat ((balanceAt s.storage sender).n - amount.n) ∧
      balanceAt s'.storage recipient = Wad.mkNat ((balanceAt s.storage recipient).n + amount.n) ∧
      (∀ a1 a2 : Address, (a1, a2) ≠ (sender, s.context.caller) →
        allowanceAt s'.storage a1 a2 = allowanceAt s.storage a1 a2) ∧
      (∀ a : Address, a ≠ sender → a ≠ recipient → balanceAt s'.storage a = balanceAt s.storage a) := by
  have hallowSubOk : Wad.subChecked (allowanceAt s.storage sender s.context.caller) amount =
      .ok (Wad.mkNat ((allowanceAt s.storage sender s.context.caller).n - amount.n)) := by
    apply Wad.subChecked_eq_ok_of
    unfold Wad.Fixed.n at *; omega
  have hallowSubOk' :
      Wad.subChecked (s.storage.allowances.get (sender, s.context.caller)).retag amount =
        .ok (Wad.mkNat ((allowanceAt s.storage sender s.context.caller).n - amount.n)) := by
    simpa [allowanceAt_dot, allowanceAt_def] using hallowSubOk
  have hbalSubOk : Wad.subChecked (balanceAt s.storage sender) amount =
      .ok (Wad.mkNat ((balanceAt s.storage sender).n - amount.n)) := by
    apply Wad.subChecked_eq_ok_of
    unfold Wad.Fixed.n at *; omega
  have hbalSubOk' :
      Wad.subChecked (s.storage.balances.get sender).retag amount =
        .ok (Wad.mkNat ((balanceAt s.storage sender).n - amount.n)) := by
    simpa [balanceAt_dot, balanceAt_def] using hbalSubOk
  simp only [Wad.mkNat] at hallowSubOk' hbalSubOk'
  set s1 : TokenStorage :=
    TokenStorage.setMapField "balances" recipient
      (Wad.mkNat ((balanceAt s.storage recipient).n + amount.n))
      (TokenStorage.setMapField "balances" sender
        (Wad.mkNat ((balanceAt s.storage sender).n - amount.n))
        (TokenStorage.setMapField2 "allowances" sender s.context.caller
          (Wad.mkNat ((allowanceAt s.storage sender s.context.caller).n - amount.n))
          s.storage))
    with hs1
  have haddOk : Wad.addChecked (balanceAt s.storage recipient) amount =
      .ok (Wad.mkNat ((balanceAt s.storage recipient).n + amount.n)) := by
    apply Wad.addChecked_eq_ok_of
    · rfl
    · exact hadd
  have hpres : (TokenStorage.setMapField "balances" sender
      (Wad.mkNat ((balanceAt s.storage sender).n - amount.n))
      (TokenStorage.setMapField2 "allowances" sender s.context.caller
        (Wad.mkNat ((allowanceAt s.storage sender s.context.caller).n - amount.n))
        s.storage)).balances.get recipient =
      s.storage.balances.get recipient := by
    unfold TokenStorage.setMapField TokenStorage.setMapField2
    simp [hne, Wad.mkNat]
  have haddOk' :
      Wad.addChecked
        ((TokenStorage.setMapField "balances" sender
          (Wad.mkNat ((balanceAt s.storage sender).n - amount.n))
          (TokenStorage.setMapField2 "allowances" sender s.context.caller
            (Wad.mkNat ((allowanceAt s.storage sender s.context.caller).n - amount.n))
            s.storage)).balances.get recipient).retag amount =
        .ok (Wad.mkNat ((balanceAt s.storage recipient).n + amount.n)) := by
    rw [hpres]
    simpa [balanceAt_dot, balanceAt_def] using haddOk
  simp only [Wad.mkNat] at haddOk'
  refine ⟨{ s with storage := s1 }, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs1]
    aesop (add simp [
      Wad.resolveMapKey, ContractM.caller,
      transferFrom, transferFromImpl, Stmt.toContractM, runS, Stmt.evalWith, Stmt.eval_def,
      hallowSubOk', hbalSubOk', haddOk', TokenStorage.getMapField, TokenStorage.getMapField2,
      TokenStorage.setMapField, TokenStorage.setMapField2, getMapField_balances,
      getMapField2_allowances, balanceAt_dot, balanceAt_def, allowanceAt_dot, allowanceAt_def,
      Wad.Fixed.retag, Wad.mkNat, BitVec.ofNat_toNat, Mapping.get_set_same,
      setMapField_balances_body, setMapField2_allowances_body, TokenEvent_transfer_wad,
      List.mapM, List.mapM.loop, Stmt.evalWith_mapSet, Stmt.evalWith_mapSet2,
      TokenStorageDsl_getMapField, TokenStorageDsl_setMapField, TokenStorageDsl_getMapField2,
      TokenStorageDsl_setMapField2])
  · rw [hs1, allowanceAt_setMapField_balances, allowanceAt_setMapField_balances,
      setMapField2_allowances_at]
  · rw [hs1, balanceAt_setMapField]
    split_ifs with h
    · exact absurd h hne
    · rw [balanceAt_setMapField, balanceAt_setMapField2_allowances]
      simp
  · rw [hs1, balanceAt_setMapField]
    simp
  · intro a1 a2 h12
    rw [hs1, allowanceAt_setMapField_balances, allowanceAt_setMapField_balances,
      setMapField2_allowances_ne _ _ _ _ _ _ h12]
  · intro a ha1 ha2
    rw [hs1, balanceAt_setMapField]
    simp [ha1, balanceAt_setMapField, ha2, balanceAt_setMapField2_allowances]

theorem transferFrom_decrements_allowance_and_transfers (sender recipient : Address) (amount : Wad)
    (s : ContractState TokenStorage)
    (hallow : amount.n ≤ (allowanceAt s.storage sender s.context.caller).n)
    (hsub : amount.n ≤ (balanceAt s.storage sender).n)
    (hadd : (balanceAt s.storage recipient).n + amount.n < 2 ^ 256)
    (hne : sender ≠ recipient) :
    ∃ s' : ContractState TokenStorage,
      runS (transferFrom sender recipient amount : TokenM Unit) s =
        .ok ((), s', [TokenEvent.Transfer (Wad.Fixed.retag amount)]) ∧
      allowanceAt s'.storage sender s.context.caller =
        Wad.mkNat ((allowanceAt s.storage sender s.context.caller).n - amount.n) ∧
      balanceAt s'.storage sender = Wad.mkNat ((balanceAt s.storage sender).n - amount.n) ∧
      balanceAt s'.storage recipient = Wad.mkNat ((balanceAt s.storage recipient).n + amount.n) ∧
      (∀ a1 a2 : Address, (a1, a2) ≠ (sender, s.context.caller) →
        allowanceAt s'.storage a1 a2 = allowanceAt s.storage a1 a2) ∧
      (∀ a : Address, a ≠ sender → a ≠ recipient → balanceAt s'.storage a = balanceAt s.storage a) :=
  runTransferFromOk sender recipient amount s hallow hsub hadd hne

/-- Concrete [`HonestERC20`](../../../Lsc/Lib/Interfaces/IERC20.lean) witness for `TokenStorage`.

Must be a `def` (data + proofs), not a `theorem`. `TokenTheorem.token_honest_erc20` wraps this
in `Nonempty (…)` to state existence as a proposition. -/
@[reducible]
def tokenHonestERC20 : HonestERC20 TokenStorage where
  ET := TokenEvent
  ErrT := TokenError
  -- Map abstract `Wad` transfer to Token's tagged `Amount` entry point.
  transferTyped recipient amount :=
    transferTyped recipient (Wad.Fixed.retag amount)
  getBalance s a := balanceAt s a
  approveTyped spender amount :=
    approveTyped spender (Wad.Fixed.retag amount)
  transferFromTyped sender recipient amount :=
    transferFromTyped sender recipient (Wad.Fixed.retag amount)
  getAllowance s a1 a2 := allowanceAt s a1 a2
  -- Conservation law: delegate to `honestTransferConserves` (itself from `runTransferOk`).
  transfer_conserves recipient sender amount ts hsub hadd hcaller := by
    obtain ⟨ts', log, hrun, hbal⟩ :=
      honestTransferConserves recipient sender amount ts hsub hadd hcaller
    refine ⟨ts', log, hrun, ?_⟩
    intro a
    exact hbal a
  -- Delegate to `runApproveOk` (`TokenProofs.lean`, above).
  approve_sets_allowance spender amount ts :=
    let ⟨s', hrun, hallow, hne, hbal⟩ := runApproveOk spender amount ts
    ⟨s', _, hrun, hallow, hne, hbal⟩
  -- Delegate to `runTransferFromOk` (`TokenProofs.lean`, above).
  transferFrom_conserves sender recipient amount ts hallow hsub hadd hne :=
    let ⟨s', hrun, hallow', hbalS, hbalR, hallowNe, hbalNe⟩ :=
      runTransferFromOk sender recipient amount ts hallow hsub hadd hne
    ⟨s', _, hrun, hallow', hbalS, hbalR, hallowNe, hbalNe⟩
