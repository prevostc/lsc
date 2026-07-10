import InterestProofs

/-!
The required `Interest` theorems (`docs/reference/INTEREST.md`), proven against `Interest.lean`.

Every theorem below is a one-liner: its statement, immediately discharged by handing off to the
correspondingly-named `..._proof` lemma in `InterestProofs.lean`. That's where the actual "how"
(unfolding `TxM`/`ContractM`, `BitVec`/`Wad` arithmetic, `native_decide`) lives — this file is
meant to be read purely as a statement-of-facts document.
-/

open Lsc Interest

/-! ## `deposit` -/

/-- **Property:** Deposit increases principal by the deposited amount. -/
theorem deposit_increases_principal
    (s s' : ContractState InterestStorage) (amount : Wad) (log : List InterestEvent)
    (hno : canAdd s.storage.principal amount)
    (h : runS (deposit amount : InterestM Unit) s = .ok ((), s', log)) :
    s'.storage.principal.raw.toNat = s.storage.principal.raw.toNat + amount.raw.toNat :=
  deposit_increases_principal_proof s s' amount log hno h

/-- Overflow witness: `principal = 2^256 - 1` (max raw `Wad`), `amount = 1.0` — adding any
positive amount to the maximum representable `Wad` overflows 256 bits. -/
theorem deposit_errors_on_overflow
    (s : ContractState InterestStorage) (amount : Wad)
    (hprincipal : s.storage.principal = ⟨BitVec.allOnes 256⟩)
    (hamount : amount = Wad.mkNat Wad.WAD) :
    runS (deposit amount : InterestM Unit) s = .error InterestError.Overflow :=
  deposit_errors_on_overflow_proof s amount hprincipal hamount

/-! ## `accrueInterest` -/

theorem accrueInterest_computes_correctly
    (s' : ContractState InterestStorage) (log : List InterestEvent)
    (h : runS (accrueInterest : InterestM Unit) accrueOkState = .ok ((), s', log)) :
    s'.storage.principal = Wad.mkNat (105 * Wad.WAD) :=
  accrueInterest_computes_correctly_proof s' log h

theorem accrueInterest_reverts_on_overflow :
    runS (accrueInterest : InterestM Unit) accrueOverflowState = .error InterestError.Overflow :=
  accrueInterest_reverts_on_overflow_proof

/-! ## `setRate` -/

theorem setRate_only_owner
    (s : ContractState InterestStorage) (newRate : Wad)
    (h : ¬ s.context.caller == s.storage.owner) :
    runS (setRate newRate : InterestM Unit) s = .error InterestError.NotOwner :=
  setRate_only_owner_proof s newRate h

theorem setRate_sets_rate_when_owner
    (s s' : ContractState InterestStorage) (newRate : Wad) (log : List InterestEvent)
    (howner : s.context.caller == s.storage.owner)
    (h : runS (setRate newRate : InterestM Unit) s = .ok ((), s', log)) :
    s'.storage.rate = newRate :=
  setRate_sets_rate_when_owner_proof s s' newRate log howner h
