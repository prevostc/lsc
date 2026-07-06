import Interest
import Lsc.Lang.Eval

/-!
Proof machinery backing `InterestTheorems.lean` (the required `Interest` theorems,
`docs/reference/INTEREST.md`) — kept in its own file so that file can be read as a clean
statement-of-facts document, without the "how" (private characterization lemmas, `Wad`/`BitVec`
arithmetic helpers, `native_decide` witness states) cluttering it.

Same two-tier style as `examples/counter/test/CounterTheorem.lean`: a private `run*Ok`
characterization lemma per transaction (unfolds the `TxM`/`ContractM` machinery via `simp` once),
which `InterestTheorems.lean` then `rw`/`cases`es on plus `omega`/`rfl`/`decide` for the arithmetic
tail. See that file's docstring for why `runS` calls below ascribe an explicit `InterestM Unit`
type.

`deposit`/`setRate` now take a real `Wad` parameter (rather than the old fixed-increment
workaround), so their `run*Ok` lemmas are stated for an arbitrary `amount`/`newRate : Wad`,
universally quantified alongside the `ContractState`, with preconditions like
`canAdd s.storage.principal amount` in place of a hardcoded literal.

`accrueInterest`'s two `native_decide` lemmas (below) are the exception: they're stated against a
fully *concrete* `ContractState` (not just concrete `principal`/`rate` fields on an otherwise-
abstract `s`) and proved by `native_decide` rather than `simp`.

Root cause, confirmed by direct experimentation: it is *not* about `σ.principal` being read twice,
nor about `ContractDSL`/`getField`'s field-name dispatch. It *is* about `LocalEnv`
(`Lsc/Core/ContractM.lean`), the structure threading `tx`-local `let`-bound variables through
`Stmt.evalWith`: it used to be represented as an opaque closure (`Ident → Option (Sigma Val)`),
which can only be unfolded via `simp`'s function-extensionality machinery, never via cheap
`dsimp`/`rfl` iota-reduction — and that, compounded across `accrueInterest`'s two sequential
`let`s (`interest`, then `p`) interacting with the checked-op case split each `let` needs, is what
made `simp` diverge (multi-GB memory, no bound). This has been fixed at the language level:
`LocalEnv` is now a plain inductive snoc-list, so `lookup` is ordinary structural recursion that
`dsimp`/`simp` reduce for free, with no closure/funext reasoning involved. That fix is real and
general — it converts what used to be an *unbounded* blowup into a *bounded, deterministic*
`simp` run for any `tx` body, regardless of how many `let`s it chains.

For `accrueInterest` specifically, that bounded run (~110s) now fully resolves the `LocalEnv`/
`getField`/`setField` plumbing and the checked-op case splits (using the `rw`-friendly ok/error
lemmas `Wad.addChecked_eq_ok_of`/`_error_of`, `Wad.mulHalfUpChecked_eq_ok_of`/`_error_of` in
`Lsc/Lib/Wad/Eval.lean`), leaving only a small, fully concrete residual goal about the single
`emit` argument's `List.mapM` traversal — but closing *that* residual with any further tactic
(`rfl`, `dsimp`, or more `simp` lemmas) re-triggers the same class of cost purely from the sheer
size of the already-substituted surrounding term (kernel type-checking cost, not tactic search —
confirmed by a `(kernel) deep recursion detected` failure on one attempt). So `native_decide`
remains the pragmatic choice for `accrueInterest` today, but the *reason* has narrowed
considerably: it's no longer "chained storage reads make `simp` diverge unboundedly", it's "this
one `emit`-with-argument residual needs one more targeted proof step that hasn't been found yet".
`deposit`/`setRate` never needed any of this, since they each only chain one checked op and don't
read a variable back out via `emit`. Pinning `s` to a fully concrete value sidesteps the issue
entirely for `accrueInterest`: `native_decide` compiles the (fully computable, since `s` is now
closed) `runS` call to native code and runs it directly, independent of term size. -/

open Lsc Interest

set_option linter.unusedSimpArgs false

/-- Convert `¬ b` (where `b : Bool`) to `b = false`. -/
theorem bool_not_to_false {b : Bool} (h : ¬ b) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

/-- `Wad.mkNat` round-trips a `Wad`'s own raw value back to itself — bridges the literal `tx`
parameters are re-embedded as (`Wad.Expr.lit amount.raw.toNat`, per
`Lsc.Deriving.FieldKind.embedLitStx`) back to the parameter value itself, so `run*Ok` lemmas
below can state their arithmetic side conditions directly in terms of `amount`/`newRate`. -/
theorem Wad.mkNat_roundtrip (w : Wad) : Wad.mkNat w.raw.toNat = w := by
  simp only [Wad.mkNat]
  cases w with
  | mk raw =>
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt raw.isLt]

/-- `canAdd a b` holds iff adding `b` to `a` will not overflow 256 bits — the two-`Wad` analogue
of `Wad.canAddNat` (`Lsc/Lib/Wad/Eval.lean`), needed here since `deposit` now adds a real `Wad`
value (not a bare `Nat` literal). -/
abbrev canAdd (a b : Wad) : Prop := a.raw.toNat + b.raw.toNat < 2 ^ 256

/-- `Wad.addChecked` in the no-overflow case, in terms of plain `Nat` sums — keeps the arithmetic
side condition (`hn`) pure-`Nat`, so it can be discharged by `norm_num`/`omega` without
`decide`/`native_decide` ever touching the `Wad`/`Except`-wrapped equality directly (a prior
attempt hung using plain `decide` on 256-bit values). -/
theorem addChecked_eq_ok_of (a b : Wad) (n : Nat)
    (hn : a.raw.toNat + b.raw.toNat = n) (hbound : n < 2 ^ 256) :
    Wad.addChecked a b = .ok (Wad.mkNat n) := by
  have hlt : a.raw.toNat + b.raw.toNat < 2 ^ 256 := hn ▸ hbound
  have htoNat : (a.raw + b.raw).toNat = a.raw.toNat + b.raw.toNat :=
    BitVec.toNat_add_of_lt hlt
  have heq : a.raw + b.raw = BitVec.ofNat 256 n := by
    apply BitVec.eq_of_toNat_eq
    rw [htoNat, hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound]
  have hnolt : ¬ a.raw + b.raw < a.raw := by
    rw [BitVec.lt_def, htoNat]; omega
  simp only [Wad.addChecked, UInt256.addChecked, heq]
  rw [if_neg (heq ▸ hnolt)]
  simp [Except.map, Wad.mkNat]

/-- `Wad.addChecked` in the overflow case, in terms of a plain `Nat` bound — the error-case
counterpart of `addChecked_eq_ok_of` above, same rationale (keeps the whole proof off
`decide`/`native_decide` on the `Wad`/`Except`-wrapped equality). -/
theorem addChecked_eq_overflow_of (a b : Wad) (h : a.raw.toNat + b.raw.toNat ≥ 2 ^ 256) :
    Wad.addChecked a b = .error .Overflow := by
  have hb : b.raw.toNat < 2 ^ 256 := b.raw.isLt
  have htoNat : (a.raw + b.raw).toNat = (a.raw.toNat + b.raw.toNat) % 2 ^ 256 :=
    BitVec.toNat_add a.raw b.raw
  have hlt : (a.raw + b.raw).toNat < a.raw.toNat := by
    rw [htoNat, Nat.mod_eq_sub_mod h]
    have hlt2 : a.raw.toNat + b.raw.toNat - 2 ^ 256 < 2 ^ 256 := by omega
    rw [Nat.mod_eq_of_lt hlt2]
    omega
  have hlt' : a.raw + b.raw < a.raw := by rw [BitVec.lt_def]; exact hlt
  simp only [Wad.addChecked, UInt256.addChecked]
  rw [if_pos hlt']
  rfl

/-! ## `deposit` -/

theorem runDepositOk
    (s : ContractState InterestStorage) (amount : Wad)
    (hno : canAdd s.storage.principal amount) :
    runS (deposit amount : InterestM Unit) s = .ok ((),
      { s with storage := { s.storage with
          principal := ⟨BitVec.ofNat 256 (s.storage.principal.raw.toNat + amount.raw.toNat)⟩ } },
      [InterestEvent.Deposited amount]) := by
  have hok : Wad.addChecked s.storage.principal amount =
      .ok ⟨BitVec.ofNat 256 (s.storage.principal.raw.toNat + amount.raw.toNat)⟩ :=
    addChecked_eq_ok_of s.storage.principal amount _ rfl hno
  simp [runS, deposit, depositImpl, Stmt.toContractM, Wad.mkNat_roundtrip, hok,
    List.mapM, List.mapM.loop, List.reverseAux]

/-- Full proof backing `deposit_increases_principal`. -/
theorem deposit_increases_principal_proof
    (s s' : ContractState InterestStorage) (amount : Wad) (log : List InterestEvent)
    (hno : canAdd s.storage.principal amount)
    (h : runS (deposit amount : InterestM Unit) s = .ok ((), s', log)) :
    s'.storage.principal.raw.toNat = s.storage.principal.raw.toNat + amount.raw.toNat := by
  rw [runDepositOk s amount hno] at h
  cases h
  simp only [BitVec.toNat_ofNat]
  omega

/-- Full proof backing `deposit_errors_on_overflow`. -/
theorem deposit_errors_on_overflow_proof
    (s : ContractState InterestStorage) (amount : Wad)
    (hprincipal : s.storage.principal = ⟨BitVec.allOnes 256⟩)
    (hamount : amount = Wad.mkNat Wad.WAD) :
    runS (deposit amount : InterestM Unit) s = .error InterestError.Overflow := by
  have hover : Wad.addChecked s.storage.principal amount = .error .Overflow := by
    apply addChecked_eq_overflow_of
    rw [hprincipal, hamount]
    simp only [BitVec.toNat_allOnes, Wad.mkNat, BitVec.toNat_ofNat, Wad.WAD]
    norm_num
  simp [runS, deposit, depositImpl, Stmt.toContractM, Wad.mkNat_roundtrip, hover,
    ContractM.revertArith]

/-! ## `accrueInterest`

See the module docstring above for why these two lemmas are stated against a fully concrete
`ContractState` and proved by `native_decide` rather than the `simp`-based technique used
everywhere else in this file. -/

/-- Witness state for `accrueInterest_computes_correctly`: `principal = 100`, `rate = 5%`. -/
def accrueOkState : ContractState InterestStorage :=
  { storage :=
      { principal := Wad.mkNat (100 * Wad.WAD)
        rate := Wad.mkNat (5 * Wad.WAD / 100)
        owner := 0 }
    context := { caller := 0, callvalue := 0, timestamp := 0, origin := 0 }
    locked := false }

theorem accrueOk_native :
    (runS (accrueInterest : InterestM Unit) accrueOkState).map (fun x => x.2.1.storage.principal) =
      .ok (Wad.mkNat (105 * Wad.WAD)) := by
  native_decide

/-- Overflow witness for `accrueInterest_reverts_on_overflow`: `principal = 2^256 - 1` (max raw
`Wad`), `rate = 2 * WAD` (200%) — the 36-decimal product `principal.raw * rate.raw` is roughly
`2 * (2^256 - 1)`, so dividing back down by `WAD` still overflows 256 bits. -/
def accrueOverflowState : ContractState InterestStorage :=
  { storage :=
      { principal := ⟨BitVec.allOnes 256⟩
        rate := Wad.mkNat (2 * Wad.WAD)
        owner := 0 }
    context := { caller := 0, callvalue := 0, timestamp := 0, origin := 0 }
    locked := false }

theorem accrueOverflow_native :
    (runS (accrueInterest : InterestM Unit) accrueOverflowState).map (fun _ => (0 : Nat)) =
      .error InterestError.Overflow := by
  native_decide

/-- Full proof backing `accrueInterest_computes_correctly`. -/
theorem accrueInterest_computes_correctly_proof
    (s' : ContractState InterestStorage) (log : List InterestEvent)
    (h : runS (accrueInterest : InterestM Unit) accrueOkState = .ok ((), s', log)) :
    s'.storage.principal = Wad.mkNat (105 * Wad.WAD) := by
  have hnative := accrueOk_native
  rw [h] at hnative
  simp only [Except.map, Except.ok.injEq] at hnative
  exact hnative

/-- Full proof backing `accrueInterest_reverts_on_overflow`. -/
theorem accrueInterest_reverts_on_overflow_proof :
    runS (accrueInterest : InterestM Unit) accrueOverflowState = .error InterestError.Overflow := by
  have h := accrueOverflow_native
  cases hrun : runS (accrueInterest : InterestM Unit) accrueOverflowState with
  | ok v => rw [hrun] at h; simp [Except.map] at h
  | error e =>
    rw [hrun] at h
    simp only [Except.map, Except.error.injEq] at h
    rw [h]

/-! ## `setRate` -/

theorem runSetRateOk
    (s : ContractState InterestStorage) (newRate : Wad)
    (howner : s.context.caller == s.storage.owner) :
    runS (setRate newRate : InterestM Unit) s = .ok ((),
      { s with storage := { s.storage with rate := newRate } },
      [InterestEvent.RateChanged newRate]) := by
  simp [runS, setRate, setRateImpl, Stmt.toContractM, Wad.mkNat_roundtrip, howner,
    List.mapM, List.mapM.loop, List.reverseAux]

/-- Full proof backing `setRate_only_owner`. -/
theorem setRate_only_owner_proof
    (s : ContractState InterestStorage) (newRate : Wad)
    (h : ¬ s.context.caller == s.storage.owner) :
    runS (setRate newRate : InterestM Unit) s = .error InterestError.NotOwner := by
  simp [runS, setRate, setRateImpl, Stmt.toContractM,
    show (s.context.caller == s.storage.owner) = false from bool_not_to_false h]

/-- Full proof backing `setRate_sets_rate_when_owner`. -/
theorem setRate_sets_rate_when_owner_proof
    (s s' : ContractState InterestStorage) (newRate : Wad) (log : List InterestEvent)
    (howner : s.context.caller == s.storage.owner)
    (h : runS (setRate newRate : InterestM Unit) s = .ok ((), s', log)) :
    s'.storage.rate = newRate := by
  rw [runSetRateOk s newRate howner] at h
  cases h
  rfl
