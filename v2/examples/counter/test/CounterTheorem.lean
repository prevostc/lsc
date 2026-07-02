import Counter
import LscV2.Lang.Eval

/-!
The 9 required `Counter` theorems (`docs/spec_idea_2/reference/COUNTER.md`),
proven against `Counter.lean` — the Lean-first-DSL (`TxM`/`deriving`)
version of the contract.

## Unfolding `increment`/`pause`/`unpause`

`Counter.lean` declares each function as a bare `def increment : TxM Unit :=
do ...` and relies on the `Coe (TxM Unit) (ContractM S E Err Unit)` instance
(`Lang/TxM.lean`) to use it directly as a `runS`-able action — no separately
named `incrementAst`/`incrementTxM` wrapper defs exist anymore. That
coercion can't always be inferred from context alone (its `S`/`E`/`Err`
metavariables aren't otherwise pinned at some of these call sites), so
`runS` calls below ascribe the type explicitly, e.g. `runS (increment :
CounterM Unit) s`, to force it. Marking `TxM.run`/`TxM.runWith`/
`TxM.toContractM`/every statement-builder combinator (`tellStmt`, `letWei`,
`setWei`, `setBool`, `requireE`, `revertE`, `emit`, ...) `@[simp]` in
`TxM.lean` means a single `simp` call reduces `increment` etc. down to the
same concrete `Stmt.seq`/`Stmt.require`/`Stmt.letBind`/... shape a
hand-written AST would have — no per-proof `simp only [...]` allowlist
needed. From that point on, the proofs use the same technique (`simp`
unfolding `Stmt.evalWith`/`ContractM.*` + `omega`) as any hand-written
contract's would.
-/

open LscV2 Counter

set_option linter.unusedSimpArgs false

/-- Convert `¬ b` (where `b : Bool`) to `b = false`. -/
private theorem bool_not_to_false {b : Bool} (h : ¬ b) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

private theorem runIncrementOk
    (s : ContractState CounterStorage)
    (hp : s.storage.paused = false)
    (hno : s.storage.number.canAddNat 1) :
    runS (increment : CounterM Unit) s = .ok ((),
      { s with storage := { s.storage with
          number := ⟨BitVec.ofNat 256 (s.storage.number.raw.toNat + 1)⟩ } },
      [CounterEvent.Incremented ⟨BitVec.ofNat 256 (s.storage.number.raw.toNat + 1)⟩]) := by
  have hok : Wei.addCheckedNat s.storage.number 1 =
      .ok ⟨BitVec.ofNat 256 (s.storage.number.raw.toNat + 1)⟩ :=
    Wei.addCheckedNat_ok s.storage.number 1 hno
  simp [runS, increment, TxM.toContractM, TxM.run, hp, hok,
    List.mapM, List.mapM.loop, List.reverseAux]

private theorem runPauseOk
    (s : ContractState CounterStorage)
    (howner : s.context.caller == s.storage.owner)
    (hp : s.storage.paused = false) :
    runS (pause : CounterM Unit) s = .ok ((),
      { s with storage := { s.storage with paused := true } },
      [CounterEvent.Paused]) := by
  simp [runS, pause, TxM.toContractM, TxM.run, howner, hp, List.mapM, List.mapM.loop, List.reverseAux]

private theorem runUnpauseOk
    (s : ContractState CounterStorage)
    (howner : s.context.caller == s.storage.owner)
    (hp : s.storage.paused = true) :
    runS (unpause : CounterM Unit) s = .ok ((),
      { s with storage := { s.storage with paused := false } },
      [CounterEvent.Unpaused]) := by
  simp [runS, unpause, TxM.toContractM, TxM.run, howner, hp, List.mapM, List.mapM.loop,
    List.reverseAux]

theorem increment_increases_number_when_not_paused
    (s s' : ContractState CounterStorage)
    (log : List CounterEvent)
    (hpaused : ¬ s.storage.paused)
    (hno : s.storage.number.canAddNat 1)
    (h : runS (increment : CounterM Unit) s = .ok ((), s', log)) :
    s'.storage.number.raw.toNat = s.storage.number.raw.toNat + 1 := by
  have hp' := bool_not_to_false hpaused
  rw [runIncrementOk s hp' hno] at h
  cases h
  simp only [BitVec.toNat_ofNat]
  omega

theorem increment_errors_when_paused
    (s : ContractState CounterStorage)
    (hp : s.storage.paused) :
    runS (increment : CounterM Unit) s = .error CounterError.Paused := by
  simp [runS, increment, TxM.toContractM, TxM.run, show s.storage.paused = true from hp]

theorem increment_does_not_change_paused
    (s s' : ContractState CounterStorage)
    (log : List CounterEvent)
    (hpaused : ¬ s.storage.paused)
    (hno : s.storage.number.canAddNat 1)
    (h : runS (increment : CounterM Unit) s = .ok ((), s', log)) :
    s'.storage.paused = s.storage.paused := by
  have hp' := bool_not_to_false hpaused
  rw [runIncrementOk s hp' hno] at h
  cases h; rfl

theorem increment_does_not_change_owner
    (s s' : ContractState CounterStorage)
    (log : List CounterEvent)
    (hpaused : ¬ s.storage.paused)
    (hno : s.storage.number.canAddNat 1)
    (h : runS (increment : CounterM Unit) s = .ok ((), s', log)) :
    s'.storage.owner = s.storage.owner := by
  have hp' := bool_not_to_false hpaused
  rw [runIncrementOk s hp' hno] at h
  cases h; rfl

theorem increment_emits_incremented
    (s s' : ContractState CounterStorage)
    (log : List CounterEvent)
    (hpaused : ¬ s.storage.paused)
    (hno : s.storage.number.canAddNat 1)
    (h : runS (increment : CounterM Unit) s = .ok ((), s', log)) :
    log = [CounterEvent.Incremented s'.storage.number] := by
  have hp' := bool_not_to_false hpaused
  rw [runIncrementOk s hp' hno] at h
  cases h; rfl

theorem increment_reverts_on_overflow
    (s : ContractState CounterStorage)
    (hpaused : ¬ s.storage.paused)
    (hov : ¬ s.storage.number.canAddNat 1) :
    runS (increment : CounterM Unit) s = .error CounterError.Overflow := by
  have hp' := bool_not_to_false hpaused
  have herr : Wei.addCheckedNat s.storage.number 1 = .error ArithError.Overflow :=
    Wei.addCheckedNat_error s.storage.number 1 hov
  simp [runS, increment, TxM.toContractM, TxM.run, hp', herr, ContractM.revertArith]

theorem pause_sets_paused_when_owner
    (s s' : ContractState CounterStorage) (log : List CounterEvent)
    (howner : s.context.caller == s.storage.owner)
    (hpaused : ¬ s.storage.paused)
    (h : runS (pause : CounterM Unit) s = .ok ((), s', log)) :
    s'.storage.paused = true := by
  have hp' := bool_not_to_false hpaused
  rw [runPauseOk s howner hp'] at h
  cases h; rfl

theorem pause_errors_when_not_owner
    (s : ContractState CounterStorage)
    (h : ¬ s.context.caller == s.storage.owner) :
    runS (pause : CounterM Unit) s = .error CounterError.NotOwner := by
  simp [runS, pause, TxM.toContractM, TxM.run,
    show (s.context.caller == s.storage.owner) = false from bool_not_to_false h]

theorem pause_errors_when_already_paused
    (s : ContractState CounterStorage)
    (howner : s.context.caller == s.storage.owner)
    (hp : s.storage.paused) :
    runS (pause : CounterM Unit) s = .error CounterError.Paused := by
  simp [runS, pause, TxM.toContractM, TxM.run, howner, show s.storage.paused = true from hp]

theorem unpause_clears_paused_when_owner
    (s s' : ContractState CounterStorage) (log : List CounterEvent)
    (howner : s.context.caller == s.storage.owner)
    (hp : s.storage.paused)
    (h : runS (unpause : CounterM Unit) s = .ok ((), s', log)) :
    s'.storage.paused = false := by
  have heq : s.storage.paused = true := hp
  rw [runUnpauseOk s howner heq] at h
  cases h; rfl
