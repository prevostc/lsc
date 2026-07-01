import Counter
import LscV2.Lang.Eval

/-!
The 9 required `Counter` theorems (`docs/spec_idea_2/reference/COUNTER.md`),
proven against `Counter.lean` — the Lean-first-DSL (`TxM`/`deriving`)
version of the contract.

## Unfolding `incrementAst`/`pauseAst`/`unpauseAst`

`incrementAst := TxM.run incrementTxM` is a `Stmt` value built by `do`-
notation over `TxM := WriterT Stmt Id`. Marking `TxM.run`/`TxM.runWith` and
every statement-builder combinator (`tellStmt`, `letWei`, `setWei`,
`setBool`, `requireE`, `revertE`, `emit`, ...) `@[simp]` in `TxM.lean` (see
that file's comment above `attribute [simp] TxM.runWith TxM.run`) means a
single `simp` call reduces `incrementAst` etc. down to the same concrete
`Stmt.seq`/`Stmt.require`/`Stmt.letBind`/... shape a hand-written AST would
have — no per-proof `simp only [...]` allowlist needed. From that point on,
the proofs use the same technique (`simp` unfolding `Stmt.evalWith`/
`ContractM.*` + `omega`) as any hand-written contract's would.
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
    runS increment s = .ok ((),
      { s with storage := { s.storage with
          number := ⟨BitVec.ofNat 256 (s.storage.number.raw.toNat + 1)⟩ } },
      [CounterEvent.Incremented ⟨BitVec.ofNat 256 (s.storage.number.raw.toNat + 1)⟩]) := by
  have hok : Wei.addCheckedNat s.storage.number 1 =
      .ok ⟨BitVec.ofNat 256 (s.storage.number.raw.toNat + 1)⟩ :=
    Wei.addCheckedNat_ok s.storage.number 1 hno
  simp [runS, increment, incrementAst, incrementTxM, hp, hok,
    List.mapM, List.mapM.loop, List.reverseAux]

private theorem runPauseOk
    (s : ContractState CounterStorage)
    (howner : s.context.caller == s.storage.owner)
    (hp : s.storage.paused = false) :
    runS pause s = .ok ((),
      { s with storage := { s.storage with paused := true } },
      [CounterEvent.Paused]) := by
  simp [runS, pause, pauseAst, pauseTxM, howner, hp, List.mapM, List.mapM.loop, List.reverseAux]

private theorem runUnpauseOk
    (s : ContractState CounterStorage)
    (howner : s.context.caller == s.storage.owner)
    (hp : s.storage.paused = true) :
    runS unpause s = .ok ((),
      { s with storage := { s.storage with paused := false } },
      [CounterEvent.Unpaused]) := by
  simp [runS, unpause, unpauseAst, unpauseTxM, howner, hp, List.mapM, List.mapM.loop,
    List.reverseAux]

theorem increment_increases_number_when_not_paused
    (s s' : ContractState CounterStorage)
    (log : List CounterEvent)
    (hpaused : ¬ s.storage.paused)
    (hno : s.storage.number.canAddNat 1)
    (h : runS increment s = .ok ((), s', log)) :
    s'.storage.number.raw.toNat = s.storage.number.raw.toNat + 1 := by
  have hp' := bool_not_to_false hpaused
  rw [runIncrementOk s hp' hno] at h
  cases h
  simp only [BitVec.toNat_ofNat]
  omega

theorem increment_errors_when_paused
    (s : ContractState CounterStorage)
    (hp : s.storage.paused) :
    runS increment s = .error CounterError.Paused := by
  simp [runS, increment, incrementAst, incrementTxM, show s.storage.paused = true from hp]

theorem increment_does_not_change_paused
    (s s' : ContractState CounterStorage)
    (log : List CounterEvent)
    (hpaused : ¬ s.storage.paused)
    (hno : s.storage.number.canAddNat 1)
    (h : runS increment s = .ok ((), s', log)) :
    s'.storage.paused = s.storage.paused := by
  have hp' := bool_not_to_false hpaused
  rw [runIncrementOk s hp' hno] at h
  cases h; rfl

theorem increment_does_not_change_owner
    (s s' : ContractState CounterStorage)
    (log : List CounterEvent)
    (hpaused : ¬ s.storage.paused)
    (hno : s.storage.number.canAddNat 1)
    (h : runS increment s = .ok ((), s', log)) :
    s'.storage.owner = s.storage.owner := by
  have hp' := bool_not_to_false hpaused
  rw [runIncrementOk s hp' hno] at h
  cases h; rfl

theorem increment_emits_incremented
    (s s' : ContractState CounterStorage)
    (log : List CounterEvent)
    (hpaused : ¬ s.storage.paused)
    (hno : s.storage.number.canAddNat 1)
    (h : runS increment s = .ok ((), s', log)) :
    log = [CounterEvent.Incremented s'.storage.number] := by
  have hp' := bool_not_to_false hpaused
  rw [runIncrementOk s hp' hno] at h
  cases h; rfl

theorem increment_reverts_on_overflow
    (s : ContractState CounterStorage)
    (hpaused : ¬ s.storage.paused)
    (hov : ¬ s.storage.number.canAddNat 1) :
    runS increment s = .error CounterError.Overflow := by
  have hp' := bool_not_to_false hpaused
  have herr : Wei.addCheckedNat s.storage.number 1 = .error ArithError.Overflow :=
    Wei.addCheckedNat_error s.storage.number 1 hov
  simp [runS, increment, incrementAst, incrementTxM, hp', herr, ContractM.revertArith]

theorem pause_sets_paused_when_owner
    (s s' : ContractState CounterStorage) (log : List CounterEvent)
    (howner : s.context.caller == s.storage.owner)
    (hpaused : ¬ s.storage.paused)
    (h : runS pause s = .ok ((), s', log)) :
    s'.storage.paused = true := by
  have hp' := bool_not_to_false hpaused
  rw [runPauseOk s howner hp'] at h
  cases h; rfl

theorem pause_errors_when_not_owner
    (s : ContractState CounterStorage)
    (h : ¬ s.context.caller == s.storage.owner) :
    runS pause s = .error CounterError.NotOwner := by
  simp [runS, pause, pauseAst, pauseTxM,
    show (s.context.caller == s.storage.owner) = false from bool_not_to_false h]

theorem pause_errors_when_already_paused
    (s : ContractState CounterStorage)
    (howner : s.context.caller == s.storage.owner)
    (hp : s.storage.paused) :
    runS pause s = .error CounterError.Paused := by
  simp [runS, pause, pauseAst, pauseTxM, howner, show s.storage.paused = true from hp]

theorem unpause_clears_paused_when_owner
    (s s' : ContractState CounterStorage) (log : List CounterEvent)
    (howner : s.context.caller == s.storage.owner)
    (hp : s.storage.paused)
    (h : runS unpause s = .ok ((), s', log)) :
    s'.storage.paused = false := by
  have heq : s.storage.paused = true := hp
  rw [runUnpauseOk s howner heq] at h
  cases h; rfl
