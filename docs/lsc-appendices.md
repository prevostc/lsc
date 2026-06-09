**[← LSC Specification](lsc-spec.md)**

# LSC Appendices

Extended reference patterns and examples. Code samples follow [lsc-spec.md](lsc-spec.md) (v0.1): `ContractM E S α`, `state!`/`contract!`/`error!`, `get`/`set`, `+?`, `require`, `failWhen`, and `runS`.

| Appendix | Title |
|----------|-------|
| A | Counter (canonical example) |
| B | Versioning Roadmap |

---

## Appendix A — Counter (canonical example)

The Counter contract is the reference implementation shipping with the LSC toolchain. It demonstrates all core language features currently implemented.

### A.1 Contract (`src/Counter.lean`)

```lean4
import Lsc.Prelude
open Lsc

error! CounterError where
  | IsPausedError
  | arith : ArithError → CounterError

state! Counter where
  number : UInt256 @public
  paused : Bool

contract! Counter CounterError

@[lsc.external]
def pause : Counter Unit := do
  set .paused true

@[lsc.external]
def unpause : Counter Unit := do
  set .paused false

@[lsc.external]
def increment : Counter Unit := do
  failWhen (← get .paused) .IsPausedError
  let n ← get .number
  let n' ← n +? 1
  set .number n'
```

**What this demonstrates:**

| Feature | Where |
|---------|-------|
| `error!` macro with `arith` constructor | `CounterError` |
| `state!` with `@public` field | `number : UInt256 @public` |
| `contract!` monad alias + `Counter.view` | `contract! Counter CounterError` |
| `get`/`set` state access | `get .paused`, `set .number n'` |
| `failWhen` bool guard | `failWhen (← get .paused)` |
| Checked arithmetic `+?` | `n +? 1` |
| `@[lsc.external]` annotation | all three exports |

### A.2 Lemma (`test/CounterLemma.lean`)

AI-generated. All proofs are tactic proofs; no `sorry`.

```lean4
import Counter
import Lsc.Prelude
open Lsc

namespace CounterLemma

theorem pause_sets_paused (s s' : Counter.State) (h : runS pause s = .ok ((), s')) :
    s'.paused = true ∧ s'.number = s.number := by
  simp [runS, pause] at h
  subst h; exact ⟨rfl, rfl⟩

theorem unpause_clears_paused (s s' : Counter.State) (h : runS unpause s = .ok ((), s')) :
    s'.paused = false ∧ s'.number = s.number := by
  simp [runS, unpause] at h
  subst h; exact ⟨rfl, rfl⟩

theorem increment_increases_number_when_unpaused
    (s s' : Counter.State) (hp : ¬s.paused)
    (h : runS increment s = .ok ((), s')) :
    s'.number.val = s.number.val + 1 ∧ s'.paused = s.paused := by
  by_cases hlt : s.number.val + 1 < 2 ^ 256
  · simp [runS, increment, failWhen, hp, UInt256.addCheckedNat, dif_pos hlt] at h
    subst h
    exact ⟨rfl, (Bool.not_iff_eq_false).mp hp |>.symm⟩
  · exfalso
    simp [runS, increment, failWhen, hp, UInt256.addCheckedNat, dif_neg hlt,
          ContractM.arithFail] at h

theorem increment_errors_when_paused (s : Counter.State) (hp : s.paused) :
    runS increment s = .error (.contract .IsPausedError) := by
  have hpt : s.paused = true := hp
  simp [runS, increment, failWhen, hpt, ContractM.revert, ContractM.revertFail]

-- World-shaped variant (proofs over raw World, projecting via Counter.view)
theorem increment_increases_number_world_when_unpaused (w w' : World)
    (hp : ¬(Counter.view w).paused)
    (h : increment w = .ok ((), w')) :
    (Counter.view w').number.val = (Counter.view w).number.val + 1 ∧
    (Counter.view w').paused = (Counter.view w).paused := by
  -- (see full proof in examples/counter/test/CounterLemma.lean)
  sorry

end CounterLemma
```

### A.3 Theorem (`test/CounterTheorem.lean`)

Human-reviewed. One-line delegations.

```lean4
import Counter
import CounterLemma
import Lsc.Prelude
open Lsc

/-- On success, pause sets `paused` to `true` and leaves `number` unchanged. -/
theorem pause_sets_paused (s s' : Counter.State) (h : runS pause s = .ok ((), s')) :
    s'.paused = true ∧ s'.number = s.number :=
  CounterLemma.pause_sets_paused s s' h

/-- On success, unpause clears `paused` and leaves `number` unchanged. -/
theorem unpause_clears_paused (s s' : Counter.State) (h : runS unpause s = .ok ((), s')) :
    s'.paused = false ∧ s'.number = s.number :=
  CounterLemma.unpause_clears_paused s s' h

/-- When unpaused, increment increases `number` by exactly 1. -/
theorem increment_increases_number_when_unpaused (s s' : Counter.State) (hp : ¬s.paused)
    (h : runS increment s = .ok ((), s')) :
    s'.number.val = s.number.val + 1 ∧ s'.paused = s.paused :=
  CounterLemma.increment_increases_number_when_unpaused s s' hp h

/-- When paused, increment reverts with `.IsPausedError`. -/
theorem increment_reverts_when_paused (s : Counter.State) (hp : s.paused) :
    runS increment s = .error (.contract .IsPausedError) :=
  CounterLemma.increment_errors_when_paused s hp

/-- When unpaused, increment increases `number` by exactly 1 (full world). -/
theorem increment_increases_number_world_when_unpaused (w w' : World)
    (hp : ¬(Counter.view w).paused)
    (h : increment w = .ok ((), w')) :
    (Counter.view w').number.val = (Counter.view w).number.val + 1 ∧
    (Counter.view w').paused = (Counter.view w).paused :=
  CounterLemma.increment_increases_number_world_when_unpaused w w' hp h
```

### A.4 Proof pattern reference

**State-shaped proof (success case with `+?`):**

```lean4
-- Pattern for any function that does: let n ← get .number; let n' ← n +? 1; set .number n'
theorem f_increases_number (s s' : MyContract.State) (h : runS f s = .ok ((), s')) :
    s'.number.val = s.number.val + 1 := by
  by_cases hlt : s.number.val + 1 < 2 ^ 256
  · simp [runS, f, UInt256.addCheckedNat, dif_pos hlt] at h; subst h; rfl
  · exfalso; simp [runS, f, UInt256.addCheckedNat, dif_neg hlt, ContractM.arithFail] at h
```

**State-shaped proof (revert case with `failWhen`):**

```lean4
-- Pattern for: failWhen b .SomeError
theorem f_reverts_when_flag (s : MyContract.State) (hp : s.flag) :
    runS f s = .error (.contract .SomeError) := by
  have hpt : s.flag = true := hp
  simp [runS, f, failWhen, hpt, ContractM.revert, ContractM.revertFail]
```

**State-shaped proof (simple set, no arithmetic):**

```lean4
-- Pattern for: set .field val (no arithmetic)
theorem f_sets_field (s s' : MyContract.State) (h : runS f s = .ok ((), s')) :
    s'.field = expectedValue := by
  simp [runS, f] at h; subst h; rfl
```

---

## Appendix B — Versioning Roadmap

Current status and planned phases.

| Phase | Status | Deliverables |
|-------|--------|-------------|
| **v0.1** | Current | `ContractM`/`runS`; `state!`/`contract!`/`error!`; `get`/`set`/`+?`; Counter + proof files compile |
| **v1** | Planned | ERC-7201 storage layout; `load`/`store [ .field := val ]` syntax; emitter (Lean → Yul → bytecode); Foundry integration |
| **v2a** | Planned | `World` semantics for multi-contract proofs; `invoke` |
| **v2b** | Planned | External calls (`call`/`staticcall`); interface casts; `CALL`/`STATICCALL` lowering |
| **v3** | Future | `delegatecall`; proxy patterns; `CREATE`/`SELFDESTRUCT` |

| Feature | First available |
|---------|----------------|
| `state!`/`contract!`/`error!` macros | v0.1 |
| `get`/`set` state access | v0.1 |
| `+?` checked arithmetic | v0.1 |
| `require`/`failWhen` guards | v0.1 |
| `runS` proof runner | v0.1 |
| ERC-7201 namespaced storage | v1 |
| `load`/`store` syntax | v1 |
| Yul emitter + bytecode | v1 |
| Foundry `forge build` integration | v1 |
| `Mapping K V` | v1 |
| External calls (`call`) | v2b |
| `delegatecall` / proxy | v3 |
| `structure … extends` | Not planned — compose via nested fields |
