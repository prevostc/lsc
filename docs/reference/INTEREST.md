# Reference: Savings-Account Interest

A `Wad`-based (18-decimal fixed-point) reference contract, exercising real caller-supplied `tx` parameters on top of the `Counter` pattern.

Full design context: [DESIGN.md](../DESIGN.md). Canonical minimal pattern: [COUNTER.md](COUNTER.md) — read that first; this doc only calls out what's different here.

## Contract

```lean
structure InterestStorage where
  principal : Wad := ⟨0⟩
  rate : Wad := ⟨0⟩
  owner : Address := 0
  deriving Repr, ContractStorage

inductive InterestError where
  | NotOwner
  | Overflow
  deriving Repr, DecidableEq, ContractError

inductive InterestEvent where
  | Deposited (amount : Wad)
  | InterestAccrued (newPrincipal : Wad)
  | RateChanged (newRate : Wad)
  deriving Repr, DecidableEq, ContractEvent

tx deposit(amount : wad) {
  let p = σ.principal +? amount;
  σ.principal = p;
  emit Deposited(amount);
}

tx accrueInterest {
  let interest = σ.principal ⸢*⸣? σ.rate;
  let p = σ.principal +? interest;
  σ.principal = p;
  emit InterestAccrued(p);
}

tx setRate(newRate : wad) {
  require(msg.sender == σ.owner) else revert NotOwner();
  σ.rate = newRate;
  emit RateChanged(newRate);
}

derive_contract "Interest" InterestStorage InterestError InterestEvent
```

`principal`/`rate` are `Wad` — the 18-decimal fixed-point type (unlike `Counter.number`'s `Wei`, which has identity/0-decimal encoding). `deposit`/`setRate` no longer bump their field by a hardcoded literal: `tx <name>(p1 : ty1, p2 : ty2, ...) { ... }` (`Lsc/Lang/Syntax.lean`'s `lscTxParam` grammar, `ty` one of `uint256`/`bool`/`address`/`wei`/`wad`) declares a real, caller-supplied parameter, which is usable inside the body exactly like a `let`-bound local — `amount`/`newRate` resolve through `elabLscExpr`'s identifier case (the same `locals` association list a `let x = e;` binding extends) rather than through `σ.field`. Under the hood, each parameter becomes a real Lean function argument: `deposit`/`setRate` elaborate to `def deposit (amount : Wad) : Lsc.Stmt := ...`/`def setRate (newRate : Wad) : Lsc.Stmt := ...` (a plain `Wad → Stmt`, via `Lang/Syntax.lean`'s `flushContractTxs`, which wraps the parameter-free body in one extra `Stmt.letBind` per parameter so `Stmt.eval`'s existing `LocalEnv` is populated before anything else runs) — so a theorem/call site writes `runS (deposit amount : InterestM Unit) s`, i.e. the real value is applied first, then the resulting `Stmt` is coerced to `ContractM _ _ _ Unit` exactly as a zero-arg `tx` already was (`Stmt.toContractM`). `accrueInterest` stays zero-arg (it only ever operates on the already-stored `rate`, never a caller-supplied one), so it keeps the original `def accrueInterest : Lsc.Stmt := ...` shape.

Overflow on `+?`/`⸢*⸣?` reverts as `.error InterestError.Overflow` via `deriving ContractError`'s generated `ContractErrors.arith` (`ArithError.Overflow` → `Overflow`, by name-matching), enforced by `Lang.Checks.checkArithErrorCoverage` once all function bodies are known (see `DESIGN.md` §3.2). `Interest` declares only `NotOwner`/`Overflow` — no `Underflow`/`DivisionByZero` — because every arithmetic operation in this contract (`deposit`'s `+?`, `accrueInterest`'s `⸢*⸣?` then `+?`) only reaches `ArithError.Overflow`; `Wad.mulHalfUpChecked`/`Wad.addChecked` never reach `Underflow` (there is no `-?` anywhere in this contract) and `Wad.divDownChecked`'s `DivisionByZero` is unreachable too, since there is no `⌊/⌋?` in this contract.

## Required theorems

| Theorem | Technique |
|---------|-----------|
| `deposit_increases_principal` | `simp` + `omega`, arbitrary valid `amount` |
| `deposit_errors_on_overflow` | `simp` (error case), concrete overflow witness |
| `accrueInterest_computes_correctly` | `native_decide` on a concrete `ContractState` |
| `accrueInterest_reverts_on_overflow` | `native_decide` on a concrete `ContractState` |
| `setRate_only_owner` | `simp` (error case) |
| `setRate_sets_rate_when_owner` | `simp`, arbitrary valid `newRate` |

`deposit`/`setRate`'s theorems are universally quantified over the caller-supplied `amount`/`newRate : Wad` (alongside the `ContractState`), with preconditions like `canAdd s.storage.principal amount` (a local two-`Wad` analogue of `Wad.canAddNat`) standing in for what used to be a hardcoded literal — proved the same way as `Counter`'s theorems, by a private `run*Ok` characterization lemma per transaction (`simp` unfolding `Stmt`/`ContractM` once) followed by the public property theorem.

`accrueInterest`'s two theorems are the deliberate exception: they're stated against a fully *concrete* `ContractState` (not just concrete `principal`/`rate` fields on an otherwise-abstract `s`) and proved by `native_decide` instead. The original cause was diagnosed and fixed at the language level: `LocalEnv` (threading `tx`-local `let`-bound variables through evaluation) used to be an opaque closure, unfoldable only via `simp`'s expensive function-extensionality machinery; it's now a plain inductive list, reducible via ordinary `dsimp`/`simp` structural recursion. That change converts what used to be an *unbounded* `simp` blowup (multi-GB memory, no bound) into a *bounded, deterministic* run for any `tx`, and is a real, general improvement — not specific to this contract. For `accrueInterest` specifically, that bounded run (~110s) now fully resolves the local-variable/storage-field plumbing and the two chained checked ops (via the `rw`-friendly `Wad.addChecked_eq_ok_of`/`_error_of`, `Wad.mulHalfUpChecked_eq_ok_of`/`_error_of` lemmas in `Lsc/Lib/Wad/Eval.lean`), leaving only a small, fully concrete residual about the `emit` argument's `List.mapM` traversal — closing that residual with any further tactic re-triggers cost from the sheer size of the already-substituted term (a kernel type-checking cost, confirmed by a `(kernel) deep recursion detected` failure, not a tactic-search issue), so a fully `native_decide`-free proof for `accrueInterest` hasn't been found yet. `native_decide` remains the pragmatic choice here; `deposit`/`setRate` never needed it since they only chain one checked op each and don't read a `let`-bound variable back out via `emit`. Per the task's explicit guidance, plain `decide` is avoided throughout for a related reason (kernel reduction on 256-bit `BitVec` values, or on large generated interpreter terms, is prohibitively slow); every concrete check in this file uses `native_decide` or is phrased as a pure-`Nat` side condition discharged by `norm_num`/`omega`.

Proof hypotheses use `s.storage.field`/a concrete `ContractState` literal — not `σ.field` (source-level notation for *building* a function body). These 6 theorems are stated in `test/InterestTheorems.lean` (proved against `Interest.lean` using
characterization lemmas from `test/InterestProofs.lean`), zero `sorry`s.

## Optional contract_spec

If using [extensions/CONTRACT-SPEC.md](../extensions/CONTRACT-SPEC.md), the theorem list above maps directly to a `contract_spec Interest where …` block. Not currently required.
