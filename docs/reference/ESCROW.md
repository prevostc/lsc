# Reference: `Escrow` — a real, black-box cross-contract call

Full design context: [DESIGN.md](../DESIGN.md). Depends on [TOKEN.md](TOKEN.md) — `Escrow.release`
makes a genuine cross-contract call into `Token`, using `exec`/`read` (`Lsc/Lang/Syntax.lean`,
backed by `Lsc.ContractM.PairM` in `Lsc/Core/ContractM.lean`).

For why this looks the way it does — `PairM` vs. a general N-contract registry, and black-box
`exec`/`read` vs. an earlier whitebox `toErr`/`toEvent` design — see
[`decisions/0002`](../decisions/0002-pairm-cross-contract-model.md) and
[`decisions/0003`](../decisions/0003-exec-read-black-box.md).

## Contract

```lean
structure EscrowStorage where
  owner : Address := 0
  released : Token.Amount := ⟨0⟩
  deriving Repr, ContractStorage

inductive EscrowError where
  | NotOwner
  | Overflow
  | Underflow
  | Reentrant
  | ExternalCallFailed
  deriving Repr, DecidableEq, ContractError

inductive EscrowEvent where
  | Released (amount : Token.Amount)
  deriving Repr, DecidableEq, ContractEvent

@nonreentrant
tx release(recipient : Address, amount : Token.Amount) {
  require (msg.sender == σ.owner) else revert NotOwner();
  exec Token.transfer(recipient, amount);
  let r = σ.released +? amount;
  σ.released = r;
  emit Released(amount);
}

derive_contract "Escrow" EscrowStorage EscrowError EscrowEvent
```

`exec Target.fn(args);`/`read Target.fn(args);` call another contract's real `tx`/`view` directly
by dotted name, with plain values as arguments — see `Lsc/Lang/Syntax.lean`'s docstring for the
grammar and elaboration mechanics. `read` is `exec`'s read-only twin: it runs the callee but
discards any state change/events, keeping only the return value — unused here since `release`
genuinely mutates `Token`'s balances, but that's what a hypothetical `previewRelease` would use to
call `Token.balanceOf` without risk of mutating `Token`'s storage.

`@nonreentrant` is required on any `tx` using `exec` (enforced at elaboration time and again by
`Checks.checkNonReentrant`); read-only `read` txs are exempt. Two independent reasons this call
can't reenter `Escrow`: structurally, `Token.transfer`'s own type has no way to even mention
`EscrowStorage`/`PairM` (see `ContractM.lean`'s `PairM` docstring); and `@nonreentrant` desugars
to `Stmt.reentrancyGuard`, which lowers to a transient-storage lock (`TLOAD`/`TSTORE`) in Yul —
`release_rejects_when_already_locked` proves the proof-layer mirror of this guard.

`amount`'s type is `Token.Amount`, not the generic `Wad` — see [TOKEN.md](TOKEN.md) for why passing
some other token's amount here is a compile error, not a runtime bug.

**Black box.** On success `release` only observes `Token.transfer`'s return value; on failure it
sees a single opaque `FrameworkError.ExternalCallFailed`, never `Token`'s real `TokenError`; and
`Token`'s own events never end up in `Escrow`'s log. This is what keeps `EscrowError`/`EscrowEvent`
from ever needing to mention `Token.TokenError`/`Token.TokenEvent` (see
[`decisions/0004`](../decisions/0004-escrow-hand-written-dsl-wiring.md) for what this replaced) —
and `exec_never_silently_swallows_failure`/`read_never_silently_swallows_failure`
(`Lsc/Core/ContractM.lean`) prove there's no third "call happened but nobody checked" outcome.

**Bytecode.** `release` is in `Escrow`'s `ContractDef`; `exec Token.transfer(..)` lowers to a
checked `CALL` via `Stmt.externalExec` → `IR.externalCall` → Yul. Callee address wiring still
uses the v1 `token : Address` storage-field convention (see `docs/todo/interfaces.md` for the
full N-contract dispatch registry). The proof layer keeps a separate `PairM` `def` for
`examples/escrow/test/EscrowProofs.lean`.

## Required theorems

Two tiers, mirroring `examples/interest/test/InterestProofs.lean`/`InterestTheorems.lean`:
`examples/escrow/test/EscrowProofs.lean` characterizes `release`'s/`Token.transferTyped`'s exact
execution once, compositionally; `examples/escrow/test/EscrowTheorem.lean` states the required
properties as short corollaries, universally quantified over every address and amount.

| Theorem | Technique |
|---------|-----------|
| `EscrowProofs.runTransferOk` | Tier 1 — `simp`, characterizes `Token.transferTyped` for all addresses `a` at once |
| `EscrowProofs.runReleaseOk` | Tier 1 — `simp` + `PairM.exec_unlocked_ok` composed with `runTransferOk` |
| `release_increases_released` | Tier 2 — corollary of `runReleaseOk` |
| `release_debits_escrow` | Tier 2 — corollary of `runReleaseOk`, instantiated at the escrow's own address |
| `release_credits_recipient` | Tier 2 — corollary of `runReleaseOk`, instantiated at the recipient's address |
| `release_preserves_other_balances` | Tier 2 — corollary of `runReleaseOk`, instantiated at any other address |
| `release_self_release_is_noop` | Tier 2 — corollary of `runReleaseOk`, degenerate `escrowAddr = recipient` edge case |
| `release_emits_released` | Tier 2 — corollary of `runReleaseOk` |
| `release_rejects_non_owner` | Direct `simp`, no success-path setup needed |
| `release_rejects_when_already_locked` | Direct `simp`, no success-path setup needed |

Proved in `examples/escrow/test/EscrowProofs.lean`/`EscrowTheorem.lean` against
`examples/escrow/src/Escrow.lean`, zero `sorry`s, zero `native_decide`.
