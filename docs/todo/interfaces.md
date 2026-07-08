# Backlog: opt-in "interfaces" for `exec`/`read`

**Status: design sketch, not implemented.** Nothing described on this page exists in the
codebase yet — `exec`/`read` (`Lsc/Core/ContractM.lean`'s `PairM.exec`/`PairM.read`, see
[reference/ESCROW.md](../reference/ESCROW.md)) are fully black box today, with no opt-in
mechanism at all. This page tracks the black-box default's one real limitation — strictly weaker
proofs at a cross-contract call site than would be possible if the callee's real spec were known
and trusted — as a concrete follow-up plan.

## Why black box isn't the end of the story

The black-box model (no `toErr`/`toEvent`, every failure collapses to one opaque
`FrameworkError.ExternalCallFailed`, callee events never fold into the caller's log — see
[reference/ESCROW.md](../reference/ESCROW.md)) is the right *default* for composability: a caller
shouldn't need to enumerate every way an arbitrary callee could fail just to call it, and it keeps
proofs about the caller robust even if the callee later changes its exact error/event shape. But
it's strictly less useful when the callee's real spec genuinely *is* known and trusted (e.g.
another `Lsc`-defined contract in the same project) — today a caller can't prove anything
conditional on the callee's real behavior (e.g. "if `Token.transfer` succeeds, `Token.totalSupply`
is unchanged"), only whether the opaque call succeeded or failed at all.

## Sketch: a richer, opt-in `interface` declaration

An `interface` declaration would name a callee contract's *assumed* spec — richer than a Solidity
`interface` (function signatures only) — by additionally letting the author attach:

* the callee's real event shapes, so a caller could choose to observe/prove about them instead of
  discarding them,
* the callee's real error constructors, so a caller could pattern-match on the actual failure
  reason instead of always collapsing to `ExternalCallFailed`,
* extra assumed constraints/theorems about the callee's behavior beyond its type signature — e.g.
  "`Token.transfer` never decreases `Token.totalSupply`" — that a call site could opt into
  *trusting* (not reproving locally) for a stronger conditional proof.

## Sketch: per-call-site opt-in syntax

A call site would opt in explicitly, e.g. (exact syntax TBD):

```lean
exec[TokenInterface] Token.transfer(recipient, amount);
```

Calls without the `[..]` annotation stay exactly as black-box as `exec`/`read` are today — this is
meant to be additive, not a replacement for the black-box default.

## Note: bool-return decoding is already solved without this

Decoding a callee's real ABI-encoded `bool` return value (the ERC20 `transfer`/`transferFrom`
convention) doesn't need this mechanism: `IR.Stmt.externalCall`'s `checkBoolReturn` flag
(`Lsc/Compile/IR.lean`) already handles it generically for any callee whose declared return type
is `bool`, with no per-call-site annotation. `interface` is still needed for everything else on
this page — event shapes, error constructors, and extra assumed theorems.

## Trust model (needs its own design pass before implementation)

An `interface` is an *assumption* the contract author vouches for about a callee whose source they
don't control — not automatically verified against the callee's real implementation, unless the
callee happens to be another `Lsc`-defined contract in the same project (in which case it could
eventually be mechanically checked or derived, rather than merely assumed). Getting this trust
boundary right needs a dedicated design pass before any code ships.
