# Reference (future work, not implemented): opt-in "interfaces" for `exec`/`read`

**Status: design sketch / TODO only.** Nothing described on this page exists in the codebase yet
— `exec`/`read` (`Lsc/Core/ContractM.lean`'s `PairM.exec`/`PairM.read`, see
[ESCROW.md](ESCROW.md)) are fully black box today, with no opt-in mechanism at all. This page
exists so the black-box default's one real limitation — strictly weaker proofs at a cross-contract
call site than would be possible if the callee's real spec were known and trusted — has a
documented, concrete follow-up plan instead of being silently accepted forever.

## Why black box isn't the end of the story

`exec`/`read`'s black-box model (no `toErr`/`toEvent`, every failure collapses to one opaque
`FrameworkError.ExternalCallFailed`, see [ESCROW.md](ESCROW.md) — callee events never fold into
the caller's log) is the right
*default* for composability — a caller shouldn't need to enumerate every way an arbitrary callee
could fail just to call it at all, and it makes proofs about the caller robust even if the callee
later changes its exact error/event shape. But it's also strictly less useful than it could be
when the callee's real spec genuinely *is* known and trusted (e.g. calling another `Lsc`-defined
contract in the same project, or a well-known audited external protocol) — today, a caller has no
way to prove anything conditional on the callee's real behavior (e.g. "if `Token.transfer`
succeeds, `Token`'s `totalSupply` is unchanged"), only on whether the opaque call succeeded or
failed at all.

## Sketch: a richer, opt-in `interface` declaration

An `interface` declaration would name a callee contract's *assumed* spec — richer than a Solidity
`interface` (which is function signatures only) in that it would also let the author attach:

* the callee's real function signatures (as today, needed to type-check the call site at all),
* the callee's real event shapes (so a caller *could* choose to observe/prove about them, instead
  of them always being discarded),
* the callee's real error constructors (so a caller *could* pattern-match on the callee's actual
  failure reason, instead of always collapsing to `ExternalCallFailed`),
* extra assumed constraints/theorems about the callee's behavior beyond its raw type signature —
  e.g. `"Token.transfer never decreases Token.totalSupply"`, `"Token.balanceOf is monotonic under
  mint-only callers"` — that a call site could opt into *trusting* (not reproving locally) for a
  stronger conditional proof.

## Sketch: per-call-site opt-in syntax

A call site would opt in explicitly, e.g. (exact syntax TBD):

```lean
exec[TokenInterface] Token.transfer(recipient, amount);
```

Calls without the `[..]` annotation stay exactly as black-box as `exec`/`read` are today — this
is meant to be a strictly additive, opt-in capability, not a replacement for the black-box
default.

## Note: the `bool`-return convention is already handled without this concept

One thing this page originally motivated — decoding a callee's real ABI-encoded `bool` return
value (the ERC20 `transfer`/`transferFrom` convention) instead of only observing "succeeded or
not" — no longer needs the full opt-in `interface` mechanism above: `Lsc.Compile.IR.Stmt.
safeExternalCall`'s `checkBoolReturn` flag (`Lsc/Compile/IR.lean`, `docs/reference/ESCROW.md`)
already does this generically, for any callee whose declared return type is `bool`, with no
per-call-site annotation required. What `interface` is still for is everything *else* on this
page — a callee's real event shapes, real error constructors, and extra assumed theorems beyond
its raw type signature.

## Trust model (the hard part, needs its own design doc before implementation)

An `interface` is fundamentally an *assumption* the contract author vouches for about a callee
they don't control the source of — it is not automatically verified against the callee's real
implementation unless the callee happens to be another `Lsc`-defined contract in the same
project, in which case it could eventually be mechanically checked or even derived (rather than
merely assumed) from the callee's actual verified theorems. Getting this trust boundary right —
so a caller's proofs can't accidentally "prove" something false about a callee whose interface
declaration doesn't actually match its real behavior — needs a dedicated design pass, not a quick
addition to `PairM`. Tracked as a TODO in [TODO.md](../../TODO.md); no code for this ships until
that design exists.
