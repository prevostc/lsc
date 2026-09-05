# 0004: `Escrow` no longer needs hand-written `ContractDSL`/`ContractErrors` glue

## Context

Earlier, `EscrowEvent` carried a foreign `Token.TokenEvent` payload (a `TokenNotified`
constructor folding every `Token` event reachable during `release` into `Escrow`'s own log),
because the pre-[`0003`](0003-exec-read-black-box.md) cross-contract model needed a way to
observe the callee's events. This made `EscrowStorage`/`EscrowError`/`EscrowEvent` not fully
DSL-representable (`Ty` only has five field kinds, and a raw `Token.TokenEvent` payload isn't one
of them), forcing a hand-written `ContractDSL EscrowStorage EscrowEvent EscrowError` instance
(`getField`/`setField`/`resolveError`/`buildEvent`) plus a hand-written `ContractErrors
EscrowError` instance, instead of `deriving`.

## Decision

Now that `exec`/`read` are black box (no event folding at all, see
[`0003`](0003-exec-read-black-box.md)), `EscrowEvent` is just `Released (amount : Wad)` — every
field/constructor across `EscrowStorage`/`EscrowError`/`EscrowEvent` is one of `Ty`'s five kinds,
so plain `deriving ContractStorage`/`ContractError`/`ContractEvent` (`Lsc/Lang/Derive.lean`) is
enough.

## Consequences

No hand-written glue remains in `examples/escrow/src/Escrow.lean`. This also relies on `deriving
ContractError`'s `fromFramework` codegen doing real per-constructor matching against
`FrameworkError`'s constructors — `EscrowError` declares a same-named constructor for `Reentrant`
and `ExternalCallFailed`, but not `Unauthorized`/`InvalidSelector` (which fall back to
`EscrowError`'s first declared constructor, `NotOwner`); a single fixed fallback couldn't express
both mappings independently at the same time.
