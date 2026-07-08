# 0002: Cross-contract calls use a statically-typed `PairM`, not a general N-contract registry

## Context

A contract sometimes needs to call into a genuinely different contract, with its own storage,
event, and error types (`T`/`ET`/`ErrT`, distinct from the caller's `S`/`E`/`Err`) — e.g.
`Escrow.release` calling into `Token.transfer`.

## Decision

`PairM S T E Err A` threads an explicit **pair of states**, `ContractState S × ContractState T`,
through the whole transaction, for a caller contract that is specifically written to call one
named other contract type. `exec`/`read` are the pair-level primitives that invoke the callee's
`ContractM T ET ErrT A` computation.

## Rejected alternatives

A full `WorldSpec`/address-book/ABI-encoded-calldata dispatch layer — a general,
address-indexed N-contract registry (`WorldSpec`/`HonestWorld`-style), matching real EVM `CALL`
semantics with an arbitrary runtime target address — was considered and explicitly deferred. It
would let a caller dispatch to any address at runtime, but requires machinery (address book, ABI
encoding, an abstract `dispatch_not_reentrant` framework theorem) that doesn't exist yet. See
[`docs/todo/backlog.md`](../todo/backlog.md) for the tracked follow-up.

## Consequences

- `PairM` only supports a *statically fixed pair* of concrete contract types chosen by the
  contract author (e.g. `Escrow` hard-codes `T := Token.TokenStorage`) — no address book, no
  ABI-encoded calldata, no EVM `CALL` opcode codegen for this path yet (`Lsc/Compile/Lower.lean`
  has no representation for a second contract's storage type).
- Because the callee's type `ContractM T ET ErrT A` has no way to mention `S`, `PairM`, `exec`,
  or `read`, it is architecturally impossible for a callee written this way to call back into the
  caller — reentrancy across `PairM` calls is ruled out structurally, not just guarded (see
  [`0003`](0003-exec-read-black-box.md) for the residual guard that's still needed).
- Follow-up: once a real N-contract registry exists, callee addresses can be resolved beyond the
  v1 `token : Address` storage-field convention — tracked in
  [`docs/todo/interfaces.md`](../todo/interfaces.md). `exec`/`read` already lower to
  `IR.externalCall`/`IR.staticCall` via Yul (`SafeExternalCallTest.lean`, `StaticCallTest.lean`).
