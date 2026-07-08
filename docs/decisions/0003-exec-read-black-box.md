# 0003: `exec`/`read` are black box, replacing the whitebox `externalCall2`

## Context

A caller invoking a cross-contract call (via `PairM`, see [`0002`](0002-pairm-cross-contract-model.md))
needs some way to observe the callee's outcome. An earlier iteration, `externalCall2`, required
the caller to supply `toErr : ErrT → Err` / `toEvent : ET → E` conversion functions — a whitebox
model where every caller had to know and convert the callee's exact error/event types.

## Decision

`exec`/`read` are black box instead:

- On success: the caller only ever observes the callee's return value.
- On failure: a single opaque `FrameworkError.ExternalCallFailed` (mapped through the caller's own
  `ContractErrors.fromFramework`) — never the callee's real `ErrT`.
- The callee's events are never folded into the caller's own event log — mirroring real EVM logs,
  where a callee's `LOG` topics are separate from the caller's ABI.

Both keywords are deliberately not named `call`/`staticcall` (which would imply exact
EVM-opcode-level semantics like gas forwarding this framework doesn't model) and not `query`
(ambiguous about whether it could still write).

## Rejected alternatives

`externalCall2`'s `using toErr, toEvent` whitebox clause was dropped: requiring every caller to
enumerate a callee's exact error/event taxonomy up front doesn't scale to composable DeFi-style
calls, and makes the caller's proofs brittle to the callee's exact error/event shape changing
later.

## Consequences

- `exec`/`read` never let a callee's failure pass through unnoticed — there is no return value a
  caller could accidentally ignore, unlike a raw Solidity `address.call(...)`'s `(bool success,
  bytes data)`. `exec_never_silently_swallows_failure`/`read_never_silently_swallows_failure`
  (`Lsc/Core/ContractM.lean`) state this as a theorem.
- Composability over precision: a caller doesn't need to enumerate every way an arbitrary callee
  could fail just to call it. The cost is that a caller can't currently prove anything conditional
  on the callee's *real* behavior (e.g. "if `Token.transfer` succeeds, `totalSupply` is
  unchanged") — see [`docs/todo/interfaces.md`](../todo/interfaces.md) for the tracked, opt-in
  richer-interface follow-up.
- The real EVM `CALL` codegen path (`externalCall`, `Lsc/Compile/IR.lean`/`Yul.lean`) additionally
  reverts on a non-compliant ERC20-style callee that returns `false` without reverting. `exec`
  elaborates to `Stmt.externalExec` and lowers through that path; the direct bytecode backend
  still rejects `externalCall`/`staticCall` nodes (see [`0005`](0005-bytecode-backend-scope.md)).
