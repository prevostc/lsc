# 0005: The direct bytecode backend rejects constructs it can't yet lower

## Context

The direct bytecode backend (`Lsc/Compile/Bytecode/Codegen.lean`) compiles `IR` straight to flat
EVM `Instr` sequences, bypassing Yul text. Some `IR` nodes — e.g. `IR.Stmt.externalCall` and
`IR.Stmt.staticCall`, whose `CALL`/`STATICCALL` opcodes need careful stack ordering this
backend's simple per-operand `codegenExpr` shape doesn't give for free — aren't supported by
this backend yet, even though real, tested lowerings exist in the Yul backend
(`Lsc.Compile.Yul.irToYulContract`/`externalCallToYul`/`staticCallToYul`). Transient-storage
lock nodes (`checkReentrancyLock`/`setReentrancyLock`) are implemented in both backends.

## Decision

Unsupported nodes are rejected cleanly with a clear `Except.error` message pointing at the Yul
backend as the working alternative, rather than the codegen pass silently emitting wrong or
partial bytecode. This mirrors the same "reject cleanly, don't silently miscompile" precedent
already used in `Lsc/Compile/Lower.lean`.

## Consequences

Contracts that need cross-contract calls must currently compile through the Yul backend, not the
direct bytecode backend, until the bytecode backend's `externalCall`/`staticCall` support lands
(tracked in [`docs/todo/backlog.md`](../todo/backlog.md)).
