# 0005: The direct bytecode backend rejects constructs it can't yet lower

## Context

The direct bytecode backend (`Lsc/Compile/Bytecode/Codegen.lean`) compiles `IR` straight to flat
EVM `Instr` sequences, bypassing Yul text. Some `IR` nodes — e.g. `IR.Stmt.safeExternalCall`,
whose `CALL` opcode needs 7 stack arguments in a careful DUP-free order this backend's simple
per-operand `codegenExpr` shape doesn't give for free — aren't supported by this backend yet,
even though a real, tested lowering for the same node exists in the Yul backend
(`Lsc.Compile.Yul.irToYulContract`/`safeExternalCallToYul`).

## Decision

Unsupported nodes are rejected cleanly with a clear `Except.error` message pointing at the Yul
backend as the working alternative, rather than the codegen pass silently emitting wrong or
partial bytecode. This mirrors the same "reject cleanly, don't silently miscompile" precedent
already used in `Lsc/Compile/Lower.lean`.

## Consequences

Contracts that need cross-contract calls must currently compile through the Yul backend, not the
direct bytecode backend, until the bytecode backend's `safeExternalCall` support lands (tracked in
[`docs/todo/backlog.md`](../todo/backlog.md)).
