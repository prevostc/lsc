# Counter

Minimal stateful contract: one `count` word. `increment` / `incrementBy` /
`decrement` / `get`. No external calls.

**Proved:** a successful `increment` adds one; `incrementBy n` adds `n`;
`decrement` saturates at zero; `get` returns the stored word and does not
change state. No wealth theorem.

| File | Role |
|------|------|
| `Contract.lean` | Storage, events, functions, `lsc_contract` |
| `Spec.lean` | No wealth predicates |
| `Theorems.lean` | Exported Tx-level deltas |
| `Tests.lean` | Smoke `#guard`s |
| `Proofs/Tx.lean` | `Tx.run` deltas |
| `Proofs/Security.lean` | No security theorems |
| `Proofs/Compile.lean` | Runtime `compileRuntime` witness |
| `compiled/` | Yul, labelled Asm, bytecode, ABI, heimdall decompile |
