# Counter

Minimal stateful contract: one `count` word. `increment` / `incrementBy` /
`decrement` / `get`. No external calls.

**Proved:** each runtime function compiles to Yul that matches the high-level
model (`counter_correct`, `counter_dispatch_correct`). No wealth theorem.

| File | Role |
|------|------|
| `Contract.lean` | Storage, events, functions, `lsc_contract` |
| `Spec.lean` | Runtime `FnDef`s used by the compiler theorems |
| `Theorems.lean` | Exported compiler instance theorems |
| `Proofs/Tx.lean` | No Tx-level wealth lemmas |
| `Proofs/Security.lean` | No security theorems |
| `Proofs/Compile.lean` | Call-free `toYulFn` proofs |
| `Proofs/EndToEnd.lean` | No bytecode wealth theorems |
