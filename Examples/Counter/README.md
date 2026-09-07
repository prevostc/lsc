# Counter

Minimal stateful contract: one `count` word. `increment` / `incrementBy` /
`decrement` / `get`. No external calls.

**Proved:** each runtime function compiles to Yul that matches `Core.denote`
(`counter_correct`, `counter_dispatch_correct`). No wealth/security theorem.

| File | Role | Depends on |
|------|------|------------|
| `Contract.lean` | Storage, events, functions, `lsc_contract` | `Lsc` |
| `CompileDefs.lean` | FnDef abbreviations | `Contract.lean` |
| `CompileProof.lean` | Call-free compiler instance proofs | `CompileDefs`, `Contract` |
| `CompileTheorems.lean` | Exported `counter_*_correct` | `CompileProof` |
