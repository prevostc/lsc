# Token

Closed ERC-20-style token: `transfer`, `approve`, `transferFrom`, `mint`,
`burn`, views. No external CALLs. Storage: owner, totalSupply, balances,
allowances.

**Proved:** a successful transfer conserves the sum of the two balances (no
tokens created or destroyed). Nobody's balance falls unless they authorised
the call. Recorded balances still sum to `totalSupply` after any well-formed
trace. Those facts hold at `Tx.run` and on compiled runtime bytecode.
Deploy-then-runtime anti-extraction is proved for Token's constructor.

| File | Role |
|------|------|
| `Contract.lean` | Token surface + `lsc_contract` |
| `Spec.lean` | `claim`, `Auth`, `Inv`, codec |
| `Theorems.lean` | Exported Tx, security, compiler, and bytecode theorems |
| `Proofs/Tx.lean` | `Tx.run` lemmas and `transfer_conserves` |
| `Proofs/Security.lean` | Auth/conservation/invariant instances |
| `Proofs/Compile.lean` | Call-free compiler instance |
| `Proofs/EndToEnd.lean` | Bytecode transport glue and proofs |
| `compiled/` | Yul, labelled Asm, bytecode, ABI, heimdall decompile |
