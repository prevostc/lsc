# Token

Closed ERC-20-style token: `transfer`, `approve`, `transferFrom`, `mint`,
`burn`, views. No external CALLs. Storage: owner, totalSupply, balances,
allowances.

**Proved (plain language):** a successful transfer moves the amount and
conserves the sum of the two balances. Nobody's balance falls unless they
authorised the call (`Auth`). The contract stays solvent (balances sum to
`totalSupply`). Those facts hold at `Tx.run` and on compiled runtime bytecode.
Deploy-then-runtime anti-extraction is proved for Token's constructor.

| File | Role | Depends on |
|------|------|------------|
| `Contract.lean` | Token surface + `lsc_contract` | `Lsc` |
| `Proofs.lean` | `Tx.run` lemmas | `Contract.lean` |
| `ProofsProof.lean` | Conservation proof body | `Proofs.lean` |
| `ProofsTheorems.lean` | Exported `transfer_conserves` | `ProofsProof` |
| `Security.lean` | `Inv`, `claim`, `Auth`, instances | `Proofs*` |
| `SecurityProof.lean` | Security proof bodies | `Security.lean` |
| `SecurityTheorems.lean` | Exported wealth theorems | `SecurityProof` |
| `CompileProof.lean` | S1 compiler instance proofs | `Contract.lean` |
| `CompileTheorems.lean` | Exported `token_correct` | `CompileProof` |
| `EndToEnd.lean` | Bytecode transport glue | `Compile*`, `Security*` |
| `EndToEndProof.lean` | Bytecode theorem bodies | `EndToEnd.lean` |
| `EndToEndTheorems.lean` | Exported bytecode theorems | `EndToEndProof` |
