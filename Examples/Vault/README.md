# Vault

Single-asset vault: binds one `IERC20`, mints shares on `deposit`, burns on
`withdraw`. Pause flag. First mint is 1:1; later mints/redeems floor
(`mulDivDown`). Token pull/push after accounting.

**Proved:** an address's share count never falls unless that address called
`withdraw`. The vault stays solvent vs the token ghost. Both facts at
`Tx.run` and on compiled S2 runtime bytecode (one binding). Constructor
calls `decimals` and is outside the EVM deploy theorem.

| File | Role | Depends on |
|------|------|------------|
| `Contract.lean` | Vault surface + `lsc_contract` | `Lsc`, `Stdlib.ERC20`, `Stdlib.Scales` |
| `Proofs.lean` | `Tx.run` lemmas | `Contract.lean` |
| `Security.lean` | `Inv`, `claim`, `Auth`, holdings | `Proofs.lean` |
| `SecurityProof.lean` | Security proof bodies | `Security.lean` |
| `SecurityTheorems.lean` | Exported wealth theorems | `SecurityProof` |
| `CompileProof.lean` | S2 `toYulFn_correct_ext` proofs | `Contract.lean` |
| `CompileTheorems.lean` | Exported `vault_correct_ext` | `CompileProof` |
| `EndToEnd.lean` | Bytecode transport glue | `Compile*`, `Security*` |
| `EndToEndProof.lean` | Bytecode theorem bodies | `EndToEnd.lean` |
| `EndToEndTheorems.lean` | Exported bytecode theorems | `EndToEndProof` |
