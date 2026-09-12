# Vault

Single-asset vault: binds one `IERC20`, mints shares on `deposit`, burns on
`withdraw`. Pause flag. First mint is 1:1; later mints/redeems floor.
Token pull/push after accounting.

**Proved:** an address's redeemable assets never fall unless that address
called `withdraw`. Other depositors, pause/unpause, and views cannot debit
it. Assumed, not proved: the asset token behaves like a conforming ERC-20;
between calls the vault's token balance does not fall. The vault stays
solvent vs that token balance. Both facts at `Tx.run` and on compiled S2
runtime bytecode. The constructor binds the asset and sets the owner; it
does not CALL `decimals`.

| File | Role |
|------|------|
| `Contract.lean` | Vault surface + `lsc_contract` |
| `Spec.lean` | `claim`, `Auth`, `Inv`, codec, bytecode readers |
| `Theorems.lean` | Exported security, compiler, and bytecode theorems |
| `Proofs/Tx.lean` | `Tx.run` lemmas for deposit/withdraw/pause |
| `Proofs/Security.lean` | Invariant and authorisation instances |
| `Proofs/Compile.lean` | S2 `toYulFn_correct_ext` proofs |
| `Proofs/EndToEnd.lean` | Bytecode transport glue and proofs |
| `compiled/` | Yul, labelled Asm, bytecode, ABI, heimdall decompile |
