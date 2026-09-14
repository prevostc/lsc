# Vault

Single-asset vault: binds one typed ERC-20, mints shares on `deposit`, burns
on `withdraw`. Pause flag. First mint is 1:1; later mints/redeems floor.
The exchange rate is the live token balance (`holdings`); there is no
cached `totalAssets`. Token pull/push after storage writes. Donations raise
everyone's claim pro-rata; first-depositor inflation is not prevented by
this contract.

**Proved:** a successful deposit credits shares and raises live holdings (when
the caller is not the vault). A successful withdraw burns shares and lowers
holdings. An address's redeemable assets never fall unless that address
called `withdraw`. The vault stays solvent vs its live token balance.
Assumed of the token: it is a conforming ERC-20 per `IERC20.Spec`; no
reentrancy is modelled. Between calls the vault's token balance does not
fall and the token's `totalSupply` view stays the same.

| File | Role |
|------|------|
| `Contract.lean` | Vault surface + schema + `lsc_contract` |
| `Spec.lean` | `claim`, `Auth`, `Inv`, `holdings`, `vaultRely` |
| `Theorems.lean` | Exported Tx deltas and security theorems |
| `Proofs/Tx.lean` | `Tx.run` lemmas for deposit/withdraw/pause |
| `Proofs/Security.lean` | Invariant and authorisation instances |
| `Proofs/Compile.lean` | Runtime `compileRuntime` witness |
| `Tests.lean` | Smoke `#guard`s |
| `compiled/` | Yul, labelled Asm, bytecode, ABI, heimdall decompile |
