# Vault

Single-asset vault: binds one typed ERC-20, mints shares on `deposit`, burns
on `withdraw`. Pause flag. Share conversion uses OpenZeppelin-style virtual
offset (`10^6` virtual shares and 1 virtual asset) against the live token
balance (`holdings`); there is no cached `totalAssets`. Token pull/push after
storage writes. Donations raise everyone's claim pro-rata; a donation of
size `A` costs on the order of `10^6` wei per wei a later depositor cannot
redeem (`deposit_inflation_bounded`: `10^offset · (x − r) ≤ A + 10^offset`).

**Proved:** a successful deposit credits shares and raises live holdings
(caller is not the vault: `msg : Msg w` on a reachable `State`). A
successful withdraw burns shares and lowers holdings. Share-only deltas
(`deposit_shares` / `withdraw_shares`) are over an arbitrary `World`.
In any reachable `State`, after any `Txs`, a
shareholder's shares drop by at most what they themselves redeemed
(`vault_no_unauthorized_extraction`). The vault stays solvent:
`owed ≤ holdings` (`vault_solvent`). Inflation of the share rate is
bounded as above. Honest-counterparty (`IERC20.Spec` of the bound asset)
lives in `HasDeploy` / `State` — holdings theorems do not take it as a
hypothesis. Between calls the vault's token balance
does not fall and the token's `totalSupply` view stays the same
(`HasRely`). No reentrancy is modelled.

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
