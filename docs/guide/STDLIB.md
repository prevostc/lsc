# Stdlib

Proved once, imported by examples. `Stdlib` must not import `Examples`;
`Lsc` must not import `Stdlib`.

## IERC20

`Stdlib/ERC20.lean` is the ABI (`structure IERC20 (a : Asset)`) and the
promises `IERC20.Spec` / `IERC20.Exact`. Vault and Cpamm quantify over
`IERC20.Spec` of a bound token; they do not re-prove token arithmetic.

## ERC20 base

`Stdlib/ERC20/Base.lean` is storage and code any token can extend:

- `ERC20.Storage a` — `balances`, `allowances`, `totalSupply`
- `ERC20.Fields S a` — the three lenses; `ofParent` composes a parent
  `Field S (ERC20.Storage a)` (from `structure Storage extends ERC20.Storage a`)
- `ERC20.Events` / `ERC20.Errors` — the contract supplies constructors
- six IERC20 functions (listable in `lsc_contract`) plus `@[internal]`
  `mint` / `burn` (no access control)

`deriving Fields` instances are `Field.Lawful` (get/set/set-set) and
pairwise `Field.Independent`. `ofParent` of a lawful parent is
`Fields.Lawful`. Generic proofs (`Stdlib/ERC20/BaseTheorems.lean`) take
`[Fields.Lawful F]`:

```lean
theorem exact : IERC20.Exact (ERC20.impl F)
theorem transfer_conserves … -- pair-sum of balances
theorem transferFrom_allowance / approve_sets / mint_delta / burn_delta
```

A contract re-exports the six entrypoints as one-liners
(`def transfer := ERC20.transfer erc20`) and lists those names in
`lsc_contract`. Do not list `ERC20.mint` / `ERC20.burn`; wrap them in an
entrypoint that adds access control (Token) or pairs them with native
value (WETH `deposit` / `withdraw`).

## SafeERC20, scales, shares

`SafeERC20` wrappers are `@[internal inline]`. `Scales` is `Wad`/`Ray`/`Bps`.
`Shares` is virtual-offset share conversion.
