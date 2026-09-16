# WETH

Wraps the chain's native asset as an ERC-20. The native asset comes from
the `Chain` profile, so the same contract is a wrapped-native token on
any profile. This copy uses Ethereum ETH (18 decimals). `deposit` is
payable and credits `msg.value`. `withdraw` burns wrapped tokens and
`Native.send`s ETH to the caller.

## What is proved

- `deposit_delta` / `withdraw_delta` — storage deltas (and `nativeBalance`
  unchanged on deposit: Lean does not auto-credit `Ctx.value`).
- `transfer_conserves` — Token-style local conservation.
- `weth_exact` — `IERC20.Exact WETH.impl`; Vault/Cpamm use `.toSpec`.
- `weth_backed` — `Inv` implies `totalSupply ≤` self's native balance.

## What is assumed

- `Native.send` success is `oracle.send = some`. A reverting recipient
  reverts the withdraw with `TransferFailed`.
- Native ETH of `self` is not a Wealth `Claim`. The trace credits
  incoming value before the body; `Tx.run` does not.

## Files

- `Contract.lean` — storage, events, functions, `lsc_contract`.
- `Spec.lean` — `Inv`, `claim`, `Auth`, `inflow`, `holdings`.
- `Theorems.lean` — exported statements.
- `Proofs/` — Tx, Implements, Compile.
- `Tests.lean` — smoke `#guard`s and `Exact.toSpec`.
- `compiled/` — artefacts after `export_bytecode.sh`.
