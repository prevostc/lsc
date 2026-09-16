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
- `weth_no_unauthorized_extraction` — no sequence of calls by other
  parties lowers an account's wrapped balance; the only authorised
  reductions are that account's own `transfer`/`withdraw`, or a
  `transferFrom` within an allowance it granted. Environment steps may
  not drop this contract's native balance.

## What is assumed

- `Native.send` success is `oracle.send = some`. A reverting recipient
  reverts the withdraw with `TransferFailed`. Honest send (`DebitsOnSend`)
  debits `self`'s native balance by the sent amount.
- Incoming call value is credited onto `self` in the trace `step` before
  the body; `Tx.run` itself does not.

## Files

- `Contract.lean` — storage, events, functions, `lsc_contract`.
- `Spec.lean` — `Inv`, `claim`, `Auth`, `inflow`, `holdings`, `rely`.
- `Theorems.lean` — exported statements.
- `Proofs/` — Tx, Implements, Security, Compile.
- `Tests.lean` — smoke `#guard`s and `Exact.toSpec`.
- `compiled/` — artefacts after `export_bytecode.sh`.
