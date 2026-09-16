# WETH

Wraps the chain's native asset as an ERC-20. Storage is
`extends ERC20.Storage native`. `deposit` is payable: `ERC20.mint` then
`Deposit` (the mint also emits `Transfer` from `0`). `withdraw` burns,
`Native.send`s ETH, then emits `Withdrawal`. The six IERC20 entrypoints
are one-line re-exports of the ERC20 base.

## What is proved

- `deposit_delta` / `withdraw_delta` — storage deltas (and `nativeBalance`
  unchanged on deposit: Lean does not auto-credit `Ctx.value`).
- `transfer_conserves` — Token-style local conservation.
- `weth_exact` — `IERC20.Exact WETH.impl`; Vault/Cpamm use `.toSpec`.
- `weth_backed` — in any state the contract can actually reach, wrapped
  `totalSupply` never exceeds the native balance it holds. Deployment
  starts at supply 0; deposit credits and mints the same amount (a
  wrapping credit is a dispatcher revert); withdraw burns and sends;
  only this contract's code can move its ETH, so the environment cannot
  lower `self`'s native balance.
- `weth_no_unauthorized_extraction` — no sequence of calls by other
  parties lowers an account's wrapped balance except by the amount that
  account authorised: its own `transfer`/`withdraw`, or a `transferFrom`
  of its tokens. Only accepted calls count.

## What is assumed

- `Native.send` success is `oracle.send = some`. A reverting recipient
  reverts the withdraw with `TransferFailed`. Honest send (`DebitsOnSend`)
  debits `self`'s native balance by the sent amount.
- Incoming call value is credited onto `self` in the trace `step` before
  the body; `Tx.run` itself does not. Payable entries revert if the
  credited balance would wrap (`selfbalance() < callvalue()`).
- Model facts, not trace hypotheses: only this contract's code can move
  its ETH (environment steps do not drop `self`'s native balance);
  `sender ≠ self` (only `self`'s code can emit a message from `self`;
  nested calls are the oracle's `nested_lock_reverts`).

## Files

- `Contract.lean` — storage, events, functions, `lsc_contract`.
- `Spec.lean` — `claim`, `Auth`, `inflow`, `holdings`, `rely`, `spentCall`.
- `Theorems.lean` — exported statements.
- `Proofs/` — Tx, Implements, Security (`Inv`), Compile.
- `Tests.lean` — smoke `#guard`s and `Exact.toSpec`.
- `compiled/` — artefacts after `export_bytecode.sh`.
