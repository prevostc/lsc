# Security model

The headline guarantee is victim-side: **nobody can reduce your protocol
claim without your authorisation**, and **the contract does not owe more
than it holds**, along any well-formed sequence of calls.

## What you declare

For each contract:

- **Invariant** — what must stay true (Token: balances sum to total supply
  on a finite support; Vault: share accounting, and the vault's token
  balance covers `totalAssets`; AMM: each reserve is covered by the
  corresponding token balance, plus share accounting).
- **Claim** — what the protocol owes each account (Token: ERC-20 balance;
  Vault: pro-rata redeemable assets; AMM: LP share count for extraction,
  pro-rata reserves for solvency).
- **Auth** — who may reduce whose claim (Token: sender of `transfer`/`burn`,
  or a `transferFrom` within allowance; Vault: only that account's
  `withdraw`; AMM: only that account's `removeLiquidity`).
- **Holdings** — assets the contract actually controls (Token: recorded
  total supply; Vault/AMM: ghost ERC-20 balance of the contract).

`lsc_contract` generates per-entrypoint obligations: the invariant is
preserved; a claim falls only when `Auth` says so; optionally, claims are
conserved up to inflow. Conservation is optional when solvency already
follows from the invariant (Vault: floor-rounded pro-rata claims are not
conservative per step; solvency is the statement that matters). One extra
obligation: the invariant is preserved by environment steps that obey the
token `Rely`.

## What the generic theorems say

If those local facts hold, then on every well-formed trace:

- An account that authorised no call never sees its claim fall.
- If the invariant implies solvency, solvency still holds after the trace.
- The invariant itself still holds.

A reverted call leaves the world unchanged. Constructors are not trace
steps; deployment from empty storage is a separate `init` fact when proved.

## What the adversary may do

Any addresses may call any entrypoint with any arguments, in any order,
interleaved with honest calls. Between our calls, the environment may
update external ghosts only in ways the token `Rely` allows (our token
balance does not fall; `decimals` stay put). Traces are well-formed:
callers are not the contract itself.

Token, Vault, and AMM instantiate this at the spec. Token and Vault also
have it on compiled runtime bytecode. AMM has unauthorised-extraction on
bytecode; solvency stays at the spec.

## Out of scope

Private-key compromise, block-producer ordering / MEV, gas griefing of
*our* execution, and token behaviour excluded by the external-call
hypotheses (fee-on-transfer, down-rebasing, ERC-777 hooks). Blacklist,
pause, revert-on-zero, callee out-of-gas, and allowance shortfall are in
scope: they are treated as a failed external call that reverts us.

`claim` measures what the protocol owes, not the caller's external wallet.
A deposit that would mint zero shares is a caller loss the claim does not
see; Vault and AMM `require` a positive mint/burn to exclude that.

---

For the curious: the theorems behind this are `no_unauthorized_extraction`
and `solvent_run` (with `inv_run` for the invariant).
