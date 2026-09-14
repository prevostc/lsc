# Security model

The headline guarantee is victim-side: **nobody can reduce your protocol
claim without your authorisation**, and **the contract does not owe more
than it holds**.

## What you declare

For each contract:

- **Invariant** — what must stay true (Token: balances sum to total supply
  on a finite support; Vault: share accounting; Cpamm: each reserve plus
  protocol bucket is covered by the live token balance, plus share
  accounting).
- **Claim** — what the protocol owes each account (Token: ERC-20 balance;
  Vault: pro-rata redeemable assets; Cpamm: LP share count for extraction,
  pro-rata reserves for solvency).
- **Auth** — who may reduce whose claim (Token: sender of `transfer`/`burn`,
  or a `transferFrom` within allowance; Vault: only that account's
  `withdraw`; Cpamm: only that account's `removeLiquidity`).
- **Holdings** — assets the contract actually controls (Token: recorded
  total supply; Vault/Cpamm: live `tok.balanceOf` via `IERC20.Impl`).

`lsc_contract` generates per-entrypoint obligations: the invariant is
preserved; a claim falls only when `Auth` says so; optionally, claims are
conserved up to inflow. Conservation is optional when solvency already
follows from the invariant (Vault: floor-rounded pro-rata claims are not
conservative per step; solvency is the statement that matters). One extra
obligation: the invariant is preserved by environment steps that obey
`vaultRely` / `cpammRely` (live token `balanceOf` does not fall).

## What the generic theorems say

If those local facts hold, then:

- An account that authorised no call never sees its claim fall. The
  unrestricted theorem does not require the caller to differ from the
  contract.
- If the invariant implies solvency, solvency still holds after any
  well-formed trace. Vault and Cpamm use the `_at` variants, which do
  require well-formedness (caller ≠ contract), because their invariant
  talks about this contract's token balance.
- The invariant itself still holds along a well-formed trace.

A reverted call leaves the world unchanged. Constructors are not trace
steps; deployment from empty storage is a separate `init` fact when proved.

## What the adversary may do

Any addresses may call any entrypoint with any arguments, in any order,
interleaved with honest calls — sandwich of *our* calls is this
quantifier (`run` in `Trace.lean`, `no_unauthorized_extraction`). Between our
calls, the environment may update `ext` only in ways `vaultRely` /
`cpammRely` allow (our token `balanceOf` does not fall; `totalSupply`
stays put). Well-formedness — callers are not the contract itself — is
required for invariant and solvency preservation and for the `_at`
extraction theorems (Vault, Cpamm), not for Token-style unrestricted
extraction.

Token, Vault, and Cpamm instantiate this at the spec. The compiler lifts
a trace fact onto bytecode with `transport_claim_ext` /
`transport_exists_claim_ext`; examples do not ship `*_bytecode_*` theorems.

## Out of scope

Private-key compromise, block-producer ordering across *other* contracts,
gas griefing of *our* execution, and token behaviour excluded by the
external-call hypotheses (fee-on-transfer, down-rebasing, ERC-777 hooks).
Blacklist,
pause, revert-on-zero, callee out-of-gas, and allowance shortfall are in
scope: they are treated as a failed external call that reverts us.

`claim` measures what the protocol owes, not the caller's external wallet.
A deposit that would mint zero shares is a caller loss the claim does not
see; Vault and Cpamm `require` a positive mint/burn to exclude that.

---

For the curious: the theorems behind this are `no_unauthorized_extraction`
and `solvent_run` (with `inv_run` for the invariant).
