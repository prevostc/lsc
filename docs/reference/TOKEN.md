# Reference: `Token` — a real, generic ERC20-shaped token

Full design context: [DESIGN.md](../DESIGN.md). Canonical minimal pattern: [COUNTER.md](COUNTER.md).
See also [ESCROW.md](ESCROW.md) — `Escrow.release` calls into `Token` as a genuine, black-box other
contract, via `exec`/`read`, knowing nothing about `Token`'s internals.

`Token` holds a genuine address-keyed balance mapping (`Lsc.Wad.WadMap`,
[Lib/Wad/Syntax.lean](../../Lsc/Lib/Wad/Syntax.lean)) and exposes the real ERC20 surface for any
number of holders.

## Contract

```lean
declare_token_amount Amount

structure TokenStorage where
  owner : Address := 0
  totalSupply : Amount := ⟨0⟩
  balances : Wad.WadMap := fun _ => Wad.mkNat 0
  deriving ContractStorage

inductive TokenError where
  | Overflow
  | Underflow
  | NotOwner
  deriving Repr, DecidableEq, ContractError

inductive TokenEvent where
  | Transfer (amount : Amount)
  | Mint (amount : Amount)
  deriving Repr, DecidableEq, ContractEvent

view balanceOf(who : Address) : Amount => σ.balances[who];

tx transfer(recipient : Address, amount : Amount) {
  σ.balances[msg.sender] -=? amount;
  σ.balances[recipient] +=? amount;
  emit Transfer(amount);
}

tx mint(recipient : Address, amount : Amount) {
  require (msg.sender == σ.owner) else revert NotOwner();
  σ.totalSupply +=? amount;
  σ.balances[recipient] +=? amount;
  emit Mint(amount);
}

derive_contract "Token" TokenStorage TokenError TokenEvent
```

`declare_token_amount Amount` (see [src/Token.lean](../../examples/escrow/src/Token.lean)) names
this token's own 18-decimal fixed-point unit — `Token.Amount`, not the generic `Wad` — so any other
contract moving `Token` balances (e.g. [`Escrow`](ESCROW.md)) can reference it by name. It carries
two compile-time guarantees, both from `Lsc.Wad.Fixed d tag`
([Lib/Wad/Syntax.lean](../../Lsc/Lib/Wad/Syntax.lean)): a different-decimals token would be a
genuinely different type (only `Fixed 18`-shaped tokens are supported by this DSL today — a
different-decimals token needs a hand-written `ContractM` contract, tracked in
[`docs/todo/backlog.md`](../todo/backlog.md)); and a *different* token, even at the same 18
decimals, is also a different type, since each `declare_token_amount` mints its own nominal `Tag`.
Mixing them — e.g. passing some other token's amount where `Token.Amount` is expected at an
`exec`/`read` call site — is a compile error, not a silent unit-confusion bug (see
`Lsc/Lang/NominalTokenTagTest.lean` for a worked example). `Fixed.convert` is the one sanctioned way
to cross between two different decimals *of the same token*; there is no cross-*token* conversion,
since that needs real exchange-rate logic outside this framework's scope.

`balanceOf` is a `view` — the DSL's read-only, value-returning declaration form (see
`Lsc/Lang/Syntax.lean`), enforced to never mutate storage/emit events and to always `return` on
every path. `transfer`/`mint` are ordinary `tx`s, fully compiled to bytecode/Yul; nothing about
`Token` itself needs the cross-contract machinery — it's `Escrow.release` that calls into it (see
[ESCROW.md](ESCROW.md)). There's no `require`-based balance check on `transfer`: this grammar has
no `>=`/`<=` yet, so insufficient balance is instead caught by the checked subtraction (`-?`)
itself, reverting with `Underflow`.

## Scope limitations (deliberate)

* **No `approve`/`transferFrom`.** The allowance half of ERC20 needs a double-keyed mapping
  (`address → address → Wad`); `Lsc.Wad.WadMap` only supports a single `Address` key. Tracked in
  [`docs/todo/backlog.md`](../todo/backlog.md).
* **Single-field events.** DSL event payloads support 0-or-1 arguments today, so `Transfer`/`Mint`
  carry only `amount`, not the real ERC20 `(from, to, amount)`. Tracked in
  [`docs/todo/backlog.md`](../todo/backlog.md).
* **Owner-gated `mint`.** ERC20 itself doesn't standardize minting access control; gating on a
  fixed `owner` (like `Counter`'s `pause`/`unpause`) is the simplest faithful choice.

## Role in cross-contract proofs (`HonestERC20`)

`Token` is the **reference callee** for the escrow example — not a stand-in for every on-chain
ERC20. It witnesses that [`HonestERC20`](../decisions/0009-ierc20-interface-honest-assumptions.md)
(`Lsc/Lib/Interfaces/IERC20.lean`) is satisfiable:

* `examples/escrow/test/TokenHonest.lean` — `instance : HonestERC20 TokenStorage` from
  `EscrowProofs.runTransferOk` (mechanical, not assumed).
* Escrow calls the on-chain token via `exec σ.token.transfer(..)` (interface-typed storage field),
  not `exec Token.transfer(..)`. Tier-B balance theorems for arbitrary tokens require
  `[HonestERC20 T]`; the reference `Token` corollaries show the instance for the co-developed token.

Excluded from `HonestERC20`: fee-on-transfer, rebasing, callback/reentrancy hooks — see ADR 0009.

## Required theorems

Two-tier proof style (`docs/DESIGN.md`'s "state it like a human first" invariant): Tier 1
(`examples/escrow/test/TokenProofs.lean`) fully characterizes each function's outcome, universally
quantified over every state/address/amount; Tier 2 (`examples/escrow/test/TokenTheorem.lean`)
states the actual required properties as short, plainly-readable corollaries — no `native_decide`,
no concrete witness states.

| Theorem | Technique |
|---------|-----------|
| `TokenProofs.runBalanceOfOk` | Tier 1 — `simp`, characterizes `balanceOf` for every state/address |
| `TokenProofs.runTransferOk` | Tier 1 — `simp`, characterizes `transfer` for all addresses `a` at once |
| `TokenProofs.runTransferErr` | Tier 1 — `simp` + `Wad.subChecked_eq_error_of` |
| `TokenProofs.runMintOk` | Tier 1 — `simp`, characterizes `mint`'s `totalSupply`/balance/other-addresses effect |
| `TokenProofs.runMintErrNotOwner` | Tier 1 — direct `simp` |
| `TokenProofs.runMintErrOverflow` | Tier 1 — `simp` + `Wad.addChecked_eq_error_of` |
| `balanceOf_returns_stored_balance` | Tier 2 — corollary of `runBalanceOfOk` |
| `balanceOf_zero_by_default` | Tier 2 — corollary of `runBalanceOfOk`, instantiated at `zeroBalances` |
| `transfer_debits_sender` | Tier 2 — corollary of `runTransferOk`, instantiated at the caller's address |
| `transfer_credits_recipient` | Tier 2 — corollary of `runTransferOk`, instantiated at the recipient's address |
| `transfer_preserves_other_balances` | Tier 2 — corollary of `runTransferOk`, instantiated at any other address |
| `transfer_self_transfer_is_noop` | Tier 2 — corollary of `runTransferOk`, degenerate `recipient = caller` edge case |
| `transfer_reverts_on_insufficient_balance` | Tier 2 — corollary of `runTransferErr` |
| `mint_increases_total_supply` | Tier 2 — corollary of `runMintOk` |
| `mint_increases_recipient_balance` | Tier 2 — corollary of `runMintOk` |
| `mint_preserves_other_balances` | Tier 2 — corollary of `runMintOk` |
| `mint_reverts_for_non_owner` | Tier 2 — corollary of `runMintErrNotOwner` |
| `mint_reverts_on_overflow` | Tier 2 — corollary of `runMintErrOverflow` |

Note `ContractState TokenStorage` itself isn't `DecidableEq` (`balances` is a function, `Address →
Wad`), so proofs project out only the specific fields under test (`Except.map`) rather than
comparing whole post-states, as any test touching `balances` already had to.
