# Reference: `Token` — a real, generic ERC20-shaped token

Full design context: [DESIGN.md](../DESIGN.md). Canonical minimal pattern: [COUNTER.md](COUNTER.md). See also [ESCROW.md](ESCROW.md) — `Escrow.release` calls into `Token` as a genuine, black-box other contract, via `exec`/`read` (`Lang/Syntax.lean`), knowing nothing about `Token`'s internals.

Unlike this contract's earlier "two-party ledger" cut (`holderBalance`/`escrowBalance`,
`transferToEscrow`/`transferFromEscrow` — `Escrow`-specific, not a real token), `Token` now holds
a genuine address-keyed balance mapping (`Lsc.Wad.WadMap`, [Lib/Wad/Syntax.lean](../../Lsc/Lib/Wad/Syntax.lean)) and exposes the real ERC20 surface for any number of holders.

## `Token.Amount`: this token's own declared unit, not the generic `Wad`

`Token.Amount` (`declare_token_amount Amount`, [src/Token.lean](../../examples/escrow/src/Token.lean)) names *this token's own* fixed-point unit — currently 18 decimals, since this is an ordinary ERC20, but declared as its own name rather than every field/parameter spelling out the generic `Wad` directly. `balances`/`totalSupply`/`transfer`/`mint`/`balanceOf` are all typed `Token.Amount`, not `Wad`, so any other contract moving `Token` balances (e.g. [`Escrow`](ESCROW.md)) can reference *this token's own unit* by name.

Two independent guarantees are baked into `Token.Amount`'s type, both from `Lsc.Wad.Fixed d tag` (`Lsc/Lib/Wad/Syntax.lean`):

* **Decimals.** `Wad` itself is `Lsc.Wad.Fixed 18 Untagged` — a decimals-indexed type: a hypothetical future, genuinely different-decimals token (e.g. a 6-decimals, USDC-shaped one) would declare its own `Fixed 6 _`, a **different Lean type** from `Token.Amount` whenever its decimals differ, so wiring the wrong one into a caller expecting `Token.Amount` is a compile error, not a silent unit mismatch — `Fixed.convert` is the one sanctioned, explicit way to cross between two genuinely different decimals *of the same token*. Only a `Fixed 18`-shaped type is accepted by this DSL's `tx`/storage-field grammar today (`Lsc.Deriving.fieldKindOfExpr`'s docstring) — a genuinely different-decimals token needs to be authored as a hand-written `ContractM` contract instead (tracked as a follow-up in `TODO.md`).
* **Which token.** `declare_token_amount Amount` (run inside `namespace Token`) also mints a fresh, nominal `Tag` marker type and defines `Amount := Lsc.Wad.Fixed 18 Tag`. Because `Tag` is a brand-new `inductive` unique to this `declare_token_amount` invocation, `Token.Amount` and any *other* token's `Amount` are genuinely different Lean types **even when both happen to be 18 decimals** — Lean's unifier can't equate two different inductives, so passing one token's amount where a different token's is expected is a compile error, not merely a differently-*named* but interchangeable `abbrev` for the same `Fixed 18`. This is enforced precisely at the one place mixing is otherwise possible: an `exec`/`read` cross-contract call site (see `Fixed.retag`'s docstring and `Lsc/Lang/NominalTokenTagTest.lean` for a worked positive/negative example). `Fixed.convert` deliberately stays same-tag-only — there is no generic cross-tag conversion, since swapping between two different tokens' amounts isn't a scaling operation, it needs real exchange-rate logic outside this framework's scope.

## Scope limitations (deliberate)

* **No `approve`/`transferFrom`.** The allowance half of ERC20 needs a *double*-keyed mapping
  (`address → address → Wad`); `Lsc.Wad.WadMap` only supports a single `Address` key. Shipping
  `balanceOf`/`transfer`/`mint` as the real ERC20 core, with `approve`/`transferFrom` tracked as
  a follow-up (see [`TODO.md`](../../TODO.md)), is the explicit scope this pass targets.
* **Single-field events.** `Ty`'s five DSL-level kinds support 0-or-1-argument event payloads
  (`Lang/Derive.lean`'s `getCtorFieldKind`) — the real ERC20 `Transfer(from, to, amount)`/
  `Mint(to, amount)` (2-3 args) don't fit yet, so `Token`'s `Transfer`/`Mint` events carry only
  `amount`. Widening event payloads to more than one field is tracked in `TODO.md`.
* **Owner-gated `mint`.** ERC20 itself doesn't standardize minting access control; gating on a
  fixed `owner` (exactly like `Counter`'s `pause`/`unpause`) is the simplest faithful choice.

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

derive_contract_dsl TokenStorage TokenError TokenEvent

-- Read-only query, declared with the `view` DSL grammar (`Lang/Syntax.lean`) rather than a
-- hand-written `ContractM` function. `view`'s generated `balanceOf` has exactly the shape
-- `PairM.read`'s callee argument expects, so `read Token.balanceOf(who);` (from another
-- contract) works directly. Never reverts — `σ.balances[who]` alone already reflects
-- `Wad.WadMap`'s total-function model (every address reads as `0` until written).
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

derive_contract_def "Token" TokenStorage TokenError TokenEvent
```

`balanceOf` is a `view` — the DSL's read-only, value-returning function declaration
(`Lang/Syntax.lean`). Unlike `tx`, a `view` body must end in `return e;` on every path
(`Checks.checkViewReturns`) and must never mutate storage or emit an event
(`Checks.checkViewPurity`) — enforced at `derive_contract_def`/`derive_contract` time, alongside
every other structural check. Two equivalent surface forms are supported: the expression
shorthand used above (`view name(params) : RetTy => e;`) and a block form for anything needing
`let`/`if` first (`view name(params) : RetTy { ...; return e; }`). Like `tx`, `view` compiles all
the way to bytecode — `derive_contract_def`'s selector-dispatch table routes to it exactly like an
`.external` function, except its body ends in a real ABI-encoding `RETURN` rather than `STOP`.

`transfer`/`mint` are ordinary, fully-compiled (bytecode/Yul included) `tx`s — nothing about
`Token` itself needs the cross-contract machinery; it's `Escrow.release` (`ESCROW.md`) that calls
into `Token` cross-contract, via `exec Token.transfer(..);`. There is no `require`-based balance
check on `transfer`: this grammar has no `>=`/`<=` comparison operators yet (only `==`,
`Lang/Syntax.lean`'s `lscExpr`), so "can't transfer more than you have" is instead enforced by the
checked subtraction (`-?`) itself, which reverts with `Underflow` on insufficient balance.

`Wad.WadMap` (`balances`) is modeled as a total function `Address → Wad`, not a partial
`HashMap` — every address reads as `0` until written, matching real EVM storage semantics
exactly (there is no "absent" vs. "zero" entry). `σ.field[key]` (read) and `σ.field[key] = e;`
(write) are the surface syntax for indexing it; `key` must be `msg.sender` or a bare local
identifier (a `tx` parameter or `let`-bound `Address` value) — see `Lsc.Wad.MapKey`'s docstring
for why only these two forms are supported. `σ.field[key] +=? e;`/`σ.field[key] -=? e;` (used
above) are checked-add/-sub-and-write sugar for `σ.field[key] = σ.field[key] +? e;`/
`σ.field[key] = σ.field[key] -? e;` — the same sugar (`σ.field +=? e;`/`σ.field -=? e;`) is also
available for a plain `Wei`-/`Wad`-kind scalar field, as `mint`'s `σ.totalSupply +=? amount;`
shows.

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
