# Reference: `Escrow` — a real, black-box cross-contract call

Full design context: [DESIGN.md](../DESIGN.md). Depends on [TOKEN.md](TOKEN.md) — `Escrow.release`
makes a genuine cross-contract call into `Token`, using `Lsc.ContractM.PairM`
(`Lsc/Core/ContractM.lean`) via the real `exec`/`read` surface syntax (`Lsc/Lang/Syntax.lean`).

## The `PairM` combinator

`ContractM.externalCall`/`Stmt.externalCall`/`externalCall { .. }` (a toy, since deleted: the
"callee" ran on the *same* storage type `S` as the caller — never a genuinely different
contract) has been fully replaced by `PairM`, which threads an explicit **pair** of concrete
storage types through a transaction:

```lean
def PairM (S T E Err : Type) (A : Type) : Type :=
  ContractState S → ContractState T →
    Except Err (A × ContractState S × ContractState T × List E)

def PairM.exec [ContractErrors Err] {ET ErrT : Type} (callee : ContractM T ET ErrT A) :
    PairM S T E Err A

def PairM.read [ContractErrors Err] {ET ErrT : Type} (callee : ContractM T ET ErrT A) :
    PairM S T E Err A
```

`S`/`E`/`Err` are the caller's storage/event/error types; `T`/`ET`/`ErrT` are the callee's — a
genuinely *different* contract, with its own storage and its own event/error types.
`PairM.liftCaller`/`PairM.liftCallee` lift a plain `ContractM` computation from either side into
`PairM`, so a `PairM` `do`-block can freely mix "do something to my own storage" and "invoke the
other contract" steps.

## Black box, not whitebox: no `toErr`/`toEvent`

An earlier iteration of this design (`externalCall2`) required the caller to supply
`toErr : ErrT → Err`/`toEvent : ET → E` conversion functions, forcing every caller to know and
convert the callee's *exact* error/event types — a whitebox model. `exec`/`read` are
deliberately **black box** instead (composability over precision, matching how real
cross-contract DeFi calls are reasoned about — a callee can fail in ways the caller never
enumerated up front):

* On success: the caller only ever observes the callee's return value `A`.
* On failure: a single opaque `FrameworkError.ExternalCallFailed` (mapped through the caller's own
  `ContractErrors.fromFramework`, exactly like `Reentrant`/`Unauthorized`/`InvalidSelector`) —
  never the callee's real `ErrT`.
* The callee's events are never folded into the caller's own typed event log — mirroring real EVM
  logs, where a callee's `LOG` topics are separate from the caller's ABI, not re-emitted under it.

**Safe by default, made explicit.** `exec`/`read` never let a callee's failure pass through
unnoticed — there is no return value a caller could accidentally ignore, unlike a raw Solidity
`address.call(...)`'s `(bool success, bytes data)`. `Lsc.ContractM.exec_never_silently_swallows_failure`/
`read_never_silently_swallows_failure` (`Lsc/Core/ContractM.lean`) state this as a real theorem:
every call either fully succeeds or aborts the caller's whole `tx` via `Except.error`, with no
third "the call happened but nobody checked" outcome reachable at all. The real EVM `CALL`
codegen path below additionally reverts on a non-compliant ERC20-style callee that returns
`false` without reverting (the actual scenario OpenZeppelin's `SafeERC20.safeTransfer` exists to
reject) — but that is a plain, untagged EVM revert today, with no Lean-level `FrameworkError`
counterpart, since `exec`/`read` aren't wired to that codegen path yet (see "Follow-ups" below).

This is what makes `Escrow` fully decoupled from `Token`'s internals: no `TokenNotified` event
wrapper, no `tokenErrToEscrowErr`/`tokenEvToEscrowEvent` glue — `Escrow`'s own `EscrowError`/
`EscrowEvent` never need to mention `Token.TokenError`/`Token.TokenEvent` at all.

`read` is `exec`'s read-only twin: it still actually runs the callee against the current callee
state, but discards any resulting state change and events afterward — only the return value `A`
survives into the caller's `PairM`. `Escrow` doesn't need `read` (`release` genuinely mutates
`Token`'s balances), but a hypothetical `previewRelease` view function would use it to call
`Token.balanceOf` without any risk of it durably mutating `Token`'s storage.

## Scope: one specific, statically-named callee — not a registry

`PairM`/`exec`/`read` support a **statically fixed pair** of concrete contract types chosen by
the contract author (`Escrow` hard-codes `T := Token.TokenStorage`), not a general
address-indexed N-contract world. There is no address book, no ABI-encoded calldata, and no EVM
`CALL` opcode codegen for this yet (`Lsc/Compile/Lower.lean` has no representation for a second
contract's storage type). A real address-based, ABI-encoded, N-contract dispatch registry
(`WorldSpec`/`HonestWorld`-style) is deliberately out of scope here — the abstract
`dispatch_not_reentrant` framework theorem is deferred to that later step, per the project plan.
See also `docs/reference/INTERFACES.md` for a related, also-deferred idea: an opt-in way for a
caller to declare (and get to assume, for stronger proofs) a *richer* spec for a known callee,
rather than staying fully black box.

## Surface syntax: real `tx { .. }` grammar, not a hand-written `PairM` `do`-block

`exec`/`read` *do* fit into ordinary `tx { .. }` syntax now — no more hand-authored `PairM`
`do`-blocks. `Lsc.Syntax.stmtsUseExecOrRead` scans a `tx`'s body (before elaboration) for either
keyword; if found, `tx`'s elaborator (a) requires `@nonreentrant` immediately (a cross-contract
`tx` is never added to the caller's own `ContractDef.functions` — see
`Lsc.Deriving.contractCrossCallExt`'s docstring — so ordinary `@nonreentrant`
runtime-lock-based reentrancy protection is the only guard that still applies to it), and (b)
elaborates the whole body to a `PairM S T E Err Unit`-valued `def` via
`Lsc.Syntax.elabStmtListPairM`, instead of the usual `Lsc.Stmt`-valued one:

```lean
@nonreentrant
tx release(recipient : Address, amount : Token.Amount) {
  require (msg.sender == σ.owner) else revert NotOwner();
  exec Token.transfer(recipient, amount);
  let r = σ.released +? amount;
  σ.released = r;
  emit Released(amount);
}
```

`amount`'s type is `Token.Amount` (imported from `Token`, see [TOKEN.md](TOKEN.md)), not the
generic `Wad` — likewise `EscrowStorage.released` and `EscrowEvent.Released`'s payload. Because
`Token.Amount` is `declare_token_amount`'s nominal `Fixed 18 Token.Tag` (not merely a same-shape
`abbrev`), this type-checks *against that specific token's own declared unit* two ways at once:
against a future, genuinely different-decimals token (a decimals mismatch would be a compile
error, not a silent unit-confusion bug — `Fixed.convert` is the one sanctioned, explicit way to
cross between two genuinely different decimals *of the same token*), and against any *other*,
even same-decimals, token — passing some other token's `Amount` into `release`/`exec
Token.transfer(..)` is rejected at compile time, since Lean's unifier can't equate `Token.Tag`
with a different token's own fresh `Tag` inductive. This is enforced at exactly this boundary —
the callee's real, callable `def` for a cross-contract-called `tx` (here `Token.transfer`'s
`.Typed` companion, `Token.transferTyped`) is generated with the *author's own declared*
parameter types, not `Token.transfer`'s own generic-`Wad` signature (needed so `Token.transfer`
itself stays callable with plain, untagged `Wad` literals from same-contract code, e.g.
`TokenTheorem.lean`) — see `Lsc.Wad.Fixed`'s docstring
([Lib/Wad/Syntax.lean](../../Lsc/Lib/Wad/Syntax.lean)) and
`Lsc/Lang/NominalTokenTagTest.lean` for a worked positive/negative example.

`exec Target.fn(args);`/`read Target.fn(args);` name the target contract's real `tx`-derived
function directly (dotted `Token.transfer`, lexed as one token exactly like
`σ.field`/`msg.sender`), with plain identifiers as arguments (real Lean values — `tx`
parameters/locals, not `lscExpr` AST nodes). `T`/`ET`/`ErrT` (the callee's storage/event/error
types) are never named in the `tx` body at all — inferred purely by Lean unification (helped by
marking `E`/`Err` as `outParam` on `ContractDSL`, so the caller's own `S → E`/`Err` link stays
resolvable even though a cross-contract `tx` has no ordinary-segment-only inference path).

Because `Lsc/Compile/*` still has no representation for a second contract's storage type,
`release` is deliberately *not* part of `Escrow`'s `ContractDef`/bytecode/Yul output — wiring it
end-to-end through real EVM `CALL` codegen remains a documented follow-up (see below). Its
Lean-level semantics are real regardless: fully executable, and proved correct in
`examples/escrow/test/EscrowTheorem.lean`.

A real, tested `IR.Stmt.safeExternalCall` node/Yul lowering for the `CALL` opcode itself already
exists (`Lsc/Compile/IR.lean`/`Lsc/Compile/Yul.lean`'s `safeExternalCallToYul`,
`Lsc/Compile/SafeExternalCallTest.lean`) — **safe by construction, no opt-out**: there is no
lower-level "raw call" primitive in the codegen pipeline a contract author could reach instead,
so its generated Yul always includes `iszero(success) { revert(0, 0) }`, and (when the callee's
declared return type is `bool`, the ERC20 `transfer`/`transferFrom` convention) additionally
decodes the returned word and reverts if it is `false` — unless the callee returned *no* data at
all, which is treated as success (matching real-world tokens that omit the return value, the
other half of OpenZeppelin's `SafeERC20.safeTransfer` compatibility shim). This revert is plain
and untagged today (no distinguishable Lean-level error), since what's still missing is the glue
connecting this node to real `exec`/`read` surface syntax: ABI-encoding a specific `tx`'s real
arguments into calldata, and picking the right target address — the general, address-indexed
N-contract dispatch registry item below. Once that glue exists, a real Lean-level signal for this
case (not necessarily a `FrameworkError` case — see `TODO.md`) should be (re-)designed then.

## Reentrancy: structural, not just guarded

`Token.transfer`'s type (`Address → Wad → Lsc.Stmt`, i.e. `Token.TokenM Unit = ContractM
Token.TokenStorage Token.TokenEvent Token.TokenError Unit` once evaluated) has no way to mention
`EscrowStorage`, `PairM`, or `exec`/`read` at all — there is no nested cross-contract call a
hostile `Token` could even attempt to write down. Real reentrancy into `Escrow` *during*
`Token`'s execution is therefore ruled out by construction, not merely by a runtime lock check.
`exec`/`read` still carry the same `locked`-flag guard `ContractM.externalCall` used, both for
uniformity and to cover the one residual case this model doesn't rule out structurally:
`release` being invoked while `Escrow`'s own state is already `locked` (e.g. via some future,
more general dispatch path that could reenter `Escrow` itself). `release_rejects_when_already_locked`
proves exactly this.

## No hand-written `ContractDSL` boilerplate

Earlier, `EscrowEvent` carried a foreign `Token.TokenEvent` payload (`TokenNotified`), which made
`EscrowStorage`/`EscrowError`/`EscrowEvent` *not* fully DSL-representable, forcing a hand-written
`ContractDSL EscrowStorage EscrowEvent EscrowError` instance (`getField`/`setField`/
`resolveError`/`buildEvent`) plus a hand-written `ContractErrors EscrowError` instance. Now that
`exec`/`read` are black box (no event folding at all), `EscrowEvent` is just `Released (amount :
Wad)` — every field/constructor across `EscrowStorage`/`EscrowError`/`EscrowEvent` is one of
`Ty`'s five kinds, so plain `deriving ContractStorage`/`ContractError`/`ContractEvent` (`Lsc/Lang/
Derive.lean`) are enough; no hand-written glue remains in `examples/escrow/src/Escrow.lean`.

This also relies on `deriving ContractError`'s `fromFramework` codegen doing real
**per-constructor** matching against `FrameworkError`'s constructors
(`Reentrant`/`Unauthorized`/`InvalidSelector`/`ExternalCallFailed`) —
`EscrowError` declares a same-named constructor for each of `Reentrant` and `ExternalCallFailed`,
but not `Unauthorized`/`InvalidSelector` (which fall back to
`EscrowError`'s first declared constructor, `NotOwner`); a single fixed fallback (the old
algorithm) couldn't express "`Reentrant`→`Reentrant` *and* `ExternalCallFailed`→
`ExternalCallFailed`, independently" at the same time.

## Required theorems

Two tiers, mirroring `examples/interest/test/InterestProofs.lean`/`InterestTheorems.lean`:
`examples/escrow/test/EscrowProofs.lean` characterizes `release`'s/`Token.transferTyped`'s exact
`PairM`/`ContractM` execution (once, compositionally, via `simp` and `PairM.exec_unlocked_ok`);
`examples/escrow/test/EscrowTheorem.lean` then states the required properties as short
corollaries — universally quantified over **every** address and amount, not concrete witness
states.

| Theorem | Technique |
|---------|-----------|
| `EscrowProofs.runTransferOk` | Tier 1 — `simp`, characterizes `Token.transferTyped` for all addresses `a` at once |
| `EscrowProofs.runReleaseOk` | Tier 1 — `simp` + `PairM.exec_unlocked_ok` composed with `runTransferOk` |
| `release_increases_released` | Tier 2 — corollary of `runReleaseOk` |
| `release_debits_escrow` | Tier 2 — corollary of `runReleaseOk`, instantiated at the escrow's own address |
| `release_credits_recipient` | Tier 2 — corollary of `runReleaseOk`, instantiated at the recipient's address |
| `release_preserves_other_balances` | Tier 2 — corollary of `runReleaseOk`, instantiated at any other address |
| `release_self_release_is_noop` | Tier 2 — corollary of `runReleaseOk`, degenerate `escrowAddr = recipient` edge case |
| `release_emits_released` | Tier 2 — corollary of `runReleaseOk` |
| `release_rejects_non_owner` | Direct `simp`, no success-path setup needed |
| `release_rejects_when_already_locked` | Direct `simp`, no success-path setup needed |

Proved in `examples/escrow/test/EscrowProofs.lean`/`EscrowTheorem.lean` against
`examples/escrow/src/Escrow.lean`, zero `sorry`s, zero `native_decide`.

## Follow-ups (explicitly out of scope here)

* Wiring `exec`/`read` end-to-end to the real `IR.Stmt.safeExternalCall`/Yul codegen that already
  exists (`Lsc/Compile/IR.lean`/`Yul.lean`): extend `Lsc/Compile/Lower.lean` to lower a
  cross-contract `tx` for a genuinely two-contract `ContractDef`, and add real ABI-encoded
  calldata generation for a `tx`'s actual arguments (today's node takes an already-encoded
  calldata span) — `release`'s *Lean-level* semantics are real and proved correct today; only
  this bytecode integration remains.
* A general, address-indexed N-contract dispatch registry (replacing "one statically-named
  callee type" with a real address book + ABI-encoded calldata).
* The abstract `dispatch_not_reentrant` framework-level theorem (deferred until the registry
  above exists) — `release_rejects_when_already_locked` is the concrete, `Escrow`-specific
  substitute for now.
* The opt-in richer "interface" concept described in `docs/reference/INTERFACES.md` — letting a
  caller declare (and prove against) a known callee's real spec instead of staying fully black
  box, on a per-call-site basis.
