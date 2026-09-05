# Interface Model

Adopted external-contract contract: a deterministic canonical **may**-model, static binding,
and a minimal ghost. Alternatives (exact model, law-only, relational oracle, composed LSC
worlds) are rejected: the `Tx` monad stays deterministic and `simp`-shaped; foreign tokens
are not our contracts; failure outside the ghost is one fault oracle, not non-conformance.

## Types

`World S X E` — `self : S`, `ext : X` (ghosts, one field per bound external), `log`,
`faults : Nat → Bool`, `ncalls : Nat`.

`Tx S X E ε α := ReaderT Ctx (StateT (World S X E) (Except (Err ε))) α`.
`Err` gains `callFailed`. External failure reverts the caller.

```
Interface := { Ghost, Method, n, model, abi, idx }
  model : Method → Address → List Nat → Ghost → Option (Nat × Ghost)
  abi   : Method → { selector, arity, ret }   -- ret ∈ {word, boolOpt, none}; compiler only
  idx   : Method ≃ Fin n

Binding I S X := { addr : S → Address, get : X → I.Ghost, set : X → I.Ghost → X }
```

`Tx.call binding method args` takes **no address**. The compiled call `sload`s the bound
storage field; `Core.effects` frames it immutable (no `store` to that field in any entrypoint).
The model updates the bound ghost. `Tx.callUnit` is the `Stmt` form. `run_call` is `rfl`.
Bindings are explicit constants (`def assetB : Binding IERC20 Storage Ext := ⟨…⟩`); a `bind`
command is sugar to add later.

Files: `Lsc/Lang/Interface.lean` (`Interface`, `Binding`, `Tx.call`, `run_call`);
`Lsc/Stdlib/ERC20.lean` (ghost, model, `Rely`, `IERC20`, `IERC20.Ref`, `Binding.*` aliases).

## ERC20

Ghost = `balances` + `decimals` only (no allowances). Methods: `transfer`, `transferFrom`,
`balanceOf`, `decimals`. `transfer`/`transferFrom` succeed iff the source balance covers the
amount, then `move`. `decimals` is immutable in the model.

`Rely self g g' := g.balances self ≤ g'.balances self ∧ g'.decimals = g.decimals`
(no approvals granted by us).

## Conforms, Implements, RelyEnv

`Conforms I self addr ext` refines powdr's `ExternalCalls` through an abstraction
`α : WorldView → I.Ghost`. For every successful call from `self` to `addr`: decode matches
some `m, args`; `I.model` returns the observed word and `α(post) = g'`; our storage and
transient are unchanged; other bindings' `α` are unchanged. Failed calls need no model
clause (`finishCall` rolls back; our code reverts).

Non-interference is **assumed**, justified informally by the `tload`/`tstore` lock.
Bytecode-level proof from the lock is deferred.

`Implements C I` (with `β : C.S → I.Ghost`): our own contracts refine the may-model on success.
Used to validate Token, never as the model of a foreign token.

`RelyEnv`: between two of our calls, each binding's ghost evolves under `I.Rely self`.

## Non-conforming tokens

| Behaviour | Status |
|---|---|
| Fee-on-transfer | Excluded by `Conforms` (`α(post) ≠ g'`). A future `IERC20Fee` would need `balanceOf` accounting. |
| Down-rebasing / admin burn | Excluded by `Rely`. |
| Up-rebasing | `Rely`-conforming (donation-like). |
| ERC777 hooks / calls to other bound tokens | Excluded by non-interference / no cross-binding. |
| Blacklist, pause, revert-on-zero, callee OOG, allowance shortfall | Conforming: absorbed by the fault oracle. Allowances are not in the ghost, so OZ infinite-allowance shortcuts cannot break `α`. |
| USDT-style missing return | Conforming: handled in Yul lowering (`boolOpt`). |

## Vault (first consumer)

- Stored `totalAssets` with coupling `totalAssets ≤ ghost balance of self`.
  `holdings self w = w.ext.asset.balances self`. Donation-immune by construction; idle
  donations until a future `sync` (re-analyse then).
- `decimals` is an `IERC20.Method`, cached in vault storage at construction. Fallback: a
  constructor argument if powdr's deploy theorem cannot take external calls in init code.
- Type-level scales of external assets are opaque symbols. `rescale` / `Amount.one` take
  runtime scale words. `Vault.assetScale := WAD` and the IERC20 shim in `Amount.lean` are
  deleted.

## Core and `toYul_correct`

Core gains exactly `Op.call b m args` and `Stmt.call b m args`. `ContractSchema.ext` supplies
`call : Nat → Nat → List Nat → Tx`. Lowering: `YUL_TARGET.md`. `letCall` / fault-oracle shape:
`PROOF_CHAIN.md`. TCB: `TRUSTED_COMPUTING_BASE.md`.

## Resolved implementation decisions

- `Amount τ s` is a `structure` (a `def` newtype unifies with `Nat` and across units once unfolded,
  so it gives no unit safety). Core still denotes into `Nat`; the reifier inserts `toNat`/`ofNat`
  at the boundary and the certificate for an `Amount`-valued function is
  `Amount.ofNat <$> Core.denote … = f`, still closed by `rfl`.
- `Inv : World S X E → Prop`; protocols instantiate it at their own address (`Vault.Inv self`).
  Trace well-formedness `Wf self tr`: every call has `target = self` and `sender ≠ self`.
- `World.faults` defaults to `fun _ => false`; theorems quantify over all oracles.
- ERC20 may-model: `transferFrom` ignores allowances (pull succeeds iff `src`'s balance covers
  and the call is not faulted); `move` uses unbounded `Nat` addition — `Conforms` maps on-chain
  balances to values `< 2^256`, so no wrap is modelled.
- Bindings are explicit constants for now: `def assetB : Binding IERC20 Storage Ext := ⟨…⟩`.
  A `bind` command is sugar to add later.
- `extCallGas := 1_000_000` (a literal; the EVM caps it at 63/64 of available gas).
- `IERC20.Ref := Address` (`abbrev`); typing is carried by the `Binding`, not by the field type.
- `#lsc_obligations` also lists `C.inv_rely` when `Ext ≠ Unit` (`rely := fun _ _ => True` for
  `Unit`), and requires `C.holdings`.
- Traces are `List (Step C)` with `Step := call | env`; `NoAuthAlong` skips `env` steps.
- Constructor arguments (`calldataload` in creation code vs powdr's empty `initState`) are a
  pre-existing gap of the deploy link, tracked in `PROOF_CHAIN.md`, not part of this refactor.
  Constructor-time `call` (for `decimals`) is covered by `compileObject_correct` under
  `evmWithExternal`.
- `@[simp] run_call` may be dropped if it loops in protocol proofs; then use it by `rw`.
