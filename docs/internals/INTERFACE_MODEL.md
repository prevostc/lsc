# Interface Model

An interface is two ordinary Lean structures: `Fn`/`View` field types (the ABI)
and a user-written `Prop` `I.Spec` over `T : I.Impl …`, in theorem shape
(success as hypothesis, state delta as conclusion). `deriving Interface`
(`Lsc/Lang/InterfaceDeriving.lean`) builds the method table, `I.Ref` / `I.Try` /
`I.Impl`, and `Impl.ofRef`. Callee behaviour is a deterministic, memory-blind
`Oracle` on `World.ext`; `oracle.call = none` is revert. The adversarial oracle
is the baseline; a `Spec` hypothesis restricts it. Views are pure `oracle.view`
reads. Reentrancy during a call is not modelled (`self` unchanged).

## Types

`World S X E` — `self : S`, `ext : X` (compiled contracts: `Lsc.ExtState`),
`log`, `oracle : Oracle X`. `WorldView X` is `{ ext, oracle }`: what an external
`I.Impl` of a `Ref` actually reads.

`Tx S X E ε α := ReaderT Ctx (StateT (World S X E) (Except (Err ε))) α`.
`Err` includes `callFailed`.

```
structure IERC20 (a : Asset) where
  totalSupply  : View (Amount a)
  balanceOf    : View (Address → Amount a)
  allowance    : View (Address → Address → Amount a)
  transfer     : Fn (Address → Amount a → Bool)
  transferFrom : Fn (Address → Address → Amount a → Bool)
  approve      : Fn (Address → Amount a → Bool)
  deriving Interface

structure IERC20.Ref (a : Asset) where
  addr : Address

-- storage field
asset : Ref (IERC20 vaultAsset)

let tok ← read asset
let ta ← tok.balanceOf me
safeTransferFrom tok who me assets .TransferFailed
```

`asset.impl` is `I.Impl.ofRef asset` over `WorldView` (no dummy `World`). View
fields of a `Ref` Impl take that view (`balanceOf who v`) and are total
(`decodeOrDefault`). Fn fields take `Ctx` and a `WorldView` and return `Option`
(no error parameter): a successful `Tx.run` on the full `World` is that `some`
on `w.view` via `oracle.call`, with the post-view `{ v with ext := x' }`.
`Tx.call` / `Tx.view` take an address and selector; the typed methods supply
both from the `Ref`. A contract that *is* the interface (Token) still has
`C.impl` over `World`.

Files: `Lsc/Lang/Interface.lean`, `Lsc/Lang/InterfaceDeriving.lean`;
`Stdlib/ERC20.lean` (`IERC20`, `IERC20.Spec`); `Stdlib/SafeERC20.lean`.

## `IERC20.Spec`

`IERC20.Spec T` (`Stdlib/ERC20.lean`) is what a well-behaved ERC-20 promises of
`T : IERC20.Impl a W`. Token proves it of its own implementation:

```
lsc_contract Token … implements IERC20 Token.tokenAsset
theorem erc20 : IERC20.Spec Token.impl
```

Vault/Cpamm theorems that mention the token take
`hT : IERC20.Spec w.self.asset.impl` (or both tokens). Live holdings are
`tok.impl.balanceOf me w.view`. Between our calls, `vaultRely` /
`cpammRely` constrain `ext` so that those `balanceOf` views do not fall and
each token's `totalSupply` view stays the same.

## Compiler layer (S2)

`ExtOracle` / `Oracle.ofExt` / `ExtOracle.NoReentry` live in
`Lsc/Compiler/ExtOracle.lean` (`Externals.lean` re-exports them), never in
`Lsc/Lang`. S2 bytecode glue uses that memory-blind oracle.
`bytecode_call_correct_ext` and `transport_claim_ext` quantify over it with
`NoReentry`.

## Resolved implementation decisions

- `Amount a` is a one-field structure (`raw : Word`); an abbrev would unify
  every amount back to `Word`. Reify erases `.mk`/`.raw`. Certificates are
  `Core.denote Γ f.core args = f`.
- `Inv : World S X E → Prop`. Internal `Wf self tr w` is `External`: every call
  has `target = self` and `sender ≠ self`. The 256-bit native wrap is a
  compiled payable guard (`lt(selfbalance(), callvalue())`), not a `Wf`
  hypothesis. Public theorems use `State` / `Txs`.
- `I.Ref` is `{ addr : Address }`, generated per interface; `Ref (IERC20 a)` is
  that type. Storage fields are `Ref (IERC20 …)`, not a parallel `Binding`.
- `World.ext` is the fixed `Lsc.ExtState` for compiled contracts (DECISIONS
  2026-09-13).
- `#lsc_obligations` lists `C.inv_rely` when there is an environment and
  requires `C.holdings`.
- Traces are `List (Step C)` with `Step := call | env`; `NoAuthAlong` skips
  `env` steps.
- Constructor arguments (`calldataload` in creation code vs powdr's empty
  `initState`) are a pre-existing gap of the deploy link, tracked in
  `PROOF_CHAIN.md`.
