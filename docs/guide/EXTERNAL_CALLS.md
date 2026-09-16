# External calls

Lsc does not let you pass an arbitrary address to `CALL`. You declare an
**interface** (`structure IERC20 (a : Asset) … deriving Interface`) and store
an `I.Ref` (`{ addr : Address }`). `deriving Interface` generates the method
table, typed calls, `I.Impl`, and `Impl.ofRef`. `asset.impl` is that
`Impl` over `WorldView` (oracle plus `ext`). `I.Spec` is a user-written
`Prop` over `T : I.Impl …` (success as
hypothesis, state delta as conclusion). The callee is the world's `Oracle`;
a `Spec` hypothesis restricts it. Reentrancy into this contract while the
transient lock is held reverts; the CALL model restores `self` storage.

## Binding a token

Vault stores one typed ref (`Examples/Vault/Contract.lean`):

```lean
structure Storage where
  asset : Ref (IERC20 vaultAsset)
  -- …
```

Deposit reads the ref and pulls after it has computed a positive mint:

```lean
let tok ← read asset
let ta ← tok.balanceOf me
-- … storage writes …
safeTransferFrom tok who me assets .TransferFailed
```

Cpamm binds two tokens, `token0` and `token1`, and requires `t0 ≠ t1` in
the constructor. External transfers run **after** requires and storage
updates. A nested CALL/STATICCALL into this contract while the runtime
lock is held reverts; the CALL model restores `self` storage / transient /
self-logs (`ExtOracle.noReentry`). ETH balances are not restored.

## What `IERC20.Spec` means here

`IERC20` is the ABI: `totalSupply`, `balanceOf`, `allowance`, `transfer`,
`transferFrom`, `approve`. `IERC20.Spec T` (`Stdlib/ERC20.lean`) is what a
well-behaved token promises of `T : IERC20.Impl …`: a successful `transfer` /
`transferFrom` moves `amount` and touches no one else; transfers do not
change `totalSupply`; `transferFrom` spends allowance when `sender ≠ src`;
`approve` writes the allowance; nobody can lower your balance except you or
a spender you approved.

Live holdings in Vault/Cpamm specs are `tok.impl.balanceOf me w.view`, not a
hand-decoded `oracle.view`. Token itself implements the interface:
`lsc_contract Token … implements IERC20 Token.tokenAsset` emits
`Token.impl`, and `theorem token_spec : IERC20.Spec Token.impl`.

Between our calls, Vault's `vaultRely` / Cpamm's `cpammRely` say: this
contract's token `balanceOf` does not fall, and each token's `totalSupply`
view stays the same. Up-rebasing (a donation) is allowed; a falling
balance is not.

## What is assumed, not proved

Theorems that mention the token take `hT : IERC20.Spec (w.self.asset.impl : AssetImpl)`
(or both tokens, for Cpamm). Failed calls are `.callFailed` and revert us.
USDT-style missing return values are treated as success (`boolOpt`).
Fee-on-transfer and reentrancy are outside `IERC20.Spec` as stated.

`IERC20.Exact T` is `IERC20.Spec T` as a class (`extends`); Vault/Cpamm
keep taking `hT : IERC20.Spec _` and discharge it with `exact.toSpec`.
WETH proves `weth_exact : IERC20.Exact WETH.impl`.

`Native.send` is a value-carrying CALL with empty calldata (not an
`I.Ref` method). The Yul is `call(extCallGas, to, value, 0, 0, 0, 0)`.
`Oracle.send` is the Lean hook; `Oracle.ofExt` fills `CallRequest.value`.

Call-free contracts (Counter, Token) use a closed model: no `CALL`.

---

For the curious: the compiler theorem that consumes an `ExtOracle` is
`bytecode_call_correct_ext`; example authors apply `transport_claim_ext`.
