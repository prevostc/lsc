# External calls

Lsc does not let you pass an arbitrary address to `CALL`. You declare an
**interface** (today: `IERC20`) and a **binding**: which storage field holds
the address, and which ghost field holds that token's balances and
decimals. `Tx.call` takes the binding and the method, not an address. The
compiler `sload`s the bound slot.

## Binding a token

Vault binds one asset (`Examples/Vault/Contract.lean`):

```lean
def assetB : Binding IERC20 Storage Ext :=
  ⟨(·.asset), (·.asset), fun x g => { x with asset := g }⟩
```

Deposit pulls after it has computed a positive mint:

```lean
let _ ← Binding.transferFrom assetB who me assets
```

AMM binds two tokens, `token0B` and `token1B`, and requires `t0 ≠ t1` in
the constructor. External transfers run **after** requires and storage
updates. That is sound only because the hypotheses below rule out
reentrancy into our storage.

## What `IERC20` means here

The ghost is `balances` plus `decimals` (no allowances, no `totalSupply`).
`transfer` / `transferFrom` succeed if the source balance covers the
amount, then move the funds. `transferFrom` in this model does **not**
check allowances: a pull succeeds if the source has the balance and the
call is not faulted. `decimals` is immutable in the model.

Between our calls, `Rely` says: our balance at that token is
non-decreasing, and `decimals` is unchanged. Up-rebasing (a donation) is
allowed; down-rebasing and admin burns are not.

## What is assumed, not proved

Successful calls from us to the bound address are assumed to **conform**:
the calldata decodes to a method of `IERC20`, the ghost update matches the
model, return data decodes, and **non-interference** holds — our storage
and transient storage are unchanged, ETH balances are unchanged (calls
send zero value), other bound tokens' ghosts are unchanged, and the
callee's logs are not attributed to us. Failed calls are unconstrained;
our code reverts and rolls back.

Reentrancy is excluded by that non-interference hypothesis. The compiler
does **not** emit a reentrancy lock.

Fee-on-transfer tokens are excluded (the post-ghost would not match).
ERC-777 hooks that call another bound token are excluded. USDT-style
missing return values are treated as success (`boolOpt`). Blacklist,
pause, revert-on-zero, callee out-of-gas, and allowance shortfall are
absorbed as faults.

Foreign ERC-20 storage layout is not proved in general. Vault supplies a
concrete Solidity-layout reading (balances mapping, decimals slot) so the
abstraction is inhabited; AMM reuses it at both token addresses, which
must differ.

Call-free contracts (Counter, Token) use a closed model: no `CALL`.

---

For the curious: the theorem that consumes these hypotheses is
`bytecode_call_correct_ext`.
