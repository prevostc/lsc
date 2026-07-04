# TokenAmount — Value Custody

**Represents**: custody of a quantity of fungible tokens.

**The invariant enforced**: token value cannot be created from a raw number. The only sources of `TokenAmount` are `mint` (restricted) and external calls that return one. The only sinks are `burn` (restricted) and external calls that consume one.

```lean
opaque TokenAmount : Type

namespace TokenAmount

def mint (amount : UInt256) : ContractM S E Err TokenAmount
  -- Only in functions with `canMint` permission

def burn (t : TokenAmount) : ContractM S E Err UInt256
  -- Only in functions with `canBurn` permission

def split (t : TokenAmount) (amount : UInt256)
    (h : amount ≤ t.value) : TokenAmount × TokenAmount

def merge (t1 t2 : TokenAmount) : TokenAmount

def value (t : TokenAmount) : UInt256  -- read-only, not linear

theorem split_conserves (t : TokenAmount) (amount : UInt256) (h : amount ≤ t.value) :
    let (t1, t2) := split t amount h
    t1.value + t2.value = t.value

theorem merge_conserves (t1 t2 : TokenAmount) :
    (merge t1 t2).value = t1.value + t2.value

end TokenAmount
```

## Theorems eliminated per contract

- `transfer_conserves_total_value`
- `no_phantom_minting`
- `transfer_does_not_increase_sender_balance` (structural: sender's token is consumed)

## Compilation target

`UInt256` in the IR. The linear wrapper is erased.

## What remains to prove

Arithmetic correctness within contract logic. Conservation of the token object itself is structural. Protocol-level invariants (e.g. LP shares = reserve ratio) still need theorems.

## Example — AMM swap

Storage reserves are `Wad` (see [reference/AMM.md](../../reference/AMM.md)). `TokenAmount` wraps in-flight token flows — tokens received from or sent to external ERC20 calls — not reserve fields in storage.

```lean
open scoped Lsc.Wad

def swap : Tx := do
  let inputToken ← ERC20.receiveFrom(msg.sender, amountIn);
  let r0 ← $.reserve0;
  let r1 ← $.reserve1;
  let num ← wadFrom(inputToken.value) ⸢*⸣? r1;
  let denom ← r0 +? wadFrom(inputToken.value);
  let outputWad ← num ⌊/⌋? denom;
  $.reserve0 := r0 -? outputWad;
  $.reserve1 := r1 +? wadFrom(inputToken.value);
  let outputToken ← TokenAmount.wrap(outputWad);
  ERC20.sendTo(msg.sender, outputToken);
  TokenAmount.burn(inputToken);
```

Every linear value (`inputToken`, `outputToken`) must be consumed exactly once on all paths.
