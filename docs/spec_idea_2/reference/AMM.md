# Reference: Constant Product AMM

Target DeFi contract validating the full design: `Wad`/`Ray` math, `TokenAmount`, IERC20 external calls, `HonestWorld`, `ReentrancyLock`, multi-field storage, conservation invariants.

Related docs: [DESIGN.md §14](../DESIGN.md), [extensions/MATH.md](../extensions/MATH.md), [extensions/TYPE-CONSTRAINTS.md](../extensions/TYPE-CONSTRAINTS.md), [extensions/linear-types/](../extensions/linear-types/).

## Storage

Reserves are **`Wad`** in storage (not `UInt256`, not `TokenAmount`). `TokenAmount` wraps in-flight ERC20 custody during swaps and liquidity operations only.

```lean
structure AMMStorage where
  reserve0  : Wad
  reserve1  : Wad
  lpSupply  : Wad
  fee       : Wad
  paused    : Bool
  owner     : Address
```

Field constraints (optional): see [TYPE-CONSTRAINTS.md](../extensions/TYPE-CONSTRAINTS.md) for `@bounded(1, 10^24)` on reserves.

## Errors

Swap uses `+?`, `-?`, and `⌊/⌋?` — declare all matching arith variants (strict 1:1 map):

```lean
errors:
  | Overflow
  | Underflow
  | DivByZero
  | Paused
  | ...
```

## World model

```lean
structure AMMWorld where
  self   : ContractState AMMStorage
  token0 : ERC20State
  token1 : ERC20State

class HonestWorld (W : Type) [WorldSpec W] where
  token0_conserves  : ...
  token1_conserves  : ...
  no_hostile_reentry : ...
```

## Swap flow (sketch)

```lean
open scoped Lsc.Wad

def swap (amountIn : Wad) : Tx := do
  let lock ← ReentrancyLock.acquire;
  let inputToken ← ERC20.receiveFrom(msg.sender, amountIn);
  let r0 ← $.reserve0;
  let r1 ← $.reserve1;
  let num ← amountIn ⸢*⸣? r1;
  let denom ← r0 +? amountIn;
  let outputWad ← num ⌊/⌋? denom;
  $.reserve0 := r0 -? outputWad;
  $.reserve1 := r1 +? wadFrom(inputToken.value);
  let outputToken ← TokenAmount.wrap(outputWad);
  let (_, lock) ← externalCall(lock, token0, TRANSFER_SELECTOR, [outputToken]);
  ReentrancyLock.release(lock);
```

See [TokenAmount.md](../extensions/linear-types/TokenAmount.md) for custody details.

## Access control

`setFee` uses `Capability` (see [Capability.md](../extensions/linear-types/Capability.md) — API shape still open):

```lean
def setFee (newFee : Wad) : Tx := do
  let cap ← Capability.require(.Owner);
  $.fee := newFee;
  Capability.consume(cap);
```

## Required theorems

```lean
-- Core AMM invariant (still needs proof — arithmetic, not structural)
theorem swap_preserves_k [HonestWorld AMMWorld] ... :
    w'.reserve0 * w'.reserve1 ≥ w.reserve0 * w.reserve1

theorem addLiquidity_conserves_tokens [HonestWorld AMMWorld] ... :
    totalTokensIn w' = totalTokensIn w + deposited

-- Structural via ReentrancyLock
theorem swap_not_reentrant ... :
    ∀ reentrantCall, reentrantCall.reverts

-- Structural via Capability (once API is fixed)
theorem setFee_only_owner ...
```

## Math

`computeOutput` may be factored as `@math` (named `wadMulHalfUp` / `wadDivDown` internally) — see [MATH.md](../extensions/MATH.md). Contract surface uses bracket pairs (`⸢*⸣?`, `⌊/⌋?`) or inlines them as above.
