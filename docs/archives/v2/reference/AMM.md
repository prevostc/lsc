# Reference: Constant Product AMM

Target DeFi contract validating the full design. Must exercise: `Wad`/`Ray` math, `TokenAmount` linear type, `IERC20` external interface, `HonestWorld`, `ReentrancyLock`, multi-field storage, and conservation invariants.

Related docs: [DESIGN.md §13](../DESIGN.md), [extensions/MATH.md](../extensions/MATH.md), [extensions/TYPE-CONSTRAINTS.md](../extensions/TYPE-CONSTRAINTS.md), [extensions/linear-types/](../extensions/linear-types/).

---

## Storage

Reserves are **`Wad`** in storage. `TokenAmount` wraps in-flight ERC20 custody during swap and liquidity operations only — it is not used for storage.

```lean
structure AMMStorage where
  reserve0  : Wad
  reserve1  : Wad
  lpSupply  : Wad
  fee       : Wad
  paused    : Bool
  owner     : Address
```

Optional decorators (see [TYPE-CONSTRAINTS.md](../extensions/TYPE-CONSTRAINTS.md)):

```lean
@bounded(1, 10^24) reserve0 : Wad := 0
@bounded(1, 10^24) reserve1 : Wad := 0
@bounded(0.0001, 0.01) fee  : Wad := 0.003
@immutable token0 : Address
@immutable token1 : Address
```

---

## Errors

Swap uses `+?`, `-?`, and `⌊/⌋?` — all three `ArithError` variants are reachable. Strict 1:1 mapping required (see DESIGN §6):

```lean
errors:
  | Overflow
  | Underflow
  | DivByZero
  | Paused
  | NotOwner
```

---

## World model

```lean
structure AMMWorld where
  self   : ContractState AMMStorage
  token0 : ERC20State
  token1 : ERC20State

instance : WorldSpec AMMWorld where
  Self := AMMStorage
  Env  := AMMEnv   -- bundles token0, token1
  ...

class HonestWorld (W : Type) [WorldSpec W] where
  token0_conserves   : transferConserves (getEnv w).token0
  token1_conserves   : transferConserves (getEnv w).token1
  no_hostile_reentry : ∀ call, externalCallSafe call
```

---

## Swap flow

```lean
open scoped Lsc.Wad

def swap (amountIn : Wad) : Tx := do
  require (¬ $.paused) else revert Paused;
  let lock ← ReentrancyLock.acquire;
  -- Receive input tokens (returns a TokenAmount representing in-flight custody)
  let inputToken ← externalCall(lock, token0, TRANSFER_FROM_SELECTOR, [msg.sender, amountIn]);
  -- Compute output using current reserves
  let r0 := $.reserve0;
  let r1 := $.reserve1;
  let num ← amountIn ⸢*⸣? r1;         -- wadMulHalfUp, checked
  let denom ← r0 +? amountIn;           -- checked add
  let outputWad ← num ⌊/⌋? denom;      -- wadDivDown, checked
  -- Update reserves (all Wad ops)
  $.reserve0 := r0 +? amountIn;         -- now holds the input
  $.reserve1 := r1 -? outputWad;        -- reduced by output
  -- Send output tokens and release lock
  let (_, lock) ← externalCall(lock, token1, TRANSFER_SELECTOR, [msg.sender, outputWad]);
  ReentrancyLock.release(lock);
```

Note: reserve updates use `+?`/`-?` on `Wad`. The `@bounded(1, 10^24)` constraints on reserves imply underflow cannot occur in practice when `outputWad ≤ reserve1`; the proof is part of `swap_preserves_k`.

---

## Access control

`setFee` uses `Capability`. API shape (parameter vs internal `require`) is an open question; the sketch below uses explicit parameter:

```lean
def setFee (newFee : Wad) (cap : Capability .Owner) : Tx := do
  Capability.consume(cap);
  $.fee := newFee;
```

See [extensions/linear-types/Capability.md](../extensions/linear-types/Capability.md) for details.

---

## Math

Factor the output computation as a `@math` function (see [MATH.md](../extensions/MATH.md)):

```lean
@math
def computeOutput (amountIn r0 r1 : Wad) : Except ArithError Wad :=
  (Wad.mulHalfUp amountIn r1).andThen (·.divDown (r0.add amountIn |>.getD default))
```

The compiler generates `AMM.computeOutput.ideal : ℝ → ℝ → ℝ → ℝ` automatically:

```lean
def AMM.computeOutput.ideal (amountIn r0 r1 : ℝ) : ℝ :=
  amountIn * r1 / (r0 + amountIn)
```

---

## Required theorems

```lean
-- Core invariant: k = reserve0 * reserve1 does not decrease
-- Requires WayRayMath for the Wad arithmetic; not a structural theorem
theorem swap_preserves_k [HonestWorld AMMWorld]
    (w w' : AMMWorld) (amountIn : Wad) ... :
    w'.self.storage.reserve0.raw * w'.self.storage.reserve1.raw ≥
    w.self.storage.reserve0.raw  * w.self.storage.reserve1.raw

-- Conservation: no tokens created or destroyed
theorem addLiquidity_conserves_tokens [HonestWorld AMMWorld] ...

-- Structural via ReentrancyLock: closes by simp
theorem swap_not_reentrant ... :
    ∀ reentrantCall, reentrantCall.reverts

-- Structural via Capability: closes by simp once Capability API is fixed
theorem setFee_only_owner (cap : Capability .Owner) ...

-- Faithfulness: swap output within ε of ideal (uses WayRayMath)
theorem computeOutput_faithful
    (amountIn r0 r1 : Wad)
    (h0 : wadLit 1 ≤ r0) (h1 : wadLit 1 ≤ r1)
    (ha : wadLit 1 ≤ amountIn) :
    |decode out_impl - AMM.computeOutput.ideal (decode amountIn) (decode r0) (decode r1)|
    ≤ AMM.OUTPUT_ε
```

Note the distinction: `swap_preserves_k` is **arithmetic** (requires WayRayMath-style reasoning about Wad precision); `swap_not_reentrant` and `setFee_only_owner` are **structural** (close by `simp` from the linear type framework).
