# WayRayMath

RAY fixed-point library (Aave `WadRayMath` style). Part of the standalone **CapProofs** package.

## Files (by number representation)

| File | Representation | Role |
|------|----------------|------|
| `Nat.lean` | `ℕ` (`WayRayMath.Nat`) | Constants, ops, helper lemmas, rounding bounds, composition |
| `Evm.lean` | EVM (`WayRayMath.Evm`) | On-chain wrappers + simulation theorems |
| `Real.lean` | `ℝ` codec (`WayRayMath.Real`) | `decode`, `toReal`, bridge lemmas only (no duplicate ℝ ops) |

## Semantic layers

| Layer | Modules |
|-------|---------|
| L0 Constants | `Nat`, `Evm` |
| L1 Code | `Nat`, `Evm` |
| L2 Numerator | `Nat` |
| L3 Bounds | `Nat` |
| L4 Real | `Real` |

## Import tiers

```lean
import WayRayMath.Nat     -- ℕ code + verified bounds
import WayRayMath.Evm     -- EVM-faithful Except API
import WayRayMath.Real    -- codec + ℝ distance bounds
import WayRayMath         -- Nat + Evm (no Real)
```

## Namespaces

```lean
Nat.rayMulHalfUp a b       -- WayRayMath.Nat
Evm.rayMulHalfUp a b       -- WayRayMath.Evm (Except)
Real.decode n              -- WayRayMath.Real (codec only; use decode a * decode b for ℝ math)
```

## Standalone extract

From the `CapProofs` root, copy:

- `WayRayMath/`
- `WayRayMath.lean`

Add to your `lakefile.toml`:

```toml
[[lean_lib]]
name = "WayRayMath"

[[require]]
name = "mathlib"
scope = "leanprover-community"
```

`Nat.lean` imports Mathlib (project uses `autoImplicit = false`). `Real.lean` also requires Mathlib.
