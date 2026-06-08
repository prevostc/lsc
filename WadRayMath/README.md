# WadRayMath

RAY fixed-point library (Aave `WadRayMath` style). Part of the standalone **CapProofs** package.

## Files (by number representation)

| File | Representation | Role |
|------|----------------|------|
| `Nat.lean` | `ℕ` (`WadRayMath.Nat`) | Constants, ops, helper lemmas, rounding bounds, composition |
| `Evm.lean` | EVM (`WadRayMath.Evm`) | On-chain wrappers + simulation theorems |
| `Real.lean` | `ℝ` codec (`WadRayMath.Real`) | `decode`, `toReal`, bridge lemmas only (no duplicate ℝ ops) |

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
import WadRayMath.Nat     -- ℕ code + verified bounds
import WadRayMath.Evm     -- EVM-faithful Except API
import WadRayMath.Real    -- codec + ℝ distance bounds
import WadRayMath         -- Nat + Evm (no Real)
```

## Namespaces

```lean
Nat.rayMulHalfUp a b       -- WadRayMath.Nat
Evm.rayMulHalfUp a b       -- WadRayMath.Evm (Except)
Real.decode n              -- WadRayMath.Real (codec only; use decode a * decode b for ℝ math)
```

## Standalone extract

From the `CapProofs` root, copy:

- `WadRayMath/`
- `WadRayMath.lean`

Add to your `lakefile.toml`:

```toml
[[lean_lib]]
name = "WadRayMath"

[[require]]
name = "mathlib"
scope = "leanprover-community"
```

`Nat.lean` imports Mathlib (project uses `autoImplicit = false`). `Real.lean` also requires Mathlib.
