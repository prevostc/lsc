# Allowance — Spending Permission

**Represents**: a granted permission to spend tokens on behalf of another address, up to a specified amount.

**The invariant enforced**: `transferFrom` cannot spend more than the approved amount. Guaranteed by the type of `consume`, not by a bypassable runtime check.

```lean
opaque Allowance : Type

namespace Allowance

def grant (owner : Address) (spender : Address) (amount : UInt256)
    : ContractM S E Err Allowance

def consume (a : Allowance) (amount : UInt256) (h : amount ≤ a.remaining)
    : ContractM S E Err Allowance

def revoke (a : Allowance) : ContractM S E Err Unit

def remaining (a : Allowance) : UInt256

end Allowance
```

## Theorems eliminated

- `transferFrom_cannot_exceed_allowance` — structural: `h : amount ≤ a.remaining` in `consume`
- `allowance_not_negative` — structural: `UInt256` cannot be negative

## Compilation target

Storage slot `(owner, spender) → UInt256` (remaining amount). `grant` writes initial value; `consume` subtracts; `revoke` writes zero.
