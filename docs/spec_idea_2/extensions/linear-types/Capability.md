# Capability — Access Permission

**Represents**: proof that the current caller has a specific privilege.

**The invariant enforced**: privileged operations cannot complete without first obtaining and consuming a `Capability`. The only way to obtain one is to pass an identity check — the check cannot be forgotten on any path that uses the capability.

> **Open design question**: This type's API shape is under review. The sketch below uses internal `Capability.require` inside the function body. An alternative is a `Capability` function parameter. See [reference/AMM.md](../../reference/AMM.md) for the current sketch. Pick one surface syntax before v1 ships.

```lean
inductive Cap
  | Owner
  | Pauser
  | Guardian

opaque Capability (c : Cap) : Type

namespace Capability

def obtain (c : Cap) : ContractM S E Err (Option (Capability c))

def require (c : Cap) : ContractM S E Err (Capability c)

def consume (cap : Capability c) : ContractM S E Err Unit

end Capability
```

## Usage pattern (internal require)

```lean
def setFee (newFee : UInt256) : Tx := do
  let cap ← Capability.require(.Owner);
  $.fee := newFee;
  Capability.consume(cap);
```

## Alternative (parameter form)

```lean
def setFee (newFee : UInt256) (cap : Capability .Owner) : Tx := do
  $.fee := newFee;
  Capability.consume(cap);
```

## Theorems eliminated

- `setFee_only_owner`
- `pause_only_pauser`
- Every `only_X_can_do_Y` theorem where Y requires a capability

## Compilation target

**Nothing.** The identity check inside `Capability.require` compiles to `if caller() != sload(OWNER_SLOT) { revert }`. The capability value itself has no runtime representation.

## Notes for revision

When reworking this type, consider: composability across multiple roles, naming (`RoleProof`, `AccessWitness`, …), and whether access control should remain a linear type or become static function annotations. Do not remove without an explicit replacement documented in DESIGN.
