# ReentrancyLock — Exclusive Execution

**Represents**: proof that this contract's reentrancy guard is held.

**The invariant enforced**: external calls can only be made while holding the lock. The lock can only be acquired once. Any reentrant call hits the lock check and reverts before touching state.

```lean
opaque ReentrancyLock : Type

namespace ReentrancyLock

def acquire : ContractM S E Err ReentrancyLock

def release (lock : ReentrancyLock) : ContractM S E Err Unit

end ReentrancyLock
```

## External calls

At the AST level, external calls use `lockAcquire`, `externalCall`, and `lockRelease` as separate statement nodes (see [DESIGN.md §6](../../DESIGN.md) and [framework/IMPLEMENTATION.md](../../framework/IMPLEMENTATION.md)). The recommended DSL pattern wraps these:

```lean
def externalCall
    (lock   : ReentrancyLock)
    (target : Address)
    (selector : UInt32)
    (args   : List UInt256)
    : ContractM S E Err (UInt256 × ReentrancyLock)
```

```lean
def withdrawAll : Tx := do
  let amount := $.balance;
  $.balance := 0;
  let lock ← ReentrancyLock.acquire;
  let (result, lock) ← externalCall(lock, $.recipient, TRANSFER_SELECTOR, [amount]);
  ReentrancyLock.release(lock);
```

## Theorems eliminated

- `external_calls_require_lock`
- `no_reentrant_state_modification`

## Compilation target

The `locked : Bool` field in `ContractState`. `acquire` → `if sload(LOCK_SLOT) { revert } sstore(LOCK_SLOT, 1)`; `release` → `sstore(LOCK_SLOT, 0)`.
