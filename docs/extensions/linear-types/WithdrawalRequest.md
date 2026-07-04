# WithdrawalRequest — CEI Order Enforcement

**Represents**: a staged withdrawal — state updated (effects), funds not yet moved (interaction pending).

**The invariant enforced**: `execute` can only happen after `stage`. Checks-effects-interactions order is structural.

```lean
opaque WithdrawalRequest : Type

namespace WithdrawalRequest

def stage (recipient : Address) (amount : UInt256)
    : ContractM S E Err WithdrawalRequest

def execute (req : WithdrawalRequest)
    : ContractM S E Err Unit

def cancel (req : WithdrawalRequest)
    : ContractM S E Err Unit

end WithdrawalRequest
```

## Theorems eliminated

- `state_updated_before_transfer`
- `no_double_withdraw`

## Compilation target

Storage record `(recipient, amount, pending: Bool)`. `stage` sets `pending = true`; `execute` / `cancel` set `pending = false`.
