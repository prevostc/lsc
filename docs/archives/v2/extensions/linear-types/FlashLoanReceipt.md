# FlashLoanReceipt — Repayment Obligation

**Represents**: an outstanding flash loan that has not yet been repaid.

**The invariant enforced**: any function that borrows must repay before returning, on all code paths including error paths. This temporal ordering property is hard to state as a theorem but trivial to enforce with a linear type.

```lean
opaque FlashLoanReceipt : Type

namespace FlashLoanReceipt

def borrow (amount : UInt256)
    : ContractM S E Err (TokenAmount × FlashLoanReceipt)
  -- Permission: `canFlashBorrow`

def repay (receipt : FlashLoanReceipt) (repayment : TokenAmount)
    (h : repayment.value ≥ receipt.amount)
    : ContractM S E Err Unit

def amount (r : FlashLoanReceipt) : UInt256

end FlashLoanReceipt
```

## What the linearity pass catches

```lean
-- REJECTED: receipt dropped on error path
def badFlashLoan : Tx := do
  let (funds, receipt) ← FlashLoanReceipt.borrow(1000);
  if (someCondition) {
    FlashLoanReceipt.repay(receipt, funds, ...);
  } else {
    revert BadCondition;  -- linearity error: receipt outstanding
  }
```

## Theorems eliminated

- `flashloan_always_repaid`
- `flashloan_repayment_covers_principal`

## Compilation target

Boolean storage slot `loan_outstanding`. Runtime check on `borrow` is belt-and-suspenders — linearity already guarantees no two outstanding borrows from the same function path.
