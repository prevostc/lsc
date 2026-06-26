# PositionTicket — Open Debt Obligation

**Represents**: an open position in a lending or perpetuals protocol. Must eventually be closed or liquidated — cannot be abandoned.

**The invariant enforced**: bad debt cannot accumulate silently. If a function opens a position and returns without closing it, the linearity check fails.

```lean
opaque PositionTicket : Type

namespace PositionTicket

def open (collateral : TokenAmount) (debt : UInt256)
    : ContractM S E Err PositionTicket

def close (ticket : PositionTicket) (repayment : TokenAmount)
    (h : repayment.value ≥ ticket.debt)
    : ContractM S E Err TokenAmount

def liquidate (ticket : PositionTicket)
    (h : isUndercollateralized ticket)
    : ContractM S E Err TokenAmount

def collateralValue (t : PositionTicket) : UInt256
def debt (t : PositionTicket) : UInt256

end PositionTicket
```

## Theorems eliminated

- `positions_always_resolved`
- `liquidation_requires_undercollateralization`
- `close_requires_full_repayment`

## Compilation target

Storage record per position: `(owner, collateral, debt, open: Bool)`.
