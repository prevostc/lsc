# TwoPartyAgreement — Atomic Settlement

**Status**: optional extension, not planned for the core library ([DESIGN.md §7](../../DESIGN.md)); not yet implemented.

**Represents**: a commitment by two parties to exchange assets (atomic swaps, OTC trades, settlement protocols).

**The invariant enforced**: settlement requires both parties' committed funds. Party A can always cancel and recover if Party B never commits.

```lean
opaque Offer     : Type
opaque Agreement : Type

namespace TwoPartyAgreement

def offer (funds : TokenAmount) (requestedAmount : UInt256) (counterparty : Address)
    : ContractM S E Err Offer

def accept (o : Offer) (funds : TokenAmount)
    (h : funds.value ≥ o.requestedAmount)
    : ContractM S E Err Agreement

def settle (a : Agreement)
    : ContractM S E Err (TokenAmount × TokenAmount)

def cancel (o : Offer)
    : ContractM S E Err TokenAmount

end TwoPartyAgreement
```

## Theorems eliminated

- `settlement_requires_both_parties`
- `party_a_funds_recoverable`

## Compilation target

Storage records tracking offer state and committed amounts.
