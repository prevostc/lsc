# OracleReading — Price Freshness

**Represents**: a price reading fetched this transaction, guaranteed fresh relative to a declared maximum age.

**The invariant enforced**: stale prices cannot be used. The only way to get a price is through `fetch`, which checks the oracle timestamp. The reading cannot be cached across transactions — no storage representation.

```lean
opaque OracleReading : Type

namespace OracleReading

def fetch (oracle : Address) (maxAge : UInt256)
    : ContractM S E Err OracleReading

def consume (r : OracleReading) : ContractM S E Err UInt256

def price (r : OracleReading) : UInt256

end OracleReading
```

## Theorems eliminated

- `price_not_stale` — structural: `fetch` checks staleness

## Compilation target

`(UInt256, UInt256)` — price and timestamp at fetch time. `fetch` calls the oracle, checks `block.timestamp - timestamp ≤ maxAge`.
