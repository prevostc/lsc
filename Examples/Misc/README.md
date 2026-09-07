# Misc examples

Not protocol walkthroughs. Used as compiler/language tests.

| File | Role | Depends on |
|------|------|------------|
| `AmountDemo.lean` | Amount storage/maps; `lsc_reify` certificates by `rfl` (no `lsc_contract`) | `Lsc`, `Stdlib.Scales` |
| `YulTests.lean` | Executable Yul interpreter checks for Counter and Token | `Examples.Counter.Contract`, `Examples.Token.Contract` |
