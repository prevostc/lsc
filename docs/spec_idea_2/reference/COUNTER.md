# Reference: Pausable Counter

Canonical minimal reference contract. Every framework feature should be exercised here before attempting DeFi contracts.

Full design context: [DESIGN.md §13](../DESIGN.md). Implementation walkthrough: [IMPLEMENTATION.md Step 11](../IMPLEMENTATION.md).

## Contract

Surface syntax follows [IMPLEMENTATION.md](../IMPLEMENTATION.md) (`$.field`, `+?`, `require … else revert`, `msg.sender`):

```lean
contract Counter where
  storage:
    number : UInt256 := 0
    paused : Bool    := false
    owner  : Address

  errors:
    | Paused
    | NotOwner
    | Overflow

  events:
    | Incremented (n : UInt256)
    | Paused
    | Unpaused

  def increment : Tx := do
    require (!$.paused) else revert Paused;
    let n ← $.number +? 1;
    $.number := n;
    emit Incremented(n);

  def pause : Tx := do
    require (msg.sender == $.owner) else revert NotOwner;
    require (!$.paused) else revert Paused;
    $.paused := true;
    emit Paused();

  def unpause : Tx := do
    require (msg.sender == $.owner) else revert NotOwner;
    require ($.paused) else revert Paused;
    $.paused := false;
    emit Unpaused();
```

Overflow on `+? 1` reverts as `.error CounterError.Overflow` via strict 1:1 `ContractErrors.arith` (`ArithError.Overflow` → `Overflow`). Counter does not declare `Underflow` or `DivByZero` because the body uses only `+?`; adding `-?` or `/?` would require those variants in `errors:`.

## Required theorems

Each must be provable with `simp` + `omega` in at most ~5 lines:

| Theorem | Technique |
|---------|-----------|
| `increment_increases_number_when_not_paused` | `simp` + `omega` |
| `increment_errors_when_paused` | `simp` (error case) |
| `increment_does_not_change_paused` | `rfl` / struct update |
| `increment_does_not_change_owner` | `rfl` |
| `increment_emits_incremented` | `simp` on event log |
| `pause_sets_paused_when_owner` | `simp` |
| `pause_errors_when_not_owner` | `simp` |
| `pause_errors_when_already_paused` | `simp` |
| `unpause_clears_paused_when_owner` | `simp` |

Proof hypotheses use `s.storage.field` on `ContractState` snapshots — not `$.field`.

## Optional contract_spec

If using [extensions/CONTRACT-SPEC.md](../extensions/CONTRACT-SPEC.md), the theorem list above maps directly to a `contract_spec Counter where …` block. Not required for v1.
