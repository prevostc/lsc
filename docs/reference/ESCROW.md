# Reference: `Escrow` — a real, black-box cross-contract call

Full design context: [DESIGN.md](../DESIGN.md). Depends on [TOKEN.md](TOKEN.md) — `Escrow.release`
makes a genuine cross-contract call into an ERC20 token, using `exec`/`read` (`Lsc/Lang/Syntax.lean`,
backed by `Lsc.ContractM.PairM` in `Lsc/Core/ContractM.lean`).

For why this looks the way it does — `PairM` vs. a general N-contract registry, black-box
`exec`/`read`, and the new `HonestERC20` trust boundary — see
[`decisions/0002`](../decisions/0002-pairm-cross-contract-model.md),
[`decisions/0003`](../decisions/0003-exec-read-black-box.md), and
[`decisions/0009`](../decisions/0009-ierc20-interface-honest-assumptions.md).

## Contract

```lean
structure EscrowStorage where
  owner : Address := 0
  released : EscrowAmount := ⟨0⟩
  token : IERC20
  deriving Repr, ContractStorage

constructor (token_ : IERC20, owner_ : Address) {
  σ.token = token_;
  σ.owner = owner_;
}

@nonreentrant
tx release(recipient : Address, amount : EscrowAmount) {
  require (msg.sender == σ.owner) else revert NotOwner();
  exec SafeERC20.safeTransfer(σ.token, recipient, amount);
  σ.released = σ.released +? amount;
  emit Released(amount);
}

derive_contract "Escrow" EscrowStorage EscrowError EscrowEvent
```

Deploy calldata is a single ABI-encoded `address` at word 0 (no selector) — the token contract
the escrow will call via `release`. `owner` is set automatically to `msg.sender` (the deployer).

`exec SafeERC20.safeTransfer(σ.token, ..)` is inlined at compile time: one real IERC20 `transfer`
`CALL` on the `token` storage address, `let ok = mload(0)` binding, and `require (ok)` revert on
`false` — no separate SafeERC20 contract address in bytecode. The library body re-elaborates in
the caller's error enum (`ExternalCallFailed`). Unannotated `exec Token.transfer(..)` (module call)
stays black box for co-developed LSC callees.

## Trust boundary (what is proved vs assumed)

| Tier | Assumption | Examples |
|------|------------|----------|
| **A — Escrow-local** | none (any callee) | `release_rejects_non_owner`, `release_rejects_when_already_locked`, `release_atomic_on_transfer_failure` on `releaseHonest` |
| **B — Token effects** | `[HonestERC20 T]` | balance debit/credit/preservation (`release_honest_*`, and reference `Token` corollaries) |

`HonestERC20` (`Lsc/Lib/Interfaces/IERC20.lean`) bundles standard/honest ERC20 `transfer`
behavior (conservation, no fee-on-transfer/rebasing/hooks). It is **narrower** than “any
ABI-compatible ERC20.” The deployer vouches that the wired token satisfies it; the LSC reference
`Token` is a **witness instance** (`examples/escrow/test/TokenHonest.lean`), not a universal
quantifier over all tokens.

## Required theorems

Proof machinery: `examples/escrow/test/EscrowProofs.lean`. Statements:
`examples/escrow/test/EscrowTheorem.lean`.

### Tier A (Escrow-local)

| Theorem | Technique |
|---------|-----------|
| `release_rejects_non_owner` | Direct `simp` |
| `release_rejects_when_already_locked` | Direct `simp` |
| `release_atomic_on_transfer_failure` | `release_honest_atomic_on_transfer_failure` |

### Tier B — generic (`[HonestERC20 T]`)

| Theorem | Technique |
|---------|-----------|
| `EscrowProofs.runReleaseOkHonest` | Tier 1 — `HonestERC20Lemmas.exec_transfer_ok` + bookkeeping |
| `release_honest_increases_released` | Corollary |
| `release_honest_debits_escrow` | Corollary |
| `release_honest_credits_recipient` | Corollary |

### Tier B — reference `Token` instance

| Theorem | Technique |
|---------|-----------|
| `EscrowProofs.runTransferOk` / `runReleaseOk` | Tier 1 — full `Token.transferTyped` characterization |
| `release_increases_released` … `release_emits_released` | Corollaries of `runReleaseOk` |

Proved with zero `sorry`s, zero `native_decide`.
