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
  released : Token.Amount := ⟨0⟩
  token : IERC20 := default
  deriving Repr, ContractStorage

@nonreentrant
tx release(recipient : Address, amount : Token.Amount) {
  require (msg.sender == σ.owner) else revert NotOwner();
  exec σ.token.transfer(recipient, amount);
  let r = σ.released +? amount;
  σ.released = r;
  emit Released(amount);
}

derive_contract "Escrow" EscrowStorage EscrowError EscrowEvent
```

`exec σ.token.transfer(..);` is Solidity-style interface syntax: the callee address is loaded from
the `token : IERC20` storage field (`"token"` slot at codegen), and `transfer` enables ERC20-style
`bool` return checking at the `CALL` site. The interface is recorded in `ContractDef.interfaces`
from the storage field type. Unannotated `exec Token.transfer(..)` (module call) stays black box
for co-developed LSC callees.

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
