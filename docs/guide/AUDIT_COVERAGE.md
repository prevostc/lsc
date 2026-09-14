# Audit coverage

DeFi-oriented cut of SWC / OWASP Smart Contract Top 10 / Solodit. Status is
**today’s code** (grep, no `lake`). One status per row.

| Key | Meaning |
|---|---|
| **Impossible** | Impossible by construction (language/compiler) |
| **Proved** | Proved in example (named theorem) |
| **Assumed** | Documented assumption |
| **Open** | Not covered |

| Class | Status | Evidence | Gap/Next |
|---|---|---|---|
| Reentrancy (classic, RO, cross-fn) | Assumed | lock emitted + held-lock revert proved; `NoReentry` hypothesis remains until 8C | Compiler: drop `hNR` (8C) |
| Integer overflow/underflow | Impossible | `Tx.addChecked` / `+?` revert; wrapping only `+↻` (`Prim.addWrap`) | Don’t use `+↻` in money paths |
| Rounding / precision loss | Proved | `mulDiv↓`/`↑`; `swap0for1_k`; `removeLiquidity_paid`; `vault_solvent` (floor dust) | 512-bit `mulDiv` (Cpamm docstring) |
| First-depositor / share inflation / donation | Open | Vault README: inflation “not prevented”; `deposit` rates off live `balanceOf`; Vault first mint `assets.as`; Cpamm first mint `a0.as lpShare` (no `min(a0,a1)`, no dead shares); `require (0 < minted)` only | Stdlib virtual offset / dead shares |
| Access control / missing auth | Proved | `token_no_unauthorized_extraction` + `Auth`; Vault/Cpamm own `withdraw`/`removeLiquidity`; `NotOwner` on mint/pause | `Auth` is per-contract; missing `require` still compiles until proofs fail |
| Unchecked CALL return | Impossible | `if iszero(ok) { revert(0,0) }`; `SafeERC20` `require (ok = true)`; `boolOpt` empty→true | Raw `r.transfer` without `safe*` still compiles |
| Fee-on-transfer / rebase / weird ERC20 | Assumed | `IERC20.Spec.transfer_moves` exact `amount`; SECURITY.md fee-on-transfer, down-rebase excluded; `vaultRely` allows up-rebase | Stdlib: credit `Δ balanceOf` |
| Approve front-running | Open | `approve_sets` overwrite; no `increaseAllowance` | Stdlib `increaseAllowance` |
| Price-oracle manipulation | Open | No oracle `Interface`; Cpamm price = reserves | Stdlib Chainlink/TWAP `Spec` |
| Sandwich / MEV ordering | Assumed | Own entrypoints’ order is the `run` / `WealthTheorems` quantifier; block-producer ordering across other contracts is out of scope | Stdlib `deadline`; don’t claim cross-contract MEV-safety |
| Flash-loan amplification | Assumed | Trace = any senders/args/order (DECISIONS); same-tx callback = `NoReentry` | Close inflation; 8C |
| Signature replay / malleability | Impossible | No `ecrecover`/`permit` in `Core.Op` | Add only with nonce `Spec` |
| `delegatecall` / `selfdestruct` / proxy layout | Impossible | YulDefs: never emitted; `stepOp_delegatecall = none`; no `create` | — |
| `tx.origin` auth | Impossible | Surface `Tx.sender` only; no `Tx.origin` | — |
| Uninitialized state / constructor | Assumed | `Mapping` default 0; `constructor` not a trace step; TRUST.md EVM ctor-args gap; Vault/Cpamm ctor `CALL` out of scope | Model CREATE suffix; `init_inv` for S2 |
| Unbounded loops / gas DoS | Impossible | `Core` loop-free; Yul never `for`; gas griefing of *our* exec out of scope | — |
| DoS via revert-in-callback / unexpected ETH | Assumed | Failed CALL reverts us (SECURITY.md); ABI `nonpayable`; no `receive` | Liveness vs token-revert griefing |
| Timestamp / block dependence | Open | `Tx.timestamp` / `blockNumber` are `Core.Op` and compile | Lint/ban in `Auth` |
| ETH / `payable` / stuck funds | Assumed | Interface “payable methods are not modelled”; outgoing `call(..., 0, ...)` | Model payable; sweep force-ETH |
| Decimals mismatch / unit confusion | Open | `Amount a` blocks mixed `+?`; `Amount.as` is 1:1 retag (Vault/Cpamm first mint) | Ban `.as` except explicit mint |
| Unsafe casts / silent truncation | Open | `Amount.ofWord`; `decodeOrDefault` on views | Fail closed on bad view ABI |
| ERC-777 / token-hook reentrancy | Assumed | SECURITY.md ERC-777 hooks out of scope; `NoReentry` | 8C + token `Spec` |
| Governance / admin key | Assumed | Owner `pause`/`setFeeTo`; vault: pause blocks, claim unchanged; Cpamm README: fee redirect not proved | Example: own-call fairness (DECISIONS, not landed) |
| Slippage / deadline missing | Open | Cpamm `require (minOut ≤ out)`; no deadline; no exported `out ≥ minOut` | Stdlib `deadline` + theorem |
| Stale / failing external views | Assumed | Failed STATICCALL → poison (`Oracle.ofExt`); `decodeOrDefault`; `vaultRely` | `Impl` views must not silently `default` |
| Cross-contract invariant breaks | Assumed | `TokensIndependent`; DECISIONS `implements_to_conforms` **not in Lean** | Land compose theorem |
| Upgradeability | Impossible | No `delegatecall`/`create`; no proxy | New model if wanted |
| Insolvency (claims > holdings) | Proved | `token_solvent`; `vault_solvent`; `cpamm_solvent` | — |
| Unknown selector / fallback | Impossible | `selectorsNodup`; `runtimeBlock` `default { revert(0,0) }` | — |
| Self-call (`sender = self`) | Assumed | `Wf`: `sender ≠ self`; SECURITY.md “no self-call” | 8C makes EVM callback revert |

## Highest-value gaps

Ordered by value/cost. One cheapest close each.

1. **Reentrancy hyp `hNR`** — compiler: finish 8C; lock emitted + held-lock revert proved; `NoReentry` hypothesis remains until 8C.
2. **Share inflation / donation** — stdlib: virtual offset or Uniswap-style dead shares (code has neither).
3. **Fee-on-transfer / down-rebase** — model: `IERC20.Spec` from `Δ balanceOf`, not stated `amount`.
4. **`implements_to_conforms`** — model: Lsc callee discharges `Conforms` (DECISIONS only).
5. **Deadline + `minOut`** — stdlib + one Cpamm theorem (`out ≥ minOut`, `timestamp ≤ deadline`).
6. **Admin fairness** — example: `setFeeTo`/`pause` cannot cut another’s *claim* is proved; prove they cannot redirect *value*.
7. **Price oracle** — stdlib `IOracle.Spec` (freshness, bounds); none today.
8. **Approve race** — stdlib `increaseAllowance` / `safeApprove` pattern.
9. **CREATE args / S2 constructors** — model: TRUST.md gap; Vault/Cpamm ctor `CALL`.
10. **`Amount.as` / `decodeOrDefault`** — language: fail closed on unit retag and bad view payloads.
