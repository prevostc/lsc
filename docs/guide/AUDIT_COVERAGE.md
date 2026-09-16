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
| Reentrancy (classic, RO, cross-fn) | Proved | lock prologue + held-lock revert; `NoReentry` is a lemma. `[Reentrant]` skips acquire/release; store-after-call rejected unless `[Reentrant.Unsafe]` | `[Reentrant]` is not covered by the lock while that function runs |
| Integer overflow/underflow | Impossible | `Tx.addChecked` / `+?` revert; wrapping only `+↻` (`Prim.addWrap`) | Don’t use `+↻` in money paths |
| Rounding / precision loss | Proved | `mulDiv↓`/`↑`; `swap0for1_k`; `removeLiquidity_paid`; `vault_solvent` (floor dust) | 512-bit `mulDiv` (Cpamm docstring) |
| First-depositor / share inflation / donation | Proved | Vault: `Shares` virtual offset `10^6`; `deposit_inflation_bounded` / `Shares.inflation_bound_raw` (`V · (x − r) ≤ A + V`); Cpamm: Uniswap-v2 `MINIMUM_LIQUIDITY` lock, `addLiquidity_min_liquidity` (first mint → `1000 ≤ totalShares`) | Weaker `r ≥ x − x/V − 1` is false when the mint is 0; attacker-cost form is what is proved |
| Access control / missing auth | Proved | `token_no_unauthorized_extraction` + `Auth`; Vault/Cpamm own `withdraw`/`removeLiquidity`; WETH `weth_no_unauthorized_extraction`; `NotOwner` on mint/pause | `Auth` is per-contract; missing `require` still compiles until proofs fail |
| Unchecked CALL return | Impossible | `if iszero(ok) { revert(0,0) }`; `SafeERC20` `require (ok = true)`; `Native.send` reverts with `err`; `boolOpt` empty→true | Raw `r.transfer` / `Native.try.send` without a check still compiles |
| Fee-on-transfer / rebase / weird ERC20 | Assumed | `IERC20.Spec.transfer_moves` exact `amount`; SECURITY.md fee-on-transfer, down-rebase excluded; `vaultRely` allows up-rebase | Stdlib: credit `Δ balanceOf` |
| Approve front-running | Open | `approve_sets` overwrite; no `increaseAllowance` | Stdlib `increaseAllowance` |
| Price-oracle manipulation | Open | No oracle `Interface`; Cpamm price = reserves | Stdlib Chainlink/TWAP `Spec` |
| Sandwich / MEV ordering | Assumed | Own entrypoints’ order is the `run` / `WealthTheorems` quantifier; block-producer ordering across other contracts is out of scope | Stdlib `deadline`; don’t claim cross-contract MEV-safety |
| Flash-loan amplification | Assumed | Trace = any senders/args/order (DECISIONS); same-tx callback = `NoReentry` | Close inflation; 8C |
| Signature replay / malleability | Impossible | No `ecrecover`/`permit` in `Core.Op` | Add only with nonce `Spec` |
| `delegatecall` / `selfdestruct` / proxy layout | Impossible | YulDefs: never emitted; `stepOp_delegatecall = none`; no `create` | — |
| `tx.origin` auth | Impossible | Surface `Tx.sender` only; no `Tx.origin` | — |
| Uninitialized state / constructor | Assumed | `Mapping` default 0; `constructor` not a trace step; `Deployed` / `State` (Token, WETH); TRUST.md EVM ctor-args gap; Vault/Cpamm ctor `CALL` out of scope | Model CREATE suffix; Vault/Cpamm `State` |
| Unbounded loops / gas DoS | Impossible | `Core` loop-free; Yul never `for`; gas griefing of *our* exec out of scope | — |
| DoS via revert-in-callback / unexpected ETH | Assumed | Failed CALL reverts us (SECURITY.md); ABI `nonpayable`; no `receive` | Liveness vs token-revert griefing |
| Timestamp / block dependence | Open | `Tx.timestamp` / `blockNumber` are `Core.Op` and compile | Lint/ban in `Auth` |
| ETH / `payable` / stuck funds | Proved | `[Payable]` + typed `Tx.value`; dispatcher `callvalue` revert and payable wrap guard `lt(selfbalance(), callvalue())`; `Native.send`; WETH `weth_backed` / `weth_no_unauthorized_extraction` from `State` | Trace `step` credits `ctx.value` before `Tx.run` |
| Decimals mismatch / unit confusion | Proved | `Amount a` blocks mixed `+?`; `x.as b` requires `a.decimals? = b.decimals?` at elaboration (rejects `USDC(6)→DAI(18)` and `none` vs `some`); `asUnchecked` only for documented cross-scale retags (Cpamm first mint) | `decodeOrDefault` on views still fail-open |
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

1. **`[Reentrant]` callbacks** — the lock does not cover a reentrant function while it runs; CEI lint is syntactic. `[Reentrant.Unsafe]` is a human override.
2. **Fee-on-transfer / down-rebase** — model: `IERC20.Spec` from `Δ balanceOf`, not stated `amount`.
3. **`implements_to_conforms`** — model: Lsc callee discharges `Conforms` (DECISIONS only).
4. **Deadline + `minOut`** — stdlib + one Cpamm theorem (`out ≥ minOut`, `timestamp ≤ deadline`).
5. **Admin fairness** — example: `setFeeTo`/`pause` cannot cut another’s *claim* is proved; prove they cannot redirect *value*.
6. **Price oracle** — stdlib `IOracle.Spec` (freshness, bounds); none today.
7. **Approve race** — stdlib `increaseAllowance` / `safeApprove` pattern.
8. **CREATE args / S2 constructors** — model: TRUST.md gap; Vault/Cpamm ctor `CALL`.
9. **`decodeOrDefault`** — language: fail closed on bad view payloads (`Amount.as` is already decimals-checked).
