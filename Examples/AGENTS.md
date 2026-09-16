# `Examples/<Name>/`

Exactly:

- `Contract.lean` — module docstring (what the contract does, for a Solidity
  developer, ≤8 lines); `Asset` / `Chain` constants (`def chain : Chain := .ethereum`,
  `abbrev native := Chain.native chain`);
  `Storage`, `Event`, `Error`; the
  user-facing functions, each with a one-line docstring; the single
  `lsc_contract` line. `Contract.lean` may `extends` a Stdlib storage and
  re-export base entrypoints (`def transfer := ERC20.transfer erc20`).
  `[Payable]` / `[Reentrant]` / `[Reentrant.Unsafe]`
  instance binders may sit on a user-facing function. `instance` is
  allowed only for Stdlib `Events` / `Errors`. `write f (read f op x)`
  elaborates directly (`write` elaborates the argument at `M`; fallible ops
  accept `M` on either side). Nested `←` (`(← (←`) is forbidden. FORBIDDEN: `theorem`, `lemma`, `example`,
  `@[simp]`, `#guard`, `#eval`, `#check`, `#guard_msgs`, any
  `.core`/`core_denote`/`Core.*`/`Spec.exec` mention, `Amount.ofWord`/`.raw`/
  word-level plumbing, helper duplicates (`*Raw`, `*U`, `*Unit`, `*Impl`
  suffixes), named arithmetic where an operator exists (`+? -? *? /?`,
  `mulDiv↓`/`mulDiv↑`). `@[internal]` / `@[internal inline]` helpers are
  allowed (not listed in `lsc_contract`).
- `Spec.lean` — invariant, rely, authorisation/value predicates, named world
  readers (e.g. `holdings w`), and `spentCall` (amount an accepted call moved
  out on `a`'s authority). No theorems, no proofs. `Inv` / `Auth` / `claim`
  are proof machinery consumed by `Proofs/Security.lean`, not public
  hypotheses.
- `Theorems.lean` — every exposed theorem about the *contract*: Tx-level
  deltas, security, `implements` conformance. Trace theorems quantify
  `State C` and `Txs w` with conclusions in storage fields; no `Inv` /
  `Wf` / `RelyAlong` / `NoAuthAlong` hypotheses. Honest-counterparty
  (`IERC20.Spec`, `TokensIndependent`) lives in `HasDeploy` / `State`.
  Per-call theorems that need nothing about the environment (Token, WETH,
  Counter, Cpamm swaps, Vault `deposit_shares` / `withdraw_shares`) stay
  over `C.World` with `msg : Ctx`. Per-call theorems whose conclusion
  depends on an external contract (Vault `deposit_holdings` /
  `withdraw_holdings`) quantify `w : State` and `msg : Msg w` (`sender ≠
  self`; the honest token is `w.reachable`); do not put `IERC20.Spec` on
  the theorem. Plain-language docstring on each; body is a one-line
  reference into `Proofs/`. NO
  compiler/bytecode theorems: the compiler's theorems quantify over all
  contracts, per-contract instances add nothing.
- `Proofs/` — `Tx.lean`, `Security.lean`, `Implements.lean` (when the contract
  implements an interface), `Compile.lean` (only the
  `#guard (compileRuntime C.contract).isSome` witness and, if a contract needs
  the memory-spill path, a comment saying so), plus helper files. All proof
  code lives here.
- `Tests.lean` — executable smoke `#guard`s, `#eval`s, negative `#guard_msgs`.
- `README.md` — what it does, what is proved (prose, no Lean names beyond
  theorem names), what is assumed of external contracts, one line per file.
- `compiled/` — generated artefacts (unchanged policy).

`Checks.lean` imports `Examples.<Name>.Theorems` only. Agents update
`Checks.lean` when a pinned theorem is added or renamed. This is the
example-level instance of the Theorems/Proof split in `Lsc/AGENTS.md`; the
docstring checker treats `Theorems.lean` as a Theorems file (glob
`*Theorems.lean` matches).

Theorem hygiene per root `AGENTS.md` (success as hypothesis, delta form, no
unnecessary hypotheses, no edge-case exclusions unless genuinely false).
`scripts/check-examples.sh` enforces the Contract/Theorems layout.

Proof performance (`Proofs/Tx.lean`, budget: whole file ≤ 10 s, never
`maxHeartbeats`): peel the monadic body with `rw [fn, run_req_*,
run_*_binds, …]` and `simp only` with a small set; never `simp [fn, …]` on
the whole body. Success-shape lemmas (`∃ …, Tx.run … = .ok …`) must not
mention external `Tx.run (call …)` terms in their `∃` — the kernel
re-checks the CALL every time they are destructured (Vault: 40 s per
`rcases`). State the post-condition on the tail after the call instead.
