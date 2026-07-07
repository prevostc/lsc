# Framework note: `LocalEnv` and the `accrueInterest` `native_decide` case

Framework-developer note on a proof-engineering issue hit (and fixed at the language level) while
proving `examples/interest/test/InterestTheorems.lean`'s `accrueInterest_computes_correctly`/
`accrueInterest_reverts_on_overflow`. Not needed to *use* the framework — see
[reference/INTEREST.md](../reference/INTEREST.md) for the contract-author-facing summary.

`accrueInterest`'s two theorems are stated against a fully *concrete* `ContractState` and proved by
`native_decide`, unlike every other theorem in the reference contracts (which are universally
quantified and proved by `simp`/`omega`). The original cause: `LocalEnv` (threading `tx`-local
`let`-bound variables through evaluation) used to be an opaque closure, unfoldable only via `simp`'s
expensive function-extensionality machinery. Making it a plain inductive list, reducible via
ordinary `dsimp`/`simp` structural recursion, converts what used to be an *unbounded* `simp` blowup
(multi-GB memory, no bound) into a bounded, deterministic run for any `tx` — a real, general fix,
not specific to this contract.

For `accrueInterest` specifically, that bounded run (~110s) now fully resolves the local-variable/
storage-field plumbing and the two chained checked ops (via the `rw`-friendly
`Wad.addChecked_eq_ok_of`/`_error_of`, `Wad.mulHalfUpChecked_eq_ok_of`/`_error_of` lemmas in
`Lsc/Lib/Wad/Eval.lean`), leaving only a small, fully concrete residual about the `emit` argument's
`List.mapM` traversal — closing that residual with any further tactic re-triggers cost from the
sheer size of the already-substituted term (a kernel type-checking cost, confirmed by a `(kernel)
deep recursion detected` failure, not a tactic-search issue). A fully `native_decide`-free proof for
`accrueInterest` hasn't been found yet; `native_decide` remains the pragmatic choice.
`deposit`/`setRate` never needed it since they only chain one checked op each and don't read a
`let`-bound variable back out via `emit`.

Plain `decide` is avoided throughout the codebase for a related reason: kernel reduction on 256-bit
`BitVec` values, or on large generated interpreter terms, is prohibitively slow. Every concrete
check uses `native_decide` or is phrased as a pure-`Nat` side condition discharged by
`norm_num`/`omega`.
