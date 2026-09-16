# What is trusted

An end-to-end theorem is a Lean proof about compiled bytecode. It still
rests on foundations that are reviewed or assumed, not proved in this
repo.

## Foundations

- The Lean 4 kernel. The chain uses only the standard axioms `propext`,
  `Classical.choice`, and `Quot.sound`. There is no `sorry`, no
  `native_decide` / `bv_decide`, and no project-specific axiom. CI prints
  the footprint in `Checks`.
- The language spec (`Tx`, `Oracle`, `Core.denote`, `IERC20` / `IERC20.Spec`).
  Reviewed, not proved.
- powdr's EVM semantics (relational, conformance-tested) and Yul
  semantics (adequacy proved by its authors), plus the Yul-to-EVM
  compiler: fork `prevostc/yul-compiler` at `30230e1`, which differs
  from upstream powdr `330923e0` only by the classic `switch` lowering
  (jump-on-match, out-of-line bodies), verified in the fork's own
  `Checks.lean` with the same axiom footprint. Pinned in
  `lake-manifest.json`.
- How bytecode storage is read back as contract state (the layout
  relation).
- Keccak: injective on the storage keys we form; the compile-time
  selector engine agrees with the EVM keccak.
- That Ethereum clients implement the specification.

The reifier, the Core-to-Yul compiler, and the Yul-to-EVM compiler are
**checked**, not trusted: each has a theorem. A former home-grown
EVM/codegen stack is gone.

## Hypotheses of the bytecode theorems

The EVM frame is a normal Osaka runtime call (not a precompile, empty
call stack). Gas is existential from powdr's compiler theorem. The
compiler accepted the contract. Worlds, contexts, ABI arguments, and
addresses used as keys fit in a 256-bit word; keccak keys do not collide
with scalar slots.

The trace call step credits incoming value onto `self`'s native balance
only for an accepted payable call; a nonzero-value call to a non-payable
function is a revert step (world unchanged). That matches compiler
`valueOk` / `dispatchedFn`.

For contracts that call out: theorems that mention the token take
`IERC20.Spec` as in [External calls](EXTERNAL_CALLS.md); the CALL oracle
is memory-blind (other contracts cannot see this contract's private
memory, which is true of the EVM) and is a function of the request and
observable world. The compiler may have used either the erase path or
powdr spill. CREATE installs exactly those `compileRuntime` bytes
(`deploy_installs_runtime`), so every runtime theorem covers the
deployed code. The oracle model restores `self`'s storage, transient
storage, and self-attributed logs after every external CALL. This is
justified because (i) in the EVM only a frame executing at address `self`
can write `self`'s storage or emit `self`'s logs (no EXTSLOAD/EXTSSTORE;
CALLCODE/DELEGATECALL by others run at *their* address) — an EVM fact
not mechanized here — and (ii) such a frame is a CALL/STATICCALL into
our runtime, which reverts in the 11-step lock prefix with the parent
snapshot restored (`nested_lock_reverts`, mechanized in 8C-1 against
evm-semantics). ETH balances are not restored: a callee can credit
`self` via `SELFDESTRUCT` without running our code, and `balanceOf` of
other accounts is a real CALL effect. Security statements remain "for
every starting world". Example authors apply `transport_claim_ext` /
`transport_exists_claim_ext` rather than per-contract bytecode theorems.

Other contracts are modelled as deterministic functions of the call and
the on-chain state they can see: the same call against the same
observable world always yields the same response. That is how the EVM
behaves, given the world state and the block environment; every other
contract's storage, balance, and code are already part of that world.
What is excluded is an adversary with hidden state outside the modelled
chain, which no real deployment can exhibit. The previous extra
hypothesis that the CALL oracle always returns a result is now a fact of
this model rather than an assumption.

The adversary is the one in [Security model](SECURITY.md).

## Modelling choices that are not powdr

If a compiled call halts reverted, post-storage is the pre-storage. Raw
powdr runs do not roll back; the project's Yul observation does, to match
`Tx` (a revert discards the world).

Each call in a bytecode trace is modelled as a fresh EVM state with empty
logs; only our storage is tracked across the trace.

The theorems quantify over every halted matching EVM run of an arbitrary
calldata list: unknown selectors are no-ops (empty revert), decoded calls
are the security steps. powdr's compiler theorem is forward (Yul run
implies some EVM steps). Progress plus EVM determinism identifies every
halted matching run, so powdr's "every EVM execution is a Yul run" is not
required.

## Not covered

Yul constructors follow the Solidity CREATE convention (arguments as a
suffix of `env.code`). The EVM deploy theorem starts from init code with
empty calldata and no trailing bytes, so **appended constructor arguments
are not in that EVM model**. Runtime theorems exclude constructors.
Vault/Cpamm constructors that `CALL` are out of scope.

The runtime emits `if tload(0) { revert(0,0) }` on every entry
(`lockCheckStmt`), including `[Reentrant]` functions. Functions with
`locks f` (`¬reentrant ∧ hasExtCall ∧ ¬ isPureRead`) `tstore(0,1)` after
the size guard and `tstore(0,0)` before committing `return`/`stop`.
`[Reentrant]` skips acquire/release; a store after an external call is
rejected unless `[Reentrant.Unsafe]`. Held lock ⇒ revert, empty returndata,
committed storage/transient/logs unchanged (`lock_held_reverts_yul`,
`lock_held_reverts_yul_open`, `lock_held_reverts_evm`; no oracle
hypothesis). A nested CALL/STATICCALL into the compiled runtime while the
lock is held reverts in the prefix and restores the parent snapshot
(`nested_lock_reverts`). These lock theorems keep their current
statements (the prologue is still per-runtime). Core outside the supported
fragment (including most `letPure`, nested pair returns, and unusual
require/revert/emit arities) is not compiled. Bytecode glue talks about
word-level core; Vault's Amount ABI is identified with the reifier
certificate.

The differential harness (`scripts/difftest.sh`) is defence in depth, not
a proof.

---

For the curious: the Core-to-Yul theorems are `toYulFn_correct_callFree`
and `toYulFn_correct_ext`.
