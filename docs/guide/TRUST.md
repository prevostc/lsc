# What is trusted

An end-to-end theorem is a Lean proof about compiled bytecode. It still
rests on foundations that are reviewed or assumed, not proved in this
repo.

## Foundations

- The Lean 4 kernel. The chain uses only the standard axioms `propext`,
  `Classical.choice`, and `Quot.sound`. There is no `sorry`, no
  `native_decide` / `bv_decide`, and no project-specific axiom. CI prints
  the footprint in `Checks`.
- The language spec (`Tx`, external call, the core interpreter, the
  `IERC20` may-model). Reviewed, not proved.
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

For contracts that call out: every successful `CALL` from us to a bound
address conforms to `IERC20` as in [External calls](EXTERNAL_CALLS.md);
the CALL oracle is memory-blind (other contracts cannot see this
contract's private memory, which is true of the EVM) and always returns
(the opcode always returns a success flag and data); powdr's external
model is inhabited. The compiler may have used either the erase path or
powdr spill. The bytecode proof existentially picks a fault oracle so
core and Yul agree on each external outcome. Security statements remain
"for every starting world".

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
Vault/AMM constructors that `CALL` are out of scope.

No bytecode-level reentrancy lock is emitted. Core outside the supported
fragment (including most `letPure`, nested pair returns, and unusual
require/revert/emit arities) is not compiled. Bytecode glue talks about
word-level core; Vault's Amount ABI is identified with the reifier
certificate.

The differential harness (`scripts/difftest.sh`) is defence in depth, not
a proof.

---

For the curious: the Core-to-Yul theorems are `toYulFn_correct_callFree`
and `toYulFn_correct_ext`.
