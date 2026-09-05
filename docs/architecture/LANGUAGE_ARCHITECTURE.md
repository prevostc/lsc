# Language Architecture

Decision record from the September 2026 architecture review. Verdict: **SIMPLIFY** — keep the
language core, replace the backend, delete everything else.

## Shape

```
plain Lean defs in `Tx`  --reify (untrusted) + rfl certificate-->  Core (ANF)
Core  --toYul (ours)-->  Yul AST (powdr yul-semantics)  --powdr compile_correct-->  EVM bytecode
```

## Surface

- A contract function is an ordinary Lean definition in `Tx S E ε α :=
  ReaderT Ctx (StateT (World S E) (Except (Err ε))) α`. Users write `do` blocks; theorems are
  stated about the function itself (`Tx.run f ctx w = …`), never about an AST.
- Arithmetic is checked by default (`+?`, `-?`, `*?`, `/?` revert on overflow/underflow/zero);
  wrapping ops are explicit and rare.
- Units are types: `Amount τ s` is a newtype over `ℕ` tagged with an asset marker `τ` and a scale
  `s`. It must be a `structure` (a `def` lets defeq accept unit mixing). Mixed-unit arithmetic is a
  type error; conversions require an explicit rounding mode.
- Storage is a Lean `structure`; mappings are `K → V` with default zero (≤ 2 keys).
- Reentrancy: every state-changing entrypoint acquires a transient-storage lock; views check it.
  `@[reentrant]` opt-out is deferred until a use case needs it.
- Not in the language: loops, inline assembly, `delegatecall`, `selfdestruct`, untyped low-level
  calls, dynamic arrays/bytes in storage. External calls go only through declared `Interface`s
  (see `SECURITY_MODEL.md`).

## Core: the only IR

- Loop-free ANF over words with de Bruijn locals; one denotation `Core.denote : Core → List ℕ →
  Tx …`. Storage fields, events and errors are indices into a generated schema.
- The reifier (`lsc_reify`, MetaM) is **untrusted**: every run emits `f.core_denote :
  Core.denote schema f.core args = f args := rfl`, kernel-checked. A reifier bug is a build error,
  never a miscompile. Rejections carry a positioned message naming the offending subterm.
- `Core.effects` (reads/writes/emits/calls) with a generic frame theorem replaces per-function
  `f_preserves_x` proofs.
- No typed Core, no optimisation passes, no gas IR: powdr ships a verified Yul optimiser.

## Arithmetic domains (Q/R/N)

- `ℕ` is the semantic domain; the word bound `2^256` appears only as a revert condition.
- `ℚ` is a proof-side tool for `mulDiv` floor/ceil characterisations, monotonicity and
  rounding-toward-protocol arguments. It never appears in semantics or user-facing statements.
- `ℝ` is not used.
- `BitVec 256` appears only inside `toYul_correct` through one `ℕ ↔ BitVec 256` lemma pack.

## Proof UX

- Primary automation is the `run_*` simp normal form over `Tx.run` plus `omega`; this closes
  Token/Vault theorems in 9–16 lines. `mvcgen'` specs are added only if the Token gate shows the
  need.
- `lsc_contract` generates the statements of the per-entrypoint security obligations
  (invariant preservation, authorisation, conservation); AI fills the proofs; frame obligations are
  discharged generically from `Core.effects`.

## Backend

- `toYul : ContractDef → Yul object` (dispatcher, ABI decode/encode, error and Panic encoding,
  Solidity-style storage layout with keccak mapping slots, `tload`/`tstore` lock, external `call`
  with a literal gas word because powdr rejects `gas()`).
- `toYul_correct : Core.denote c ≈ YulSemantics.Run (toYul c)` under the layout relation `R` is
  the **only compiler theorem we own**. It is structured-to-structured and loop-free.
- Yul → bytecode is powdr's `compileObject_correct` (Apache-2.0, pinned commit). We do not
  reason about Yul beyond the statement of `toYul_correct`.

## Toolchain

Lean 4.33 and powdr's Mathlib revision; Lake dependencies `yul-semantics`, `evm-semantics`,
`yul-compiler`, `KeccakEngine` (concrete keccak for selectors and executable tests). EvmYulLean is
dropped.
