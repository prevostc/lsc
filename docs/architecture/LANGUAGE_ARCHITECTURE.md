# Language Architecture

Decision record from the September 2026 architecture review. Verdict: **SIMPLIFY** — keep the
language core, replace the backend, delete everything else.

## Shape

```
plain Lean defs in `Tx`  --reify (untrusted) + rfl certificate-->  Core (ANF)
Core  --toYul (ours)-->  Yul AST (powdr yul-semantics)  --powdr compile_correct-->  EVM bytecode
```

## Surface

- A contract function is an ordinary Lean definition in `Tx S X E ε α :=
  ReaderT Ctx (StateT (World S X E) (Except (Err ε))) α`. Users write `do` blocks; theorems are
  stated about the function itself (`Tx.run f ctx w = …`), never about an AST.
  `World S X E` carries storage `self`, external ghosts `ext : X`, `log`, and the fault
  oracle `faults`/`ncalls` (`INTERFACE_MODEL.md`).
- Arithmetic is checked by default (`+?`, `-?`, `*?`, `/?` revert on overflow/underflow/zero);
  wrapping ops are explicit and rare.
- Units are types: `Amount τ s` is a newtype over `ℕ` tagged with an asset marker `τ` and a scale
  `s`. It must be a `structure` (a `def` lets defeq accept unit mixing). Mixed-unit arithmetic is a
  type error; conversions require an explicit rounding mode. For external assets `s` is an
  opaque symbol (unit safety needs only distinctness). `rescale` and `Amount.one` take runtime
  scale words; the reifier rejects a symbolic scale where it would emit a literal. The IERC20
  shim does not live in `Amount.lean`.
- Storage is a Lean `structure`; mappings are `K → V` with default zero (≤ 2 keys).
- Reentrancy: every state-changing entrypoint acquires a transient-storage lock; views check it.
  `@[reentrant]` opt-out is deferred until a use case needs it.
- Not in the language: loops, inline assembly, `delegatecall`, `selfdestruct`, untyped low-level
  calls, dynamic arrays/bytes in storage. External calls go only through a `Binding` of a
  declared `Interface` (see `INTERFACE_MODEL.md`).

## Core: the only IR

- Loop-free ANF over words with de Bruijn locals; compiler denotation `Core.denote : Core → List ℕ →
  Tx …`. Storage fields, events and errors are indices into a generated schema.
  `ContractSchema.ext` supplies `call : Nat → Nat → List Nat → Tx`. Core gains exactly
  `Op.call b m args` and `Stmt.call b m args`. Amount surface programs have a second interp
  `denoteAWord` / `denoteAUnit` used only in `f.core_denote` (same AST; compiler still uses
  `Core.denote`).
  **Interim decision (Sept 2026):** `Amount.ofNat <$> Core.denote = f` is not definitional
  (`Functor.map` does not push through `bind`/`ite`), so the typed interp is the certificate
  target. Its limits: one `(τ, s)` per function, so mixed-unit programs (the Vault) stay on `Nat`
  storage for now. The principled end state is a **type-directed interp with erasure**: Core
  ops tagged with their unit, `denoteTyped` producing surface types, one generic theorem
  `denoteTyped c = ofNat <$> Core.denote (erase c)` proved once by induction, compiler on the
  erased term. Scheduled after the first end-to-end bytecode theorem; not on its critical path.
- The reifier (`lsc_reify`, MetaM) is **untrusted**: every run emits `f.core_denote` by `rfl`,
  kernel-checked — `Core.denote schema f.core args = f args` for word-typed programs, or
  `Core.denoteAWord` / `Core.denoteAUnit` when the surface returns `Amount` or is `Unit` with
  `Amount` storage. A reifier bug is a build error, never a miscompile. Rejections carry a
  positioned message naming the offending subterm.
- `Core.effects` (reads/writes/emits/`calls : List (binding × method)`) with a generic frame
  theorem replaces per-function `f_preserves_x` proofs. The frame includes: no `store` to
  field `f` in any entrypoint ⇒ `f` immutable (bound addresses).
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
  (invariant preservation, authorisation, conservation) plus the per-contract `Inv`
  preserved by `Rely`; AI fills the proofs; frame obligations are discharged generically from
  `Core.effects`.

## Backend

- `toYul : ContractDef → Yul object` (dispatcher, ABI decode/encode, error and Panic encoding,
  Solidity-style storage layout with keccak mapping slots, `tload`/`tstore` lock, `Op.call` /
  `Stmt.call` lowering with a literal gas word because powdr rejects `gas()`).
- `toYul_correct : Core.denote c ≈ YulSemantics.Run (toYul c)` under the layout relation `R` is
  the **only compiler theorem we own**. It is structured-to-structured and loop-free. The
  `letCall` case existentially chooses the fault oracle (`PROOF_CHAIN.md`).
- Yul → bytecode is powdr's `compileObject_correct` (Apache-2.0, pinned commit). We do not
  reason about Yul beyond the statement of `toYul_correct`.

## Toolchain

Lean 4.33 and powdr's Mathlib revision; Lake dependencies `yul-semantics`, `evm-semantics`,
`yul-compiler`, `KeccakEngine` (concrete keccak for selectors and executable tests). EvmYulLean is
dropped.
