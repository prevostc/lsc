# Language Architecture

Decision record from the September 2026 architecture review. Verdict: **SIMPLIFY** — keep the
language core, replace the backend, delete everything else.

## Shape

```
plain Lean defs in `Tx`  --reify (untrusted) + kernel certificate-->  Core (ANF)
Core  --toYul (ours)-->  Yul AST (powdr yul-semantics)  --powdr compile_correct-->  EVM bytecode
```

## Surface

- A contract function is an ordinary Lean definition in `Tx S X E ε α :=
  ReaderT Ctx (StateT (World S X E) (Except (Err ε))) α`. Users write `do` blocks; theorems are
  stated about the function itself (`Tx.run f ctx w = …`), never about an AST.
  `World S X E` carries storage `self`, external state `ext : X` (compiled contracts use
  the fixed `Lsc.ExtState`), `log`, and the callee `oracle` (`INTERFACE_MODEL.md`).
- Arithmetic is checked by default (`+?`, `-?`, `*?`, `/?` revert on overflow/underflow/zero);
  fused `mulDiv↓` / `mulDiv↑` are `⌊x·y/z⌋` / `⌈x·y/z⌉` (`y`/`z` two `Amount`s or two `Word`s).
  `x *?↓ r` / `x *?↑ r` scale an `Amount` by a `Fixed d` (`⌊x·r/10^d⌋` / ceil). Either operand
  of those ops (and the value of `write`) may be `Tx`; `write f (read f +? x)`
  elaborates (`write` probes `Tx`, checked ops use a binop elaborator). `x.as b` is the
  1:1 retag. Wrapping ops are explicit and rare.
- Units are types: `structure Amount (a : Asset) where raw : Word` (`Lsc/Lang/Amount.lean`).
  `Asset` is `{name : Lean.Name, decimals? : Option Nat}` — `some d` when static (LP shares),
  `none` when decimals are only known on chain. `abbrev Fixed d := Amount (Asset.fixed d)`
  (`Asset.fixed d := ⟨`fixed, some d⟩`; named scales in `Stdlib/Scales.lean`). It must be a
  `structure` (an abbrev would unify every amount back to `Word`). Same-asset `+? -?`;
  `*? /?` only against a `Word` scalar; `*?↓` / `*?↑` only against a `Fixed d` (a non-fixed
  `Amount b` is a type error). Mixed-unit arithmetic is a type error.
- Storage is a Lean `structure`; mappings are `K → V` with default zero (≤ 2 keys).
- Reentrancy during a call is not modelled at Tx (`self` is unchanged). The
  runtime emits `if tload(0) { revert(0,0) }` on every entry; `locks f`
  acquire/release the slot unless `[Reentrant]`. Held-lock revert is proved
  (`lock_held_reverts_*`); S2/transport use `ExtOracle.noReentry`
  (`YUL_TARGET.md`, `TRUSTED_COMPUTING_BASE.md`).
- Not in the language: loops, inline assembly, `delegatecall`, `selfdestruct`, untyped low-level
  calls, dynamic arrays/bytes in storage. External calls go only through an `I.Ref` of a
  declared interface (`deriving Interface`; see `INTERFACE_MODEL.md`).

## Core: the only IR

- Loop-free ANF over words with de Bruijn locals; compiler denotation `Core.denote : Core → List ℕ →
  Tx …`. Constructors: `ret`, `opTail`/`stmtTail`/`revertTail`, `letOp`, `seq`, `letPure`,
  expression-level `ite`, and statement-level `seqIf c th el k` (run `th` or `el`, then `k`
  once — word-like branches bind the result as `var 0` in `k`). Storage fields, events and errors
  are indices into a generated schema.
  There is no binding table: `Op.call` / `Stmt.call` carry a target `Atom`, selector,
  args, and `AbiRet`. `Amount a` is erased to a word by Reify.
- The reifier (`lsc_contract` / `lsc_reify`, MetaM) is **untrusted**: every run emits `f.core_denote`,
  kernel-checked — `Core.denote schema f.core args = f args`. The proof is `rfl`
  when the sides are definitionally equal, otherwise
  the `Tx` monad laws (`bind` is not definitionally associative). A propositional
  certificate is not a trust extension: a reifier bug is still a build error. Rejections
  carry a positioned message naming the offending subterm.
- `Core.effects` (reads/writes/emits/`calls`/`views` : lists of field or selector `Nat`)
  with a generic frame theorem replaces per-function `f_preserves_x` proofs. The frame
  includes: no `store` to field `f` in any entrypoint ⇒ `f` immutable (bound addresses).
- No typed Core, no optimisation passes, no gas IR: powdr ships a verified Yul optimiser.

## Arithmetic domains (Q/R/N)

- `ℕ` is the semantic domain; the word bound `2^256` appears only as a revert condition.
- `ℚ` is a proof-side tool for `mulDiv` floor/ceil characterisations, monotonicity and
  rounding-toward-protocol arguments. It never appears in semantics or user-facing statements.
- `ℝ` is not used.
- `BitVec 256` appears only inside `toYulFn_correct_callFree` / `toYulFn_correct_ext`
  through one `ℕ ↔ BitVec 256` lemma pack.

## Proof UX

- Primary automation is the `run_*` simp normal form over `Tx.run` plus `omega`.
- `lsc_contract` generates the statements of the per-entrypoint security obligations
  (invariant preservation, authorisation, conservation) plus the per-contract `Inv`
  preserved by `RelyAlong`; AI fills the proofs; frame obligations are discharged generically from
  `Core.effects`.

## Backend

- `toYul : ContractDef → Yul object` (dispatcher, ABI decode/encode, error and Panic encoding,
  Solidity-style storage layout with keccak mapping slots, `Op.call` /
  `Stmt.call` lowering with a literal gas word because powdr rejects `gas()`).
  Lock emitted (`lockCheckStmt`; `locks f` `tstore(0,1)` / `tstore(0,0)`);
  held-lock revert proved; `NoReentry` remains until 8C.
- Core → Yul is the compiler theorem this repo owns, in two strata (`DECISIONS.md`):
  `toYulFn_correct_callFree` (S1, closed model) and `toYulFn_correct_ext` (S2, backward
  simulation). Dispatchers:
  `runtimeBlock_correct_callFree` / `runtimeBlock_correct_ext`. Yul → bytecode is powdr's
  `compile_correct` / `compileObject_correct` (Apache-2.0, pinned commit).
- Public compile entry: `Lsc.Compiler.compileContract` (`Pipeline.lean`) →
  `Artifacts {runtimeHex, deployHex, abi, yul, …}`.

## Lake libraries

Lake packages the meaning of programs separately from compilation: `LscSemantics`
is `Lsc.Lang`, `Lsc.Security`, and `Lsc.Util` (Tx monad, World, Core and its
denotation, security trace framework); `Lsc` depends on it and is `Lsc.Compiler`
plus the remaining `Lsc.*` modules (how programs compile and why that is correct).
`Stdlib` sits between `Lsc` and `Examples`. Module names are unchanged.
`scripts/check-layering.sh` forbids semantics files from importing `Lsc.Compiler.*`
and `Lsc/` from importing `Examples.*` or `Stdlib.*`.

## Toolchain

Lean 4.33 and powdr's Mathlib revision; Lake dependencies `yul-semantics`, `evm-semantics`,
`yul-compiler`, `KeccakEngine` (concrete keccak for selectors and executable tests). EvmYulLean is
dropped.
