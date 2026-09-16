Status: in progress
Slice: 1 of 4
Written against HEAD `8863bb8`

# Internal calls (Core → Yul functions)

Today both `@[internal]` and `@[internal inline]` are substituted (`Lsc/Lang/Inline.lean`, `Reify.deltaUnfold`). Goal: `InternalKind.call` → one Yul `function` (JUMP-called); `InternalKind.inline` stays substituted. User theorems stay on `Tx.run`. No new TCB hypothesis.

## 1. Core IR

**Table** on `ContractDef` (`Lsc/Lang/Contract.lean`), not `ContractSchema`:

```
structure InternalDef where
 ident : String -- Yul name `i_{n}`
 arity : Nat -- word args
 ret : RetTy
 body : Core ret
-- ContractDef.internals : List InternalDef
```

**Constructors** on `Core` (`Lsc/Lang/Core.lean`); do **not** reuse `Op.call` / `Stmt.call` (ABI CALL/STATICCALL):

```
| letCall {t u} (f : Nat) (args : List Atom) (k : Core u) : Core u
| callTail {t} (f : Nat) (args : List Atom) : Core t
```

`letCall` is ANF bind (like `letOp`); `callTail` is tail position (like `opTail`/`stmtTail`). Unit discard = `callTail` at `.unit` (or `letCall` + ignore). Extend `Core.rename`, `seqUnit`, `bindWord`/`bindAddr`/`bindFlag`, `Core.effects`, `storeAfterCallSeen`, `coreWF`, `coreExtraDepth` (`YulDefs.lean`).

**Typing.** Args are words (`Atom`); `Amount`/`Address`/`Flag` already erased by Reify. No `Field`/`Fields`/`SwapDirection` as args (not runtime). Returns are existing `RetTy` (`.unit | .word | .addr | .flag | .pair`). Flatten with `retAtoms`/`retWords`. Nested pairs flatten left-to-right. Arity cap: flattened return length ≤ 16 (yul-compiler `.funDef` rejects `rs.length > 16`). Bind flattened rets de Bruijn: last word `var 0` (matches `let (a,b) ←`).

**Denotation** (`Core.denote` gains `tbl : List InternalDef`, default `[]`):

```
denote Γ tbl (.callTail i args) env
 = denote Γ tbl (tbl[i].body) (args.map (·.eval env))
denote Γ tbl (.letCall i args k) env
 = denote Γ tbl (.callTail i args) env >>= fun v =>
 denote Γ tbl k (flatten v ++ env)
```

Call-by-value at the evaluated arg env (not syntactic atom subst). Certificate Link 1 becomes `Core.denote C.schema C.contract.internals f.core args = f args`.

**Recursion.** Lsc has none. (1) `validateInternal` rejects self-const (`Inline.lean`). (2) `assembleContract` (`Reify.lean`): DFS on `InternalKind.call` names; reject cycles. (3) Store internals in topo order (callees first). `coreWF`: `f < tbl.length`, `args.length = arity`, calls only to strictly smaller `f`. `denote` well-founded on `(f, sizeOf core)`. Ill-indexed lookup → `Tx.revert` dummy (rejected by `coreWF`/`toYulFn = none`).

`Core.effects (.letCall i …)` = `effects tbl[i].body ∪ effects k`. `hasExtCall`/`isPureRead`/`locks` follow callees so a thin `swap0for1` wrapper still locks.

## 2. Reifier

`InternalKind.inline` / `isRefMethod` / ERC20 six entrypoints: keep `deltaUnfold` (fuel 8). `InternalKind.call` application: do not unfold. Split args: compile-time (specialise; not Yul params): `Field`/`ERC20.Fields`, `SwapDirection` ctor, `Asset`, typeclass `[Events]`/`[Errors]`, other closed non-word structs. Runtime → `Atom`s: `Address`, `Amount`, `Word`, `Flag`/`Bool`. Key = `(const Name, fingerprint of closed specialised args)`; one `InternalDef` per key per contract. `Cpamm.swap d`: two internals; non-literal `d` rejected. `[Payable]`/`[Reentrant]` stay entrypoint binders; internals get no dispatcher `callvalue()`/`tstore`; body may still `Tx.value`. Certificates: emit `i_n.core_denote` once; caller certificate uses `denote_letCall` + callee certificate; `InternalKind.call` names drop from the unfold list. `lsc_contract` still rejects listing an `@[internal]`.

## 3. Yul emission

`runtimeBlock` (`YulDefs.lean`), after `memoryGuardStmt`/`lockCheckStmt`, before the calldata-size guard: `function i_n(i_n_0, …) -> i_n_r0, … { … }` (0 rets: no `->`); `emitCoreInternal`: haltUnit=false, clearLock=false. Dispatcher cases emit `let … := i_n(v_…)`/`i_n(v_…)`. Internal `ret`: assign flattened words to `i_n_r*`, fall through. Do not emit `return(0x80,…)`/`stop()`/lock-clear. `revert`/require-fail/extcall-fail keep `revert(...)`; never `leave`. `coreWF` enforces ≤ 16 rets; yul-compiler frames may push past DUP16 — `compileBlock` must still succeed. Constructor (`toYulCtor`): expand internals (slices 1–3). `noExtExpr` treats Yul `.call f args` as non-external.

## 4. Correctness chain

User theorems unchanged. Link 1 threads `tbl`. This repo: `toYulFn_correct_callFree` (`SimM1` cases), `toYulFn_correct_ext`/`core_sim_ext_callFree` (`SimExt`), `runtimeBlock_correct_{callFree,ext}` (hoist `funDef`s), `CallFree`/`S2Frag`/`M1Frag` (allow `letCall` iff callee in fragment), `worldAfter_callFree_congr`, `effects_frame`, `locks`/`storeAfterCall`. New lemma `sim_letCall`/`toYulInternal_correct`: `Tx.run (denote tbl[i].body args)` vs Yul `Step.callOk`/`callHalt` (yul-semantics `BigStep.lean`). Yul→EVM already covered by `YulEvmCompiler.compile_correct` (functions/leave/≤16 rets). New hypothesis `internalsWF c` + `toYulInternals c = some …`, bundled into `toYulFn c f = some yul`/`runtimeBlock c = some rt` — compiler acceptance, not a new axiom.

## 5. Phasing

Slice 1: Core constructors + `tbl` denote + WF/effects/locks; `emitCore` expands (bytecode identical). Slice 2: reifier `InternalKind.call` → intern + `letCall`; certificates via callee `core_denote`; still expand. Slice 3: real `funDef` emission + `sim_letCall` for S1 (`CallFree`); Token+WETH hex change. Slice 4: S2 `SimExt` + Cpamm. Size: Cpamm `swap` −1.4–1.5 KB (~25%); Token/WETH +40–80 B per one-site function.

## 6. Owner decisions (fixed)

1. `SwapDirection`: specialise into two Yul functions. 2. Constructor: expand internals. 3. One-site helpers still `InternalKind.call` (size must not grow with sites; users may mark `@[internal inline]`). 4. `compileBlock = none` after frames → reject compile, never silently re-inline. 5. Flatten `RetTy.pair` up to 16; nested-pair `seqIf` rejected as today.

## 7. Cleanup

Rename theorem `Token.erc20` → `Token.token_spec`; lens `Token.base` → `Token.erc20`; Checks pin follows; docs: `docs/internals/{TRUSTED_COMPUTING_BASE,PROOF_CHAIN,INTERFACE_MODEL}.md`, `docs/guide/{CONTRACTS,EXTERNAL_CALLS}.md`, `Examples/Token/README.md`.
