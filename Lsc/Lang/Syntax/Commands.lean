import Lsc.Lang.Syntax.CrossCall

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Meta Lean.Parser.Term

namespace Lsc.Syntax

/-- `tx <name> { <lscStmt>* }` — the delimiter/entry point. Buffers its raw `lscStmt*` syntax
under the current namespace (`Lsc.Deriving.contractTxSyntaxExt`) rather than elaborating
immediately; `Lsc.Deriving.flushContractTxs` (run by `derive_contract_def`/`derive_contract`)
elaborates and emits the real `def name : Stmt := ...` declarations later, all at once — see
`docs/decisions/0007-tx-body-elaboration-deferred.md` for why.

`@nonreentrant` — decorates the immediately-following `tx`, marking it as performing a mutating
cross-contract `exec`. This `elab` requires the decorator on (and only on) any `tx` whose body
contains a top-level `exec` node; `read`-only txs are exempt. A `tx` with neither compiles the
same whether or not it is decorated (the decorator is a requirement for `exec`, not a universal
precondition). Modeled as a plain optional leading atom on `tx`'s own `elab` (rather than Lean's
general `declModifiers`/`@[attr]` machinery, which targets `structure`/`def`/... declarations
`tx` isn't one of) — the same "optional trailing/leading Syntax group" technique
`derive_contract_def`'s `(functions)?`/`(topic0)?`/`(ctor)?` groups already use just below. -/
elab nrStx:("@nonreentrant")? "tx " name:ident params:(optional("(" lscTxParam,* ")")) "{" stmts:lscStmt* "}" : command => do
  let ns ← getCurrNamespace
  let fnName := ns ++ name.getId
  let isNonReentrant := nrStx.isSome
  let paramsStx : Array (TSyntax `lscTxParam) :=
    if params.raw.getNumArgs > 0 then
      params.raw[1]!.getSepArgs.map fun s => (⟨s⟩ : TSyntax `lscTxParam)
    else #[]
  let paramsResolved ← liftTermElabM <| paramsStx.toList.mapM elabTxParam
  -- `name.raw` (the plain, un-namespaced ident) is kept alongside `fnName` (the fully-qualified
  -- one) so `flushContractTxs` can later declare `def name : Stmt := ...` with the *plain* name
  -- — letting Lean prepend the (then-current) namespace itself, exactly once — while still using
  -- `fnName` for `contractFnsExt` bookkeeping/cross-referencing.
  modifyEnv fun env =>
    Lsc.Deriving.contractTxSyntaxExt.modifyState env fun m =>
      m.insert ns ((m.find? ns |>.getD []) ++ [(fnName, name.raw, paramsResolved, stmts.map (·.raw))])
  -- Also stash each parameter's *un-resolved* `(name, ty)` syntax verbatim, keyed by this `tx`'s
  -- own fully-qualified `fnName` (`Lsc.Deriving.contractParamTyExt`'s docstring) — consulted both
  -- by `flushContractTxs`'s cross-contract-call branch (for *this* `tx`'s own signature) and, from
  -- a different contract's module entirely, by `elabExecOrReadTerm` (to bridge an `exec`/`read`
  -- call's arguments against *this* `tx`'s real declared parameter types).
  stashParamTys fnName paramsStx
  if isNonReentrant then
    modifyEnv fun env => Lsc.Deriving.contractNonReentrantExt.modifyState env (·.insert fnName true)
  -- `exec` requires `@nonreentrant` (desugars to `Stmt.reentrancyGuard`); `read` alone does not.
  -- Syntax rejects bare `exec` early; `Checks.checkNonReentrant` enforces the same on `ContractDef`.
  if stmtsUseExec stmts then
    unless isNonReentrant do
      throwErrorAt name "`{name.getId}` uses `exec`, but is not marked \
`@nonreentrant` — add `@nonreentrant` immediately before `tx {name.getId}(...)` \
(i.e. `@nonreentrant tx {name.getId}(...) \{ ... }`)"
    modifyEnv fun env => Lsc.Deriving.contractExecCallExt.modifyState env (·.insert fnName true)

/-- `constructor (p : ty, ...) { <lscStmt>* }` — deployment initializer. Buffered under
`Lsc.Deriving.contractCtorSyntaxExt` and elaborated by `flushContractCtor` at `derive_contract`
time (same deferred pattern as `tx`). At most one per namespace. -/
elab "constructor " params:(optional("(" lscTxParam,* ")")) "{" stmts:lscStmt* "}" : command => do
  let ns ← getCurrNamespace
  if (Lsc.Deriving.contractCtorSyntaxExt.getState (← getEnv)).find? ns |>.isSome then
    throwError "only one `constructor` block is allowed per contract namespace"
  let paramsStx : Array (TSyntax `lscTxParam) :=
    if params.raw.getNumArgs > 0 then
      params.raw[1]!.getSepArgs.map fun s => (⟨s⟩ : TSyntax `lscTxParam)
    else #[]
  let paramsResolved ← liftTermElabM <| paramsStx.toList.mapM elabTxParam
  modifyEnv fun env =>
    Lsc.Deriving.contractCtorSyntaxExt.modifyState env fun m =>
      m.insert ns (some (paramsResolved, stmts.map (·.raw)))

/-- Elaborate and emit the buffered `constructor { .. }` body for the current namespace. -/
def flushContractCtor : CommandElabM Unit := do
  let ns ← getCurrNamespace
  match (Lsc.Deriving.contractCtorSyntaxExt.getState (← getEnv)).find? ns with
  | none | some none => pure ()
  | some (some (params, stmtsRaw)) =>
    let stmts : Array (TSyntax `lscStmt) := stmtsRaw.map (⟨·⟩)
    let implId := mkIdent `constructorImpl
    let bodyTerm ← liftTermElabM do
      let storageName ← Lsc.Deriving.currContractStorageName
      let (t, _) ← elabStmtList storageName params stmts
      return t
    elabCommand (← `(command| def $implId : Lsc.Stmt := $bodyTerm))
    let implFnName := ns ++ `constructorImpl
    modifyEnv fun env =>
      Lsc.Deriving.contractCtorFnsExt.modifyState env fun m =>
        m.insert ns (some (implFnName, params))
  modifyEnv fun env => Lsc.Deriving.contractCtorSyntaxExt.modifyState env (·.insert ns none)

/-- `view name(params) : RetTy { <lscStmt>* }` — a read-only, value-returning function
declaration (the DSL counterpart of a hand-written hand-written `def balanceOf (..) : ContractM
... Wad := fun s => ...`, see `examples/escrow/src/Token.lean`'s pre-`view` `balanceOf`). Every
control-flow path through the body must end in a `return e;` of the declared `RetTy`
(`Checks.checkViewReturns`, enforced once the full `ContractDef` exists — at buffering time here
we only resolve `RetTy` itself, exactly like a `tx` parameter's `ty`). The body must also never
mutate storage or emit an event (`Checks.checkViewPurity`) — a `view` is meant to be a pure,
`STATICCALL`-style read (`Core/ContractM.lean`'s `PairM.read`).

Like `tx`, buffers its raw `lscStmt*` syntax under the current namespace
(`Lsc.Deriving.contractViewSyntaxExt`) rather than elaborating immediately, for the same reason
(`σ.field`'s storage `Ty` isn't registered yet) — `flushContractViews` (run by
`derive_contract_def`/`derive_contract`, alongside `flushContractTxs`) elaborates and emits the
real `def`s later.

**Why the generated return type stays generic `Val Ty.wad` (no per-token tag), unlike a
cross-contract `tx`'s parameter (see `flushContractTxs`'s cross-call branch):** `Val`/`Ty`
(`Lsc/Lang/AST.lean`, `Lsc/Core/ContractM.lean`) are the DSL's single, global, tag-erased sum
types — `Ty.wad` has no slot for `Fixed`'s `tag` parameter at all, so there is no Lean type to
attach the author's declared `RetTy` (e.g. `Token.Amount`) to at this boundary; retagging the
`Wad` payload *inside* a `Val.wad` before returning it would change nothing about the function's
visible return type, which stays `Val Ty.wad` either way. This is consistent with today's actual
attack surface: a `read`'s result is always discarded (`composeSegments`'s `>>= fun _ => ..`,
`isExecOrReadStmt`'s docstring) — there is no `let x = read Target.fn(..);` syntax yet to capture
it into a tagged local at all. `Fixed.retag` (`Lsc/Lib/Wad/Syntax.lean`) exists precisely for the
day that changes: once a `view`'s result can be captured by name with its own declared `RetTy`,
the capture site (not this generated `def`'s signature) is where `Fixed.retag` should be applied,
exactly the same way a cross-contract `tx` parameter's exact declared type is threaded through
today. -/
elab "view " name:ident params:(optional("(" lscTxParam,* ")")) " : " retTy:ident
    "{" stmts:lscStmt* "}" : command => do
  let ns ← getCurrNamespace
  let fnName := ns ++ name.getId
  let paramsStx : Array (TSyntax `lscTxParam) :=
    if params.raw.getNumArgs > 0 then
      params.raw[1]!.getSepArgs.map fun s => (⟨s⟩ : TSyntax `lscTxParam)
    else #[]
  let paramsResolved ← liftTermElabM <| paramsStx.toList.mapM elabTxParam
  let retKind ← liftTermElabM <| elabLscTyIdent retTy
  stashParamTys fnName paramsStx
  modifyEnv fun env =>
    Lsc.Deriving.contractViewSyntaxExt.modifyState env fun m =>
      m.insert ns ((m.find? ns |>.getD []) ++
        [(fnName, name.raw, paramsResolved, retKind, stmts.map (·.raw))])

/-- `view name(params) : RetTy => e;` — expression-shorthand form of `view`, for the common
single-expression case (e.g. `view balanceOf(who : Address) : Wad => σ.balances[who];`).
Desugars to the block form's `return e;`, then buffers exactly the same way. -/
elab "view " name:ident params:(optional("(" lscTxParam,* ")")) " : " retTy:ident
    " => " e:lscExpr ";" : command => do
  let ns ← getCurrNamespace
  let fnName := ns ++ name.getId
  let paramsStx : Array (TSyntax `lscTxParam) :=
    if params.raw.getNumArgs > 0 then
      params.raw[1]!.getSepArgs.map fun s => (⟨s⟩ : TSyntax `lscTxParam)
    else #[]
  let paramsResolved ← liftTermElabM <| paramsStx.toList.mapM elabTxParam
  let retKind ← liftTermElabM <| elabLscTyIdent retTy
  let retStmt ← `(lscStmt| return $e ;)
  stashParamTys fnName paramsStx
  modifyEnv fun env =>
    Lsc.Deriving.contractViewSyntaxExt.modifyState env fun m =>
      m.insert ns ((m.find? ns |>.getD []) ++
        [(fnName, name.raw, paramsResolved, retKind, #[retStmt.raw])])

/-- Elaborate and emit every `view name(..) : Ty { .. }`/`view name(..) : Ty => e;` body buffered
so far under the current namespace (`Lsc.Deriving.contractViewSyntaxExt`) into real `def`s,
mirroring `flushContractTxs` — see that function's docstring for the general shape. Two `def`s
are always emitted per `view` (unlike `flushContractTxs`'s zero-arg optimization): a hidden
`name.Impl : Lsc.Stmt` holding the raw, `Expr.var`-parameterized body (the one
`elabContractDefBody` embeds into `FunctionDef.body` for the bytecode/Yul pipeline, via
`Lsc.Deriving.contractViewFnsExt`), and the real, callable `name : .. → ContractM S E Err (Val
retKind) := ..` built with `Stmt.evalView`, which literal-embeds each parameter into a fresh
`Stmt.letBind` (exactly like `flushContractTxs`'s parameterized case) before calling
`Stmt.evalView` on the result. -/
def flushContractViews : CommandElabM Unit := do
  let ns ← getCurrNamespace
  let pending := (Lsc.Deriving.contractViewSyntaxExt.getState (← getEnv)).find? ns |>.getD []
  for (fnName, nameRaw, params, retKind, stmtsRaw) in pending do
    let stmts : Array (TSyntax `lscStmt) := stmtsRaw.map (⟨·⟩)
    let nameId : Lean.Ident := ⟨nameRaw⟩
    let implId := mkIdent (Name.mkSimple (nameRaw.getId.toString ++ "Impl"))
    let bodyTerm ← liftTermElabM do
      let storageName ← Lsc.Deriving.currContractStorageName
      let (t, _) ← elabStmtList storageName params stmts
      return t
    elabCommand (← `(command| def $implId : Lsc.Stmt := $bodyTerm))
    let retTypeTerm ← liftTermElabM do
      let storageName ← Lsc.Deriving.currContractStorageName
      let (errName, eventName) ← Lsc.Deriving.currContractTypes
      let storageId := mkIdent storageName
      let errId := mkIdent errName
      let eventId := mkIdent eventName
      let retTyConst ← retKind.tyConst
      `(Lsc.ContractM $storageId $eventId $errId (Lsc.Val $retTyConst))
    if params.isEmpty then
      let bodyTerm2 ← liftTermElabM do
        let retTyConst ← retKind.tyConst
        `(Lsc.Stmt.evalView $retTyConst $implId)
      elabCommand (← `(command| def $nameId : $retTypeTerm := $bodyTerm2))
    else
      let sigTerm ← liftTermElabM do
        let paramTys ← params.mapM (·.2.leanTypeStx)
        paramTys.foldrM (init := retTypeTerm) fun ty acc => `($ty → $acc)
      let fullBody ← liftTermElabM do
        let wrappedBody ← params.foldrM (init := (← `($implId))) fun (pname, k) acc => do
          let pid : Term := ⟨mkIdent (Name.mkSimple pname)⟩
          let tyConst ← k.tyConst
          let litStx ← k.embedLitStx pid
          `(Lsc.Stmt.seq (Lsc.Stmt.letBind $(quote pname) ⟨$tyConst, $litStx⟩) $acc)
        let retTyConst ← retKind.tyConst
        let evalTerm ← `(Lsc.Stmt.evalView $retTyConst $wrappedBody)
        params.foldrM (init := evalTerm) fun (pname, _) acc => do
          let pid := mkIdent (Name.mkSimple pname)
          `(fun $pid:ident => $acc)
      elabCommand (← `(command| def $nameId : $sigTerm := $fullBody))
    let implFnName := ns ++ Name.mkSimple (nameRaw.getId.toString ++ "Impl")
    modifyEnv fun env =>
      Lsc.Deriving.contractViewFnsExt.modifyState env fun m =>
        m.insert ns ((m.find? ns |>.getD []) ++ [(fnName, implFnName, params, retKind)])
  modifyEnv fun env => Lsc.Deriving.contractViewSyntaxExt.modifyState env (·.insert ns [])

/-- Elaborate and emit every `tx name { .. }` body buffered so far under the current namespace
(`Lsc.Deriving.contractTxSyntaxExt`) into a real `def name : Lsc.Stmt := ...`, exactly as
`tx` itself used to do inline — see `tx`'s docstring above for why this is now deferred rather
than immediate. Also pushes each name into `Lsc.Deriving.contractFnsExt`, matching `tx`'s old
self-registration, so `derive_contract_def`'s auto-derived `functions` list still works
unchanged. Clears the namespace's buffer once flushed, so re-running (e.g. a stray second
`derive_contract_def` in the same namespace) is a no-op rather than re-emitting duplicate
`def`s. -/
def flushContractTxs (libraryMode : Bool := false) : CommandElabM Unit := do
  let ns ← getCurrNamespace
  let pending := (Lsc.Deriving.contractTxSyntaxExt.getState (← getEnv)).find? ns |>.getD []
  let execCallState := Lsc.Deriving.contractExecCallExt.getState (← getEnv)
  let nonReentrantState := Lsc.Deriving.contractNonReentrantExt.getState (← getEnv)
  let paramTyState := Lsc.Deriving.contractParamTyExt.getState (← getEnv)
  for (fnName, nameRaw, params, stmtsRaw) in pending do
    let stmts : Array (TSyntax `lscStmt) := stmtsRaw.map (⟨·⟩)
    let nameId : Lean.Ident := ⟨nameRaw⟩
    let bodyTerm ← liftTermElabM do
      let storageName ← Lsc.Deriving.currContractStorageName
      let (t, _) ← elabStmtList storageName params stmts
      let wrapped ← if (nonReentrantState.find? fnName).getD false then
          `(Lsc.Stmt.reentrancyGuard $t)
        else
          pure t
      return wrapped
    let isExecTx := (execCallState.find? fnName).getD false
    let needsPairMDef ← liftTermElabM do
      if !isExecTx then return false
      for s in stmts do
        match s with
        | `(lscStmt| exec $fn:ident ( $_,* ) ;) =>
          if splitSigmaMethodCall? fn.getId |>.isNone then
            let fnName := fn.getId
            let env ← getEnv
            let libNs := fnName.getPrefix
            let isLibrary := Lsc.Deriving.isLibraryModule env libNs &&
              (env.contains (Lsc.Deriving.libraryInlineConstName libNs) ||
                List.any (Lsc.Deriving.getLibraryEntries libNs env) fun (entryFn, _, _) =>
                  entryFn == fnName)
            unless isLibrary do
              return true
        | _ => pure ()
      return false
    -- PairM proof-layer `def` for cross-module `exec` txs (e.g. `exec Token.transfer(..)`).
    -- Interface-only `exec σ.field.method(..)` txs keep Stmt `*Impl` only — proofs use
    -- hand-written `IERC20Spec` lemmas (`releaseHonest`, etc.) instead.
    if needsPairMDef then
      let bodyPairM ← liftTermElabM do
        let storageName ← Lsc.Deriving.currContractStorageName
        let (errName, eventName) ← Lsc.Deriving.currContractTypes
        let raw ← elabStmtListPairM storageName params params stmts
        let storageId := mkIdent storageName
        let errId := mkIdent errName
        let eventId := mkIdent eventName
        `(($raw : Lsc.ContractM.PairM $storageId _ $eventId $errId _))
      let origParamTys : List (String × Name) := paramTyState.find? fnName |>.getD []
      let wrappedPairM ← liftTermElabM do
        params.foldrM (init := bodyPairM) fun (pname, k) acc => do
          let pid := mkIdent (Name.mkSimple pname)
          let tyStx : Term ← match origParamTys.find? (·.1 == pname) with
            | some (_, tyName) => pure ⟨mkIdent tyName⟩
            | none => k.leanTypeStx
          `(fun ($pid : $tyStx) => $acc)
      elabCommand (← `(command| def $nameId := $wrappedPairM))
    -- `stmtDefFnName` is the fully-qualified name of whichever `def` actually holds the
    -- parameter-free `Stmt` value (`fn.body`'s ABI/bytecode-facing shape — see
    -- `Lsc.Deriving.contractFnsExt`'s docstring): for the zero-arg (unchanged) case that's just
    -- `nameId` itself; for the parameterized case it's a separate, hidden `nameId.Impl` def
    -- holding the raw (still-`Expr.var`-parameterized) body, with `nameId` itself instead
    -- becoming the real *callable* `def nameId (p1 : ty1) ... : Stmt := ...` — see this
    -- function's module-level design note in `Lsc.Deriving.contractFnsExt`.
    -- `exec` txs reserve the plain `nameId` for the PairM proof `def` above, so their Stmt
    -- body always lives in a hidden `nameImpl` def instead (same suffix as the parameterized
    -- non-`exec` case).
    let stmtDefFnName ← if isExecTx && !libraryMode then
        let implId := mkIdent (Name.mkSimple (nameRaw.getId.toString ++ "Impl"))
        elabCommand (← `(command| def $implId : Lsc.Stmt := $bodyTerm))
        pure (ns ++ Name.mkSimple (nameRaw.getId.toString ++ "Impl"))
      else if params.isEmpty then
        elabCommand (← `(command| def $nameId : Lsc.Stmt := $bodyTerm))
        pure fnName
      else do
        let implId := mkIdent (Name.mkSimple (nameRaw.getId.toString ++ "Impl"))
        elabCommand (← `(command| def $implId : Lsc.Stmt := $bodyTerm))
        let sigTerm ← liftTermElabM do
          let paramTys ← params.mapM (·.2.leanTypeStx)
          paramTys.foldrM (init := (← `(Lsc.Stmt))) fun ty acc => `($ty → $acc)
        let lamBody ← liftTermElabM do
          params.foldrM (init := (← `($implId))) fun (pname, k) acc => do
            let pid : Term := ⟨mkIdent (Name.mkSimple pname)⟩
            let tyConst ← k.tyConst
            let litStx ← k.embedLitStx pid
            `(Lsc.Stmt.seq (Lsc.Stmt.letBind $(quote pname) ⟨$tyConst, $litStx⟩) $acc)
        -- Fold `fun p1 => fun p2 => ... => lamBody` from the *last* parameter inward, rather
        -- than a single `fun p1 p2 ... => lamBody` splice, to avoid needing a
        -- `TSyntaxArray \`Lean.Parser.Term.funBinder` (plain `Ident`s aren't directly
        -- splice-compatible with that category).
        let wrappedBody ← liftTermElabM do
          params.foldrM (init := lamBody) fun (pname, _) acc => do
            let pid := mkIdent (Name.mkSimple pname)
            `(fun $pid:ident => $acc)
        elabCommand (← `(command| def $nameId : $sigTerm := $wrappedBody))
        -- Also emit a `.Typed` companion preserving each parameter's exact author-declared type
        -- (e.g. `Token.Amount`, not this def's own generic `Wad`) — this is what a *different*
        -- module's `exec`/`read` call site (`elabExecOrReadTerm`) actually calls, when present,
        -- so that mixing up two different tokens' amounts across a cross-contract call is a
        -- compile error even though `nameId` itself must stay generic (see `Lsc.Wad.Fixed`'s
        -- docstring for why `nameId` can't just be tagged directly: same-contract internal/test
        -- code, e.g. `TokenTheorem.lean`, calls it directly with plain untagged `Wad` literals).
        -- A companion `def` (rather than reusing `Lsc.Deriving.contractParamTyExt` directly from
        -- `elabExecOrReadTerm`) is what makes this work *across* module/import boundaries at
        -- all — that plain in-memory `EnvExtension` doesn't survive a `.olean` round-trip, but an
        -- ordinary declaration like this one naturally does.
        unless params.isEmpty do
          let origParamTys : List (String × Name) := paramTyState.find? fnName |>.getD []
          let typedId := mkIdent (Name.mkSimple (nameRaw.getId.toString ++ "Typed"))
          let typedSigTerm ← liftTermElabM do
            let paramTys ← params.mapM fun (pname, k) =>
              match origParamTys.find? (·.1 == pname) with
              | some (_, tyName) => pure (⟨mkIdent tyName⟩ : Term)
              | none => k.leanTypeStx
            paramTys.foldrM (init := (← `(Lsc.Stmt))) fun ty acc => `($ty → $acc)
          let typedBody ← liftTermElabM do
            let argTerms ← params.mapM fun (pname, k) => do
              let pid : Term := ⟨mkIdent (Name.mkSimple pname)⟩
              if k == .wad then `(Lsc.Wad.Fixed.retag $pid) else pure pid
            argTerms.foldlM (init := (← `($nameId))) fun acc a => `($acc $a)
          let typedWrapped ← liftTermElabM do
            params.foldrM (init := typedBody) fun (pname, _) acc => do
              let pid := mkIdent (Name.mkSimple pname)
              `(fun $pid:ident => $acc)
          elabCommand (← `(command| def $typedId : $typedSigTerm := $typedWrapped))
        pure (ns ++ Name.mkSimple (nameRaw.getId.toString ++ "Impl"))
    modifyEnv fun env =>
      Lsc.Deriving.contractFnsExt.modifyState env fun m =>
        m.insert ns ((m.find? ns |>.getD []) ++ [(fnName, stmtDefFnName, params)])
  modifyEnv fun env => Lsc.Deriving.contractTxSyntaxExt.modifyState env (·.insert ns [])

/-- The shared body of `derive_contract_def`/`derive_contract` once their three trailing optional
groups have already been unwrapped to plain `Option Term`s (by each caller — see those
elaborators below) — kept as one ordinary function, rather than re-quoted/spliced `Syntax`,
since `Option Term` splices into a `command|` quotation's optional-group slots without the
anonymous-syntax-category antiquotation issues a raw `TSyntax` re-splice would hit. See
`Lang/Derive.lean`'s docstring (right before this logic's old location, before it moved here to
be able to call `flushContractTxs`, which needs `elabStmtList`) for the full rationale/defaults. -/
def elabContractDefBody (nameStrStx : TSyntax `Lean.Parser.Term.str) (storageId errId eventId : Lean.Ident)
    (explicitFunctions? explicitTopic0? explicitCtor? : Option Term) : CommandElabM Unit := do
  let nameStr : Term := quote (nameStrStx.raw.isStrLit?.getD "")
  let storageName ← Lean.Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo storageId
  let errName ← Lean.Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo errId
  let eventName ← Lean.Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo eventId
  -- `storage : List (Ident × Ty × Option ExprAny)`, derived from `storageId`'s fields.
  let storageFields ← liftTermElabM <| Lsc.Deriving.getStructureFieldKinds storageName
  -- `wadMap` fields have no `Ty` at all (storage-only, see `FieldKind.wadMap`'s docstring) —
  -- `ContractDef.storage` has no representation for a mapping field, so they're excluded here,
  -- same as `mkGetFieldCmd`/`mkSigmaFieldCmds` (`Lang/Derive.lean`) already exclude them.
  let scalarStorageFields := storageFields.filter (·.2 != Lsc.Deriving.FieldKind.wadMap)
  let storageEntries ← scalarStorageFields.mapM fun (fname, k) => do
    liftTermElabM do
      let tyConst ← k.tyConst
      let fnameStr := quote fname.toString
      let defaultTerm ←
        match ← Lsc.Deriving.getStructureFieldDefaultExpr? storageName fname with
        | none => `(none)
        | some defExpr =>
          match ← Lsc.Deriving.embedStorageDefaultExpr k defExpr with
          | none => `(none)
          | some t => pure t
      `(($fnameStr, $tyConst, ($defaultTerm : Option Lsc.ExprAny)))
  let storageTerm ← `([$storageEntries,*])
  -- Solidity-style slot assignment over all storage fields (scalars + `wadMap` roots).
  let layoutScalarsTerm ← liftTermElabM do
    let mut scalars : Array Term := #[]
    let mut maps : Array Term := #[]
    let mut slot := 0
    for (fname, k) in storageFields do
      let fnameLit := quote fname.toString
      if k == Lsc.Deriving.FieldKind.wadMap then
        maps := maps.push (← `(($(fnameLit), $(quote slot))))
      else
        scalars := scalars.push (← `(($(fnameLit), $(quote slot))))
      slot := slot + 1
    pure (scalars, maps)
  let (layoutScalarsEntries, layoutMapsEntries) := layoutScalarsTerm
  let layoutScalarsTerm ← `([$layoutScalarsEntries,*])
  let layoutMapsTerm ← `([$layoutMapsEntries,*])
  -- `errors : List (Ident × List (Ident × Ty))`, derived from `errId`'s constructors.
  let errIndVal ← liftTermElabM <| getConstInfoInduct errName
  let errorEntries ← errIndVal.ctors.toArray.mapM fun ctorName => liftTermElabM do
    let cStr := ctorName.getString!
    let cStrLit := quote cStr
    match ← Lsc.Deriving.getCtorFieldNameKind ctorName with
    | none => `(($cStrLit, ([] : List (Lsc.Ident × Lsc.Ty))))
    | some (_, _) =>
      throwError "deriving ContractDef: error constructor `{cStr}` has parameters; \
        error constructors must be nullary"
  let errorsTerm ← `([$errorEntries,*])
  -- `events : List (Ident × List (Ident × Ty))`, derived from `eventId`'s constructors.
  let eventIndVal ← liftTermElabM <| getConstInfoInduct eventName
  let eventEntries ← eventIndVal.ctors.toArray.mapM fun ctorName => liftTermElabM do
    let cStr := ctorName.getString!
    let cStrLit := quote cStr
    match ← Lsc.Deriving.getCtorFieldNameKind ctorName with
    | none => `(($cStrLit, ([] : List (Lsc.Ident × Lsc.Ty))))
    | some (paramName, k) =>
      let tyConst ← k.tyConst
      let paramStrLit := quote paramName.toString
      `(($cStrLit, [($paramStrLit, $tyConst)]))
  let eventsTerm ← `([$eventEntries,*])
  -- `functions : List (String × Stmt)` — either the explicit override, or every `tx`
  -- self-registered under this namespace so far (`Lsc.Deriving.contractFnsExt`), in
  -- declaration order.
  -- `paramsForFn : String → List (Lsc.Ident × Lsc.Ty)` — a per-function-name lookup for
  -- `FunctionDef.params`, built from the same `tx (p : ty, ...)` declarations
  -- `Lsc.Deriving.contractFnsExt` records. Only meaningful (non-`[]`-defaulting) when
  -- `functions` itself is auto-derived: an explicit `functions` override has no matching
  -- per-name param info available here, so every function it lists gets `params := []` (an
  -- existing, documented limitation of overriding `functions` explicitly, not a regression —
  -- an override can always be written with a real ABI signature by hand if needed).
  let ns ← getCurrNamespace
  let interfaceEntries := (Lsc.Deriving.contractInterfacesExt.getState (← getEnv)).find? ns |>.getD []
  let interfacesTerm ← liftTermElabM do
    let mut acc : Term ← `([])
    for (field, iface) in interfaceEntries do
      let fieldLit := quote field
      let ifaceLit := quote iface
      acc ← `(List.cons ($fieldLit, $ifaceLit) $acc)
    return acc
  let fnEntries2 := (Lsc.Deriving.contractFnsExt.getState (← getEnv)).find? ns |>.getD []
  let paramsForFnTerm ← liftTermElabM do
    let nId := mkIdent `n
    let paramsArms ← fnEntries2.toArray.mapM fun (fnName, _stmtDefName, params) => do
      let fnStrLit := quote fnName.componentsRev.head!.toString
      let paramEntries ← params.toArray.mapM fun (pname, k) => do
        let tyConst ← k.tyConst
        `(($(quote pname), $tyConst))
      let paramsListTerm ← `([$paramEntries,*])
      `(matchAltExpr| | $fnStrLit => $paramsListTerm)
    let wc ← `(_)
    let defaultArm ← `(matchAltExpr| | $wc => ([] : List (Lsc.Ident × Lsc.Ty)))
    let alts := paramsArms.push defaultArm
    let discrs ← #[(nId : Term)].mapM Lsc.Deriving.mkDiscr
    `(fun ($nId : String) => match $[$discrs],* with $alts:matchAlt*)
  -- `nonReentrantForFnTerm : String → Bool` — mirrors `paramsForFnTerm` immediately above, but
  -- looks up each function's `@nonreentrant` decoration (`Lsc.Deriving.contractNonReentrantExt`,
  -- populated by `tx`'s own elaborator) by its fully-qualified `fnName` instead.
  let nonReentrantExtState := Lsc.Deriving.contractNonReentrantExt.getState (← getEnv)
  let nonReentrantForFnTerm ← liftTermElabM do
    let nId2 := mkIdent `n
    let nrArms ← fnEntries2.toArray.filterMapM fun (fnName, _stmtDefName, _params) => do
      if (nonReentrantExtState.find? fnName).getD false then
        let fnStrLit := quote fnName.componentsRev.head!.toString
        some <$> `(matchAltExpr| | $fnStrLit => true)
      else
        pure none
    let wc ← `(_)
    let defaultArm ← `(matchAltExpr| | $wc => false)
    let alts := nrArms.push defaultArm
    let discrs ← #[(nId2 : Term)].mapM Lsc.Deriving.mkDiscr
    `(fun ($nId2 : String) => match $[$discrs],* with $alts:matchAlt*)
  let functionsTerm ← match explicitFunctions? with
    | some t => pure t
    | none => do
      let fnEntries ← fnEntries2.toArray.mapM fun (fnName, stmtDefName, _params) => liftTermElabM do
        let fnId := mkIdent stmtDefName
        let fnStrLit := quote fnName.componentsRev.head!.toString
        `(($fnStrLit, $fnId))
      `([$fnEntries,*])
  -- `view` functions (`Lsc.Deriving.contractViewFnsExt`) are never part of the plain
  -- `String × Stmt` shape above (they carry their own `retTy`/`kind` directly, unlike a `tx`,
  -- which is always `.external`/`Ty.unit`) — built as a separate `List Lsc.FunctionDef` term and
  -- `++`-ed onto `functions` below, regardless of whether `functions` itself was overridden.
  let viewEntries := (Lsc.Deriving.contractViewFnsExt.getState (← getEnv)).find? ns |>.getD []
  let viewFnDefs ← viewEntries.toArray.mapM fun (fnName, implName, params, retKind) => liftTermElabM do
    let implId := mkIdent implName
    let fnStrLit := quote fnName.componentsRev.head!.toString
    let paramEntries ← params.toArray.mapM fun (pname, k) => do
      let tyConst ← k.tyConst
      `(($(quote pname), $tyConst))
    let paramsListTerm ← `([$paramEntries,*])
    let retTyConst ← retKind.tyConst
    `(Lsc.FunctionDef.mk $fnStrLit Lsc.FunctionKind.view $paramsListTerm $retTyConst $implId false)
  let viewFunctionsTerm ← `([$viewFnDefs,*])
  -- `topic0 : Ident → Option Nat` — either the explicit override, or a real Keccak256
  -- computation (`Lsc.computeEventTopic0`) over each event's already-derived ABI
  -- signature, matching `eventEntries` above exactly (replaces hand-written stub tables
  -- like the old non-cryptographic `name.hash.toNat` fallback).
  let topic0Term ← match explicitTopic0? with
    | some t => pure t
    | none => do
      let topic0NameId := mkIdent `name
      let topic0Arms ← eventIndVal.ctors.toArray.mapM fun ctorName => liftTermElabM do
        let cStr := ctorName.getString!
        let cStrLit := quote cStr
        let paramsTerm ← match ← Lsc.Deriving.getCtorFieldNameKind ctorName with
          | none => `(([] : List (Lsc.Ident × Lsc.Ty)))
          | some (paramName, k) =>
            let tyConst ← k.tyConst
            let paramStrLit := quote paramName.toString
            `([($paramStrLit, $tyConst)])
        `(matchAltExpr| | $cStrLit => some (Lsc.computeEventTopic0 $cStrLit $paramsTerm))
      let wc ← `(_)
      let defaultArm ← `(matchAltExpr| | $wc => none)
      let topic0Alts := topic0Arms.push defaultArm
      let topic0Discrs ← liftTermElabM <| #[(topic0NameId : Term)].mapM Lsc.Deriving.mkDiscr
      `(fun ($topic0NameId : Lsc.Ident) => match $[$topic0Discrs],* with $topic0Alts:matchAlt*)
  -- `ctor : Option FunctionDef` — explicit override, buffered `constructor` block, or (if
  -- `storageId` has `owner : Address` and no explicit ctor) the standard owner auto-ctor.
  let ownerSetStmt ←
    `(Lsc.Stmt.storageSet "owner" ⟨Lsc.Ty.address, Lsc.CoreExpr.txField Lsc.TxField.caller⟩)
  let ctorTerm ← match explicitCtor? with
    | some t => pure t
    | none => do
      let requiredFields ← liftTermElabM do
        scalarStorageFields.filterMapM fun (fname, _) => do
          if (← Lsc.Deriving.structureFieldHasDefault? storageName fname) then
            return none
          else
            return some fname.toString
      let flushedCtor := (Lsc.Deriving.contractCtorFnsExt.getState (← getEnv)).find? ns
      if requiredFields.isEmpty then
        match flushedCtor with
        | some (some (implFnName, params)) =>
          let implId := mkIdent implFnName
          let paramEntries ← liftTermElabM do
            params.toArray.mapM fun (pname, k) => do
              let tyConst ← k.tyConst
              `(($(quote pname), $tyConst))
          let paramsListTerm ← `([$paramEntries,*])
          let bodyTerm ← if storageFields.any fun (fname, k) =>
              fname == `owner && k == Lsc.Deriving.FieldKind.address then
            `(Lsc.Stmt.seq $ownerSetStmt $implId)
          else
            `( $implId )
          `(some (Lsc.FunctionDef.mk "deploy" Lsc.FunctionKind.constructor $paramsListTerm
            Lsc.Ty.unit $bodyTerm false))
        | _ =>
          if storageFields.any fun (fname, k) => fname == `owner && k == Lsc.Deriving.FieldKind.address then
            `(some (Lsc.FunctionDef.mk "deploy" Lsc.FunctionKind.constructor
              ([] : List (Lsc.Ident × Lsc.Ty)) Lsc.Ty.unit $ownerSetStmt false))
          else
            `((none : Option Lsc.FunctionDef))
      else
        match flushedCtor with
        | none | some none =>
          throwError "storage fields {requiredFields} have no struct default — declare a \
`constructor` block that initializes them (or add `:= ...` defaults)"
        | some (some (implFnName, params)) =>
          let implId := mkIdent implFnName
          let paramEntries ← liftTermElabM do
            params.toArray.mapM fun (pname, k) => do
              let tyConst ← k.tyConst
              `(($(quote pname), $tyConst))
          let paramsListTerm ← `([$paramEntries,*])
          let ctorSyntax := (Lsc.Deriving.contractCtorSyntaxExt.getState (← getEnv)).find? ns
          let writesOwner := match ctorSyntax with
            | some (some (_, stmtsRaw)) =>
              stmtsRaw.any fun stx =>
                match stx with
                | `(lscStmt| $x:ident = $_;) =>
                  Lsc.sigmaFieldName? x.getId == some "owner"
                | _ => false
            | _ => false
          let bodyTerm ←
            if storageFields.any fun (fname, k) =>
                fname == `owner && k == Lsc.Deriving.FieldKind.address && !writesOwner then
              `(Lsc.Stmt.seq $ownerSetStmt $implId)
            else
              `( $implId )
          `(some (Lsc.FunctionDef.mk "deploy" Lsc.FunctionKind.constructor $paramsListTerm
            Lsc.Ty.unit $bodyTerm false))
  -- Built via `mkIdent` (not written as literal tokens inside the
  -- `command|` quotations below) so the declared names stay plain,
  -- externally-visible identifiers rather than hygienically macro-scoped
  -- ones local to this quotation.
  let contractDefId := mkIdent `contractDef
  let configId := mkIdent `config
  let bytecodeHexId := mkIdent `bytecodeHex
  let deployHexId := mkIdent `deployHex
  let nId := mkIdent `n
  let bodyId := mkIdent `body
  -- `${Name}M`, e.g. `CounterM` for `"Counter"` — the `ContractM` monad abbreviation a contract
  -- author used to have to hand-write themselves right next to this command (argument order
  -- swapped from `storageId errId eventId` to match `ContractM`'s own `S E Err` declaration
  -- order).
  let mId := mkIdent (Name.mkSimple ((nameStrStx.raw.isStrLit?.getD "") ++ "M"))
  Lean.Elab.Command.elabCommand (← `(command|
    abbrev $mId := Lsc.ContractM $storageId $eventId $errId))
  Lean.Elab.Command.elabCommand (← `(command|
    def $contractDefId : Lsc.ContractDef where
      name := $nameStr
      storage := $storageTerm
      layoutScalars := $layoutScalarsTerm
      layoutMaps := $layoutMapsTerm
      errors := $errorsTerm
      events := $eventsTerm
      functions :=
        (($functionsTerm : List (String × Lsc.Stmt)).map fun ($nId, $bodyId) =>
          { name := $nId, kind := Lsc.FunctionKind.external, params := $paramsForFnTerm $nId,
            retTy := Lsc.Ty.unit, body := $bodyId, nonReentrant := $nonReentrantForFnTerm $nId })
        ++ $viewFunctionsTerm
      interfaces := $interfacesTerm
      deployFn := $ctorTerm))
  Lean.Elab.Command.elabCommand (← `(command|
    def $configId : Lsc.Compile.Config := Lsc.Compile.configFromContract $contractDefId $topic0Term))
  Lean.Elab.Command.elabCommand (← `(command|
    def $bytecodeHexId : String :=
      match Lsc.Compile.contractToBytecodeHex $contractDefId $topic0Term with
      | .ok hex => hex
      | .error _ => ""))
  Lean.Elab.Command.elabCommand (← `(command|
    def $deployHexId : String :=
      match Lsc.Compile.deployToBytecodeHex $contractDefId $topic0Term with
      | .ok hex => hex
      | .error _ => ""))

/-- Unwrap the shared `fnsStx:("(" term ")")? topic0Stx:("(" term ")")? ctorStx:("(" term ")")?`
trailing-groups pattern (`derive_contract_def`/`derive_contract` both take it) into plain
`Option Term`s, consumed left-to-right (`functions`, then `topic0`, then `ctor`) — giving zero
groups means "auto-derive everything", giving one means "override just `functions`", etc. -/
def unwrapContractDefTrailingGroups
    (fnsStx topic0Stx ctorStx : Option (TSyntax Name.anonymous)) :
    Option Term × Option Term × Option Term :=
  (fnsStx.map fun s => ⟨s.raw[1]!⟩, topic0Stx.map fun s => ⟨s.raw[1]!⟩, ctorStx.map fun s => ⟨s.raw[1]!⟩)

/-- Shared body of `derive_contract`: DSL assembly, flush buffered `tx`/`view` bodies, then
emit `ContractDef` + compile outputs. -/
def elabDeriveContract (nameStrStx : TSyntax `Lean.Parser.Term.str)
    (storageId errId eventId : Lean.Ident)
    (fnsStx topic0Stx ctorStx : Option (TSyntax Name.anonymous)) : CommandElabM Unit := do
  Lsc.Deriving.elabDeriveContractDsl storageId errId eventId
  flushContractTxs
  flushContractViews
  flushContractCtor
  let (fns?, topic0?, ctor?) := unwrapContractDefTrailingGroups fnsStx topic0Stx ctorStx
  elabContractDefBody nameStrStx storageId errId eventId fns? topic0? ctor?

/-- `derive_contract "Name" Storage Err Event (functions)? (topic0)? (ctor)?` — the single
author-facing closing command for a contract module: assembles `ContractDSL` from the three
`deriving`-generated glue defs, flushes every buffered `tx`/`view` body into real `def`s, and
emits `{Name}M`, `contractDef`, `config`, `bytecodeHex`, `deployHex`. Because `tx { .. }`
bodies are buffered rather than elaborated immediately (see `tx`'s docstring above), this call
sits once, *after* every `tx`/`view` block. -/
elab "derive_contract " nameStrStx:str storageId:ident errId:ident eventId:ident
    fnsStx:("(" term ")")? topic0Stx:("(" term ")")? ctorStx:("(" term ")")? : command => do
  elabDeriveContract nameStrStx storageId errId eventId fnsStx topic0Stx ctorStx

/-- Quote a `FieldKind` for embedding in a persisted `def`. -/
def mkFieldKindTerm (k : Lsc.Deriving.FieldKind) : TermElabM Term :=
  match k with
  | .wei => `(Lsc.Deriving.FieldKind.wei)
  | .wad => `(Lsc.Deriving.FieldKind.wad)
  | .bool => `(Lsc.Deriving.FieldKind.bool)
  | .address => `(Lsc.Deriving.FieldKind.address)
  | .uint256 => `(Lsc.Deriving.FieldKind.uint256)
  | .wadMap => `(Lsc.Deriving.FieldKind.wadMap)
  | .interface iface => `(Lsc.Deriving.FieldKind.interface $(quote iface))

/-- Emit persisted library inline registry + module marker (survives cross-module import). -/
def emitLibraryPersistDefs (_ns : Name)
    (pending : List (Name × Syntax × List (String × Lsc.Deriving.FieldKind) × Array Syntax)) :
    CommandElabM Unit := do
  let markerId := mkIdent `_isLibraryModule
  elabCommand (← `(def $markerId : Bool := true))
  if pending.isEmpty then return
  let inlineId := mkIdent `_libraryInline
  let mut listTerm : Term ← `([])
  for (fnName, _, params, stmts) in pending do
    let entry ← liftTermElabM do
      let fnLit : Term := quote fnName
      let paramTerms ← params.toArray.mapM fun (pname, k) => do
        let kt ← mkFieldKindTerm k
        let pLit : Term := quote pname
        `(($pLit, $kt))
      let paramsList ← `([$paramTerms,*])
      let srcTerms ← stmts.mapM fun s => do
        let strLit : Term := quote (Lsc.Deriving.stmtSyntaxToSource s)
        pure strLit
      let srcList ← `([$srcTerms,*])
      `(($fnLit, $paramsList, $srcList))
    listTerm ← `(List.cons $entry $listTerm)
  let reversedList ← `(List.reverse $listTerm)
  elabCommand (← `(def $inlineId : Lsc.Deriving.LibraryFnEntryList := $reversedList))

/-- `derive_library` — flush buffered `tx` bodies as inlinable library functions (no bytecode). -/
elab "derive_library " _nameStrStx:str storageId:ident errId:ident eventId:ident : command => do
  let ns ← getCurrNamespace
  let pending := (Lsc.Deriving.contractTxSyntaxExt.getState (← getEnv)).find? ns |>.getD []
  Lsc.Deriving.elabDeriveContractDsl storageId errId eventId
  flushContractTxs (libraryMode := true)
  flushContractViews
  emitLibraryPersistDefs ns pending
  modifyEnv fun env =>
    Lsc.Deriving.libraryFnsExt.modifyState env fun m =>
      m.insert ns (pending.map fun (fnName, _, params, stmts) =>
        (fnName, params, stmts.toList.map Lsc.Deriving.stmtSyntaxToSource))

end Lsc.Syntax
