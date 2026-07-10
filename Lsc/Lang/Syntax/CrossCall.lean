import Lsc.Lang.Syntax.ElabStmt

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Meta Lean.Parser.Term

namespace Lsc.Syntax

/-! ## Real cross-contract calls (`exec`/`read`): Stmt nodes + optional PairM proofs -/

/-- Whether `s` is (syntactically) one `exec Target.fn(..);` or `let _ = exec ..` node. -/
def isExecStmt (s : TSyntax `lscStmt) : Bool :=
  s.raw.getKind == `Lsc.Syntax.lscLetExec ||
  match s with
  | `(lscStmt| exec $_:ident ( $_,* ) ;) => true
  | _ => false

/-- Whether `s` is (syntactically) one `read Target.fn(..);` node. -/
def isReadStmt (s : TSyntax `lscStmt) : Bool :=
  match s with
  | `(lscStmt| read $_:ident ( $_,* ) ;) => true
  | _ => false

/-- Whether any *top-level* statement in `stmts` is an `exec` node. -/
def stmtsUseExec (stmts : Array (TSyntax `lscStmt)) : Bool :=
  stmts.any isExecStmt

/-- Whether any *top-level* statement in `stmts` is a `read` node. -/
def stmtsUseRead (stmts : Array (TSyntax `lscStmt)) : Bool :=
  stmts.any isReadStmt

/-- Whether any *top-level* statement in `stmts` is an `exec`/`read` node. -/
def isExecOrReadStmt (s : TSyntax `lscStmt) : Bool :=
  isExecStmt s || isReadStmt s

def stmtsUseExecOrRead (stmts : Array (TSyntax `lscStmt)) : Bool :=
  stmts.any isExecOrReadStmt

/-- Whether any top-level `exec` targets a concrete module (`Token.transfer`), not an interface
receiver (`σ.token.transfer`). Only module `exec` txs get an auto-generated `PairM` proof `def`. -/
def stmtsUseModuleExec (stmts : Array (TSyntax `lscStmt)) : Bool :=
  stmts.any fun s =>
    match s with
    | `(lscStmt| exec $fn:ident ( $_,* ) ;) => splitSigmaMethodCall? fn.getId |>.isNone
    | _ => false

/-- Resolve the real callee `Ident` an `exec`/`read` call to `fn` should actually apply its
arguments to: `fn`'s own `.Typed` companion (`flushContractTxs`'s parameterized non-cross-call
branch, above) if one was generated, else `fn` itself unchanged (e.g. a zero-arg `tx`, or a
hand-written `ContractM` function this DSL never saw). When `.Typed` exists, its signature
already carries every parameter's *exact* author-declared type (e.g. `Token.Amount`, not the
generic `Wad` `fn` itself is stuck with) — so simply applying arguments to it and letting Lean's
ordinary application elaboration/unification do the rest is what turns "passed the wrong token's
amount" into a ordinary compile error, with no manual per-argument type bookkeeping needed at this
call site at all. -/
def resolveExecReadCallee (fn : Lean.Ident) : TermElabM Lean.Ident := do
  -- `fn`'s own literal syntax (e.g. `Token.transfer`, as the author wrote it) may not already be
  -- fully-qualified — resolve it to the real, absolute constant name first (exactly what plain
  -- application elaboration of `$fn` would do anyway), so the sibling `..Typed` name below is
  -- built from the *actual* declaration's full name, not whatever prefix happened to be visible
  -- at this particular call site's own namespace/`open` scope.
  let fnName ← Lean.resolveGlobalConstNoOverload fn
  -- Sibling-flat naming (`Token.transferTyped`), matching `flushContractTxs`'s own
  -- `nameImpl`/`nameTyped` convention (`Name.mkSimple (.. ++ "Typed")`) — not a dotted
  -- `Token.transfer.Typed`, which would need a different declaration shape entirely.
  let typedName := fnName.getPrefix ++ Name.mkSimple (fnName.componentsRev.head!.toString ++ "Typed")
  if (← getEnv).find? typedName |>.isSome then
    return mkIdent typedName
  else
    return fn

def elabExecOrReadTermCore (fn : Lean.Ident) (args : Array (TSyntax `ident)) : TermElabM Term := do
  let targetNs := fn.getId.getPrefix
  if targetNs == Name.anonymous then
    throwErrorAt fn "`exec` expects a dotted `Target.fn` name (e.g. `Token.transfer`), \
got `{fn.getId}`"
  let monadName := targetNs ++ Name.mkSimple (targetNs.componentsRev.head!.toString ++ "M")
  let monadId := mkIdent monadName
  let callee ← resolveExecReadCallee fn
  `(Lsc.ContractM.PairM.exec (($callee $args*) : $monadId Unit))

def elabReadOrReadTermCore (fn : Lean.Ident) (args : Array (TSyntax `ident)) : TermElabM Term := do
  let targetNs := fn.getId.getPrefix
  if targetNs == Name.anonymous then
    throwErrorAt fn "`read` expects a dotted `Target.fn` name (e.g. `Token.balanceOf`), \
got `{fn.getId}`"
  let monadName := targetNs ++ Name.mkSimple (targetNs.componentsRev.head!.toString ++ "M")
  let monadId := mkIdent monadName
  let callee ← resolveExecReadCallee fn
  `(Lsc.ContractM.PairM.read (($callee $args*) : $monadId Unit))

/-- Elaborate one `exec Target.fn(arg1, ..);` or `read Target.fn(arg1, ..);` node directly into
a `Lsc.ContractM.PairM S T E Err Unit`-valued `Term` (never a `Lsc.Stmt` — there is no `Stmt`
constructor for this, see `lscExec`'s docstring). `arg1`, ... are spliced as bare identifier
*terms* (real Lean values — `tx` parameters, typically), directly into the callee application
`$fn $args*` (bridged first via `bridgeCalleeArgs`, above); `T`/`ET`/`ErrT` are left to Lean's
ordinary unification (against `$fn`'s `Coe Stmt (ContractM T ET ErrT Unit)`-mediated result type,
`Lang/TxM.lean`) rather than being named anywhere in this function. Both `exec`/`read` are black
box — no `toErr`/`toEvent` conversion functions are needed at all (see `lscExec`'s docstring). -/
def elabInterfaceReadTermCore (method : Lean.Ident) (_args : Array (TSyntax `ident)) :
    TermElabM Term := do
  let _ ← lookupInterfaceMethod Lsc.Interfaces.IERC20.interfaceName method.getId.toString
  throwError "abstract interface `read σ.token.{method.getId}(..)` is not yet supported — \
use black-box `read Target.{method.getId}(..)` for a concrete callee module"

def elabExecOrReadTerm (storageName : Name) (locals : List (String × Lsc.Deriving.FieldKind))
    (s : TSyntax `lscStmt) : TermElabM Term :=
  match s with
  | `(lscStmt| exec $fn:ident ( $args,* ) ;) =>
      match splitSigmaMethodCall? fn.getId with
      | some (field, method) => do
          let (stmtTerm, _) ← elabExternalInterfaceExecStmt storageName locals
            (mkSigmaFieldIdent field) (mkIdent (Name.mkSimple method)) args.getElems
          let storageId := mkIdent storageName
          `(Lsc.ContractM.PairM.liftCaller (S := $storageId) (Lsc.Stmt.eval $stmtTerm))
      | none => elabExecOrReadTermCore fn args.getElems
  | `(lscStmt| read $fn:ident ( $args,* ) ;) =>
      match splitSigmaMethodCall? fn.getId with
      | some (_, method) => elabInterfaceReadTermCore (mkIdent (Name.mkSimple method)) args.getElems
      | none => elabReadOrReadTermCore fn args.getElems
  | stx => throwErrorAt stx "Syntax.elabExecOrReadTerm: unsupported `lscStmt` node"

/-- Fold a list of already-elaborated `PairM`-valued segment `Term`s into one right-associated
`>>=` chain (`s1 >>= fun _ => s2 >>= fun _ => ... >>= fun _ => sN`) — the `PairM` analogue of
`elabStmtList`'s `Stmt.seq` fold, needed here since `PairM` has no first-order `Stmt`-like AST
node to fold into; ordinary `Monad.bind` is the only "sequencing" `PairM` has. -/
def composeSegments : List Term → TermElabM Term
  | [] => `(pure ())
  | [s] => pure s
  | s :: rest => do
      let restTerm ← composeSegments rest
      `($s >>= fun _ => $restTerm)

/-- Wrap an ordinary (non-`exec`/`read`) `Lsc.Stmt` segment's `Term` with one
`Stmt.letBind param ⟨ty, <embedded literal>⟩` per `tx` parameter, mirroring
`flushContractTxs`'s existing parameter-embedding wrapping for the plain zero-cross-call
`Stmt`-only case exactly (see `Lsc.Deriving.FieldKind.embedLitStx`'s docstring) — needed because
each segment is `Lsc.Stmt.eval`'d independently (starting from a fresh `LocalEnv.empty`, see
`elabStmtListPairM` below), so a segment after the cross-contract call still needs its own
binding for a `tx` parameter used again there (e.g. `amount` in both the `exec`/`read` call
itself *and* a later `σ.field +? amount`). -/
def wrapSegmentParams (params : List (String × Lsc.Deriving.FieldKind)) (stmtTerm : Term) :
    TermElabM Term :=
  params.foldrM (init := stmtTerm) fun (pname, k) acc => do
    let pid : Term := ⟨mkIdent (Name.mkSimple pname)⟩
    let tyConst ← k.tyConst
    let litStx ← k.embedLitStx pid
    `(Lsc.Stmt.seq (Lsc.Stmt.letBind $(quote pname) ⟨$tyConst, $litStx⟩) $acc)

/-- Elaborate a run of consecutive ordinary (non-`exec`/`read`) `lscStmt`s into one `PairM`
segment `Term`: builds the plain `Lsc.Stmt` via the existing `elabStmtList` (unchanged, reused
as-is), wraps it with `wrapSegmentParams`, then lifts the whole thing into `PairM` via
`PairM.liftCaller ∘ Stmt.eval` (`Lsc.ContractM.PairM.liftCaller`, `Core/ContractM.lean`) — used
when building the proof-layer `PairM` `def` for `exec` txs (`elabStmtListPairM`). -/
def elabOrdinarySegment (storageName : Name) (locals params : List (String × Lsc.Deriving.FieldKind))
    (buf : Array (TSyntax `lscStmt)) : TermElabM Term := do
  let (stmtTerm, _) ← elabStmtList storageName locals buf
  let wrapped ← wrapSegmentParams params stmtTerm
  -- `(S := ..)` pins the caller's storage type explicitly — without it, `ContractDSL`
  -- instance search for `Stmt.eval` gets stuck on an unresolved metavariable, since this
  -- segment is elaborated bottom-up (no top-down expected type comes from the surrounding
  -- `>>=` chain `composeSegments` builds, see that function's docstring).
  let storageId := mkIdent storageName
  `(Lsc.ContractM.PairM.liftCaller (S := $storageId) (Lsc.Stmt.eval $wrapped))

/-- Elaborate a full cross-contract-call `tx` body (one containing one or more top-level
`exec`/`read` nodes, per `stmtsUseExecOrRead`) into a single `PairM`-valued `Term`: splits
`stmts` at each `exec`/`read` node into alternating ordinary/cross-call segments (in order),
elaborates each (`elabOrdinarySegment`/`elabExecOrReadTerm`), then chains them all together
with `composeSegments`. -/
def elabStmtListPairM (storageName : Name) (locals params : List (String × Lsc.Deriving.FieldKind))
    (stmts : Array (TSyntax `lscStmt)) : TermElabM Term := do
  let mut segments : Array Term := #[]
  let mut buf : Array (TSyntax `lscStmt) := #[]
  for s in stmts do
    if isExecOrReadStmt s then
      if buf.size > 0 then
        segments := segments.push (← elabOrdinarySegment storageName locals params buf)
        buf := #[]
      segments := segments.push (← elabExecOrReadTerm storageName locals s)
    else
      buf := buf.push s
  if buf.size > 0 then
    segments := segments.push (← elabOrdinarySegment storageName locals params buf)
  composeSegments segments.toList

end Lsc.Syntax
