import Lsc.Lang.Syntax.ElabExpr

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Meta Lean.Parser Lean.Parser.Term

namespace Lsc.Syntax

def parseLscStmt (env : Environment) (src : String) : Except String (TSyntax `lscStmt) := do
  let s ← Parser.runParserCategory env `lscStmt src.trimAscii.toString "<library>"
  pure ⟨s⟩

/-- Load library entries from the in-memory extension, falling back to the persisted `_libraryInline` def. -/
unsafe def loadLibraryEntries (libNs : Name) : TermElabM (List Lsc.Deriving.LibraryFnEntry) := do
  let env ← getEnv
  let fromExt := Lsc.Deriving.getLibraryEntries libNs env
  if !fromExt.isEmpty then
    return fromExt
  let constName := Lsc.Deriving.libraryInlineConstName libNs
  unless env.contains constName do
    return []
  evalConstCheck (List Lsc.Deriving.LibraryFnEntry) `Lsc.Deriving.LibraryFnEntryList constName

/-- Fallback callee lookup via the callee's elaborated Lean type (survives cross-module import). -/
def lookupCalleeParamsFromEnv (calleeGlobal : Name) (isRead : Bool) :
    TermElabM (String × List (String × Lsc.Deriving.FieldKind)) := do
  let shortName := calleeGlobal.componentsRev.head!.toString
  let info ← getConstInfo calleeGlobal
  let telescopeResult ← Meta.forallTelescope info.type fun xs retBody => do
    let mut collected : List (String × Lsc.Deriving.FieldKind) := []
    for i in [:xs.size] do
      let x := xs[i]!
      let ty ← Meta.inferType x
      let k ← match ← Lsc.Deriving.fieldKindOfExprM ty with
        | some k => pure k
        | none =>
          if isRead then
            throwError "unsupported parameter type `{ty}` on `{calleeGlobal}` for `read`"
          else
            throwError "unsupported parameter type `{ty}` on `{calleeGlobal}` for `exec`"
      collected := collected ++ [(x.fvarId!.name.toString, k)]
    pure (collected, retBody)
  let params := telescopeResult.1
  let retTyExpr : Lean.Expr := telescopeResult.2
  if isRead then
    unless retTyExpr.getAppFn.isConstOf ``Lsc.ContractM do
      throwError "unknown view callee `{calleeGlobal}` for `read`"
  else
    unless retTyExpr.isConstOf ``Lsc.Stmt do
      throwError "unknown tx callee `{calleeGlobal}` for `exec`"
  return (shortName, params)

/-- Look up a callee's ABI name and parameter kinds from `contractFnsExt`/`contractViewFnsExt`,
or from the callee's real Lean type when the extension isn't populated (cross-module import). -/
def lookupCalleeParams (calleeGlobal : Name) (isRead : Bool) : TermElabM (String × List (String × Lsc.Deriving.FieldKind)) := do
  let shortName := calleeGlobal.componentsRev.head!.toString
  let calleeNs := calleeGlobal.getPrefix
  let env ← getEnv
  if isRead then
    let views := (Lsc.Deriving.contractViewFnsExt.getState env).find? calleeNs |>.getD []
    match views.find? fun (fnName, _, _, _) => fnName == calleeGlobal with
    | some (_, _, params, _) => return (shortName, params)
    | none => lookupCalleeParamsFromEnv calleeGlobal isRead
  else
    let fns := (Lsc.Deriving.contractFnsExt.getState env).find? calleeNs |>.getD []
    match fns.find? fun (fnName, _, _) => fnName == calleeGlobal with
    | some (_, _, params) => return (shortName, params)
    | none => lookupCalleeParamsFromEnv calleeGlobal isRead

/-- Elaborate argument idents for an `exec`/`read` call against the callee's declared param kinds. -/
def elabExternalArgExprs (storageName : Name) (locals : List (String × Lsc.Deriving.FieldKind))
    (calleeParams : List (String × Lsc.Deriving.FieldKind)) (argIdents : TSyntaxArray `ident) :
    TermElabM (Array Term) := do
  if argIdents.size != calleeParams.length then
    throwError "argument count mismatch: expected {calleeParams.length}, got {argIdents.size}"
  let mut terms : Array Term := #[]
  for i in [:argIdents.size] do
    let arg := argIdents[i]!
    let (eTerm, _) ← elabLscExpr storageName locals (← `(lscExpr| $arg:ident))
    terms := terms.push eTerm
  return terms

/-- Build `List ExprAny` term from elaborated expression terms and their kinds. -/
def mkExprAnyListTerm (exprs : Array Term) (kinds : List Lsc.Deriving.FieldKind) : TermElabM Term := do
  let pairs ← kinds.zip exprs.toList |>.mapM fun (k, e) => do
    let tyConst ← k.tyConst
    `(⟨$tyConst, $e⟩)
  let mut result : Term ← `(List.nil)
  for t in pairs.reverse do
    result ← `(List.cons $t $result)
  return result

/-- If `n` is `σ.field.method` (or `…σ.field.method`), return `(field, method)`. Lean lexes the
whole callee as one dotted `ident`, so interface calls share `exec ident(..)` with module calls. -/
def splitSigmaMethodCall? (n : Name) : Option (String × String) :=
  let parts := n.toString.splitOn "."
  match parts.findIdx? (· == "σ") with
  | some i =>
    if h : i + 2 < parts.length then
      some (parts[i + 1], parts[parts.length - 1])
    else
      none
  | none => none

/-- If `n` is `local.method` and `local` is an in-scope param / `let` local. -/
def splitLocalMethodCall? (n : Name) (locals : List (String × Lsc.Deriving.FieldKind)) :
    Option (CalleeRef × String) :=
  let parts := n.toString.splitOn "."
  if parts.length == 2 then
    let receiver := parts[0]!
    let method := parts[1]!
    if locals.any (·.1 == receiver) then
      some (.local receiver, method)
    else
      none
  else
    none

def mkCalleeRefTerm (c : CalleeRef) : TermElabM Term := do
  match c with
  | .storageField field => `(Lsc.CalleeRef.storageField $(quote field))
  | .local name => `(Lsc.CalleeRef.local $(quote name))

def mkSigmaFieldIdent (field : String) : Lean.Ident :=
  mkIdent (Name.str (Name.str Name.anonymous "σ") field)

/-- Map an ABI `Ty` to a `FieldKind` for interface-method argument checking. -/
def tyToFieldKind (t : Ty) : Option Lsc.Deriving.FieldKind :=
  match t with
  | .wei => some .wei
  | .wad => some .wad
  | .bool => some .bool
  | .address => some .address
  | .uint256 => some .uint256
  | .unit => none

/-- Require `receiver` to be a `σ.field` on an interface-typed storage slot; return field name
and interface name (`"IERC20"`, …). -/
def resolveInterfaceReceiver (storageName : Name) (receiver : Lean.Ident) :
    TermElabM (String × String) := do
  match Lsc.sigmaFieldName? receiver.getId with
  | none => throwErrorAt receiver "`exec σ.field.method(..)` expects a storage receiver \
    like `σ.token`, got `{receiver.getId}`"
  | some field =>
    let k ← storageFieldKind storageName field
    match Lsc.Deriving.FieldKind.interfaceName? k with
    | some iface => return (field, iface)
    | none => throwErrorAt receiver "storage field `{field}` is not an interface type \
      (expected e.g. `token : IERC20`)"

def lookupInterfaceMethod (iface method : String) : TermElabM Lsc.Interfaces.IERC20.MethodSpec := do
  unless iface == Lsc.Interfaces.IERC20.interfaceName do
    throwError "unknown interface `{iface}` — only `IERC20` is supported today"
  match Lsc.Interfaces.IERC20.lookupMethod method with
  | some spec => return spec
  | none => throwError "interface `{iface}` has no method `{method}`"

def resolveLocalInterfaceReceiver (localName : String) (locals : List (String × Lsc.Deriving.FieldKind)) :
    TermElabM String :=
  match locals.find? (·.1 == localName) with
  | some (_, .interface iface) => return iface
  | some _ => throwError "local `{localName}` is not an interface type (expected e.g. `IERC20`)"
  | none => throwError "unknown local `{localName}` for interface call"

def elabExternalInterfaceExecStmtCore (storageName : Name)
    (locals : List (String × Lsc.Deriving.FieldKind))
    (callee : CalleeRef) (iface : String) (method : Lean.Ident) (argIdents : TSyntaxArray `ident) :
    TermElabM (Term × List (String × Lsc.Deriving.FieldKind)) := do
  let spec ← lookupInterfaceMethod iface method.getId.toString
  unless spec.mutating do
    throwErrorAt method "`{method.getId}` is read-only on `{iface}` — use \
`read ..{method.getId}(..);` instead"
  let calleeParams := spec.params.filterMap fun (n, t) =>
    tyToFieldKind t |>.map (n, ·)
  if argIdents.size != calleeParams.length then
    throwError "argument count mismatch for `{iface}.{method.getId}`: \
expected {calleeParams.length}, got {argIdents.size}"
  let paramTys := spec.params.map (·.2)
  let selector := (Lsc.computeSelectorFromParams method.getId.toString paramTys).toNat
  let argExprs ← elabExternalArgExprs storageName locals calleeParams argIdents
  let argKinds := calleeParams.map (·.2)
  let argsTerm ← mkExprAnyListTerm argExprs argKinds
  let calleeTerm ← mkCalleeRefTerm callee
  return (← `(Lsc.Stmt.externalExec $calleeTerm $(quote selector) $argsTerm), locals)

def elabExternalInterfaceExecStmt (storageName : Name)
    (locals : List (String × Lsc.Deriving.FieldKind))
    (receiver : Lean.Ident) (method : Lean.Ident) (argIdents : TSyntaxArray `ident) :
    TermElabM (Term × List (String × Lsc.Deriving.FieldKind)) := do
  let (targetField, iface) ← resolveInterfaceReceiver storageName receiver
  elabExternalInterfaceExecStmtCore storageName locals (.storageField targetField) iface method
    argIdents

def elabLetExternalInterfaceExecStmt (storageName : Name)
    (locals : List (String × Lsc.Deriving.FieldKind))
    (bindName : String) (callee : CalleeRef) (iface : String) (method : Lean.Ident)
    (argIdents : TSyntaxArray `ident) :
    TermElabM (Term × List (String × Lsc.Deriving.FieldKind)) := do
  let spec ← lookupInterfaceMethod iface method.getId.toString
  unless spec.mutating do
    throwErrorAt method "`{method.getId}` is read-only on `{iface}` — use \
`let .. = read ..{method.getId}(..);` instead"
  match spec.retTy with
  | none => throwErrorAt method "interface `{iface}.{method.getId}` has no return value to bind"
  | some retTy =>
    let calleeParams := spec.params.filterMap fun (n, t) =>
      tyToFieldKind t |>.map (n, ·)
    if argIdents.size != calleeParams.length then
      throwError "argument count mismatch for `{iface}.{method.getId}`: \
expected {calleeParams.length}, got {argIdents.size}"
    let paramTys := spec.params.map (·.2)
    let selector := (Lsc.computeSelectorFromParams method.getId.toString paramTys).toNat
    let argExprs ← elabExternalArgExprs storageName locals calleeParams argIdents
    let argKinds := calleeParams.map (·.2)
    let argsTerm ← mkExprAnyListTerm argExprs argKinds
    let calleeTerm ← mkCalleeRefTerm callee
    let retKind ← match retTy with
      | .bool => pure Lsc.Deriving.FieldKind.bool
      | .address => pure Lsc.Deriving.FieldKind.address
      | .uint256 => pure Lsc.Deriving.FieldKind.uint256
      | .wad => pure Lsc.Deriving.FieldKind.wad
      | .wei => pure Lsc.Deriving.FieldKind.wei
      | .unit => throwError "cannot bind unit return from `{iface}.{method.getId}`"
    let retTyTerm ← match retTy with
      | .bool => `(Lsc.Ty.bool)
      | .address => `(Lsc.Ty.address)
      | .uint256 => `(Lsc.Ty.uint256)
      | .wei => `(Lsc.Ty.wei)
      | .wad => `(Lsc.Ty.wad)
      | .unit => `(Lsc.Ty.unit)
    return (← `(Lsc.Stmt.letExecBind $(quote bindName) $retTyTerm $calleeTerm
        $(quote selector) $argsTerm), (bindName, retKind) :: locals)

def elabExternalInterfaceReadStmt (storageName : Name)
    (locals : List (String × Lsc.Deriving.FieldKind))
    (receiver : Lean.Ident) (method : Lean.Ident) (argIdents : TSyntaxArray `ident) :
    TermElabM (Term × List (String × Lsc.Deriving.FieldKind)) := do
  let (targetField, iface) ← resolveInterfaceReceiver storageName receiver
  let spec ← lookupInterfaceMethod iface method.getId.toString
  if spec.mutating then
    throwErrorAt method "`{method.getId}` mutates `{iface}` state — use \
`exec {receiver.getId}.{method.getId}(..);` instead"
  let calleeParams := spec.params.filterMap fun (n, t) =>
    tyToFieldKind t |>.map (n, ·)
  if argIdents.size != calleeParams.length then
    throwError "argument count mismatch for `{iface}.{method.getId}`: \
expected {calleeParams.length}, got {argIdents.size}"
  let paramTys := spec.params.map (·.2)
  let selector := (Lsc.computeSelectorFromParams method.getId.toString paramTys).toNat
  let argExprs ← elabExternalArgExprs storageName locals calleeParams argIdents
  let argKinds := calleeParams.map (·.2)
  let argsTerm ← mkExprAnyListTerm argExprs argKinds
  let calleeTerm ← mkCalleeRefTerm (.storageField targetField)
  return (← `(Lsc.Stmt.externalRead $calleeTerm $(quote selector) $(quote spec.retWords) $argsTerm), locals)

def elabExternalExecStmt (storageName : Name) (locals : List (String × Lsc.Deriving.FieldKind))
    (fn : Lean.Ident) (argIdents : TSyntaxArray `ident) :
    TermElabM (Term × List (String × Lsc.Deriving.FieldKind)) := do
  let targetNs := fn.getId.getPrefix
  if targetNs == Name.anonymous then
    throwErrorAt fn "`exec` expects a dotted `Target.fn` name (e.g. `Token.transfer`)"
  let calleeGlobal ← Lean.resolveGlobalConstNoOverload fn
  let (shortName, calleeParams) ← lookupCalleeParams calleeGlobal false
  let targetField := Lsc.Deriving.moduleTargetField targetNs
  let paramTys := calleeParams.map (·.2.toTy)
  let selector := (Lsc.computeSelectorFromParams shortName paramTys).toNat
  let argExprs ← elabExternalArgExprs storageName locals calleeParams argIdents
  let argKinds := calleeParams.map (·.2)
  let argsTerm ← mkExprAnyListTerm argExprs argKinds
  let calleeTerm ← mkCalleeRefTerm (.storageField targetField)
  return (← `(Lsc.Stmt.externalExec $calleeTerm $(quote selector) $argsTerm), locals)

def elabExternalReadStmt (storageName : Name) (locals : List (String × Lsc.Deriving.FieldKind))
    (fn : Lean.Ident) (argIdents : TSyntaxArray `ident) :
    TermElabM (Term × List (String × Lsc.Deriving.FieldKind)) := do
  let targetNs := fn.getId.getPrefix
  if targetNs == Name.anonymous then
    throwErrorAt fn "`read` expects a dotted `Target.fn` name (e.g. `Token.balanceOf`)"
  let calleeGlobal ← Lean.resolveGlobalConstNoOverload fn
  let (shortName, calleeParams) ← lookupCalleeParams calleeGlobal true
  let targetField := Lsc.Deriving.moduleTargetField targetNs
  let paramTys := calleeParams.map (·.2.toTy)
  let selector := (Lsc.computeSelectorFromParams shortName paramTys).toNat
  let argExprs ← elabExternalArgExprs storageName locals calleeParams argIdents
  let argKinds := calleeParams.map (·.2)
  let argsTerm ← mkExprAnyListTerm argExprs argKinds
  let calleeTerm ← mkCalleeRefTerm (.storageField targetField)
  let retWords : Nat := 0
  return (← `(Lsc.Stmt.externalRead $calleeTerm $(quote selector) $(quote retWords) $argsTerm), locals)

private def isLetBindStx (raw : Syntax) : Bool :=
  raw.getKind == `Lsc.Syntax.lscLetBind

private def isLetExecStx (raw : Syntax) : Bool :=
  raw.getKind == `Lsc.Syntax.lscLetExec

/-- Extract `(binder, expr)` from an `lscLetBind` syntax node. -/
private def parseLetBindStx (stx : TSyntax `lscStmt) :
    TermElabM (TSyntax `ident × TSyntax `lscExpr) := do
  unless isLetBindStx stx.raw do
    throwError "internal error: expected `lscLetBind` node"
  let args := stx.raw.getArgs
  let binder : TSyntax `ident := ⟨args[1]!⟩
  let some exprRaw := args.find? (fun a => !a.isMissing && !a.isAtom && a != args[1]!) |
    throwError "internal error: `lscLetBind` missing expression"
  return (binder, ⟨exprRaw⟩)

def elabLetBindStmt (storageName : Name) (locals : List (String × Lsc.Deriving.FieldKind))
    (stx : TSyntax `lscStmt) : TermElabM (Term × List (String × Lsc.Deriving.FieldKind)) := do
  let (x, e) ← parseLetBindStx stx
  let (eTerm, k) ← elabLscExpr storageName locals e
  let tyConst ← k.tyConst
  let nameStr := x.getId.toString
  let stmtTerm ← `(Lsc.Stmt.letBind $(quote nameStr) ⟨$tyConst, $eTerm⟩)
  return (stmtTerm, (nameStr, k) :: locals)

/-- Extract `(binder, fn, args)` from an `lscLetExec` syntax node. -/
private def parseLetExecStx (stx : TSyntax `lscStmt) :
    TermElabM (TSyntax `ident × TSyntax `ident × TSyntaxArray `ident) := do
  unless stx.raw.getKind == `Lsc.Syntax.lscLetExec do
    throwError "internal error: expected `lscLetExec` node"
  let args := stx.raw.getArgs
  let binder : TSyntax `ident := ⟨args[1]!⟩
  let fn : TSyntax `ident := ⟨args[4]!⟩
  let argsNode := args[6]!
  let mut argIdents : TSyntaxArray `ident := #[]
  for a in argsNode.getArgs do
    if a.isIdent then argIdents := argIdents.push ⟨a⟩
  return (binder, fn, argIdents)

def elabLetExecStmt (storageName : Name) (locals : List (String × Lsc.Deriving.FieldKind))
    (stx : TSyntax `lscStmt) : TermElabM (Term × List (String × Lsc.Deriving.FieldKind)) := do
  let (x, fn, args) ← parseLetExecStx stx
  let bindName := x.getId.toString
  match splitSigmaMethodCall? fn.getId with
  | some (field, method) =>
      let (targetField, iface) ← resolveInterfaceReceiver storageName (mkSigmaFieldIdent field)
      elabLetExternalInterfaceExecStmt storageName locals bindName (.storageField targetField) iface
        (mkIdent (Name.mkSimple method)) args
  | none =>
      match splitLocalMethodCall? fn.getId locals with
      | some (callee, method) =>
          let iface ← match callee with
            | Lsc.CalleeRef.local name => resolveLocalInterfaceReceiver name locals
            | _ => throwError "internal error: local interface callee expected"
          elabLetExternalInterfaceExecStmt storageName locals bindName callee iface
            (mkIdent (Name.mkSimple method)) args
      | none => throwErrorAt fn "`let .. = exec {fn.getId}(..)` only supports interface calls today"

mutual

/-- Elaborate one `lscStmt` node into a `Lsc.Stmt`-valued `Term`, alongside the possibly-
extended `locals` list (extended only by `var`). -/
partial def elabLscStmt (storageName : Name) (locals : List (String × Lsc.Deriving.FieldKind)) :
    TSyntax `lscStmt → TermElabM (Term × List (String × Lsc.Deriving.FieldKind))
  | `(lscStmt| require ( $cond ) else revert $errCtor:ident ( ) ;) => do
      let (condTerm, k) ← elabLscExpr storageName locals cond
      unless k == .bool do throwError "`require`'s condition must be `Bool`-kind, got `{repr k}`"
      let (errName, _) ← Lsc.Deriving.currContractTypes
      let ctorTerm ← `(.$errCtor)
      let ctorStr ← Lsc.Deriving.elabErrorCtorName ctorTerm errName
      return (← `(Lsc.Stmt.require $condTerm $(quote ctorStr)), locals)
  | `(lscStmt| revert $errCtor:ident ( ) ;) => do
      let (errName, _) ← Lsc.Deriving.currContractTypes
      let ctorTerm ← `(.$errCtor)
      let ctorStr ← Lsc.Deriving.elabErrorCtorName ctorTerm errName
      return (← `(Lsc.Stmt.revert $(quote ctorStr)), locals)
  | `(lscStmt| emit $ctor:ident ( ) ;) => do
      let (_, eventName) ← Lsc.Deriving.currContractTypes
      let ctorShort := ctor.getId.toString
      let ctorName := eventName ++ Name.mkSimple ctorShort
      match ← Lsc.Deriving.getCtorFieldNameKinds ctorName with
      | [] => return (← `(Lsc.Stmt.emit $(quote ctorShort) ([] : List Lsc.ExprAny)), locals)
      | _ => throwErrorAt ctor "`emit {ctorShort}` requires arguments"
  | `(lscStmt| emit $ctor:ident ( $args,* ) ;) => do
      let (_, eventName) ← Lsc.Deriving.currContractTypes
      let ctorShort := ctor.getId.toString
      let ctorName := eventName ++ Name.mkSimple ctorShort
      let fields ← Lsc.Deriving.getCtorFieldNameKinds ctorName
      let argArr := args.getElems
      if fields.isEmpty then
        throwErrorAt ctor "`emit {ctorShort}` takes no arguments"
      let argsList := argArr.toList
      unless fields.length == argsList.length do
        throwErrorAt ctor "`emit {ctorShort}` expects {fields.length} argument(s), got {argsList.length}"
      let mut emitArgs : Array Term := #[]
      for (p, arg) in fields.zip argsList do
        let (_, k) := p
        let (argTerm, ak) ← elabLscExpr storageName locals arg
        unless ak == k do
          throwErrorAt arg "`emit {ctorShort}` expects `{repr k}`-kind argument, got `{repr ak}`"
        let tyConst ← k.tyConst
        emitArgs := emitArgs.push (← `(⟨$tyConst, $argTerm⟩))
      return (← `(Lsc.Stmt.emit $(quote ctorShort) [$emitArgs,*]), locals)
  | `(lscStmt| $x:ident = $e ;) => do
      match Lsc.sigmaFieldName? x.getId with
      | some field => do
          let k ← storageFieldKind storageName field
          let (eTerm, ek) ← elabLscExpr storageName locals e
          let ok := ek == k || match k with
            | .interface _ => ek == .address
            | _ => false
          unless ok do
            throwErrorAt x "storage field `{field}` expects a `{repr k}`-kind value, got `{repr ek}`"
          let tyConst ← k.tyConst
          return (← `(Lsc.Stmt.storageSet $(quote field) ⟨$tyConst, $eTerm⟩), locals)
      | none => throwErrorAt x "expected `σ.field = e;` on the left-hand side, got `{x.getId}`"
  | `(lscStmt| $x:ident [ $key1 ] [ $key2 ] = $e ;) => do
      match Lsc.sigmaFieldName? x.getId with
      | some field => do
          let k ← storageFieldKind storageName field
          unless Lsc.Syntax.isMapping2Field k do
            throwErrorAt x "`{field}` is not a nested mapping field, cannot index it with `[..][..]`"
          let key1Term ← elabMapKey key1
          let key2Term ← elabMapKey key2
          let (eTerm, ek) ← elabLscExpr storageName locals e
          unless ek == .wad do
            throwErrorAt x "nested mapping field `{field}` expects a `Wad`-kind value, got `{repr ek}`"
          return (← `(Lsc.Stmt.mapSet2 $(quote field) $key1Term $key2Term $eTerm), locals)
      | none =>
          throwErrorAt x "expected `σ.field[key1][key2] = e;` on the left-hand side, got `{x.getId}`"
  | `(lscStmt| $x:ident [ $key1 ] [ $key2 ] +=? $e ;) => do
      match Lsc.sigmaFieldName? x.getId with
      | some field => do
          let k ← storageFieldKind storageName field
          unless Lsc.Syntax.isMapping2Field k do
            throwErrorAt x "`{field}` is not a nested mapping field, cannot index it with `[..][..]`"
          let key1Term ← elabMapKey key1
          let key2Term ← elabMapKey key2
          let curTerm ← `(Lsc.Wad.Expr.mapGet2 $(quote field) $key1Term $key2Term)
          let (sumTerm, _) ← elabCheckedAddWith storageName locals curTerm .wad e
          return (← `(Lsc.Stmt.mapSet2 $(quote field) $key1Term $key2Term $sumTerm), locals)
      | none =>
          throwErrorAt x "expected `σ.field[key1][key2] +=? e;` on the left-hand side, got `{x.getId}`"
  | `(lscStmt| $x:ident [ $key1 ] [ $key2 ] -=? $e ;) => do
      match Lsc.sigmaFieldName? x.getId with
      | some field => do
          let k ← storageFieldKind storageName field
          unless Lsc.Syntax.isMapping2Field k do
            throwErrorAt x "`{field}` is not a nested mapping field, cannot index it with `[..][..]`"
          let key1Term ← elabMapKey key1
          let key2Term ← elabMapKey key2
          let curTerm ← `(Lsc.Wad.Expr.mapGet2 $(quote field) $key1Term $key2Term)
          let (diffTerm, _) ← elabCheckedSubWith storageName locals curTerm .wad e
          return (← `(Lsc.Stmt.mapSet2 $(quote field) $key1Term $key2Term $diffTerm), locals)
      | none =>
          throwErrorAt x "expected `σ.field[key1][key2] -=? e;` on the left-hand side, got `{x.getId}`"
  | `(lscStmt| $x:ident [ $key ] = $e ;) => do
      match Lsc.sigmaFieldName? x.getId with
      | some field => do
          let k ← storageFieldKind storageName field
          unless Lsc.Syntax.isMappingField k do
            throwErrorAt x "`{field}` is not a mapping field, cannot index it with `[..]`"
          let keyTerm ← elabMapKey key
          let (eTerm, ek) ← elabLscExpr storageName locals e
          unless ek == .wad do
            throwErrorAt x "mapping field `{field}` expects a `Wad`-kind value, got `{repr ek}`"
          return (← `(Lsc.Stmt.mapSet $(quote field) $keyTerm $eTerm), locals)
      | none => throwErrorAt x "expected `σ.field[key] = e;` on the left-hand side, got `{x.getId}`"
  | `(lscStmt| $x:ident [ $key ] +=? $e ;) => do
      match Lsc.sigmaFieldName? x.getId with
      | some field => do
          let k ← storageFieldKind storageName field
          unless Lsc.Syntax.isMappingField k do
            throwErrorAt x "`{field}` is not a mapping field, cannot index it with `[..]`"
          let keyTerm ← elabMapKey key
          let curTerm ← `(Lsc.Wad.Expr.mapGet $(quote field) $keyTerm)
          let (sumTerm, _) ← elabCheckedAddWith storageName locals curTerm .wad e
          return (← `(Lsc.Stmt.mapSet $(quote field) $keyTerm $sumTerm), locals)
      | none => throwErrorAt x "expected `σ.field[key] +=? e;` on the left-hand side, got `{x.getId}`"
  | `(lscStmt| $x:ident [ $key ] -=? $e ;) => do
      match Lsc.sigmaFieldName? x.getId with
      | some field => do
          let k ← storageFieldKind storageName field
          unless Lsc.Syntax.isMappingField k do
            throwErrorAt x "`{field}` is not a mapping field, cannot index it with `[..]`"
          let keyTerm ← elabMapKey key
          let curTerm ← `(Lsc.Wad.Expr.mapGet $(quote field) $keyTerm)
          let (diffTerm, _) ← elabCheckedSubWith storageName locals curTerm .wad e
          return (← `(Lsc.Stmt.mapSet $(quote field) $keyTerm $diffTerm), locals)
      | none => throwErrorAt x "expected `σ.field[key] -=? e;` on the left-hand side, got `{x.getId}`"
  | `(lscStmt| $x:ident +=? $e ;) => do
      match Lsc.sigmaFieldName? x.getId with
      | some field => do
          let k ← storageFieldKind storageName field
          let curTerm ← k.storageGetStx field
          let (sumTerm, sk) ← elabCheckedAddWith storageName locals curTerm k e
          let tyConst ← sk.tyConst
          return (← `(Lsc.Stmt.storageSet $(quote field) ⟨$tyConst, $sumTerm⟩), locals)
      | none => throwErrorAt x "expected `σ.field +=? e;` on the left-hand side, got `{x.getId}`"
  | `(lscStmt| $x:ident -=? $e ;) => do
      match Lsc.sigmaFieldName? x.getId with
      | some field => do
          let k ← storageFieldKind storageName field
          let curTerm ← k.storageGetStx field
          let (diffTerm, sk) ← elabCheckedSubWith storageName locals curTerm k e
          let tyConst ← sk.tyConst
          return (← `(Lsc.Stmt.storageSet $(quote field) ⟨$tyConst, $diffTerm⟩), locals)
      | none => throwErrorAt x "expected `σ.field -=? e;` on the left-hand side, got `{x.getId}`"
  | `(lscStmt| if ( $cond ) { $thn* } else { $els* }) => do
      let (condTerm, k) ← elabLscExpr storageName locals cond
      unless k == .bool do throwError "`if`'s condition must be `Bool`-kind, got `{repr k}`"
      let (thnTerm, _) ← elabStmtList storageName locals thn
      let (elsTerm, _) ← elabStmtList storageName locals els
      return (← `(Lsc.Stmt.ifThenElse $condTerm $thnTerm $elsTerm), locals)
  | `(lscStmt| if ( $cond ) { $thn* }) => do
      let (condTerm, k) ← elabLscExpr storageName locals cond
      unless k == .bool do throwError "`if`'s condition must be `Bool`-kind, got `{repr k}`"
      let (thnTerm, _) ← elabStmtList storageName locals thn
      return (← `(Lsc.Stmt.ifThenElse $condTerm $thnTerm Lsc.Stmt.skip), locals)
  | `(lscStmt| return $e ;) => do
      let (eTerm, k) ← elabLscExpr storageName locals e
      let tyConst ← k.tyConst
      return (← `(Lsc.Stmt.ret ⟨$tyConst, $eTerm⟩), locals)
  | `(lscStmt| exec $fn:ident ( $args,* ) ;) => do
      match splitSigmaMethodCall? fn.getId with
      | some (field, method) =>
          elabExternalInterfaceExecStmt storageName locals (mkSigmaFieldIdent field)
            (mkIdent (Name.mkSimple method)) args.getElems
      | none =>
          match splitLocalMethodCall? fn.getId locals with
          | some (callee, method) =>
              let iface ← match callee with
                | Lsc.CalleeRef.local name => resolveLocalInterfaceReceiver name locals
                | _ => throwError "internal error: local interface callee expected"
              elabExternalInterfaceExecStmtCore storageName locals callee iface
                (mkIdent (Name.mkSimple method)) args.getElems
          | none => do
              if let some result ← tryElabInlineLibraryExec storageName locals fn args.getElems then
                return result
              elabExternalExecStmt storageName locals fn args.getElems
  | `(lscStmt| read $fn:ident ( $args,* ) ;) =>
      match splitSigmaMethodCall? fn.getId with
      | some (field, method) =>
          elabExternalInterfaceReadStmt storageName locals (mkSigmaFieldIdent field)
            (mkIdent (Name.mkSimple method)) args.getElems
      | none => elabExternalReadStmt storageName locals fn args.getElems
  | stx => do
    if isLetExecStx stx.raw then
      elabLetExecStmt storageName locals stx
    else if isLetBindStx stx.raw then
      elabLetBindStmt storageName locals stx
    else
      throwErrorAt stx "Syntax.elabLscStmt: unsupported `lscStmt` node (kind: {stx.raw.getKind})"

/-- Fold a sequence of `lscStmt` nodes into one chained `Lsc.Stmt` term via
`Stmt.seq`/`Stmt.skip`, threading `locals` through so a `var` in an earlier statement is
visible to later ones (mirroring `TxM.run`'s fold, and the prototype's original loop). -/
partial def elabStmtList (storageName : Name) (locals : List (String × Lsc.Deriving.FieldKind))
    (stmts : Array (TSyntax `lscStmt)) : TermElabM (Term × List (String × Lsc.Deriving.FieldKind)) := do
  let mut result : Term ← `(Lsc.Stmt.skip)
  let mut locs := locals
  for s in stmts do
    let (t, locs') ← elabLscStmt storageName locs s
    result ← `(Lsc.Stmt.seq $result $t)
    locs := locs'
  return (result, locs)

/-- Inline a registered library `tx` at the call site (re-elaborate body in caller context). -/
partial def elabInlineLibraryExec (storageName : Name) (locals : List (String × Lsc.Deriving.FieldKind))
    (fnName : Name) (fn : Lean.Ident) (argIdents : TSyntaxArray `ident) :
    TermElabM (Term × List (String × Lsc.Deriving.FieldKind)) := do
  let libNs := fnName.getPrefix
  let env ← getEnv
  let entries ← if Lsc.Deriving.getLibraryEntries libNs env |>.isEmpty then
      unsafe loadLibraryEntries libNs
    else
      pure (Lsc.Deriving.getLibraryEntries libNs env)
  match entries.find? fun (entryFn, _, _) => entryFn == fnName with
  | some (_, params, stmtSources) =>
    if argIdents.size != params.length then
      throwError "argument count mismatch for library `{fn.getId}`: \
expected {params.length}, got {argIdents.size}"
    let stmts ← stmtSources.mapM fun src =>
      match parseLscStmt env src with
      | .ok stx => pure stx
      | .error e => throwError "failed to parse library inline stmt `{src}`: {e}"
    let stmtsArr : Array (TSyntax `lscStmt) := stmts.toArray
    let mut locs := locals
    let mut bindPrefix : Term ← `(Lsc.Stmt.skip)
    for (pname, k) in params do
      let argIdx := params.findIdx (·.1 == pname)
      let arg := argIdents[argIdx]!
      let (eTerm, _) ← elabLscExpr storageName locs (← `(lscExpr| $arg:ident))
      let tyConst ← k.tyConst
      locs := (pname, k) :: locs
      bindPrefix ← `(Lsc.Stmt.seq (Lsc.Stmt.letBind $(quote pname) ⟨$tyConst, $eTerm⟩) $bindPrefix)
    let (bodyTerm, _) ← elabStmtList storageName locs stmtsArr
    return (← `(Lsc.Stmt.seq $bindPrefix $bodyTerm), locals)
  | none =>
    let env ← getEnv
    unless (env.find? fnName).isSome do
      throwErrorAt fn "`{fn.getId}` is not a registered library function"
    let mut app : Term := mkIdent fnName
    for arg in argIdents do
      app ← `( $app $arg:ident )
    return (app, locals)

partial def tryElabInlineLibraryExec (storageName : Name) (locals : List (String × Lsc.Deriving.FieldKind))
    (fn : Lean.Ident) (argIdents : TSyntaxArray `ident) :
    TermElabM (Option (Term × List (String × Lsc.Deriving.FieldKind))) := do
  let fnName ← Lean.resolveGlobalConstNoOverload fn
  let libNs := fnName.getPrefix
  if libNs == Name.anonymous then
    return none
  unless Lsc.Deriving.isLibraryModule (← getEnv) fnName.getPrefix do
    return none
  let env ← getEnv
  let hasEntry :=
    List.any (Lsc.Deriving.getLibraryEntries fnName.getPrefix env) (·.1 == fnName) ||
      env.contains (Lsc.Deriving.libraryInlineConstName fnName.getPrefix)
  unless hasEntry do
    return none
  return some (← elabInlineLibraryExec storageName locals fnName fn argIdents)

end

end Lsc.Syntax
