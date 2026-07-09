import Lsc.Lang.Syntax.ElabExpr

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Meta Lean.Parser.Term

namespace Lsc.Syntax

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

def elabExternalInterfaceExecStmt (storageName : Name)
    (locals : List (String × Lsc.Deriving.FieldKind))
    (receiver : Lean.Ident) (method : Lean.Ident) (argIdents : TSyntaxArray `ident) :
    TermElabM (Term × List (String × Lsc.Deriving.FieldKind)) := do
  let (targetField, iface) ← resolveInterfaceReceiver storageName receiver
  let spec ← lookupInterfaceMethod iface method.getId.toString
  unless spec.mutating do
    throwErrorAt method "`{method.getId}` is read-only on `{iface}` — use \
`read {receiver.getId}.{method.getId}(..);` instead"
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
  return (← `(Lsc.Stmt.externalExec $(quote targetField) $(quote selector)
      $(quote spec.checkBoolReturn) $argsTerm), locals)

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
  return (← `(Lsc.Stmt.externalRead $(quote targetField) $(quote selector)
      $(quote spec.retWords) $argsTerm), locals)

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
  return (← `(Lsc.Stmt.externalExec $(quote targetField) $(quote selector) false $argsTerm), locals)

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
  let retWords : Nat := 0
  return (← `(Lsc.Stmt.externalRead $(quote targetField) $(quote selector) $(quote retWords) $argsTerm), locals)

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
      match ← Lsc.Deriving.getCtorFieldKind ctorName with
      | none => return (← `(Lsc.Stmt.emit $(quote ctorShort) ([] : List Lsc.ExprAny)), locals)
      | some _ => throwErrorAt ctor "`emit {ctorShort}` requires exactly one argument"
  | `(lscStmt| emit $ctor:ident ( $arg ) ;) => do
      let (_, eventName) ← Lsc.Deriving.currContractTypes
      let ctorShort := ctor.getId.toString
      let ctorName := eventName ++ Name.mkSimple ctorShort
      match ← Lsc.Deriving.getCtorFieldKind ctorName with
      | none => throwErrorAt ctor "`emit {ctorShort}` takes no arguments"
      | some k => do
          let (argTerm, ak) ← elabLscExpr storageName locals arg
          unless ak == k do
            throwErrorAt ctor "`emit {ctorShort}` expects a `{repr k}`-kind argument, got `{repr ak}`"
          let tyConst ← k.tyConst
          return (← `(Lsc.Stmt.emit $(quote ctorShort) [⟨$tyConst, $argTerm⟩]), locals)
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
  | `(lscStmt| $x:ident [ $key ] = $e ;) => do
      match Lsc.sigmaFieldName? x.getId with
      | some field => do
          let k ← storageFieldKind storageName field
          unless k == .wadMap do
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
          unless k == .wadMap do
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
          unless k == .wadMap do
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
  | `(lscStmt| let $x:ident = $e ;) => do
      let (eTerm, k) ← elabLscExpr storageName locals e
      let tyConst ← k.tyConst
      let nameStr := x.getId.toString
      let stmtTerm ← `(Lsc.Stmt.letBind $(quote nameStr) ⟨$tyConst, $eTerm⟩)
      return (stmtTerm, (nameStr, k) :: locals)
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
  | `(lscStmt| exec $fn:ident ( $args,* ) ;) =>
      match splitSigmaMethodCall? fn.getId with
      | some (field, method) =>
          elabExternalInterfaceExecStmt storageName locals (mkSigmaFieldIdent field)
            (mkIdent (Name.mkSimple method)) args.getElems
      | none => elabExternalExecStmt storageName locals fn args.getElems
  | `(lscStmt| read $fn:ident ( $args,* ) ;) =>
      match splitSigmaMethodCall? fn.getId with
      | some (field, method) =>
          elabExternalInterfaceReadStmt storageName locals (mkSigmaFieldIdent field)
            (mkIdent (Name.mkSimple method)) args.getElems
      | none => elabExternalReadStmt storageName locals fn args.getElems
  | stx => throwErrorAt stx "Syntax.elabLscStmt: unsupported `lscStmt` node"

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

end

end Lsc.Syntax
