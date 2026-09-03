import Lsc3.Core

/-!
# LSC v3 — reification

`lsc_schema C` derives `C.schema : ContractSchema C.Storage C.Event C.Error` from the
user's Lean types, and `lsc_reify C.f` turns the elaborated term of a contract function
`C.f : … → Tx C.Storage C.Event C.Error ρ` into

* `C.f.core : Core t` — the Core AST, and
* `C.f.core_denote : ∀ args, Core.denote C.schema C.f.core [argsₙ, …, args₁] = C.f args₁ … argsₙ`

proved by `rfl`. The reifier only accepts the *reifiable fragment* — the fixed set of
`Tx` primitives combined with `do`, `let`, `if` on decidable word comparisons, and
`pure` of words/addresses/pairs. Anything else is rejected with the offending subterm,
so a reifier bug or an out-of-fragment program is a build error, never a miscompile.

The translation follows the shapes Lean's `do` elaborator produces:

* `bind op (fun x => k)`                          → `letOp` / `seq`
* `have __do_jp := fun y => rest; body`            → reify `rest` once, then substitute it
                                                      for every `__do_jp y` leaf of `body`
* `ite c a b`, `pure v`, tail primitives          → `ite`, `ret`, `opTail`/`stmtTail`/`revertTail`
-/

open Lean Meta Elab Command Term

namespace Lsc3.Reify

initialize registerTraceClass `Lsc3.reify

inductive FieldKind
  | scalar
  | map1
  | map2
  deriving DecidableEq, Repr, Inhabited

structure FieldInfo where
  name : Name
  idx : Nat
  kind : FieldKind
  deriving Repr, Inhabited

structure ContractInfo where
  storage : Name
  event : Name
  error : Name
  schema : Name
  fields : Array FieldInfo
  evCtors : Array Name
  errCtors : Array Name

/-- A join point in scope: `have jp := fun (y : T) => rest`. `body` is `rest` reified in
the environment at the definition point (plus `y` if `hasArg`). -/
structure JoinPoint (t : RetTy) where
  fvar : FVarId
  hasArg : Bool
  depth : Nat
  body : Core t

structure Env (t : RetTy) where
  vars : List FVarId := []
  jp : Option (JoinPoint t) := none

/-! ## Contract information from the user's types -/

/-- Arity of a field type after unfolding abbreviations such as `Mapping`. -/
def fieldKind (ty : Expr) : MetaM FieldKind :=
  forallTelescopeReducing ty fun xs _ => do
    match xs.size with
    | 0 => pure .scalar
    | 1 => pure .map1
    | 2 => pure .map2
    | n => throwError "storage field with {n} keys is not supported (max 2)"

def contractInfo (ns : Name) : MetaM ContractInfo := do
  let storage := ns ++ `Storage
  let event := ns ++ `Event
  let error := ns ++ `Error
  let env ← getEnv
  unless isStructure env storage do
    throwError "{storage} must be a structure"
  let fieldNames := getStructureFields env storage
  let ctor := getStructureCtor env storage
  let fields ← forallTelescope ctor.type fun xs _ => do
    let xs := xs.extract ctor.numParams xs.size
    xs.mapIdxM fun i x => do
      let kind ← fieldKind (← inferType x)
      pure { name := fieldNames[i]!, idx := i, kind : FieldInfo }
  let evInfo ← getConstInfoInduct event
  let errInfo ← getConstInfoInduct error
  pure {
    storage, event, error, schema := ns ++ `schema, fields
    evCtors := evInfo.ctors.toArray, errCtors := errInfo.ctors.toArray }

/-! ## Schema generation -/

/-- `fun (args : List Nat) => C (args.getD 0 0) … (args.getD (n-1) 0)` for constructor `C`. -/
def ctorBuilder (ctor : Name) : MetaM Term := do
  let info ← getConstInfoCtor ctor
  let args := mkIdent `args
  let mut app : Term := mkIdent ctor
  for i in [:info.numFields] do
    app ← `($app (List.getD $args $(quote i) 0))
  `(fun ($args : List Nat) => $app)

def mkSchemaCommand (ci : ContractInfo) : MetaM Syntax := do
  let σ := mkIdent `σ
  let m := mkIdent `m
  let i := mkIdent `i
  let args := mkIdent `args
  -- One entry per field index; non-matching kinds get an inert default.
  let mut scalar : Array Term := #[]
  let mut scalarUpd : Array Term := #[]
  let mut map1 : Array Term := #[]
  let mut map1Upd : Array Term := #[]
  let mut map2 : Array Term := #[]
  let mut map2Upd : Array Term := #[]
  for f in ci.fields do
    let proj := mkIdent (`σ ++ f.name)
    let fld := mkIdent f.name
    let upd ← `(fun $σ $m => { $σ with $fld:ident := $m })
    match f.kind with
    | .scalar =>
      scalar := scalar.push (← `(fun $σ => $proj))
      scalarUpd := scalarUpd.push upd
      map1 := map1.push (← `(fun _ _ => 0)); map1Upd := map1Upd.push (← `(fun $σ _ => $σ))
      map2 := map2.push (← `(fun _ _ _ => 0)); map2Upd := map2Upd.push (← `(fun $σ _ => $σ))
    | .map1 =>
      scalar := scalar.push (← `(fun _ => 0)); scalarUpd := scalarUpd.push (← `(fun $σ _ => $σ))
      map1 := map1.push (← `(fun $σ => $proj))
      map1Upd := map1Upd.push upd
      map2 := map2.push (← `(fun _ _ _ => 0)); map2Upd := map2Upd.push (← `(fun $σ _ => $σ))
    | .map2 =>
      scalar := scalar.push (← `(fun _ => 0)); scalarUpd := scalarUpd.push (← `(fun $σ _ => $σ))
      map1 := map1.push (← `(fun _ _ => 0)); map1Upd := map1Upd.push (← `(fun $σ _ => $σ))
      map2 := map2.push (← `(fun $σ => $proj))
      map2Upd := map2Upd.push upd
  let evBuilders ← ci.evCtors.mapM ctorBuilder
  let errBuilders ← ci.errCtors.mapM ctorBuilder
  let evDefault ← ctorBuilder ci.evCtors[0]!
  let errDefault ← ctorBuilder ci.errCtors[0]!
  let S := mkIdent ci.storage
  let E := mkIdent ci.event
  let Er := mkIdent ci.error
  let name := mkIdent (`_root_ ++ ci.schema)
  `(def $name : Lsc3.ContractSchema $S $E $Er where
      st := {
        scalar := fun $i => List.getD [$scalar,*] $i (fun _ => 0)
        scalarUpd := fun $i => List.getD [$scalarUpd,*] $i (fun $σ _ => $σ)
        map1 := fun $i => List.getD [$map1,*] $i (fun _ _ => 0)
        map1Upd := fun $i => List.getD [$map1Upd,*] $i (fun $σ _ => $σ)
        map2 := fun $i => List.getD [$map2,*] $i (fun _ _ _ => 0)
        map2Upd := fun $i => List.getD [$map2Upd,*] $i (fun $σ _ => $σ) }
      ev := ⟨fun $i $args => List.getD [$evBuilders,*] $i $evDefault $args⟩
      err := ⟨fun $i $args => List.getD [$errBuilders,*] $i $errDefault $args⟩)

/-! ## Reification -/

def natLit? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.getArg! 1 with
      | .lit (.natVal n) => some n
      | _ => none
    else none

/-- Evaluate a closed `Nat` (literals, `WAD`/`RAY`/`Flag.on`, `10 ^ 18`, …) to a number.
Used so scale constants become `Atom.lit` and the certificate still closes by `rfl`. -/
def closedNat? (e : Expr) : MetaM (Option Nat) := do
  let e := e.consumeMData
  if let some n := natLit? e then return some n
  try
    let e ← reduce (skipTypes := true) e
    return natLit? e.consumeMData
  catch _ =>
    return none

def atomOf (env : Env t) (e : Expr) : MetaM Atom := do
  let e := e.consumeMData
  if let some n ← closedNat? e then return .lit n
  if let .fvar id := e then
    match env.vars.idxOf? id with
    | some i => return .var i
    | none => throwError "reify: local `{e}` is not a word in scope (only function \
        parameters and `←`-bound values can be used)"
  throwError "reify: `{e}` is not an atom; bind it first with `let x ← …` \
    (pure Nat arithmetic is not part of the language, use `+?` or `+↻`)"

/-- The storage field a projection lambda `fun σ => σ.f` (or the projection function itself) denotes. -/
def fieldOfProj (ci : ContractInfo) (proj : Expr) : MetaM FieldInfo := do
  let name? : Option Name ← lambdaTelescope proj fun _ body => do
    let body := body.consumeMData
    match body.getAppFn with
    | .const n _ => pure (some n)
    | _ =>
      match body with
      | .proj _ i _ => pure (ci.fields[i]?.map (fun f => ci.storage ++ f.name))
      | _ => pure none
  match name? with
  | some n =>
    match ci.fields.find? (fun f => ci.storage ++ f.name == n) with
    | some f => pure f
    | none => throwError "reify: `{proj}` is not a projection of {ci.storage}"
  | none => throwError "reify: `{proj}` is not a storage projection"

/-- The storage field an update lambda `fun σ m => { σ with f := m }` denotes. -/
def fieldOfUpd (ci : ContractInfo) (upd : Expr) : MetaM FieldInfo := do
  lambdaTelescope upd fun xs body => do
    let body := body.consumeMData
    unless xs.size == 2 do throwError "reify: `{upd}` is not a storage update"
    let m := xs[1]!
    let args := body.getAppArgs
    let ctor := getStructureCtor (← getEnv) ci.storage
    unless body.getAppFn.isConstOf ctor.name && args.size == ctor.numParams + ci.fields.size do
      throwError "reify: `{upd}` is not a storage update"
    let idx? := (List.range ci.fields.size).find? fun i => args[ctor.numParams + i]! == m
    match idx? with
    | some i => pure ci.fields[i]!
    | none => throwError "reify: `{upd}` does not update exactly one field"

def ctorIndex (ctors : Array Name) (e : Expr) : MetaM (Nat × Array Expr) := do
  let e := e.consumeMData
  match e.getAppFn with
  | .const n _ =>
    match ctors.idxOf? n with
    | some i =>
      let info ← getConstInfoCtor n
      pure (i, e.getAppArgs.extract info.numParams e.getAppArgs.size)
    | none => throwError "reify: `{e}` is not a constructor of the contract's event/error type"
  | _ => throwError "reify: `{e}` must be an event/error constructor application"

/-- Word-like types that may be compared: `Nat`, `Address`, `Amount`, `Flag`, `Price`. -/
def isWordLike (ty : Expr) : Bool :=
  let n := ty.getAppFn.constName?
  n == some ``Nat || n == some ``Lsc3.Address || n == some ``Lsc3.Amount
    || n == some ``Lsc3.Flag || n == some ``Lsc3.Price || n == some ``Lsc3.Fixed

partial def condOf (env : Env t) (e : Expr) : MetaM Cond := do
  let e := e.consumeMData
  let f := e.getAppFn
  let args := e.getAppArgs
  let atom := atomOf env
  let checkWord (ty : Expr) : MetaM Unit := do
    let ty ← whnfR ty
    unless isWordLike ty || ty.isConstOf ``Nat do
      throwError "reify: comparison on `{ty}` is not supported (use Nat, Address, Amount, Flag)"
  match f.constName?, args.size with
  | some ``LT.lt, 4 =>
    checkWord args[0]!
    return .lt (← atom args[2]!) (← atom args[3]!)
  | some ``LE.le, 4 =>
    checkWord args[0]!
    return .le (← atom args[2]!) (← atom args[3]!)
  | some ``GT.gt, 4 =>
    checkWord args[0]!
    return .lt (← atom args[3]!) (← atom args[2]!)
  | some ``GE.ge, 4 =>
    checkWord args[0]!
    return .le (← atom args[3]!) (← atom args[2]!)
  | some ``Eq, 3 =>
    checkWord args[0]!
    return .eq (← atom args[1]!) (← atom args[2]!)
  | some ``Ne, 3 =>
    checkWord args[0]!
    return .ne (← atom args[1]!) (← atom args[2]!)
  | some ``And, 2 => return .and (← condOf env args[0]!) (← condOf env args[1]!)
  | some ``Or, 2 => return .or (← condOf env args[0]!) (← condOf env args[1]!)
  | some ``Not, 1 => return .not (← condOf env args[0]!)
  | some ``True, 0 => return .tt
  | some ``False, 0 => return .ff
  | _, _ => throwError "reify: unsupported condition `{e}` (use <, ≤, =, ≠, ∧, ∨, ¬ on words)"

def retExprOf (env : Env t) : (s : RetTy) → Expr → MetaM (RetExpr s)
  | .unit, _ => pure .unit
  | .word, e => return .word (← atomOf env e)
  | .addr, e => return .addr (← atomOf env e)
  | .flag, e => return .flag (← atomOf env e)
  | .pair s₁ s₂, e => do
    let e := e.consumeMData
    if e.isAppOfArity ``Prod.mk 4 then
      return .pair (← retExprOf env s₁ (e.getArg! 2)) (← retExprOf env s₂ (e.getArg! 3))
    throwError "reify: expected a pair in `pure`, found `{e}`"

/-- Do not `whnf` through `Amount`/`Address`/`Flag` (`def` newtypes). `whnfR` still unfolds
the `Fixed` abbrev to `Amount Unit s`. -/
partial def retTyOf (ρ : Expr) : MetaM RetTy := do
  let ρ ← whnfR ρ
  match ρ.getAppFn.constName?, ρ.getAppNumArgs with
  | some ``Unit, 0 | some ``PUnit, 0 => pure .unit
  | some ``Nat, 0 => pure .word
  | some ``Lsc3.Address, 0 => pure .addr
  | some ``Lsc3.Flag, 0 => pure .flag
  | some ``Lsc3.Amount, 2 => pure .word
  | some ``Lsc3.Price, 3 => pure .word
  | some ``Prod, 2 => return .pair (← retTyOf (ρ.getArg! 0)) (← retTyOf (ρ.getArg! 1))
  | _, _ => throwError "reify: unsupported return type `{ρ}` \
      (Unit, Nat, Address, Flag, Amount, Price, or pairs)"

/-- Head constants that unfold to a `Tx` primitive (`Amount.add` → `Tx.addChecked`, …). -/
def isAmountOp : Name → Bool
  | ``Lsc3.Amount.add | ``Lsc3.Amount.sub
  | ``Lsc3.Amount.mulDown | ``Lsc3.Amount.mulUp
  | ``Lsc3.Amount.divDown | ``Lsc3.Amount.divUp
  | ``Lsc3.Amount.ratioDown | ``Lsc3.Amount.ratioUp
  | ``Lsc3.Amount.shareDown | ``Lsc3.Amount.shareUp
  | ``Lsc3.Amount.rescale | ``Lsc3.Amount.convert => true
  | _ => false

/-- `Rounding` must be a literal constructor so the reifier can pick `mulDivDown` vs `mulDivUp`. -/
def roundingOf (e : Expr) : MetaM Rounding := do
  let e := e.consumeMData
  match e.getAppFn.constName? with
  | some ``Lsc3.Rounding.down => return .down
  | some ``Lsc3.Rounding.up => return .up
  | _ => throwError "reify: rounding `{e}` must be a literal `.down` or `.up`"

/-- Unfold `Amount.*` (and reduce a `Rounding` match) until the head is a `Tx` primitive. -/
partial def unfoldToTx (x : Expr) (fuel : Nat := 8) : MetaM Expr := do
  let x := x.consumeMData
  let n := x.getAppFn.constName?
  if n == some ``Lsc3.Tx.addChecked || n == some ``Lsc3.Tx.subChecked
      || n == some ``Lsc3.Tx.mulChecked || n == some ``Lsc3.Tx.divChecked
      || n == some ``Lsc3.Tx.mulDivDown || n == some ``Lsc3.Tx.mulDivUp then
    return x
  if fuel = 0 then return x
  if n.any isAmountOp then
    if n == some ``Lsc3.Amount.rescale || n == some ``Lsc3.Amount.convert then
      -- Fail early with a clear message if Rounding is not a constructor.
      let args := x.getAppArgs
      if args.size > 0 then
        let _ ← roundingOf args[args.size - 2]!
    match ← unfoldDefinition? x with
    | some x' => return (← unfoldToTx x' (fuel - 1))
    | none =>
      let x' ← whnfR x
      if x' == x then return x
      else return (← unfoldToTx x' (fuel - 1))
  let x' ← whnfR x
  if x' != x then return (← unfoldToTx x' (fuel - 1))
  match ← unfoldDefinition? x with
  | some x' => unfoldToTx x' (fuel - 1)
  | none => return x

/-- Word-valued primitives. -/
def opOf (ci : ContractInfo) (env : Env t) (x : Expr) : MetaM (Option Op) := do
  let x := x.consumeMData
  let x ←
    if x.getAppFn.constName?.any isAmountOp then unfoldToTx x
    else pure x
  let args := x.getAppArgs
  let atom := atomOf env
  match x.getAppFn.constName?, args.size with
  | some ``Lsc3.Tx.load, 5 =>
    let f ← fieldOfProj ci args[4]!
    unless f.kind == .scalar do throwError "reify: `read {f.name}` needs keys"
    return some (.load f.idx)
  | some ``Lsc3.Tx.loadMap, 7 =>
    let f ← fieldOfProj ci args[5]!
    unless f.kind == .map1 do throwError "reify: `read {f.name}[k]` has the wrong number of keys"
    return some (.loadMap f.idx (← atom args[6]!))
  | some ``Lsc3.Tx.loadMap2, 9 =>
    let f ← fieldOfProj ci args[6]!
    unless f.kind == .map2 do throwError "reify: `read {f.name}[k₁, k₂]` has the wrong number of keys"
    return some (.loadMap2 f.idx (← atom args[7]!) (← atom args[8]!))
  | some ``Lsc3.Tx.sender, 3 => return some .sender
  | some ``Lsc3.Tx.value, 3 => return some .value
  | some ``Lsc3.Tx.timestamp, 3 => return some .timestamp
  | some ``Lsc3.Tx.blockNumber, 3 => return some .blockNumber
  | some ``Lsc3.Tx.selfAddress, 3 => return some .selfAddress
  | some ``Lsc3.Tx.addChecked, 5 => return some (.addChecked (← atom args[3]!) (← atom args[4]!))
  | some ``Lsc3.Tx.subChecked, 5 => return some (.subChecked (← atom args[3]!) (← atom args[4]!))
  | some ``Lsc3.Tx.mulChecked, 5 => return some (.mulChecked (← atom args[3]!) (← atom args[4]!))
  | some ``Lsc3.Tx.divChecked, 5 => return some (.divChecked (← atom args[3]!) (← atom args[4]!))
  | some ``Lsc3.Tx.mulDivDown, 6 =>
    return some (.mulDivDown (← atom args[3]!) (← atom args[4]!) (← atom args[5]!))
  | some ``Lsc3.Tx.mulDivUp, 6 =>
    return some (.mulDivUp (← atom args[3]!) (← atom args[4]!) (← atom args[5]!))
  | some ``Pure.pure, 4 => return some (.pure (← atom args[3]!))
  | _, _ => return none

/-- Unit-valued primitives. -/
def stmtOf (ci : ContractInfo) (env : Env t) (x : Expr) : MetaM (Option Stmt) := do
  let x := x.consumeMData
  let args := x.getAppArgs
  let atom := atomOf env
  match x.getAppFn.constName?, args.size with
  | some ``Lsc3.Tx.store, 6 =>
    let f ← fieldOfUpd ci args[4]!
    unless f.kind == .scalar do throwError "reify: `write {f.name}` needs keys"
    return some (.store f.idx (← atom args[5]!))
  | some ``Lsc3.Tx.storeMap, 10 =>
    let f ← fieldOfProj ci args[6]!
    let f' ← fieldOfUpd ci args[7]!
    unless f.kind == .map1 && f.idx == f'.idx do
      throwError "reify: `write {f.name}[k]` has the wrong number of keys"
    return some (.storeMap f.idx (← atom args[8]!) (← atom args[9]!))
  | some ``Lsc3.Tx.storeMap2, 13 =>
    let f ← fieldOfProj ci args[8]!
    let f' ← fieldOfUpd ci args[9]!
    unless f.kind == .map2 && f.idx == f'.idx do
      throwError "reify: `write {f.name}[k₁, k₂]` has the wrong number of keys"
    return some (.storeMap2 f.idx (← atom args[10]!) (← atom args[11]!) (← atom args[12]!))
  | some ``Lsc3.Tx.require, 6 =>
    let (i, eargs) ← ctorIndex ci.errCtors args[5]!
    return some (.require (← condOf env args[3]!) i (← eargs.toList.mapM atom))
  | some ``Lsc3.Tx.emit, 4 =>
    let (i, eargs) ← ctorIndex ci.evCtors args[3]!
    return some (.emit i (← eargs.toList.mapM atom))
  | some ``Lsc3.Tx.revert, 5 =>
    let (i, eargs) ← ctorIndex ci.errCtors args[4]!
    return some (.revert i (← eargs.toList.mapM atom))
  | _, _ => return none

/-- Pure word expressions bound by `let`. -/
def primOf (env : Env t) (v : Expr) : MetaM (Prim × List Atom) := do
  let v := v.consumeMData
  let args := v.getAppArgs
  match v.getAppFn.constName?, args.size with
  | some ``Lsc3.Tx.addWrap, 2 => return (.addWrap, [← atomOf env args[0]!, ← atomOf env args[1]!])
  | some ``Lsc3.Tx.subWrap, 2 => return (.subWrap, [← atomOf env args[0]!, ← atomOf env args[1]!])
  | some ``Lsc3.Tx.mulWrap, 2 => return (.mulWrap, [← atomOf env args[0]!, ← atomOf env args[1]!])
  | _, _ => return (.id, [← atomOf env v])

def isUnitTy (ty : Expr) : MetaM Bool := do
  let ty ← whnfR ty
  return ty.isConstOf ``Unit || ty.isConstOf ``PUnit

/-- η-expand a continuation that is not syntactically a lambda (e.g. `bind x __do_jp`). -/
def ensureLambda (k : Expr) : MetaM Expr := do
  if k.isLambda then return k
  let ty ← inferType k
  let ty ← whnf ty
  match ty with
  | .forallE n d _ bi => return .lam n d (mkApp k (.bvar 0)) bi
  | _ => throwError "reify: continuation `{k}` is not a function"

partial def reify (ci : ContractInfo) (t : RetTy) (env : Env t) (e : Expr) : MetaM (Core t) := do
  let e := e.consumeMData
  match e with
  | .letE n ty v b _ =>
    let v := v.consumeMData
    if v.isLambda then
      -- Join point: `have jp := fun (y : T) => rest; body`.
      let hasArg := !(← isUnitTy v.bindingDomain!)
      let body ← lambdaBoundedTelescope v 1 fun ys rest => do
        let vars := if hasArg then ys[0]!.fvarId! :: env.vars else env.vars
        reify ci t { env with vars } rest
      withLetDecl n ty v fun jpVar => do
        let jp : JoinPoint t := { fvar := jpVar.fvarId!, hasArg, depth := env.vars.length, body }
        reify ci t { env with jp := some jp } (b.instantiate1 jpVar)
    else
      let (p, args) ← primOf env v
      withLetDecl n ty v fun x => do
        let k ← reify ci t { env with vars := x.fvarId! :: env.vars } (b.instantiate1 x)
        return .letPure p args k
  | _ =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .fvar id =>
      match env.jp with
      | some jp =>
        unless jp.fvar == id do throwError "reify: unexpected local function `{e}`"
        let d := env.vars.length - jp.depth
        if jp.hasArg then
          unless args.size == 1 do throwError "reify: malformed join point call `{e}`"
          let a ← atomOf env args[0]!
          return jp.body.rename fun i => if i == 0 then a else .var (i - 1 + d)
        else
          return jp.body.rename fun i => .var (i + d)
      | none => throwError "reify: unexpected local function `{e}`"
    | .const name _ =>
      match name, args.size with
      | ``Bind.bind, 6 =>
        let x := args[4]!
        let k ← ensureLambda args[5]!
        if let some op ← opOf ci env x then
          lambdaBoundedTelescope k 1 fun ys body => do
            let kc ← reify ci t { env with vars := ys[0]!.fvarId! :: env.vars } body
            return .letOp op kc
        else if let some s ← stmtOf ci env x then
          lambdaBoundedTelescope k 1 fun _ body => do
            let kc ← reify ci t env body
            return .seq s kc
        else
          throwError "reify: `{x}` is not a contract primitive"
      | ``Pure.pure, 4 => return .ret (← retExprOf env t args[3]!)
      | ``ite, 5 =>
        let c ← condOf env args[1]!
        let a ← reify ci t env args[3]!
        let b ← reify ci t env args[4]!
        return .ite c a b
      | ``Lsc3.Tx.revert, 5 =>
        let (i, eargs) ← ctorIndex ci.errCtors args[4]!
        return .revertTail i (← eargs.toList.mapM (atomOf env))
      | _, _ =>
        if let some op ← opOf ci env e then
          match t with
          | .word => return .opTail op
          | .addr => return .opTailAddr op
          | .flag => return .opTailFlag op
          | _ => throwError "reify: `{e}` returns a word but the function does not"
        else if let some s ← stmtOf ci env e then
          match t with
          | .unit => return .stmtTail s
          | _ => throwError "reify: `{e}` returns Unit but the function does not"
        else
          throwError "reify: `{e}` is outside the reifiable fragment"
    | _ => throwError "reify: `{e}` is outside the reifiable fragment"

/-! ## Commands -/

/-- Unfold `abbrev`s such as `C.M` until the head is `Lsc3.Tx`. -/
partial def whnfToTx (ty : Expr) : MetaM Expr := do
  let ty := ty.consumeMData
  if ty.isAppOfArity ``Lsc3.Tx 4 then return ty
  match ← unfoldDefinition? ty with
  | some ty' => whnfToTx ty'
  | none => throwError "reify: `{ty}` is not a `Tx` type"

/-- Reify `fn` and add `fn.core` and `fn.core_denote` to the environment. -/
def reifyFunction (fn : Name) : TermElabM Unit := do
  let info ← getConstInfoDefn fn
  forallTelescope info.type fun params body => do
    let txTy ← whnfToTx body
    let S := txTy.getArg! 0
    let ρ := txTy.getArg! 3
    let some sName := S.constName? | throwError "reify: storage type `{S}` must be a constant"
    let ns := sName.getPrefix
    let ci ← contractInfo ns
    let t ← retTyOf ρ
    -- Peel the parameters off the definition body.
    let value := info.value.beta params
    let env : Env t := { vars := (params.map (·.fvarId!)).toList.reverse }
    let core ← reify ci t env value
    let coreName := fn ++ `core
    let coreTy := mkApp (Lean.mkConst ``Core) (toExpr t)
    addAndCompile <| .defnDecl (mkDefinitionValEx coreName [] coreTy core.toExpr .abbrev .safe [coreName])
    -- Certificate: Core.denote schema core [pₙ, …, p₁] = fn p₁ … pₙ
    let schema := Lean.mkConst ci.schema
    let envList ← mkListLit (Lean.mkConst ``Nat) params.toList.reverse
    let lhs := mkAppN (Lean.mkConst ``Core.denote) #[S, txTy.getArg! 1, txTy.getArg! 2, schema, toExpr t,
      Lean.mkConst coreName, envList]
    let rhs := mkAppN (Lean.mkConst fn) params
    let eq ← mkEq lhs rhs
    unless ← isDefEq lhs rhs do
      throwError "reify: certificate failed — `Core.denote` of the reified term is not \
        definitionally the original function.{indentExpr eq}\nReified Core:{indentExpr core.toExpr}"
    let stmt ← mkForallFVars params eq
    let proof ← mkLambdaFVars params (← mkEqRefl lhs)
    addDecl <| .thmDecl { name := fn ++ `core_denote, levelParams := [], type := stmt, value := proof }
    trace[Lsc3.reify] "reified {fn} : Core {repr t}\n{repr core}"

/-- `lsc_schema C` derives `C.schema` from `C.Storage`, `C.Event`, `C.Error`. -/
syntax (name := lscSchema) "lsc_schema " ident : command

@[command_elab lscSchema] def elabLscSchema : CommandElab
  | `(lsc_schema $ns:ident) => do
    let ns ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo (mkIdent (ns.getId ++ `Storage))
    let ns := ns.getPrefix
    let cmd ← liftTermElabM do
      let ci ← contractInfo ns
      mkSchemaCommand ci
    elabCommand cmd
  | _ => throwUnsupportedSyntax

/-- `lsc_reify C.f` reifies a contract function and certifies the result. -/
syntax (name := lscReify) "lsc_reify " ident+ : command

@[command_elab lscReify] def elabLscReify : CommandElab
  | `(lsc_reify $fns:ident*) => do
    for fn in fns do
      let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo fn
      liftTermElabM <| withRef fn <| reifyFunction n
  | _ => throwUnsupportedSyntax

end Lsc3.Reify

