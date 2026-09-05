import Lsc.Lang.Core
import Lsc.Lang.Contract
import Lsc.Lang.Spec

/-!
# reification

`lsc_schema C` derives `C.schema : ContractSchema C.Storage C.Event C.Error` from the
user's Lean types, plus `C.schema_lawful : C.schema.st.Lawful …`, and `lsc_reify C.f` turns the elaborated term of a contract function
`C.f : … → Tx C.Storage C.Event C.Error ρ` into

* `C.f.core : Core t` — the Core AST, and
* `C.f.core_denote : ∀ args, Core.denote C.schema C.f.core [argsₙ, …, args₁] = C.f args₁ … argsₙ`

proved by `rfl`. `lsc_contract C f₁ … fₙ` additionally defines `C.contract` and a
language-level `C.spec` (`C.Fn` / `C.entry` / `C.spec_exec_*`). `#lsc_obligations C`
prints the security theorems to prove; it does not import `Lsc.Security`.

The reifier only accepts the *reifiable fragment* — the fixed set of
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

namespace Lsc.Reify

initialize registerTraceClass `Lsc.reify

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
  `(def $name : Lsc.ContractSchema $S $E $Er where
      st := {
        scalar := fun $i => List.getD [$scalar,*] $i (fun _ => 0)
        scalarUpd := fun $i => List.getD [$scalarUpd,*] $i (fun $σ _ => $σ)
        map1 := fun $i => List.getD [$map1,*] $i (fun _ _ => 0)
        map1Upd := fun $i => List.getD [$map1Upd,*] $i (fun $σ _ => $σ)
        map2 := fun $i => List.getD [$map2,*] $i (fun _ _ _ => 0)
        map2Upd := fun $i => List.getD [$map2Upd,*] $i (fun $σ _ => $σ) }
      ev := ⟨fun $i $args => List.getD [$evBuilders,*] $i $evDefault $args⟩
      err := ⟨fun $i $args => List.getD [$errBuilders,*] $i $errDefault $args⟩)

/-- `C.schema_lawful : C.schema.st.Lawful <fields>` by `cases` / `simp` / `rfl`.
Unhygienic `i`/`j` so nested `succ i` rebinds the name the inner `cases` looks up. -/
def mkSchemaLawfulCommand (ci : ContractInfo) : MetaM (TSyntax `command) := do
  let thmName := mkIdent (`_root_ ++ ci.schema.getPrefix ++ `schema_lawful)
  let schema := mkIdent (`_root_ ++ ci.schema)
  let n := ci.fields.size
  let iId := mkIdent `i
  let jId := mkIdent `j
  let hId := mkIdent `h
  -- `elimTarget` is `nullNode` (no `h :`) plus a term; a raw `ident` is not an elimTarget.
  let mkTgt (id : Ident) : TSyntax ``Lean.Parser.Tactic.elimTarget :=
    ⟨mkNode ``Lean.Parser.Tactic.elimTarget #[mkNullNode, id]⟩
  let iTgt := mkTgt iId
  let jTgt := mkTgt jId
  let hTgt := mkTgt hId
  let fieldTerms : Array Term ← ci.fields.mapM fun f => do
    let nm : TSyntax `str := Syntax.mkStrLit f.name.getString!
    let k ← match f.kind with
      | .scalar => `(Lsc.FieldKind.scalar)
      | .map1 => `(Lsc.FieldKind.map1)
      | .map2 => `(Lsc.FieldKind.map2)
    `({ name := $nm, kind := $k, ty := Lsc.AbiTy.uint256 })
  let fieldsTerm ← `([$fieldTerms,*])
  let close ← `(Lean.Parser.Tactic.tacticSeq|
      simp [$schema:ident] <;>
        first | contradiction | (split <;> simp [$schema:ident]) |
          (funext; intro; simp [$schema:ident]) | rfl)
  let mut restI := close
  for _ in [:n] do
    restI ← `(Lean.Parser.Tactic.tacticSeq|
      cases $iTgt with
      | zero => $close
      | succ $iId => $restI)
  let mut restJ ← `(Lean.Parser.Tactic.tacticSeq| first | contradiction | cases $hTgt)
  for _ in [:n] do
    restJ ← `(Lean.Parser.Tactic.tacticSeq|
      cases $jTgt with
      | zero => (first | contradiction | ($restI))
      | succ $jId => $restJ)
  let schemaSt ← `(($schema:ident).st)
  `(command| theorem $thmName : Lsc.StorageSchema.Lawful $schemaSt $fieldsTerm := by
      constructor
      all_goals (intros $iId $jId σ x $hId; ($restJ)))

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
  n == some ``Nat || n == some ``Lsc.Address || n == some ``Lsc.Amount
    || n == some ``Lsc.Flag || n == some ``Lsc.Price || n == some ``Lsc.Fixed

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
  | some ``Lsc.Address, 0 => pure .addr
  | some ``Lsc.Flag, 0 => pure .flag
  | some ``Lsc.Amount, 2 => pure .word
  | some ``Lsc.Price, 3 => pure .word
  | some ``Prod, 2 => return .pair (← retTyOf (ρ.getArg! 0)) (← retTyOf (ρ.getArg! 1))
  | _, _ => throwError "reify: unsupported return type `{ρ}` \
      (Unit, Nat, Address, Flag, Amount, Price, or pairs)"

/-- Head constants that unfold to a `Tx` primitive (`Amount.add` → `Tx.addChecked`, …). -/
def isAmountOp : Name → Bool
  | ``Lsc.Amount.add | ``Lsc.Amount.sub
  | ``Lsc.Amount.mulDown | ``Lsc.Amount.mulUp
  | ``Lsc.Amount.divDown | ``Lsc.Amount.divUp
  | ``Lsc.Amount.ratioDown | ``Lsc.Amount.ratioUp
  | ``Lsc.Amount.shareDown | ``Lsc.Amount.shareUp
  | ``Lsc.Amount.rescale | ``Lsc.Amount.convert
  | ``Lsc.IERC20.transferFrom | ``Lsc.IERC20.transfer | ``Lsc.IERC20.balanceOf => true
  | _ => false

/-- `Rounding` must be a literal constructor so the reifier can pick `mulDivDown` vs `mulDivUp`. -/
def roundingOf (e : Expr) : MetaM Rounding := do
  let e := e.consumeMData
  match e.getAppFn.constName? with
  | some ``Lsc.Rounding.down => return .down
  | some ``Lsc.Rounding.up => return .up
  | _ => throwError "reify: rounding `{e}` must be a literal `.down` or `.up`"

/-- Unfold `Amount.*` (and reduce a `Rounding` match) until the head is a `Tx` primitive. -/
partial def unfoldToTx (x : Expr) (fuel : Nat := 8) : MetaM Expr := do
  let x := x.consumeMData
  let n := x.getAppFn.constName?
  if n == some ``Lsc.Tx.addChecked || n == some ``Lsc.Tx.subChecked
      || n == some ``Lsc.Tx.mulChecked || n == some ``Lsc.Tx.divChecked
      || n == some ``Lsc.Tx.mulDivDown || n == some ``Lsc.Tx.mulDivUp
      || n == some ``Lsc.Tx.erc20TransferFrom || n == some ``Lsc.Tx.erc20Transfer
      || n == some ``Lsc.Tx.erc20BalanceOf then
    return x
  if fuel = 0 then return x
  if n.any isAmountOp then
    if n == some ``Lsc.Amount.rescale || n == some ``Lsc.Amount.convert then
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
  | some ``Lsc.Tx.load, 5 =>
    let f ← fieldOfProj ci args[4]!
    unless f.kind == .scalar do throwError "reify: `read {f.name}` needs keys"
    return some (.load f.idx)
  | some ``Lsc.Tx.loadMap, 7 =>
    let f ← fieldOfProj ci args[5]!
    unless f.kind == .map1 do throwError "reify: `read {f.name}[k]` has the wrong number of keys"
    return some (.loadMap f.idx (← atom args[6]!))
  | some ``Lsc.Tx.loadMap2, 9 =>
    let f ← fieldOfProj ci args[6]!
    unless f.kind == .map2 do throwError "reify: `read {f.name}[k₁, k₂]` has the wrong number of keys"
    return some (.loadMap2 f.idx (← atom args[7]!) (← atom args[8]!))
  | some ``Lsc.Tx.sender, 3 => return some .sender
  | some ``Lsc.Tx.value, 3 => return some .value
  | some ``Lsc.Tx.timestamp, 3 => return some .timestamp
  | some ``Lsc.Tx.blockNumber, 3 => return some .blockNumber
  | some ``Lsc.Tx.selfAddress, 3 => return some .selfAddress
  | some ``Lsc.Tx.addChecked, 5 => return some (.addChecked (← atom args[3]!) (← atom args[4]!))
  | some ``Lsc.Tx.subChecked, 5 => return some (.subChecked (← atom args[3]!) (← atom args[4]!))
  | some ``Lsc.Tx.mulChecked, 5 => return some (.mulChecked (← atom args[3]!) (← atom args[4]!))
  | some ``Lsc.Tx.divChecked, 5 => return some (.divChecked (← atom args[3]!) (← atom args[4]!))
  | some ``Lsc.Tx.mulDivDown, 6 =>
    return some (.mulDivDown (← atom args[3]!) (← atom args[4]!) (← atom args[5]!))
  | some ``Lsc.Tx.mulDivUp, 6 =>
    return some (.mulDivUp (← atom args[3]!) (← atom args[4]!) (← atom args[5]!))
  | some ``Lsc.Tx.erc20TransferFrom, 7 =>
    return some (.erc20TransferFrom (← atom args[3]!) (← atom args[4]!)
      (← atom args[5]!) (← atom args[6]!))
  | some ``Lsc.Tx.erc20Transfer, 6 =>
    return some (.erc20Transfer (← atom args[3]!) (← atom args[4]!) (← atom args[5]!))
  | some ``Lsc.Tx.erc20BalanceOf, 5 =>
    return some (.erc20BalanceOf (← atom args[3]!) (← atom args[4]!))
  | some ``Pure.pure, 4 => return some (.pure (← atom args[3]!))
  | _, _ => return none

/-- Unit-valued primitives. -/
def stmtOf (ci : ContractInfo) (env : Env t) (x : Expr) : MetaM (Option Stmt) := do
  let x := x.consumeMData
  let args := x.getAppArgs
  let atom := atomOf env
  match x.getAppFn.constName?, args.size with
  | some ``Lsc.Tx.store, 6 =>
    let f ← fieldOfUpd ci args[4]!
    unless f.kind == .scalar do throwError "reify: `write {f.name}` needs keys"
    return some (.store f.idx (← atom args[5]!))
  | some ``Lsc.Tx.storeMap, 10 =>
    let f ← fieldOfProj ci args[6]!
    let f' ← fieldOfUpd ci args[7]!
    unless f.kind == .map1 && f.idx == f'.idx do
      throwError "reify: `write {f.name}[k]` has the wrong number of keys"
    return some (.storeMap f.idx (← atom args[8]!) (← atom args[9]!))
  | some ``Lsc.Tx.storeMap2, 13 =>
    let f ← fieldOfProj ci args[8]!
    let f' ← fieldOfUpd ci args[9]!
    unless f.kind == .map2 && f.idx == f'.idx do
      throwError "reify: `write {f.name}[k₁, k₂]` has the wrong number of keys"
    return some (.storeMap2 f.idx (← atom args[10]!) (← atom args[11]!) (← atom args[12]!))
  | some ``Lsc.Tx.require, 6 =>
    let (i, eargs) ← ctorIndex ci.errCtors args[5]!
    return some (.require (← condOf env args[3]!) i (← eargs.toList.mapM atom))
  | some ``Lsc.Tx.emit, 4 =>
    let (i, eargs) ← ctorIndex ci.evCtors args[3]!
    return some (.emit i (← eargs.toList.mapM atom))
  | some ``Lsc.Tx.revert, 5 =>
    let (i, eargs) ← ctorIndex ci.errCtors args[4]!
    return some (.revert i (← eargs.toList.mapM atom))
  | _, _ => return none

/-- Pure word expressions bound by `let`. -/
def primOf (env : Env t) (v : Expr) : MetaM (Prim × List Atom) := do
  let v := v.consumeMData
  let args := v.getAppArgs
  match v.getAppFn.constName?, args.size with
  | some ``Lsc.Tx.addWrap, 2 => return (.addWrap, [← atomOf env args[0]!, ← atomOf env args[1]!])
  | some ``Lsc.Tx.subWrap, 2 => return (.subWrap, [← atomOf env args[0]!, ← atomOf env args[1]!])
  | some ``Lsc.Tx.mulWrap, 2 => return (.mulWrap, [← atomOf env args[0]!, ← atomOf env args[1]!])
  | _, _ => return (.id, [← atomOf env v])

def isUnitTy (ty : Expr) : MetaM Bool := do
  let ty ← whnfR ty
  return ty.isConstOf ``Unit || ty.isConstOf ``PUnit

/-- Wrap `op` as a tail `Core t`. `none` when `t` is not a word-like return. -/
def opTailCore (t : RetTy) (op : Op) : Option (Core t) :=
  match t with
  | .word => some (.opTail op)
  | .addr => some (.opTailAddr op)
  | .flag => some (.opTailFlag op)
  | .unit | .pair _ _ => none

/-- Wrap `s` as a tail `Core t`. `none` when `t` is not `Unit`. -/
def stmtTailCore (t : RetTy) (s : Stmt) : Option (Core t) :=
  match t with
  | .unit => some (.stmtTail s)
  | .word | .addr | .flag | .pair _ _ => none

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
      | ``Lsc.Tx.revert, 5 =>
        let (i, eargs) ← ctorIndex ci.errCtors args[4]!
        return .revertTail i (← eargs.toList.mapM (atomOf env))
      | _, _ =>
        if let some op ← opOf ci env e then
          match opTailCore t op with
          | some c => return c
          | none => throwError "reify: `{e}` returns a word but the function does not"
        else if let some s ← stmtOf ci env e then
          match stmtTailCore t s with
          | some c => return c
          | none => throwError "reify: `{e}` returns Unit but the function does not"
        else
          throwError "reify: `{e}` is outside the reifiable fragment"
    | _ => throwError "reify: `{e}` is outside the reifiable fragment"

/-! ## Commands -/

/-- Unfold `abbrev`s such as `C.M` until the head is `Lsc.Tx`. -/
partial def whnfToTx (ty : Expr) : MetaM Expr := do
  let ty := ty.consumeMData
  if ty.isAppOfArity ``Lsc.Tx 4 then return ty
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
    trace[Lsc.reify] "reified {fn} : Core {repr t}\n{repr core}"

/-! ## Contract assembly (`lsc_contract`) -/

def abiTyOf (ty : Expr) : MetaM AbiTy := do
  let ty ← whnfR ty
  match ty.getAppFn.constName? with
  | some ``Nat => pure .uint256
  | some ``Lsc.Address => pure .address
  | some ``Lsc.Flag => pure .bool
  | some ``Lsc.Amount | some ``Lsc.Price | some ``Lsc.Fixed => pure .uint256
  | _ => throwError "lsc_contract: unsupported ABI type `{ty}` (Nat, Address, Flag, Amount)"

def ctorParams (ctor : Name) : MetaM (List Param) := do
  let info ← getConstInfoCtor ctor
  forallTelescope info.type fun xs _ => do
    let xs := xs.extract info.numParams xs.size
    xs.toList.mapM fun x => do
      let n := (← x.fvarId!.getUserName).getString!
      let abi ← abiTyOf (← inferType x)
      pure { name := n, ty := abi }

def fnKindOf (fn : Name) (t : RetTy) : FnKind :=
  if fn.getString! == "constructor" then .constructor
  else if t == RetTy.unit then .tx
  else .view

def fnMeta (fn : Name) : MetaM (List Param × RetTy × FnKind) := do
  let info ← getConstInfoDefn fn
  forallTelescope info.type fun xs body => do
    let txTy ← whnfToTx body
    let t ← retTyOf (txTy.getArg! 3)
    let params ← xs.toList.mapM fun x => do
      let n := (← x.fvarId!.getUserName).getString!
      let abi ← abiTyOf (← inferType x)
      pure { name := n, ty := abi }
    pure (params, t, fnKindOf fn t)

def mkFnDefExpr (name : String) (decl : Name) (kind : FnKind) (params : List Param)
    (ret : RetTy) (coreName : Name) : Expr :=
  mkAppN (Lean.mkConst ``FnDef.mk) #[
    toExpr name, toExpr decl, toExpr kind, toExpr params, toExpr ret, Lean.mkConst coreName]

def fieldKindToAbi : FieldKind → Lsc.FieldKind
  | .scalar => .scalar
  | .map1 => .map1
  | .map2 => .map2

/-- Assemble `C.contract : ContractDef` from reified entrypoints. Compilation to Yul is a
separate Lean function of that value (`Lsc.Compiler.toYul`). -/
def assembleContract (ns : Name) (fns : Array Name) : TermElabM Unit := do
  for fn in fns do
    unless (← getEnv).contains (fn ++ `core) do
      reifyFunction fn
  let ci ← contractInfo ns
  let fields : List FieldDef := ci.fields.toList.map fun f =>
    { name := f.name.getString!, kind := fieldKindToAbi f.kind, ty := .uint256 }
  let events : List EventDef ← ci.evCtors.toList.mapM fun ctor => do
    let params ← ctorParams ctor
    pure { name := ctor.getString!, params }
  let errors : List ErrorDef ← ci.errCtors.toList.mapM fun ctor => do
    let params ← ctorParams ctor
    pure { name := ctor.getString!, params }
  let mut fnDefs : Array Expr := #[]
  let mut ctorE : Expr := mkApp (Lean.mkConst ``Option.none [Level.zero]) (Lean.mkConst ``FnDef)
  for fn in fns do
    let (params, ret, kind) ← fnMeta fn
    let e := mkFnDefExpr fn.getString! fn kind params ret (fn ++ `core)
    if kind == .constructor then
      ctorE := mkApp2 (Lean.mkConst ``Option.some [Level.zero]) (Lean.mkConst ``FnDef) e
    else
      fnDefs := fnDefs.push e
  let fnList ← mkListLit (Lean.mkConst ``FnDef) fnDefs.toList
  let contractTy := Lean.mkConst ``ContractDef
  let contractVal := mkAppN (Lean.mkConst ``ContractDef.mk) #[
    toExpr ns.getString!, toExpr fields, fnList, ctorE, toExpr events, toExpr errors]
  addAndCompile <| .defnDecl (mkDefinitionValEx (ns ++ `contract) [] contractTy contractVal
    .abbrev .safe [ns ++ `contract])
  trace[Lsc.reify] "assembled {ns}.contract ({fns.size} functions)"

/-! ## `C.Fn` / `C.entry` / `C.spec` (generated by `lsc_contract`) -/

/-- Last name component as a public ident (`paused?` stays `paused?`). -/
def ctorIdent (fn : Name) : Ident :=
  mkIdent (Name.mkSimple fn.getString!)

/-- Render a closed type as a term; keep `Amount`/`Address` folded. -/
partial def exprToTerm (e : Expr) : MetaM Term := do
  let e := (← instantiateMVars e).consumeMData
  if let some n := e.constName? then
    return ⟨mkIdent n⟩
  if e.isApp then
    if let some n := e.getAppFn.constName? then
      let f : Term := ⟨mkIdent n⟩
      let args ← e.getAppArgs.mapM exprToTerm
      return ← `($f $args*)
  Lean.PrettyPrinter.delab e

/-- Right-nested product: `Unit` / `A` / `A × B × C`. -/
def mkProdType (tys : Array Term) : MetaM Term := do
  match tys.size with
  | 0 => `(Unit)
  | 1 => return tys[0]!
  | n =>
    let mut acc := tys[n - 1]!
    for i in [:n - 1] do
      acc ← `($(tys[n - 2 - i]!) × $acc)
    return acc

/-- Right-nested tuple: `()` / `a` / `(a, b, c)`. -/
def mkTuple (xs : Array Term) : MetaM Term := do
  match xs.size with
  | 0 => `(())
  | 1 => return xs[0]!
  | n =>
    let mut acc := xs[n - 1]!
    for i in [:n - 1] do
      acc ← `(($(xs[n - 2 - i]!), $acc))
    return acc

/-- Projection of the `i`-th component (0-based) of a right-nested `n`-tuple `p`. -/
def mkNestedProj (p : Term) (n i : Nat) : MetaM Term := do
  if n ≤ 1 then return p
  let mut e := p
  for _ in [:i] do
    e ← `($e.2)
  if i + 1 < n then
    e ← `($e.1)
  return e

def mkRunTerm (fn : Name) (arity : Nat) : MetaM Term := do
  let f : Term := ⟨mkIdent fn⟩
  match arity with
  | 0 => `(fun _ => $f)
  | 1 => return f
  | n => do
    let p := mkIdent `p
    let pTerm : Term := ⟨p⟩
    let mut args : Array Term := #[]
    for i in [:n] do
      args := args.push (← mkNestedProj pTerm n i)
    `(fun $p => $f $args*)

/-- Parameter names/types and the `Tx S E ε ρ` indices of `fn`. -/
def fnSurface (fn : Name) : MetaM (Expr × Expr × Expr × Array (Name × Expr) × Expr) := do
  let info ← getConstInfoDefn fn
  forallTelescope info.type fun xs body => do
    let txTy ← whnfToTx body
    let params ← xs.mapIdxM fun i x => do
      let n := ← x.fvarId!.getUserName
      let n := if n.hasMacroScopes then Name.mkSimple s!"a{i}" else n
      pure (n, ← inferType x)
    pure (txTy.getArg! 0, txTy.getArg! 1, txTy.getArg! 2, params, txTy.getArg! 3)

def entrypointFns (fns : Array Name) : MetaM (Array Name) :=
  fns.filterM fun fn => do
    let (_, _, kind) ← fnMeta fn
    return kind != .constructor

def mkEntryRhs (fn : Name) : MetaM Term := do
  let (_, _, _, params, ρ) ← fnSurface fn
  let argTys ← params.mapM fun (_, ty) => exprToTerm ty
  let argsTy ← mkProdType argTys
  let retTy ← exprToTerm ρ
  let run ← mkRunTerm fn params.size
  `(⟨$argsTy, $retTy, $run⟩)

def mkSpecExecCommand (ns fn : Name) : MetaM (TSyntax `command) := do
  let (_, _, _, params, _) ← fnSurface fn
  let ctor := ctorIdent fn
  let specId : Term := ⟨mkIdent (ns ++ `spec)⟩
  let f : Term := ⟨mkIdent fn⟩
  let args : Array Term := params.map fun (n, _) => ⟨mkIdent n⟩
  let argStx ← mkTuple args
  let rhs ← `($f $args*)
  let binders : TSyntaxArray ``Lean.Parser.Term.bracketedBinderF ←
    params.mapM fun (n, ty) => do
      let id := mkIdent n
      let t ← exprToTerm ty
      `(Lean.Parser.Term.bracketedBinderF| ($id : $t))
  let thmName := mkIdent (ns ++ Name.mkSimple s!"spec_exec_{fn.getString!}")
  `(command| @[simp] theorem $thmName $binders:bracketedBinder* :
      Lsc.Spec.exec $specId .$ctor:ident $argStx = $rhs := rfl)

/-- `C.Fn`, reducible `C.entry` / `C.spec`, and `@[simp] C.spec_exec_*` lemmas. -/
def mkSpecCommands (ns : Name) (fns : Array Name) : TermElabM (Array (TSyntax `command)) := do
  let entries ← entrypointFns fns
  let fnName := mkIdent (ns ++ `Fn)
  let ctorIds : Array Ident := entries.map ctorIdent
  let fnCmd ←
    `(command| inductive $fnName where $[| $ctorIds:ident]* deriving DecidableEq, Repr)
  let (S₀, E₀, ε₀) ←
    if entries.isEmpty then
      pure (Lean.mkConst (ns ++ `Storage), Lean.mkConst (ns ++ `Event),
        Lean.mkConst (ns ++ `Error))
    else
      let (S, E, ε, _, _) ← fnSurface entries[0]!
      pure (S, E, ε)
  let S ← exprToTerm S₀
  let E ← exprToTerm E₀
  let ε ← exprToTerm ε₀
  let entryName := mkIdent (ns ++ `entry)
  let alts : TSyntaxArray ``Lean.Parser.Term.matchAlt ← entries.mapM fun fn => do
    let ctor := ctorIdent fn
    let rhs ← mkEntryRhs fn
    `(Lean.Parser.Term.matchAltExpr| | .$ctor:ident => $rhs)
  let entryCmd ←
    if entries.isEmpty then
      `(command| @[reducible] def $entryName : $fnName → Lsc.Entry $S $E $ε :=
          fun fn => nomatch fn)
    else
      `(command| @[reducible] def $entryName : $fnName → Lsc.Entry $S $E $ε
          $alts:matchAlt*)
  let specName := mkIdent (ns ++ `spec)
  let specCmd ←
    `(command| @[reducible] def $specName : Lsc.Spec $S $E $ε := ⟨$fnName, $entryName⟩)
  let mut cmds : Array (TSyntax `command) := #[fnCmd, entryCmd, specCmd]
  for fn in entries do
    cmds := cmds.push (← mkSpecExecCommand ns fn)
  return cmds

def obligationsMissing (ns : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut missing : Array Name := #[]
  for s in #[`Inv, `claim, `Auth, `inflow] do
    unless env.contains (ns ++ s) do
      missing := missing.push (ns ++ s)
  return missing

/-- Copy-pasteable security theorems for `C`'s generated `Fn` (not imported from Security). -/
def obligationsText (ns : Name) (ctors : List Name) : String :=
  let C := ns.toString
  let leaf (n : Name) : String := n.getString!
  let thm (fn : Name) (suffix ty args : String) : String :=
    s!"theorem {C}.{leaf fn}_{suffix} : {ty} {C}.spec {args} .{leaf fn} := by sorry"
  let preserves := ctors.map fun fn =>
    thm fn "preserves_inv" "Lsc.Security.PreservesInvFn" s!"{C}.Inv"
  let auths := ctors.map fun fn =>
    thm fn "auth" "Lsc.Security.NoUnauthorizedDecreaseFn" s!"{C}.claim {C}.Auth"
  let conserves := ctors.map fun fn =>
    thm fn "conserves" "Lsc.Security.ConservesFn" s!"{C}.claim {C}.inflow"
  let arms (suffix : String) : String :=
    "\n".intercalate (ctors.map fun fn =>
      s!"    | .{leaf fn} => {C}.{leaf fn}_{suffix}")
  let assembler (name ty ofFns suffix : String) : String :=
    s!"theorem {C}.{name} : {ty} :=\n  {ofFns} fun fn =>\n    match fn with\n{arms suffix}"
  let extraction :=
    "theorem " ++ C ++ ".no_unauthorized_extraction\n" ++
    "    (tr : List (Lsc.Security.Call " ++ C ++ ".spec)) " ++
    "(w : Lsc.World " ++ C ++ ".Storage " ++ C ++ ".Event) (a : Lsc.Address)\n" ++
    "    (hA : Lsc.Security.NoAuthAlong " ++ C ++ ".Auth a tr w) :\n" ++
    "    " ++ C ++ ".claim a w.self ≤ " ++ C ++
    ".claim a (Lsc.Security.run tr w).self :=\n" ++
    "  Lsc.Security.no_unauthorized_extraction " ++ C ++ ".no_unauth tr w a hA"
  let body :=
    (preserves ++
      [assembler "preserves_inv" s!"Lsc.Security.PreservesInv {C}.spec {C}.Inv"
        "Lsc.Security.PreservesInv.of_fns" "preserves_inv"] ++
      auths ++
      [assembler "no_unauth"
        s!"Lsc.Security.NoUnauthorizedDecrease {C}.spec {C}.claim {C}.Auth"
        "Lsc.Security.NoUnauthorizedDecrease.of_fns" "auth"] ++
      [extraction] ++
      conserves ++
      [assembler "conserves" s!"Lsc.Security.Conservation {C}.spec {C}.claim {C}.inflow"
        "Lsc.Security.Conservation.of_fns" "conserves"])
  s!"-- Proof obligations for {C}\n" ++ "\n\n".intercalate body

/-- `lsc_schema C` derives `C.schema` from `C.Storage`, `C.Event`, `C.Error`. -/
syntax (name := lscSchema) "lsc_schema " ident : command

@[command_elab lscSchema] def elabLscSchema : CommandElab
  | `(lsc_schema $ns:ident) => do
    let ns ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo (mkIdent (ns.getId ++ `Storage))
    let ns := ns.getPrefix
    let (cmd, thm) ← liftTermElabM do
      let ci ← contractInfo ns
      let cmd ← mkSchemaCommand ci
      let thm ← mkSchemaLawfulCommand ci
      pure (cmd, thm)
    elabCommand cmd
    elabCommand thm
  | _ => throwUnsupportedSyntax

/-- `lsc_reify C.f` reifies a contract function and certifies the result. -/
syntax (name := lscReify) "lsc_reify " ident+ : command

@[command_elab lscReify] def elabLscReify : CommandElab
  | `(lsc_reify $fns:ident*) => do
    for fn in fns do
      let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo fn
      liftTermElabM <| withRef fn <| reifyFunction n
  | _ => throwUnsupportedSyntax

/-- `lsc_contract C f₁ … fₙ` reifies each `C.fᵢ` if needed, then defines
`C.contract : ContractDef` (the compiler's input, see `Lsc.Compiler`) and
`C.Fn` / `C.entry` / `C.spec` with `@[simp] C.spec_exec_*` lemmas. Unit-returning
functions are `tx`; a function named `constructor` is the constructor; the rest are `view`. -/
syntax (name := lscContract) "lsc_contract " ident ident+ : command

@[command_elab lscContract] def elabLscContract : CommandElab
  | `(lsc_contract $ns:ident $fns:ident*) => do
    let nsName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo (mkIdent (ns.getId ++ `Storage))
    let nsName := nsName.getPrefix
    let mut resolved : Array Name := #[]
    for fn in fns do
      let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo (mkIdent (nsName ++ fn.getId))
      resolved := resolved.push n
    liftTermElabM <| assembleContract nsName resolved
    let cmds ← liftTermElabM <| mkSpecCommands nsName resolved
    for cmd in cmds do
      elabCommand cmd
  | _ => throwUnsupportedSyntax

/-- `#lsc_obligations C` prints the `PreservesInvFn` / `NoUnauthorizedDecreaseFn` /
`ConservesFn` theorems to prove for `C.spec`, plus the `of_fns` assemblers. Requires
`C.Inv`, `C.claim`, `C.Auth`, and `C.inflow`. -/
syntax (name := lscObligations) "#lsc_obligations " ident : command

@[command_elab lscObligations] def elabLscObligations : CommandElab
  | `(#lsc_obligations $ns:ident) => do
    let nsName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo (mkIdent (ns.getId ++ `Storage))
    let nsName := nsName.getPrefix
    liftTermElabM <| withRef ns do
      let env ← getEnv
      unless env.contains (nsName ++ `Fn) do
        throwError "#lsc_obligations: {nsName}.Fn not found; run `lsc_contract` first"
      unless env.contains (nsName ++ `spec) do
        throwError "#lsc_obligations: {nsName}.spec not found; run `lsc_contract` first"
      let missing ← obligationsMissing nsName
      unless missing.isEmpty do
        throwError "#lsc_obligations: missing {missing.toList} \
          (need {nsName}.Inv, {nsName}.claim, {nsName}.Auth, {nsName}.inflow)"
      let info ← getConstInfoInduct (nsName ++ `Fn)
      logInfo m!"{obligationsText nsName info.ctors}"
  | _ => throwUnsupportedSyntax

end Lsc.Reify

