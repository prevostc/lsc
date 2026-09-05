import Lsc.Lang.Core
import Lsc.Lang.Contract
import Lsc.Lang.Spec

/-!
# reification

`lsc_schema C` derives `C.schema : ContractSchema C.Storage C.Ext C.Event C.Error` from the
user's Lean types, plus `C.schema_lawful : C.schema.st.Lawful …`, and `lsc_reify C.f` turns the elaborated term of a contract function
`C.f : … → Tx C.Storage C.Ext C.Event C.Error ρ` (or `Unit` when there is no `Ext`) into

* `C.f.core : Core t` — the Core AST, and
* `C.f.core_denote` — `Core.denote C.schema C.f.core [args] = C.f args` for word-typed
  programs, or `Core.denoteAWord` / `Core.denoteAUnit` when the surface returns
  `Amount` or has `Amount` storage, both proved by `rfl`.

`lsc_contract C f₁ … fₙ` additionally defines `C.contract` and a
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
  /-- Value type (for mappings, the type stored at a key). -/
  valTy : Expr
  deriving Inhabited

structure BindingInfo where
  name : Name
  fieldSlot : Nat
  iface : Name
  deriving Repr, Inhabited

structure ContractInfo where
  storage : Name
  event : Name
  error : Name
  schema : Name
  fields : Array FieldInfo
  evCtors : Array Name
  errCtors : Array Name
  ext? : Option Name
  bindings : Array BindingInfo

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

/-- Arity of a field type after unfolding abbreviations such as `Mapping`, plus the value type. -/
def fieldKindAndVal (ty : Expr) : MetaM (FieldKind × Expr) :=
  forallTelescopeReducing ty fun xs val => do
    match xs.size with
    | 0 => pure (.scalar, val)
    | 1 => pure (.map1, val)
    | 2 => pure (.map2, val)
    | n => throwError "storage field with {n} keys is not supported (max 2)"

/-- Unfold abbrevs such as `abbrev Dai := Amount …`. -/
def whnfAmount? (ty : Expr) : MetaM (Option (Expr × Expr)) := do
  let ty ← whnfD ty
  if ty.isAppOfArity ``Lsc.Amount 2 then
    return some (ty.getArg! 0, ty.getArg! 1)
  else
    return none

def isAmountTy (ty : Expr) : MetaM Bool :=
  return (← whnfAmount? ty).isSome

/-- `some (τ, s)` when the certificate uses `Core.denoteAWord` / `Core.denoteAUnit`.
Amount **return** always; Amount **storage** only for `Unit` returns (the first Amount
field's `(τ, s)`). Nat/Flag/Addr returns stay on `Core.denote`, so
`Vault.deposit : Amount → M Nat` is unchanged even if storage later becomes `Amount`. -/
def amountAnnot (ci : ContractInfo) (ρ : Expr) : MetaM (Option (Expr × Expr)) := do
  match ← whnfAmount? ρ with
  | some ts => return some ts
  | none =>
    let ρ ← whnfR ρ
    unless ρ.isConstOf ``Unit || ρ.isConstOf ``PUnit do return none
    for f in ci.fields do
      if let some ts ← whnfAmount? f.valTy then return some ts
    return none

def findBindings (ns storage ext : Name) : MetaM (Array BindingInfo) := do
  let env ← getEnv
  let mut out : Array BindingInfo := #[]
  let storageFields := getStructureFields env storage
  for f in getStructureFields env ext do
    let stem := f.getString!
    let cands := #[ns ++ Name.mkSimple (stem ++ "B"), ns ++ f]
    let mut found := false
    for cand in cands do
      unless found do
        unless env.contains cand do continue
        let info ← getConstInfo cand
        let ty ← whnfD info.type
        unless ty.isAppOf ``Lsc.Binding do continue
        let args := ty.getAppArgs
        unless args.size ≥ 3 do continue
        let some ifaceN := args[0]!.constName? | continue
        let some fieldIdx :=
          storageFields.toList.findIdx? (fun sf => sf.getString! == stem)
          | throwError "reify: binding `{cand}` has no storage field `{stem}`"
        out := out.push { name := cand, fieldSlot := fieldIdx, iface := ifaceN }
        found := true
  return out

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
      let (kind, valTy) ← fieldKindAndVal (← inferType x)
      pure { name := fieldNames[i]!, idx := i, kind, valTy : FieldInfo }
  let evInfo ← getConstInfoInduct event
  let errInfo ← getConstInfoInduct error
  let extName := ns ++ `Ext
  let ext? := if isStructure env extName then some extName else none
  let bindings ←
    match ext? with
    | some ext => findBindings ns storage ext
    | none => pure #[]
  pure {
    storage, event, error, schema := ns ++ `schema, fields
    evCtors := evInfo.ctors.toArray, errCtors := errInfo.ctors.toArray
    ext?, bindings }

/-! ## Schema generation -/

/-- `fun (args : List Nat) => C (ofNat (args.getD 0 0)) …` for constructor `C`.
Amount fields are rebuilt with `ofNat`; `Address`/`Flag`/`Nat` are words. -/
def ctorBuilder (ctor : Name) : MetaM Term := do
  let info ← getConstInfoCtor ctor
  let argsId := mkIdent `args
  forallTelescope info.type fun xs _ => do
    let xs := xs.extract info.numParams xs.size
    let mut app : Term := mkIdent ctor
    for i in [:xs.size] do
      let ty ← inferType xs[i]!
      let get ← `(List.getD $argsId $(quote i) 0)
      let arg ← if ← isAmountTy ty then `(Lsc.Amount.ofNat $get) else pure get
      app ← `($app $arg)
    `(fun ($argsId : List Nat) => $app)

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
  let mut map1Set : Array Term := #[]
  let mut map2Set : Array Term := #[]
  for f in ci.fields do
    let proj := mkIdent (`σ ++ f.name)
    let fld := mkIdent f.name
    let amt? ← isAmountTy f.valTy
    let k := mkIdent `k
    let v := mkIdent `v
    match f.kind with
    | .scalar =>
      if amt? then
        scalar := scalar.push (← `(fun $σ => Lsc.Amount.toNat $proj))
        scalarUpd := scalarUpd.push (← `(fun $σ $m => { $σ with $fld:ident := Lsc.Amount.ofNat $m }))
      else
        scalar := scalar.push (← `(fun $σ => $proj))
        scalarUpd := scalarUpd.push (← `(fun $σ $m => { $σ with $fld:ident := $m }))
      map1 := map1.push (← `(fun _ _ => 0)); map1Upd := map1Upd.push (← `(fun $σ _ => $σ))
      map2 := map2.push (← `(fun _ _ _ => 0)); map2Upd := map2Upd.push (← `(fun $σ _ => $σ))
      map1Set := map1Set.push (← `(fun $σ _ _ => $σ))
      map2Set := map2Set.push (← `(fun $σ _ _ _ => $σ))
    | .map1 =>
      scalar := scalar.push (← `(fun _ => 0)); scalarUpd := scalarUpd.push (← `(fun $σ _ => $σ))
      if amt? then
        map1 := map1.push (← `(fun $σ $k => Lsc.Amount.toNat ($proj $k)))
        map1Upd := map1Upd.push
          (← `(fun $σ $m => { $σ with $fld:ident := fun $k => Lsc.Amount.ofNat ($m $k) }))
        map1Set := map1Set.push
          (← `(fun $σ $k $v =>
            { $σ with $fld:ident := Function.update $proj $k (Lsc.Amount.ofNat $v) }))
      else
        map1 := map1.push (← `(fun $σ => $proj))
        map1Upd := map1Upd.push (← `(fun $σ $m => { $σ with $fld:ident := $m }))
        map1Set := map1Set.push
          (← `(fun $σ $k $v => { $σ with $fld:ident := Function.update $proj $k $v }))
      map2 := map2.push (← `(fun _ _ _ => 0)); map2Upd := map2Upd.push (← `(fun $σ _ => $σ))
      map2Set := map2Set.push (← `(fun $σ _ _ _ => $σ))
    | .map2 =>
      scalar := scalar.push (← `(fun _ => 0)); scalarUpd := scalarUpd.push (← `(fun $σ _ => $σ))
      map1 := map1.push (← `(fun _ _ => 0)); map1Upd := map1Upd.push (← `(fun $σ _ => $σ))
      map1Set := map1Set.push (← `(fun $σ _ _ => $σ))
      if amt? then
        let k₁ := mkIdent `k₁; let k₂ := mkIdent `k₂
        map2 := map2.push (← `(fun $σ $k₁ $k₂ => Lsc.Amount.toNat ($proj $k₁ $k₂)))
        map2Upd := map2Upd.push
          (← `(fun $σ $m => { $σ with $fld:ident := fun $k₁ $k₂ => Lsc.Amount.ofNat ($m $k₁ $k₂) }))
        map2Set := map2Set.push
          (← `(fun $σ $k₁ $k₂ $v =>
            let m := $proj
            { $σ with $fld:ident :=
              Function.update m $k₁ (Function.update (m $k₁) $k₂ (Lsc.Amount.ofNat $v)) }))
      else
        let k₁ := mkIdent `k₁; let k₂ := mkIdent `k₂
        map2 := map2.push (← `(fun $σ => $proj))
        map2Upd := map2Upd.push (← `(fun $σ $m => { $σ with $fld:ident := $m }))
        map2Set := map2Set.push
          (← `(fun $σ $k₁ $k₂ $v =>
            let m := $proj
            { $σ with $fld:ident :=
              Function.update m $k₁ (Function.update (m $k₁) $k₂ $v) }))
  let evBuilders ← ci.evCtors.mapM ctorBuilder
  let errBuilders ← ci.errCtors.mapM ctorBuilder
  let evDefault ← ctorBuilder ci.evCtors[0]!
  let errDefault ← ctorBuilder ci.errCtors[0]!
  let S := mkIdent ci.storage
  let E := mkIdent ci.event
  let Er := mkIdent ci.error
  let X : Term ←
    match ci.ext? with
    | some ext => pure ⟨mkIdent ext⟩
    | none => `(Unit)
  let extTerm : Term ←
    match ci.ext?, ci.bindings.size with
    | none, _ | some _, 0 => `(Lsc.ExtSchema.noneCall.call)
    | some _, n => do
      let b := mkIdent `b
      let mm := mkIdent `m
      let args' := mkIdent `args
      let mut acc ← `(fun (_ : Lsc.Ctx) (_ : Lsc.World $S $X $E) =>
          Except.error (α := Nat × Lsc.World $S $X $E) Lsc.Err.callFailed)
      for k in (List.range n).reverse do
        let bi := ci.bindings[k]!
        let bId := mkIdent bi.name
        let iface := mkIdent bi.iface
        let kLit := quote k
        let body ←
          `(if h : $mm < ($iface).n then
              Lsc.Tx.call $bId (($iface).idx.invFun ⟨$mm, h⟩) $args'
            else fun (_ : Lsc.Ctx) (_ : Lsc.World $S $X $E) =>
              Except.error (α := Nat × Lsc.World $S $X $E) Lsc.Err.callFailed)
        acc ← `(if $b = $kLit then $body else $acc)
      `(fun $b $mm $args' => $acc)
  let name := mkIdent (`_root_ ++ ci.schema)
  `(def $name : Lsc.ContractSchema $S $X $E $Er where
      st := {
        scalar := fun $i => List.getD [$scalar,*] $i (fun _ => 0)
        scalarUpd := fun $i => List.getD [$scalarUpd,*] $i (fun $σ _ => $σ)
        map1 := fun $i => List.getD [$map1,*] $i (fun _ _ => 0)
        map1Upd := fun $i => List.getD [$map1Upd,*] $i (fun $σ _ => $σ)
        map2 := fun $i => List.getD [$map2,*] $i (fun _ _ _ => 0)
        map2Upd := fun $i => List.getD [$map2Upd,*] $i (fun $σ _ => $σ)
        map1Set := fun $i => List.getD [$map1Set,*] $i (fun $σ _ _ => $σ)
        map2Set := fun $i => List.getD [$map2Set,*] $i (fun $σ _ _ _ => $σ) }
      ev := ⟨fun $i $args => List.getD [$evBuilders,*] $i $evDefault $args⟩
      err := ⟨fun $i $args => List.getD [$errBuilders,*] $i $errDefault $args⟩
      ext := { call := $extTerm })

def abiTyOf (ty : Expr) : MetaM AbiTy := do
  let ty ← whnfR ty
  match ty.getAppFn.constName? with
  | some ``Nat => pure .uint256
  | some ``Lsc.Address => pure .address
  | some ``Lsc.Flag => pure .bool
  | some ``Lsc.Amount | some ``Lsc.Price | some ``Lsc.Fixed => pure .uint256
  | _ => throwError "lsc_contract: unsupported ABI type `{ty}` (Nat, Address, Flag, Amount)"

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
    let abi ← abiTyOf f.valTy
    let abiT ← match abi with
      | .uint256 => `(Lsc.AbiTy.uint256)
      | .address => `(Lsc.AbiTy.address)
      | .bool => `(Lsc.AbiTy.bool)
    `({ name := $nm, kind := $k, ty := $abiT })
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

partial def atomOf (env : Env t) (e : Expr) : MetaM Atom := do
  let e := e.consumeMData
  -- Amount boundary: Core stores the underlying word.
  if e.isAppOf ``Lsc.Amount.toNat || e.isAppOf ``Lsc.Amount.ofNat
      || e.isAppOf ``Lsc.Amount.mk then
    return (← atomOf env e.appArg!)
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
    let body :=
      if body.isAppOf ``Lsc.Amount.toNat then body.appArg! else body
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
the `Fixed` abbrev to `Amount Unit s`; user `abbrev`s such as `Dai := Amount …` are
unfolded one step on the fallback path so `Address` stays folded. -/
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
  | _, _ =>
    match ← unfoldDefinition? ρ with
    | some ρ' => retTyOf ρ'
    | none => throwError "reify: unsupported return type `{ρ}` \
        (Unit, Nat, Address, Flag, Amount, Price, or pairs)"

/-- Head constants that unfold to a `Tx` primitive (`Amount.add` → `addChecked`,
`Binding.transfer` → `Tx.call`, …). Compared as names so Reify need not import
`Stdlib.ERC20`. -/
def isSurfaceOp : Name → Bool
  | .str (.str `Lsc "Amount") s =>
      s == "add" || s == "sub" || s == "mulDown" || s == "mulUp" || s == "divDown"
        || s == "divUp" || s == "ratioDown" || s == "ratioUp" || s == "shareDown"
        || s == "shareUp" || s == "rescale" || s == "convert"
  | .str (.str `Lsc "Binding") s =>
      s == "transfer" || s == "transferFrom" || s == "balanceOf" || s == "decimals"
        || s == "transferUnit" || s == "transferFromUnit"
  | _ => false

/-- `Rounding` must be a literal constructor so the reifier can pick `mulDivDown` vs `mulDivUp`. -/
def roundingOf (e : Expr) : MetaM Rounding := do
  let e := e.consumeMData
  match e.getAppFn.constName? with
  | some ``Lsc.Rounding.down => return .down
  | some ``Lsc.Rounding.up => return .up
  | _ => throwError "reify: rounding `{e}` must be a literal `.down` or `.up`"

/-- Unfold `Amount.*` / `Binding.*` (and reduce a `Rounding` match) until the head is a
`Tx` primitive. -/
partial def unfoldToTx (x : Expr) (fuel : Nat := 8) : MetaM Expr := do
  let x := x.consumeMData
  let n := x.getAppFn.constName?
  if n == some ``Lsc.Tx.addChecked || n == some ``Lsc.Tx.subChecked
      || n == some ``Lsc.Tx.mulChecked || n == some ``Lsc.Tx.divChecked
      || n == some ``Lsc.Tx.mulDivDown || n == some ``Lsc.Tx.mulDivUp
      || n == some ``Lsc.Tx.call || n == some ``Lsc.Tx.callUnit then
    return x
  if fuel = 0 then return x
  if n.any isSurfaceOp then
    if n == some ``Lsc.Amount.rescale || n == some ``Lsc.Amount.convert then
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

partial def atomsOfList (env : Env t) (e : Expr) : MetaM (List Atom) := do
  let e := e.consumeMData
  if e.isAppOf ``List.nil then return []
  if e.isAppOf ``List.cons then
    let args := e.getAppArgs
    let hd ← atomOf env args[args.size - 2]!
    let tl ← atomsOfList env args[args.size - 1]!
    return hd :: tl
  throwError "reify: expected a list of atoms, found `{e}`"

def bindingIndex (ci : ContractInfo) (b : Expr) : MetaM Nat := do
  let b := b.consumeMData
  match b.getAppFn.constName? with
  | some n =>
    match ci.bindings.findIdx? (fun bi => bi.name == n) with
    | some i => pure i
    | none => throwError "reify: binding `{n}` must be a constant"
  | none => throwError "reify: binding `{b}` must be a constant"

def methodIndex (m : Expr) : MetaM Nat := do
  let m ← whnfR m.consumeMData
  match m.getAppFn.constName? with
  | some n =>
    let info ← getConstInfoCtor n
    let iinfo ← getConstInfoInduct info.induct
    match iinfo.ctors.toArray.idxOf? n with
    | some i => pure i
    | none => throwError "reify: `{n}` is not a method constructor"
  | none => throwError "reify: method `{m}` must be an interface method constructor"

/-- Word-valued primitives. -/
def opOf (ci : ContractInfo) (env : Env t) (x : Expr) : MetaM (Option Op) := do
  let x := x.consumeMData
  let n0 := x.getAppFn.constName?
  -- Amount.add/sub/share* are explicit `if`s, not `addChecked`; match before unfolding.
  if n0 == some ``Lsc.Amount.add || n0 == some ``Lsc.Amount.sub
      || n0 == some ``Lsc.Amount.shareDown || n0 == some ``Lsc.Amount.shareUp then
    let args := x.getAppArgs
    let atom := atomOf env
    match n0, args.size with
    | some ``Lsc.Amount.add, n =>
      return some (.addChecked (← atom args[n - 2]!) (← atom args[n - 1]!))
    | some ``Lsc.Amount.sub, n =>
      return some (.subChecked (← atom args[n - 2]!) (← atom args[n - 1]!))
    | some ``Lsc.Amount.shareDown, n =>
      return some (.mulDivDown (← atom args[n - 3]!) (← atom args[n - 2]!) (← atom args[n - 1]!))
    | some ``Lsc.Amount.shareUp, n =>
      return some (.mulDivUp (← atom args[n - 3]!) (← atom args[n - 2]!) (← atom args[n - 1]!))
    | _, _ => return none
  let x ←
    if n0.any isSurfaceOp then unfoldToTx x
    else pure x
  let args := x.getAppArgs
  let atom := atomOf env
  match x.getAppFn.constName?, args.size with
  | some ``Lsc.Tx.load, 6 =>
    let f ← fieldOfProj ci args[5]!
    unless f.kind == .scalar do throwError "reify: `read {f.name}` needs keys"
    return some (.load f.idx)
  | some ``Lsc.Tx.loadMap, 8 =>
    let f ← fieldOfProj ci args[6]!
    unless f.kind == .map1 do throwError "reify: `read {f.name}[k]` has the wrong number of keys"
    return some (.loadMap f.idx (← atom args[7]!))
  | some ``Lsc.Tx.loadMap2, 10 =>
    let f ← fieldOfProj ci args[7]!
    unless f.kind == .map2 do throwError "reify: `read {f.name}[k₁, k₂]` has the wrong number of keys"
    return some (.loadMap2 f.idx (← atom args[8]!) (← atom args[9]!))
  | some ``Lsc.Tx.sender, 4 => return some .sender
  | some ``Lsc.Tx.value, 4 => return some .value
  | some ``Lsc.Tx.timestamp, 4 => return some .timestamp
  | some ``Lsc.Tx.blockNumber, 4 => return some .blockNumber
  | some ``Lsc.Tx.selfAddress, 4 => return some .selfAddress
  | some ``Lsc.Tx.addChecked, 6 => return some (.addChecked (← atom args[4]!) (← atom args[5]!))
  | some ``Lsc.Tx.subChecked, 6 => return some (.subChecked (← atom args[4]!) (← atom args[5]!))
  | some ``Lsc.Tx.mulChecked, 6 => return some (.mulChecked (← atom args[4]!) (← atom args[5]!))
  | some ``Lsc.Tx.divChecked, 6 => return some (.divChecked (← atom args[4]!) (← atom args[5]!))
  | some ``Lsc.Tx.mulDivDown, 7 =>
    return some (.mulDivDown (← atom args[4]!) (← atom args[5]!) (← atom args[6]!))
  | some ``Lsc.Tx.mulDivUp, 7 =>
    return some (.mulDivUp (← atom args[4]!) (← atom args[5]!) (← atom args[6]!))
  | some ``Lsc.Tx.call, n =>
    if n < 3 then return none
    let bIdx ← bindingIndex ci args[n - 3]!
    let mIdx ← methodIndex args[n - 2]!
    let as ← atomsOfList env args[n - 1]!
    return some (.call bIdx mIdx as)
  | some ``Lsc.Amount.add, n =>
    return some (.addChecked (← atom args[n - 2]!) (← atom args[n - 1]!))
  | some ``Lsc.Amount.sub, n =>
    return some (.subChecked (← atom args[n - 2]!) (← atom args[n - 1]!))
  | some ``Lsc.Amount.shareDown, n =>
    return some (.mulDivDown (← atom args[n - 3]!) (← atom args[n - 2]!) (← atom args[n - 1]!))
  | some ``Lsc.Amount.shareUp, n =>
    return some (.mulDivUp (← atom args[n - 3]!) (← atom args[n - 2]!) (← atom args[n - 1]!))
  | some ``Pure.pure, 4 => return some (.pure (← atom args[3]!))
  | _, _ => return none

/-- Unit-valued primitives. -/
def stmtOf (ci : ContractInfo) (env : Env t) (x : Expr) : MetaM (Option Stmt) := do
  let x := x.consumeMData
  let x ←
    if x.getAppFn.constName?.any isSurfaceOp then unfoldToTx x
    else pure x
  let args := x.getAppArgs
  let atom := atomOf env
  match x.getAppFn.constName?, args.size with
  | some ``Lsc.Tx.store, 7 =>
    let f ← fieldOfUpd ci args[5]!
    unless f.kind == .scalar do throwError "reify: `write {f.name}` needs keys"
    return some (.store f.idx (← atom args[6]!))
  | some ``Lsc.Tx.storeMap, 11 =>
    let f ← fieldOfProj ci args[7]!
    let f' ← fieldOfUpd ci args[8]!
    unless f.kind == .map1 && f.idx == f'.idx do
      throwError "reify: `write {f.name}[k]` has the wrong number of keys"
    return some (.storeMap f.idx (← atom args[9]!) (← atom args[10]!))
  | some ``Lsc.Tx.storeMap2, 14 =>
    let f ← fieldOfProj ci args[9]!
    let f' ← fieldOfUpd ci args[10]!
    unless f.kind == .map2 && f.idx == f'.idx do
      throwError "reify: `write {f.name}[k₁, k₂]` has the wrong number of keys"
    return some (.storeMap2 f.idx (← atom args[11]!) (← atom args[12]!) (← atom args[13]!))
  | some ``Lsc.Tx.require, 7 =>
    let (i, eargs) ← ctorIndex ci.errCtors args[6]!
    return some (.require (← condOf env args[4]!) i (← eargs.toList.mapM atom))
  | some ``Lsc.Tx.emit, 5 =>
    let (i, eargs) ← ctorIndex ci.evCtors args[4]!
    return some (.emit i (← eargs.toList.mapM atom))
  | some ``Lsc.Tx.revert, 6 =>
    let (i, eargs) ← ctorIndex ci.errCtors args[5]!
    return some (.revert i (← eargs.toList.mapM atom))
  | some ``Lsc.Tx.callUnit, n =>
    if n < 3 then return none
    let bIdx ← bindingIndex ci args[n - 3]!
    let mIdx ← methodIndex args[n - 2]!
    let as ← atomsOfList env args[n - 1]!
    return some (.call bIdx mIdx as)
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
      | ``Lsc.Tx.revert, 6 =>
        let (i, eargs) ← ctorIndex ci.errCtors args[5]!
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
  if ty.isAppOfArity ``Lsc.Tx 5 then return ty
  match ← unfoldDefinition? ty with
  | some ty' => whnfToTx ty'
  | none => throwError "reify: `{ty}` is not a `Tx` type"

/-- Reify `fn` and add `fn.core` and `fn.core_denote` to the environment. -/
def reifyFunction (fn : Name) : TermElabM Unit := do
  let info ← getConstInfoDefn fn
  forallTelescope info.type fun params body => do
    let txTy ← whnfToTx body
    let S := txTy.getArg! 0
    let X := txTy.getArg! 1
    let E := txTy.getArg! 2
    let ε := txTy.getArg! 3
    let ρ := txTy.getArg! 4
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
    -- Certificate: `Core.denote schema core env = f`, or `Core.denoteAWord/AUnit = f`
    -- when the surface is Amount-typed (return or storage). `Functor.map ofNat` over
    -- `Core.denote` is not definitionally `Amount.add` (bind does not push through `ite`).
    let schema := Lean.mkConst ci.schema
    -- Amount parameters are words in Core; insert `toNat` at the boundary.
    let envAtoms : List Expr ← params.toList.reverse.mapM fun p => do
      let ty ← inferType p
      if ← isAmountTy ty then mkAppM ``Lsc.Amount.toNat #[p]
      else pure p
    let envList ← mkListLit (Lean.mkConst ``Nat) envAtoms
    let annot ← amountAnnot ci ρ
    let lhs ←
      match t, annot with
      | .word, some (τ, sc) =>
        mkAppOptM ``Core.denoteAWord
          #[some S, some X, some E, some ε, some τ, some sc, some schema,
            some (toExpr t), some (Lean.mkConst coreName), some envList]
      | .unit, some (τ, sc) =>
        mkAppOptM ``Core.denoteAUnit
          #[some S, some X, some E, some ε, some τ, some sc, some schema,
            some (toExpr t), some (Lean.mkConst coreName), some envList]
      | _, _ =>
        pure <| mkAppN (Lean.mkConst ``Core.denote)
          #[S, X, E, ε, schema, toExpr t, Lean.mkConst coreName, envList]
    let rhs := mkAppN (Lean.mkConst fn) params
    let eq ← mkEq lhs rhs
    unless ← isDefEq lhs rhs do
      throwError "reify: certificate failed — denotation of the reified term is not \
        definitionally the original function.{indentExpr eq}\nReified Core:{indentExpr core.toExpr}"
    let stmt ← mkForallFVars params eq
    let proof ← mkLambdaFVars params (← mkEqRefl lhs)
    addDecl <| .thmDecl { name := fn ++ `core_denote, levelParams := [], type := stmt, value := proof }
    trace[Lsc.reify] "reified {fn} : Core {repr t}\n{repr core}"

/-! ## Contract assembly (`lsc_contract`) -/

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
    let t ← retTyOf (txTy.getArg! 4)
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

/-- ABI rows for a declared interface (IERC20 in this slice). -/
def methodsOfIface (iface : Name) : MetaM (List (String × AbiSpec)) := do
  if iface.getString! == "IERC20" then
    return [
      ("transfer", { selector := 0xa9059cbb, arity := 2, ret := .boolOpt }),
      ("transferFrom", { selector := 0x23b872dd, arity := 3, ret := .boolOpt }),
      ("balanceOf", { selector := 0x70a08231, arity := 1, ret := .word }),
      ("decimals", { selector := 0x313ce567, arity := 0, ret := .word })
    ]
  throwError "lsc_contract: unknown interface `{iface}` (only IERC20 is wired)"

/-- Assemble `C.contract : ContractDef` from reified entrypoints. Compilation to Yul is a
separate Lean function of that value (`Lsc.Compiler.toYul`). -/
def assembleContract (ns : Name) (fns : Array Name) : TermElabM Unit := do
  for fn in fns do
    unless (← getEnv).contains (fn ++ `core) do
      reifyFunction fn
  let ci ← contractInfo ns
  let fields : List FieldDef ← ci.fields.toList.mapM fun f => do
    let abi ← abiTyOf f.valTy
    pure { name := f.name.getString!, kind := fieldKindToAbi f.kind, ty := abi }
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
  let bindings : List BindingDef ← ci.bindings.toList.mapM fun bi => do
    -- Method names/ABI: evaluate `I.abi` at each constructor of `I.Method`.
    let ifaceInfo ← getConstInfo bi.iface
    let ifaceTy ← whnfD ifaceInfo.type
    unless ifaceTy.isConstOf ``Lsc.Interface do
      throwError "lsc_contract: `{bi.iface}` is not an Interface"
    let methods ← methodsOfIface bi.iface
    pure {
      name := bi.name.getString!
      fieldSlot := bi.fieldSlot
      ifaceName := bi.iface.getString!
      methods }
  let contractTy := Lean.mkConst ``ContractDef
  let contractVal := mkAppN (Lean.mkConst ``ContractDef.mk) #[
    toExpr ns.getString!, toExpr fields, fnList, ctorE, toExpr events, toExpr errors,
    toExpr bindings]
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

/-- Parameter names/types and the `Tx S X E ε ρ` indices of `fn`. -/
structure FnSurface where
  S : Expr
  X : Expr
  E : Expr
  ε : Expr
  params : Array (Name × Expr)
  ρ : Expr

def fnSurface (fn : Name) : MetaM FnSurface := do
  let info ← getConstInfoDefn fn
  forallTelescope info.type fun xs body => do
    let txTy ← whnfToTx body
    let params ← xs.mapIdxM fun i x => do
      let n := ← x.fvarId!.getUserName
      let n := if n.hasMacroScopes then Name.mkSimple s!"a{i}" else n
      pure (n, ← inferType x)
    pure {
      S := txTy.getArg! 0, X := txTy.getArg! 1, E := txTy.getArg! 2
      ε := txTy.getArg! 3, params, ρ := txTy.getArg! 4 }

def entrypointFns (fns : Array Name) : MetaM (Array Name) :=
  fns.filterM fun fn => do
    let (_, _, kind) ← fnMeta fn
    return kind != .constructor

def mkEntryRhs (fn : Name) : MetaM Term := do
  let surf ← fnSurface fn
  let argTys ← surf.params.mapM fun (_, ty) => exprToTerm ty
  let argsTy ← mkProdType argTys
  let retTy ← exprToTerm surf.ρ
  let run ← mkRunTerm fn surf.params.size
  `(⟨$argsTy, $retTy, $run⟩)

def mkSpecExecCommand (ns fn : Name) : MetaM (TSyntax `command) := do
  let surf ← fnSurface fn
  let ctor := ctorIdent fn
  let specId : Term := ⟨mkIdent (ns ++ `spec)⟩
  let f : Term := ⟨mkIdent fn⟩
  let args : Array Term := surf.params.map fun (n, _) => ⟨mkIdent n⟩
  let argStx ← mkTuple args
  let rhs ← `($f $args*)
  let binders : TSyntaxArray ``Lean.Parser.Term.bracketedBinderF ←
    surf.params.mapM fun (n, ty) => do
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
  let (S₀, X₀, E₀, ε₀) ←
    if entries.isEmpty then
      let env ← getEnv
      let X :=
        if isStructure env (ns ++ `Ext) then Lean.mkConst (ns ++ `Ext)
        else Lean.mkConst ``Unit
      pure (Lean.mkConst (ns ++ `Storage), X, Lean.mkConst (ns ++ `Event),
        Lean.mkConst (ns ++ `Error))
    else
      let surf ← fnSurface entries[0]!
      pure (surf.S, surf.X, surf.E, surf.ε)
  let S ← exprToTerm S₀
  let X ← exprToTerm X₀
  let E ← exprToTerm E₀
  let ε ← exprToTerm ε₀
  let entryName := mkIdent (ns ++ `entry)
  let alts : TSyntaxArray ``Lean.Parser.Term.matchAlt ← entries.mapM fun fn => do
    let ctor := ctorIdent fn
    let rhs ← mkEntryRhs fn
    `(Lean.Parser.Term.matchAltExpr| | .$ctor:ident => $rhs)
  let entryCmd ←
    if entries.isEmpty then
      `(command| @[reducible] def $entryName : $fnName → Lsc.Entry $S $X $E $ε :=
          fun fn => nomatch fn)
    else
      `(command| @[reducible] def $entryName : $fnName → Lsc.Entry $S $X $E $ε
          $alts:matchAlt*)
  let specName := mkIdent (ns ++ `spec)
  let specCmd ←
    `(command| @[reducible] def $specName : Lsc.Spec $S $X $E $ε := ⟨$fnName, $entryName⟩)
  let mut cmds : Array (TSyntax `command) := #[fnCmd, entryCmd, specCmd]
  for fn in entries do
    cmds := cmds.push (← mkSpecExecCommand ns fn)
  return cmds

def obligationsMissing (ns : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut missing : Array Name := #[]
  for s in #[`Inv, `claim, `Auth, `inflow, `holdings] do
    unless env.contains (ns ++ s) do
      missing := missing.push (ns ++ s)
  return missing

/-- Copy-pasteable security theorems for `C`'s generated `Fn` (not imported from Security). -/
def obligationsText (ns : Name) (ctors : List Name) (extName : String) : String :=
  let C := ns.toString
  let leaf (n : Name) : String := n.getString!
  let world := s!"Lsc.World {C}.Storage {extName} {C}.Event"
  let thm (fn : Name) (suffix ty args : String) : String :=
    s!"theorem {C}.{leaf fn}_{suffix} : {ty} {C}.spec {args} .{leaf fn} := by sorry"
  let preserves := ctors.map fun fn =>
    thm fn "preserves_inv" "Lsc.Security.PreservesInvFn" s!"{C}.Inv"
  let auths := ctors.map fun fn =>
    thm fn "auth" "Lsc.Security.NoUnauthorizedDecreaseFn" s!"{C}.Inv {C}.claim {C}.Auth"
  let conserves := ctors.map fun fn =>
    thm fn "conserves" "Lsc.Security.ConservesFn" s!"{C}.Inv {C}.claim {C}.inflow"
  let arms (suffix : String) : String :=
    "\n".intercalate (ctors.map fun fn =>
      s!"    | .{leaf fn} => {C}.{leaf fn}_{suffix}")
  let assembler (name ty ofFns suffix : String) : String :=
    s!"theorem {C}.{name} : {ty} :=\n  {ofFns} fun fn =>\n    match fn with\n{arms suffix}"
  let rely :=
    if extName == "Unit" then "fun _ _ => True" else s!"{C}.rely"
  let invRely :=
    s!"theorem {C}.inv_rely : Lsc.Security.PreservesInvEnv {C}.spec {C}.Inv ({rely}) := by sorry"
  let extraction :=
    "theorem " ++ C ++ ".no_unauthorized_extraction\n" ++
    "    (self : Lsc.Address) (tr : List (Lsc.Security.Step " ++ C ++ ".spec))\n" ++
    "    (w : " ++ world ++ ") (a : Lsc.Address)\n" ++
    "    (hw : " ++ C ++ ".Inv w) (hW : Lsc.Security.Wf self tr)\n" ++
    "    (hR : Lsc.Security.RelyAlong (" ++ rely ++ ") tr w)\n" ++
    "    (hA : Lsc.Security.NoAuthAlong " ++ C ++ ".Auth a tr w) :\n" ++
    "    " ++ C ++ ".claim a w.self ≤ " ++ C ++
    ".claim a (Lsc.Security.run tr w).self :=\n" ++
    "  Lsc.Security.no_unauthorized_extraction " ++ C ++ ".no_unauth " ++
    C ++ ".preserves_inv " ++ C ++ ".inv_rely self tr w a hw hW hR hA"
  let body :=
    (preserves ++
      [assembler "preserves_inv" s!"Lsc.Security.PreservesInv {C}.spec {C}.Inv"
        "Lsc.Security.PreservesInv.of_fns" "preserves_inv"] ++
      [invRely] ++
      auths ++
      [assembler "no_unauth"
        s!"Lsc.Security.NoUnauthorizedDecrease {C}.spec {C}.Inv {C}.claim {C}.Auth"
        "Lsc.Security.NoUnauthorizedDecrease.of_fns" "auth"] ++
      [extraction] ++
      conserves ++
      [assembler "conserves" s!"Lsc.Security.Conservation {C}.spec {C}.Inv {C}.claim {C}.inflow"
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
          (need {nsName}.Inv, {nsName}.claim, {nsName}.Auth, {nsName}.inflow, {nsName}.holdings)"
      let info ← getConstInfoInduct (nsName ++ `Fn)
      let extName :=
        if isStructure env (nsName ++ `Ext) then (nsName ++ `Ext).toString else "Unit"
      logInfo m!"{obligationsText nsName info.ctors extName}"
  | _ => throwUnsupportedSyntax

end Lsc.Reify

