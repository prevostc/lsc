import Lsc.Lang.Core
import Lsc.Lang.Contract
import Lsc.Lang.Inline
import Lsc.Lang.Spec

/-!
# reification

`lsc_schema C` derives `C.schema : ContractSchema C.Storage C.Ext C.Event C.Error` from the
user's Lean types, plus `C.schema_lawful : C.schema.st.Lawful …`, and `lsc_reify C.f` turns the elaborated term of a contract function
`C.f : … → Tx C.Storage C.Ext C.Event C.Error ρ` (or `Unit` when there is no `Ext`) into

* `C.f.core : Core t` — the Core AST, and
* `C.f.core_denote` — `Core.denote C.schema C.f.core [args] = C.f args` for word-typed
  programs, or `Core.denoteAWord` / `Core.denoteAUnit` when the surface returns
  `Amount` or has `Amount` storage. Proved by `rfl` when the sides are
  definitionally equal; otherwise by the `Tx` monad laws (`bind` is not
  definitionally associative, so an `@[lsc_inline]` helper mid-`do` needs them).
  A propositional certificate is not a trust extension: the kernel still checks
  `denote (reify f) = f`.

`lsc_contract C f₁ … fₙ` additionally defines `C.contract` and a
language-level `C.spec` (`C.Fn` / `C.entry` / `C.spec_exec_*`). `#lsc_obligations C`
prints the security theorems to prove; it does not import `Lsc.Security`.

The reifier only accepts the *reifiable fragment* — the fixed set of
`Tx` primitives combined with `do`, `let`, `if` on decidable word comparisons, and
`pure` of words/addresses/pairs. Library helpers tagged `@[lsc_inline]` are
delta-unfolded (β with arguments, fuel-bounded; recursive defs are rejected at
the attribute) and reified from the resulting body. Anything else is rejected
with the offending subterm, so a reifier bug or an out-of-fragment program is a
build error, never a miscompile.

The translation follows the shapes Lean's `do` elaborator produces:

* `bind op (fun x => k)`                          → `letOp` / `seq`
* `bind (bind x k₁) k₂` (inlined helper mid-`do`) → reassociate to ANF, then `letOp` / `seq`
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
        || s == "checkOk" || s == "safeTransfer" || s == "safeTransferFrom"
        || s == "safeApprove"
  | _ => false

/-- `Rounding` must be a literal constructor so the reifier can pick `mulDivDown` vs `mulDivUp`. -/
def roundingOf (e : Expr) : MetaM Rounding := do
  let e := e.consumeMData
  match e.getAppFn.constName? with
  | some ``Lsc.Rounding.down => return .down
  | some ``Lsc.Rounding.up => return .up
  | _ => throwError "reify: rounding `{e}` must be a literal `.down` or `.up`"

/-- Heads that `deltaUnfold` must not unfold past (primitives, `do` combinators,
and `Amount.add`/`sub`/`share*` whose bodies are `if`s, not `Tx.*`). -/
def isDeltaStop : Name → Bool
  | ``Lsc.Tx.addChecked | ``Lsc.Tx.subChecked | ``Lsc.Tx.mulChecked | ``Lsc.Tx.divChecked
  | ``Lsc.Tx.mulDivDown | ``Lsc.Tx.mulDivUp
  | ``Lsc.Tx.call | ``Lsc.Tx.callUnit
  | ``Lsc.Tx.load | ``Lsc.Tx.loadMap | ``Lsc.Tx.loadMap2
  | ``Lsc.Tx.store | ``Lsc.Tx.storeMap | ``Lsc.Tx.storeMap2
  | ``Lsc.Tx.require | ``Lsc.Tx.emit | ``Lsc.Tx.revert
  | ``Lsc.Tx.sender | ``Lsc.Tx.value | ``Lsc.Tx.timestamp | ``Lsc.Tx.blockNumber
  | ``Lsc.Tx.selfAddress
  | ``Bind.bind | ``Pure.pure | ``ite
  | ``Lsc.Amount.add | ``Lsc.Amount.sub | ``Lsc.Amount.shareDown | ``Lsc.Amount.shareUp =>
    true
  | _ => false

def isLscInline (n : Name) : MetaM Bool := do
  return Lsc.lscInlineAttr.hasTag (← getEnv) n

/-- Error when an `@[lsc_inline]` body (or a non-primitive bind) is out of fragment. -/
def throwInlineOr {α : Type} (inline? : Option Name) (sub : Expr) (fallback : MessageData) :
    MetaM α :=
  match inline? with
  | some n =>
    throwError "reify: `@[lsc_inline]` `{.ofConstName n}` body is outside the reifiable fragment; offending sub-term:{indentExpr sub}"
  | none => throwError fallback

/-- Unfold `@[lsc_inline]` (and `isSurfaceOp` fallback), reducing `Rounding` matches.
Before unfolding `rescale`/`convert`, `roundingOf` requires a literal `.down`/`.up`. -/
partial def deltaUnfold (e : Expr) (fuel : Nat := 8) : MetaM (Expr × Option Name) := do
  let rec go (e : Expr) (fuel : Nat) (seen : Option Name) : MetaM (Expr × Option Name) := do
    let e := e.consumeMData
    if fuel = 0 then return (e, seen)
    let n? := e.getAppFn.constName?
    if n?.any isDeltaStop then return (e, seen)
    if let some n := n? then
      let tagged ← isLscInline n
      if tagged || isSurfaceOp n then
        if n == (.str (.str `Lsc "Amount") "rescale")
            || n == (.str (.str `Lsc "Amount") "convert") then
          let args := e.getAppArgs
          if args.size > 0 then
            let _ ← roundingOf args[args.size - 2]!
        let seen' := if tagged then some n else seen
        match ← unfoldDefinition? e with
        | some e' => return (← go e' (fuel - 1) seen')
        | none =>
          let e' ← whnfR e
          if e' == e then return (e, seen')
          else return (← go e' (fuel - 1) seen')
    match ← unfoldDefinition? e with
    | some e' => go e' (fuel - 1) seen
    | none =>
      let e' ← whnfR e
      if e' == e then return (e, seen)
      else go e' (fuel - 1) seen
  go e fuel none

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
  let x ← do
    match n0 with
    | some n =>
      if (← isLscInline n) || isSurfaceOp n then
        pure (← deltaUnfold x).1
      else
        pure x
    | none => pure x
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
  let n0 := x.getAppFn.constName?
  let x ← do
    match n0 with
    | some n =>
      if (← isLscInline n) || isSurfaceOp n then
        pure (← deltaUnfold x).1
      else
        pure x
    | none => pure x
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

/-- `(inner >>= innerK) >>= k` as `inner >>= fun a => innerK a >>= k` (ANF). -/
def assocBindRight (innerBind k γ : Expr) : MetaM Expr := do
  let innerBind := innerBind.consumeMData
  unless innerBind.isAppOfArity ``Bind.bind 6 do
    throwError "reify: expected a nested `bind`"
  let iargs := innerBind.getAppArgs
  let bindFn := innerBind.getAppFn
  let m := iargs[0]!
  let inst := iargs[1]!
  let α := iargs[2]!
  let β := iargs[3]!
  let inner := iargs[4]!
  let innerK ← ensureLambda iargs[5]!
  let k ← ensureLambda k
  withLocalDeclD `a α fun a => do
    let innerKa := innerK.beta #[a]
    let body := mkAppN bindFn #[m, inst, β, γ, innerKa, k]
    let composedK ← mkLambdaFVars #[a] body
    return mkAppN bindFn #[m, inst, α, γ, inner, composedK]

partial def reify (ci : ContractInfo) (t : RetTy) (env : Env t) (e : Expr)
    (inline? : Option Name := none) : MetaM (Core t) := do
  let e := e.consumeMData
  match e with
  | .letE n ty v b _ =>
    let v := v.consumeMData
    if v.isLambda then
      -- Join point: `have jp := fun (y : T) => rest; body`.
      let hasArg := !(← isUnitTy v.bindingDomain!)
      let body ← lambdaBoundedTelescope v 1 fun ys rest => do
        let vars := if hasArg then ys[0]!.fvarId! :: env.vars else env.vars
        reify ci t { env with vars } rest inline?
      withLetDecl n ty v fun jpVar => do
        let jp : JoinPoint t := { fvar := jpVar.fvarId!, hasArg, depth := env.vars.length, body }
        reify ci t { env with jp := some jp } (b.instantiate1 jpVar) inline?
    else
      let (p, args) ← primOf env v
      withLetDecl n ty v fun x => do
        let k ← reify ci t { env with vars := x.fvarId! :: env.vars } (b.instantiate1 x) inline?
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
        let x0 := args[4]!
        let k ← ensureLambda args[5]!
        let (x, seen) ← deltaUnfold x0
        let inline? := seen.orElse fun _ => inline?
        if x.isAppOfArity ``Bind.bind 6 then
          reify ci t env (← assocBindRight x k args[3]!) inline?
        else if let some op ← opOf ci env x then
          lambdaBoundedTelescope k 1 fun ys body => do
            let kc ← reify ci t { env with vars := ys[0]!.fvarId! :: env.vars } body inline?
            return .letOp op kc
        else if let some s ← stmtOf ci env x then
          lambdaBoundedTelescope k 1 fun _ body => do
            let kc ← reify ci t env body inline?
            return .seq s kc
        else
          throwInlineOr inline? x m!"reify: `{x0}` is not a contract primitive"
      | ``Pure.pure, 4 => return .ret (← retExprOf env t args[3]!)
      | ``ite, 5 =>
        let c ← condOf env args[1]!
        let a ← reify ci t env args[3]! inline?
        let b ← reify ci t env args[4]! inline?
        return .ite c a b
      | ``Lsc.Tx.revert, 6 =>
        let (i, eargs) ← ctorIndex ci.errCtors args[5]!
        return .revertTail i (← eargs.toList.mapM (atomOf env))
      | _, _ =>
        let (e', seen) ← deltaUnfold e
        let inline? := seen.orElse fun _ => inline?
        if e' != e then
          reify ci t env e' inline?
        else if let some op ← opOf ci env e then
          match opTailCore t op with
          | some c => return c
          | none => throwInlineOr inline? e m!"reify: `{e}` returns a word but the function does not"
        else if let some s ← stmtOf ci env e then
          match stmtTailCore t s with
          | some c => return c
          | none => throwInlineOr inline? e m!"reify: `{e}` returns Unit but the function does not"
        else
          throwInlineOr inline? e m!"reify: `{e}` is outside the reifiable fragment"
    | _ => throwInlineOr inline? e m!"reify: `{e}` is outside the reifiable fragment"

/-! ## Commands -/

/-- `@[lsc_inline]` names reachable from `fn` (the helper and its callees). -/
def inlinesUsedBy (fn : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let info ← getConstInfoDefn fn
  let mut acc : Array Name := #[]
  let mut seen : NameSet := {}
  let mut work : Array Name := #[]
  for n in info.value.getUsedConstants do
    if Lsc.lscInlineAttr.hasTag env n then
      work := work.push n
  let mut i := 0
  while h : i < work.size do
    let n := work[i]
    i := i + 1
    if seen.contains n then continue
    seen := seen.insert n
    acc := acc.push n
    if let some v := (env.find? n).bind (·.value?) then
      for m in v.getUsedConstants do
        if Lsc.lscInlineAttr.hasTag env m && !seen.contains m then
          work := work.push m
  return acc

def bindArgs? (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``Bind.bind 6 then some (e.getArg! 4, e.getArg! 5)
  else none

/-- Unfold `Core.denote*` and `@[lsc_inline]` so a diagnostic can see the `bind`s. -/
partial def unfoldCertHead (e : Expr) (fuel : Nat := 16) : MetaM Expr := do
  let e := e.consumeMData
  if fuel = 0 then return e
  match e.getAppFn.constName? with
  | some ``Core.denote | some ``Core.denoteAWord | some ``Core.denoteAUnit =>
    match ← unfoldDefinition? e with
    | some e' => unfoldCertHead e' (fuel - 1)
    | none =>
      let e' ← whnfR e
      if e' == e then return e else unfoldCertHead e' (fuel - 1)
  | some n =>
    if (← isLscInline n) || isSurfaceOp n then
      match ← unfoldDefinition? e with
      | some e' => unfoldCertHead e' (fuel - 1)
      | none => return e
    else return e
  | none => return e

/-- First `Bind.bind` whose bound computations are not defeq, if any. -/
partial def firstDifferingBind (lhs rhs : Expr) (fuel : Nat := 32) :
    MetaM (Option (Expr × Expr)) := do
  if fuel = 0 then return some (lhs, rhs)
  if ← withNewMCtxDepth (withDefault (isDefEq lhs rhs)) then return none
  let lhs ← unfoldCertHead lhs
  let rhs ← unfoldCertHead rhs
  match bindArgs? lhs, bindArgs? rhs with
  | some (lx, lk), some (rx, rk) =>
    if ← withNewMCtxDepth (withDefault (isDefEq lx rx)) then
      match lk, rk with
      | .lam n t b _, .lam _ _ b' _ =>
        withLocalDeclD n t fun x =>
          firstDifferingBind (b.instantiate1 x) (b'.instantiate1 x) (fuel - 1)
      | _, _ => firstDifferingBind lk rk (fuel - 1)
    else
      return some (lhs, rhs)
  | none, none =>
    if lhs.isAppOfArity ``ite 5 && rhs.isAppOfArity ``ite 5 then
      if let some d ← firstDifferingBind (lhs.getArg! 3) (rhs.getArg! 3) (fuel - 1) then
        return some d
      firstDifferingBind (lhs.getArg! 4) (rhs.getArg! 4) (fuel - 1)
    else if lhs.isLambda && rhs.isLambda then
      lambdaBoundedTelescope lhs 1 fun xs b =>
        firstDifferingBind b (rhs.bindingBody!.instantiate1 xs[0]!) (fuel - 1)
    else
      return some (lhs, rhs)
  | _, _ => return some (lhs, rhs)

/--
Generate the `f.core_denote` proof term.

The certificate tactic is `first | rfl | (simp only [<fn>, <@[lsc_inline]
helpers>, Tx.bind_assoc, Tx.pure_bind, Tx.bind_pure, Tx.map_eq_pure_bind]; rfl)`.
`rfl` (`isDefEq` / `mkEqRefl`) is the fast path when no inlines are used.
With inlines the `rfl` attempt is skipped (it times out on a large
non-matching `do` block) and only the `simp only` branch runs. A
propositional certificate is not a trust extension: the reifier is still
untrusted MetaM, and the kernel checks `Core.denote (reify f) = f`.
-/
def certifyDenote (fn : Name) (lhs rhs coreE : Expr) : TermElabM Expr := do
  let eq ← mkEq lhs rhs
  let inlines ← inlinesUsedBy fn
  -- `isDefEq` on a large non-matching `do` block (inlined helper mid-body)
  -- burns the heartbeat budget; skip it when inlines are present.
  if inlines.isEmpty then
    if ← withNewMCtxDepth (withDefault (isDefEq lhs rhs)) then
      return (← mkEqRefl lhs)
  let mut ids : Array Ident := #[
    mkIdent ``Lsc.Tx.bind_assoc,
    mkIdent ``Lsc.Tx.pure_bind,
    mkIdent ``Lsc.Tx.bind_pure,
    mkIdent ``Lsc.Tx.map_eq_pure_bind,
    mkIdent fn]
  for n in inlines do
    ids := ids.push (mkIdent n)
  let tac ←
    if inlines.isEmpty then
      `(by first | rfl | (simp only [$[$ids:ident],*]; rfl))
    else
      `(by simp only [$[$ids:ident],*]; rfl)
  try
    withoutErrToSorry (elabTermAndSynthesize tac eq)
  catch _ =>
    let extra ← do
      if let some (l, r) ← firstDifferingBind lhs rhs then
        pure m!"\nFirst differing bind:{indentExpr l}\nversus:{indentExpr r}"
      else pure m!""
    throwError "reify: certificate failed — denotation of the reified term is not \
      equal to the original function (even after Tx monad laws).{indentExpr eq}{extra}\n\
      Reified Core:{indentExpr coreE}"

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
    let pf ← withDeclName (fn ++ `core_denote) <| certifyDenote fn lhs rhs core.toExpr
    let stmt ← mkForallFVars params eq
    let proof ← mkLambdaFVars params pf
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
  enableRealizationsForConst (ns ++ `contract)
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

/-! ## Generated transport codec (`C.fnDef` / `C.encode` / `C.decode` / …) -/

def retTyTerm : RetTy → MetaM Term
  | .unit => `(Lsc.RetTy.unit)
  | .word => `(Lsc.RetTy.word)
  | .addr => `(Lsc.RetTy.addr)
  | .flag => `(Lsc.RetTy.flag)
  | .pair a b => do
      let aT ← retTyTerm a
      let bT ← retTyTerm b
      `(Lsc.RetTy.pair $aT $bT)

def paramTerm (p : Param) : MetaM Term := do
  let nm := Syntax.mkStrLit p.name
  let ty ← match p.ty with
    | .uint256 => `(Lsc.AbiTy.uint256)
    | .address => `(Lsc.AbiTy.address)
    | .bool => `(Lsc.AbiTy.bool)
  `({ name := $nm, ty := $ty })

def isAddressTy (ty : Expr) : MetaM Bool := do
  let ty ← whnfR ty
  return ty.isConstOf ``Lsc.Address

def isFlagTy (ty : Expr) : MetaM Bool := do
  let ty ← whnfR ty
  return ty.isConstOf ``Lsc.Flag

def encodeWordTerm (ty : Expr) (x : Term) : MetaM Term := do
  if ← isAmountTy ty then `(Lsc.Amount.toNat $x)
  else if ← isAddressTy ty then `(Lsc.Address.toWord $x)
  else pure x

def decodeWordTerm (ty : Expr) (n : Term) : MetaM Term := do
  if ← isAmountTy ty then
    match ← whnfAmount? ty with
    | some (τ, s) =>
      let τT ← exprToTerm τ
      let sT ← exprToTerm s
      `(Lsc.Amount.ofNat (τ := $τT) (s := $sT) $n)
    | none => `(Lsc.Amount.ofNat $n)
  else pure n

def dummyTerm (ty : Expr) : MetaM Term := do
  decodeWordTerm ty (← `(0))

def mkFnDefAlt (fn : Name) : MetaM (TSyntax ``Lean.Parser.Term.matchAlt) := do
  let ctor := ctorIdent fn
  let (params, ret, kind) ← fnMeta fn
  let nameLit := Syntax.mkStrLit fn.getString!
  let kindT ← match kind with
    | .tx => `(Lsc.FnKind.tx)
    | .view => `(Lsc.FnKind.view)
    | .constructor => `(Lsc.FnKind.constructor)
  let retT ← retTyTerm ret
  let paramTs ← params.toArray.mapM paramTerm
  let paramsT ← `([$paramTs,*])
  let coreT : Term := ⟨mkIdent (fn ++ `core)⟩
  let declT := quote fn
  `(Lean.Parser.Term.matchAltExpr|
      | .$ctor:ident =>
        { name := $nameLit, decl := $declT, kind := $kindT,
          params := $paramsT, ret := $retT, core := $coreT })

def mkEncodeAlt (fn : Name) : MetaM (TSyntax ``Lean.Parser.Term.matchAlt) := do
  let ctor := ctorIdent fn
  let surf ← fnSurface fn
  let n := surf.params.size
  match n with
  | 0 => `(Lean.Parser.Term.matchAltExpr| | .$ctor:ident, _ => [])
  | 1 => do
      let x := mkIdent `x
      let enc ← encodeWordTerm surf.params[0]!.2 ⟨x⟩
      `(Lean.Parser.Term.matchAltExpr| | .$ctor:ident, $x:ident => [$enc])
  | 2 => do
      let x0 := mkIdent `x0; let x1 := mkIdent `x1
      let e0 ← encodeWordTerm surf.params[0]!.2 ⟨x0⟩
      let e1 ← encodeWordTerm surf.params[1]!.2 ⟨x1⟩
      `(Lean.Parser.Term.matchAltExpr| | .$ctor:ident, ($x0, $x1) => [$e0, $e1])
  | 3 => do
      let x0 := mkIdent `x0; let x1 := mkIdent `x1; let x2 := mkIdent `x2
      let e0 ← encodeWordTerm surf.params[0]!.2 ⟨x0⟩
      let e1 ← encodeWordTerm surf.params[1]!.2 ⟨x1⟩
      let e2 ← encodeWordTerm surf.params[2]!.2 ⟨x2⟩
      `(Lean.Parser.Term.matchAltExpr| | .$ctor:ident, ($x0, $x1, $x2) => [$e0, $e1, $e2])
  | _ => throwError "lsc_contract: encode supports at most 3 parameters"

def mkDecodeAlts (fn : Name) : MetaM (Array (TSyntax ``Lean.Parser.Term.matchAlt)) := do
  let ctor := ctorIdent fn
  let surf ← fnSurface fn
  let n := surf.params.size
  match n with
  | 0 =>
    let alt ← `(Lean.Parser.Term.matchAltExpr| | .$ctor:ident, _ => ())
    return #[alt]
  | 1 => do
      let nId := mkIdent `n
      let d ← decodeWordTerm surf.params[0]!.2 ⟨nId⟩
      let dum ← dummyTerm surf.params[0]!.2
      let a1 ← `(Lean.Parser.Term.matchAltExpr| | .$ctor:ident, $nId:ident :: _ => $d)
      let a2 ← `(Lean.Parser.Term.matchAltExpr| | .$ctor:ident, _ => $dum)
      return #[a1, a2]
  | 2 => do
      let x0 := mkIdent `x0; let x1 := mkIdent `x1
      let d0 ← decodeWordTerm surf.params[0]!.2 ⟨x0⟩
      let d1 ← decodeWordTerm surf.params[1]!.2 ⟨x1⟩
      let dum0 ← dummyTerm surf.params[0]!.2
      let dum1 ← dummyTerm surf.params[1]!.2
      let a1 ← `(Lean.Parser.Term.matchAltExpr| | .$ctor:ident, $x0:ident :: $x1:ident :: _ => ($d0, $d1))
      let a2 ← `(Lean.Parser.Term.matchAltExpr| | .$ctor:ident, _ => ($dum0, $dum1))
      return #[a1, a2]
  | 3 => do
      let x0 := mkIdent `x0; let x1 := mkIdent `x1; let x2 := mkIdent `x2
      let d0 ← decodeWordTerm surf.params[0]!.2 ⟨x0⟩
      let d1 ← decodeWordTerm surf.params[1]!.2 ⟨x1⟩
      let d2 ← decodeWordTerm surf.params[2]!.2 ⟨x2⟩
      let dum0 ← dummyTerm surf.params[0]!.2
      let dum1 ← dummyTerm surf.params[1]!.2
      let dum2 ← dummyTerm surf.params[2]!.2
      let a1 ← `(Lean.Parser.Term.matchAltExpr|
          | .$ctor:ident, $x0:ident :: $x1:ident :: $x2:ident :: _ => ($d0, $d1, $d2))
      let a2 ← `(Lean.Parser.Term.matchAltExpr| | .$ctor:ident, _ => ($dum0, $dum1, $dum2))
      return #[a1, a2]
  | _ => throwError "lsc_contract: decode supports at most 3 parameters"

def mkDecodeFnExpr (entries : Array Name) : MetaM Term := do
  let f := mkIdent `f
  let mut acc ← `(none)
  for fn in entries.reverse do
    let ctor := ctorIdent fn
    let nm := Syntax.mkStrLit fn.getString!
    acc ← `(if ($f).name = $nm then some (.$ctor:ident) else $acc)
  `(fun ($f : Lsc.FnDef) => $acc)

def mkCoreEqAlt (ns fn : Name) : MetaM (TSyntax ``Lean.Parser.Tactic.inductionAlt) := do
  let ctor := ctorIdent fn
  let surf ← fnSurface fn
  let n := surf.params.size
  let coreDenote := mkIdent (fn ++ `core_denote)
  let specExec := mkIdent (ns ++ Name.mkSimple s!"spec_exec_{fn.getString!}")
  let fnDefId := mkIdent (ns ++ `fnDef)
  let encodeId := mkIdent (ns ++ `encode)
  let schemaId := mkIdent (ns ++ `schema)
  let specId := mkIdent (ns ++ `spec)
  let coreId : Term := ⟨mkIdent (fn ++ `core)⟩
  let argsId := mkIdent `args
  let ctxId := mkIdent `ctx
  let wId := mkIdent `w
  let binders : Array Ident := surf.params.mapIdx fun i (nm, _) =>
    mkIdent (if nm.hasMacroScopes then Name.mkSimple s!"a{i}" else nm)
  let tac ←
    match n with
    | 0 =>
      `(Lean.Parser.Tactic.tacticSeq|
          cases $argsId:ident
          dsimp [$fnDefId:ident, $encodeId:ident]
          change Lsc.Lang.worldAfter (Lsc.Core.denote $schemaId $coreId []) $ctxId $wId =
            Lsc.Lang.worldAfter (Lsc.Spec.exec $specId .$ctor:ident ()) $ctxId $wId
          rw [$coreDenote:ident, $specExec:ident]
          rfl)
    | 1 => do
      let enc ← encodeWordTerm surf.params[0]!.2 ⟨argsId⟩
      `(Lean.Parser.Tactic.tacticSeq|
          dsimp [$fnDefId:ident, $encodeId:ident, Lsc.Address.toWord]
          change Lsc.Lang.worldAfter (Lsc.Core.denote $schemaId $coreId [$enc]) $ctxId $wId =
            Lsc.Lang.worldAfter (Lsc.Spec.exec $specId .$ctor:ident $argsId) $ctxId $wId
          rw [$coreDenote:ident, $specExec:ident]
          rfl)
    | 2 => do
      let b0 := binders[0]!; let b1 := binders[1]!
      let e0 ← encodeWordTerm surf.params[0]!.2 ⟨b0⟩
      let e1 ← encodeWordTerm surf.params[1]!.2 ⟨b1⟩
      `(Lean.Parser.Tactic.tacticSeq|
          rcases $argsId:ident with ⟨$b0, $b1⟩
          dsimp [$fnDefId:ident, $encodeId:ident, Lsc.Address.toWord]
          change Lsc.Lang.worldAfter (Lsc.Core.denote $schemaId $coreId [$e1, $e0]) $ctxId $wId =
            Lsc.Lang.worldAfter (Lsc.Spec.exec $specId .$ctor:ident ($b0, $b1)) $ctxId $wId
          rw [$coreDenote:ident, $specExec:ident]
          rfl)
    | 3 => do
      let b0 := binders[0]!; let b1 := binders[1]!; let b2 := binders[2]!
      let e0 ← encodeWordTerm surf.params[0]!.2 ⟨b0⟩
      let e1 ← encodeWordTerm surf.params[1]!.2 ⟨b1⟩
      let e2 ← encodeWordTerm surf.params[2]!.2 ⟨b2⟩
      `(Lean.Parser.Tactic.tacticSeq|
          rcases $argsId:ident with ⟨$b0, $b1, $b2⟩
          dsimp [$fnDefId:ident, $encodeId:ident, Lsc.Address.toWord]
          change Lsc.Lang.worldAfter (Lsc.Core.denote $schemaId $coreId [$e2, $e1, $e0]) $ctxId $wId =
            Lsc.Lang.worldAfter (Lsc.Spec.exec $specId .$ctor:ident ($b0, $b1, $b2)) $ctxId $wId
          rw [$coreDenote:ident, $specExec:ident]
          rfl)
    | _ => throwError "lsc_contract: worldAfter_core_eq supports at most 3 parameters"
  `(Lean.Parser.Tactic.inductionAlt| | $ctor:ident => $tac)

def mkEncodeDecodeAlt (ns fn : Name) : MetaM (TSyntax ``Lean.Parser.Tactic.inductionAlt) := do
  let ctor := ctorIdent fn
  let surf ← fnSurface fn
  let n := surf.params.size
  let fnDefId := mkIdent (ns ++ `fnDef)
  let encodeId := mkIdent (ns ++ `encode)
  let decodeId := mkIdent (ns ++ `decode)
  let hId := mkIdent `h
  let aId := mkIdent `a
  let bId := mkIdent `b
  let cId := mkIdent `c
  let eqId := mkIdent `hns
  let tac ←
    match n with
    | 0 =>
      `(Lean.Parser.Tactic.tacticSeq|
          simp [$fnDefId:ident] at $hId:ident
          subst $hId:ident
          rfl)
    | 1 =>
      `(Lean.Parser.Tactic.tacticSeq|
          simp [$fnDefId:ident] at $hId:ident
          obtain ⟨$aId, $eqId⟩ := Lsc.length_eq_one.mp $hId
          subst $eqId:ident
          simp [$encodeId:ident, $decodeId:ident, Lsc.Address.toWord])
    | 2 =>
      `(Lean.Parser.Tactic.tacticSeq|
          simp [$fnDefId:ident] at $hId:ident
          obtain ⟨$aId, $bId, $eqId⟩ := Lsc.length_eq_two.mp $hId
          subst $eqId:ident
          simp [$encodeId:ident, $decodeId:ident, Lsc.Address.toWord])
    | 3 =>
      `(Lean.Parser.Tactic.tacticSeq|
          simp [$fnDefId:ident] at $hId:ident
          obtain ⟨$aId, $bId, $cId, $eqId⟩ := Lsc.length_eq_three.mp $hId
          subst $eqId:ident
          simp [$encodeId:ident, $decodeId:ident, Lsc.Address.toWord])
    | _ => throwError "lsc_contract: encode supports at most 3 parameters"
  `(Lean.Parser.Tactic.inductionAlt| | $ctor:ident => $tac)

partial def mkDecodeOfMemTac (ns : Name) (entries : Array Name) (i : Nat) :
    MetaM (TSyntax ``Lean.Parser.Tactic.tacticSeq) := do
  let ctor := ctorIdent entries[i]!
  if i + 1 = entries.size then
    `(Lean.Parser.Tactic.tacticSeq|
        subst hf
        exact ⟨.$ctor:ident, rfl, rfl⟩)
  else
    let rest ← mkDecodeOfMemTac ns entries (i + 1)
    `(Lean.Parser.Tactic.tacticSeq|
        rcases hf with h | hf
        · subst h; exact ⟨.$ctor:ident, rfl, rfl⟩
        · ($rest))

/-- `C.fnDef`, `C.encode`, `C.decodeFn`, `C.decode`, inverse lemmas, and
`C.worldAfter_core_eq` (Core vs Spec post-worlds). -/
def mkCodecCommands (ns : Name) (fns : Array Name) : MetaM (Array (TSyntax `command)) := do
  let entries ← entrypointFns fns
  if entries.isEmpty then return #[]
  let surf0 ← fnSurface entries[0]!
  let S ← exprToTerm surf0.S
  let X ← exprToTerm surf0.X
  let E ← exprToTerm surf0.E
  let fnName : Term := ⟨mkIdent (ns ++ `Fn)⟩
  let specId : Term := ⟨mkIdent (ns ++ `spec)⟩
  let contractId := mkIdent (ns ++ `contract)
  let schemaId : Term := ⟨mkIdent (ns ++ `schema)⟩
  let fnDefId := mkIdent (ns ++ `fnDef)
  let encodeId := mkIdent (ns ++ `encode)
  let decodeFnId := mkIdent (ns ++ `decodeFn)
  let decodeId := mkIdent (ns ++ `decode)
  let fnDefAlts ← entries.mapM mkFnDefAlt
  let encodeAlts ← entries.mapM mkEncodeAlt
  let mut decodeAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  for fn in entries do
    decodeAlts := decodeAlts ++ (← mkDecodeAlts fn)
  let decodeFnVal ← mkDecodeFnExpr entries
  let fnDefCmd ←
    `(command| def $fnDefId : $fnName → Lsc.FnDef
        $fnDefAlts:matchAlt*)
  let encodeCmd ←
    `(command| def $encodeId : (fn : $fnName) → Lsc.Spec.Args $specId fn → List Nat
        $encodeAlts:matchAlt*)
  let decodeFnCmd ←
    `(command| def $decodeFnId : Lsc.FnDef → Option $fnName := $decodeFnVal)
  let decodeCmd ←
    `(command| def $decodeId : (fn : $fnName) → List Nat → Lsc.Spec.Args $specId fn
        $decodeAlts:matchAlt*)
  let memThm := mkIdent (ns ++ `fnDef_mem)
  let memCmd ←
    `(command| theorem $memThm (fn : $fnName) : $fnDefId fn ∈ ($contractId).functions := by
        cases fn <;> simp [$fnDefId:ident, $contractId:ident])
  let lenThm := mkIdent (ns ++ `encode_length)
  let lenCmd ←
    `(command| theorem $lenThm (fn : $fnName) (args : Lsc.Spec.Args $specId fn) :
        ($encodeId fn args).length = ($fnDefId fn).params.length := by
        cases fn <;> simp [$encodeId:ident, $fnDefId:ident])
  let decFnThm := mkIdent (ns ++ `decodeFn_fnDef)
  let decFnCmd ←
    `(command| theorem $decFnThm (fn : $fnName) : $decodeFnId ($fnDefId fn) = some fn := by
        cases fn <;> simp [$decodeFnId:ident, $fnDefId:ident])
  let ofMemThm := mkIdent (ns ++ `decodeFn_of_mem)
  let ofMemTac ← mkDecodeOfMemTac ns entries 0
  let ofMemCmd ←
    `(command| theorem $ofMemThm (f : Lsc.FnDef) (hf : f ∈ ($contractId).functions) :
        ∃ fn, $decodeFnId f = some fn ∧ f = $fnDefId fn := by
        simp [$contractId:ident] at hf
        ($ofMemTac))
  let fnB := mkIdent `fn
  let argsB := mkIdent `args
  let nsB := mkIdent `ns
  let hB := mkIdent `h
  let ctxB := mkIdent `ctx
  let wB := mkIdent `w
  let encDecAlts ← entries.mapM (mkEncodeDecodeAlt ns)
  let encDecThm := mkIdent (ns ++ `encode_decode)
  let encDecCmd ←
    `(command| theorem $encDecThm : ∀ ($fnB : $fnName) ($nsB : List Nat)
        ($hB : List.length $nsB = List.length ($fnDefId $fnB).params),
        $encodeId $fnB ($decodeId $fnB $nsB) = $nsB := by
        intros $fnB $nsB $hB
        cases $fnB:ident with
        $encDecAlts:inductionAlt*)
  let decEncThm := mkIdent (ns ++ `decode_encode)
  let decEncCmd ←
    `(command| theorem $decEncThm : ∀ ($fnB : $fnName) ($argsB : Lsc.Spec.Args $specId $fnB),
        $decodeId $fnB ($encodeId $fnB $argsB) = $argsB := by
        intros $fnB $argsB
        cases $fnB:ident <;> simp [$decodeId:ident, $encodeId:ident, Lsc.Address.toWord])
  let coreAlts ← entries.mapM (mkCoreEqAlt ns)
  let coreThm := mkIdent (ns ++ `worldAfter_core_eq)
  let coreCmd ←
    `(command| theorem $coreThm : ∀ ($fnB : $fnName) ($argsB : Lsc.Spec.Args $specId $fnB)
        ($ctxB : Lsc.Ctx) ($wB : Lsc.World $S $X $E),
        Lsc.Lang.worldAfter (Lsc.Core.denote $schemaId ($fnDefId $fnB).core
          (List.reverse ($encodeId $fnB $argsB))) $ctxB $wB =
        Lsc.Lang.worldAfter (Lsc.Spec.exec $specId $fnB $argsB) $ctxB $wB := by
        intros $fnB $argsB $ctxB $wB
        cases $fnB:ident with
        $coreAlts:inductionAlt*)
  return #[fnDefCmd, encodeCmd, decodeFnCmd, decodeCmd, memCmd, lenCmd, decFnCmd,
    ofMemCmd, encDecCmd, decEncCmd, coreCmd]

def mkSchemaFieldsTerm (ci : ContractInfo) : MetaM Term := do
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
  `([$fieldTerms,*])

def mkTgtIdent (id : Ident) : TSyntax ``Lean.Parser.Tactic.elimTarget :=
  ⟨mkNode ``Lean.Parser.Tactic.elimTarget #[mkNullNode, id]⟩

def nestedCasesNat (n : Nat) (var : Ident)
    (close : TSyntax ``Lean.Parser.Tactic.tacticSeq) :
    MetaM (TSyntax ``Lean.Parser.Tactic.tacticSeq) := do
  let tgt := mkTgtIdent var
  let mut rest := close
  for _ in [:n] do
    rest ← `(Lean.Parser.Tactic.tacticSeq|
      cases $tgt with
      | zero => $close
      | succ $var => $rest)
  return rest

/-- Identity of `scalarUpd` / `map1Upd` / `map2Upd` on the wrong field kind. -/
def mkSchemaIdCommands (ci : ContractInfo) : MetaM (Array (TSyntax `command)) := do
  let schema := mkIdent (`_root_ ++ ci.schema)
  let S := mkIdent ci.storage
  let fieldsTerm ← mkSchemaFieldsTerm ci
  let n := ci.fields.size
  let iId := mkIdent `i
  let close ← `(Lean.Parser.Tactic.tacticSeq|
      simp [$schema:ident] at h ⊢
      first | contradiction | rfl)
  let casesI ← nestedCasesNat n iId close
  let scalarId := mkIdent (ci.schema.getPrefix ++ `schema_scalarUpd_id)
  let map1Id := mkIdent (ci.schema.getPrefix ++ `schema_map1Upd_id)
  let map2Id := mkIdent (ci.schema.getPrefix ++ `schema_map2Upd_id)
  let c1 ←
    `(command| theorem $scalarId (i : Nat) (σ : $S) (v : Nat)
        (h : ($fieldsTerm)[i]?.map (·.kind) ≠ some Lsc.FieldKind.scalar) :
        ($schema).st.scalarUpd i σ v = σ := by ($casesI))
  let c2 ←
    `(command| theorem $map1Id (i : Nat) (σ : $S) (m : Nat → Nat)
        (h : ($fieldsTerm)[i]?.map (·.kind) ≠ some Lsc.FieldKind.map1) :
        ($schema).st.map1Upd i σ m = σ := by ($casesI))
  let c3 ←
    `(command| theorem $map2Id (i : Nat) (σ : $S) (m : Nat → Nat → Nat)
        (h : ($fieldsTerm)[i]?.map (·.kind) ≠ some Lsc.FieldKind.map2) :
        ($schema).st.map2Upd i σ m = σ := by ($casesI))
  return #[c1, c2, c3]

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
    "    (tr : List (Lsc.Security.Step " ++ C ++ ".spec))\n" ++
    "    (w : " ++ world ++ ") (a : Lsc.Address)\n" ++
    "    (hw : " ++ C ++ ".Inv w)\n" ++
    "    (hR : Lsc.Security.RelyAlong (" ++ rely ++ ") tr w)\n" ++
    "    (hA : Lsc.Security.NoAuthAlong " ++ C ++ ".Auth a tr w) :\n" ++
    "    " ++ C ++ ".claim a w.self ≤ " ++ C ++
    ".claim a (Lsc.Security.run tr w).self :=\n" ++
    "  Lsc.Security.no_unauthorized_extraction " ++ C ++ ".no_unauth " ++
    C ++ ".preserves_inv " ++ C ++ ".inv_rely tr w a hw hR hA"
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
`C.Fn` / `C.entry` / `C.spec` with `@[simp] C.spec_exec_*` lemmas, plus the
transport codec `C.fnDef` / `C.encode` / `C.decodeFn` / `C.decode` and
`C.worldAfter_core_eq`. Unit-returning functions are `tx`; a function named
`constructor` is the constructor; the rest are `view`. -/
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
    let codecCmds ← liftTermElabM do mkCodecCommands nsName resolved
    for cmd in codecCmds do
      elabCommand cmd
  | _ => throwUnsupportedSyntax

/-- `lsc_codec C` packages generated `C.fnDef` / `C.encode` / … into
`C.codec : TransportCodec`. Requires `import Lsc.Compiler.Transport.Defs`. -/
syntax (name := lscCodec) "lsc_codec " ident : command

@[command_elab lscCodec] def elabLscCodec : CommandElab
  | `(lsc_codec $ns:ident) => do
    let nsName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo (mkIdent (ns.getId ++ `Storage))
    let nsName := nsName.getPrefix
    unless (← getEnv).contains (`Lsc.Compiler.TransportCodec : Name) do
      throwError "lsc_codec: import Lsc.Compiler.Transport.Defs first"
    unless (← getEnv).contains (nsName ++ `fnDef) do
      throwError "lsc_codec: {nsName}.fnDef not found; run `lsc_contract` first"
    unless (← getEnv).contains (nsName ++ `worldAfter_core_eq) do
      throwError "lsc_codec: {nsName}.worldAfter_core_eq not found; run `lsc_contract` first"
    let codecId := mkIdent (nsName ++ `codec)
    let tc : Term := ⟨mkIdent (`Lsc.Compiler.TransportCodec : Name)⟩
    let contractId : Term := ⟨mkIdent (nsName ++ `contract)⟩
    let schemaId : Term := ⟨mkIdent (nsName ++ `schema)⟩
    let specId : Term := ⟨mkIdent (nsName ++ `spec)⟩
    let fnDefId : Term := ⟨mkIdent (nsName ++ `fnDef)⟩
    let encodeId : Term := ⟨mkIdent (nsName ++ `encode)⟩
    let coreEq : Term := ⟨mkIdent (nsName ++ `worldAfter_core_eq)⟩
    let waL : Term := ⟨mkIdent (`Lsc.Lang.worldAfter : Name)⟩
    let denoteId : Term := ⟨mkIdent (`Lsc.Core.denote : Name)⟩
    let execId : Term := ⟨mkIdent (`Lsc.Spec.exec : Name)⟩
    let cmd ← `(command|
      def $codecId : $tc $contractId $schemaId $specId where
        fnDef := $(mkIdent (nsName ++ `fnDef))
        encode := $(mkIdent (nsName ++ `encode))
        decodeFn := $(mkIdent (nsName ++ `decodeFn))
        decode := $(mkIdent (nsName ++ `decode))
        mem := $(mkIdent (nsName ++ `fnDef_mem))
        encode_length := $(mkIdent (nsName ++ `encode_length))
        decodeFn_fnDef := $(mkIdent (nsName ++ `decodeFn_fnDef))
        decodeFn_of_mem := $(mkIdent (nsName ++ `decodeFn_of_mem))
        encode_decode := $(mkIdent (nsName ++ `encode_decode))
        decode_encode := $(mkIdent (nsName ++ `decode_encode))
        core_exec := fun fn args ctx w => by
          change $waL ($denoteId $schemaId ($fnDefId fn).core ($encodeId fn args).reverse) ctx w =
            $waL ($execId $specId fn args) ctx w
          exact $coreEq fn args ctx w)
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

