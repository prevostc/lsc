import Lsc.Lang.Core
import Lsc.Lang.Contract
import Lsc.Lang.ExtState
import Lsc.Lang.Inline
import Lsc.Lang.Spec
import Lsc.Lang.TxTheorems

/-!
# reification

`lsc_schema C` derives `C.schema : ContractSchema C.Storage Lsc.ExtState C.Event C.Error`
from the user's Lean types, plus `C.schema_lawful : C.schema.st.Lawful …`,
per-field `@[simp]` reductions `C.schema_read_<field>` / `C.schema_write_<field>`
(and `C.schema_ev_*` / `C.schema_err_*`), and
`lsc_reify C.f` turns the elaborated term of a contract function
`C.f : … → Tx C.Storage Lsc.ExtState C.Event C.Error ρ` into

* `C.f.core : Core t` — the Core AST, and
* `C.f.core_denote` — `Core.denote C.schema C.f.core [args] = C.f args`
  for word/address/flag/unit programs. Amount-returning functions certify
  `Amount.ofWord <$> Core.denote = f`; Bool-returning functions certify
  `Tx.natToBool <$> Core.denote = f` (`natToBool n` is `n != 0`).
  Intermediate `Amount` / `Ref` loads are peeled with `load_bind_ofWord` /
  `bind_map` and the generated schema-read lemmas. Proved by `rfl`
  when the sides are definitionally equal;
  otherwise by the `Tx` monad laws (`bind` is not definitionally associative,
  so an `@[lsc_inline]` helper mid-`do` needs them). A propositional
  certificate is not a trust extension: the kernel still checks
  `denote (reify f) = f`.

`lsc_contract C f₁ … fₙ implements I args, …` additionally defines `C.contract`, a
language-level `C.spec` (`C.Fn` / `C.entry` / `C.spec_exec_*`), and `C.impl_<I>`
(`C.impl` when there is exactly one `implements` clause). Function kind
(`view` / `tx`) is decided by effects (`Core.isPureRead`: no writes, emits,
or CALLs ⇒ `view`), never by return type. `#lsc_obligations C`
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

/-- Arity of a field type after unfolding abbreviations such as `Mapping`, plus the value type. -/
def fieldKindAndVal (ty : Expr) : MetaM (FieldKind × Expr) :=
  forallTelescopeReducing ty fun xs val => do
    match xs.size with
    | 0 => pure (.scalar, val)
    | 1 => pure (.map1, val)
    | 2 => pure (.map2, val)
    | n => throwError "storage field with {n} keys is not supported (max 2)"

/-- Unfold abbrevs such as `Fixed d`. `Amount a` is a one-field structure. -/
def isAmountTy (ty : Expr) : MetaM Bool := do
  let ty ← whnfD ty
  return ty.isAppOf ``Lsc.Amount

/-- Unfold abbrevs such as `IERC20.Ref a`. Per-interface `I.Ref` is a one-field
address structure (the `Ref (I args)` macro expands to this). -/
def isRefTy (ty : Expr) : MetaM Bool := do
  let ty ← whnfD ty
  match ty.getAppFn.constName? with
  | some n => return n.getString! == "Ref"
  | none => return false

def isProdTy (ty : Expr) : MetaM Bool := do
  let ty ← whnfD ty
  return ty.isAppOfArity ``Prod 2

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
  pure {
    storage, event, error, schema := ns ++ `schema, fields
    evCtors := evInfo.ctors.toArray, errCtors := errInfo.ctors.toArray }

/-! ## Schema generation -/

/-- `fun (args : List Nat) => C (ofWord (args.getD 0 0)) …` for constructor `C`.
Amount fields are rebuilt with `ofWord`; `Ref` fields with `{ addr := … }`. -/
def ctorBuilder (ctor : Name) : MetaM Term := do
  let info ← getConstInfoCtor ctor
  let argsId := mkIdent `args
  forallTelescope info.type fun xs _ => do
    let xs := xs.extract info.numParams xs.size
    let mut app : Term := mkIdent ctor
    for i in [:xs.size] do
      let ty ← inferType xs[i]!
      let get ← `(List.getD $argsId $(quote i) 0)
      let arg ←
        if ← isAmountTy ty then `(Lsc.Amount.ofWord $get)
        else if ← isRefTy ty then `({ addr := $get })
        else pure get
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
    let ref? ← isRefTy f.valTy
    let k := mkIdent `k
    let v := mkIdent `v
    match f.kind with
    | .scalar =>
      if amt? then
        scalar := scalar.push (← `(fun $σ => Lsc.Amount.raw $proj))
        scalarUpd := scalarUpd.push
          (← `(fun $σ $m => { $σ with $fld:ident := Lsc.Amount.ofWord $m }))
      else if ref? then
        scalar := scalar.push (← `(fun $σ => Lsc.Address.toWord ($proj).addr))
        scalarUpd := scalarUpd.push
          (← `(fun $σ $m => { $σ with $fld:ident := { addr := $m } }))
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
        map1 := map1.push (← `(fun $σ $k => Lsc.Amount.raw ($proj $k)))
        map1Upd := map1Upd.push
          (← `(fun $σ $m => { $σ with $fld:ident := fun $k => Lsc.Amount.ofWord ($m $k) }))
        map1Set := map1Set.push
          (← `(fun $σ $k $v =>
            { $σ with $fld:ident := Function.update $proj $k (Lsc.Amount.ofWord $v) }))
      else if ref? then
        map1 := map1.push (← `(fun $σ $k => Lsc.Address.toWord ($proj $k).addr))
        map1Upd := map1Upd.push
          (← `(fun $σ $m => { $σ with $fld:ident := fun $k => { addr := $m $k } }))
        map1Set := map1Set.push
          (← `(fun $σ $k $v =>
            { $σ with $fld:ident := Function.update $proj $k { addr := $v } }))
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
        map2 := map2.push (← `(fun $σ $k₁ $k₂ => Lsc.Amount.raw ($proj $k₁ $k₂)))
        map2Upd := map2Upd.push
          (← `(fun $σ $m => { $σ with $fld:ident := fun $k₁ $k₂ => Lsc.Amount.ofWord ($m $k₁ $k₂) }))
        map2Set := map2Set.push
          (← `(fun $σ $k₁ $k₂ $v =>
            let m := $proj
            { $σ with $fld:ident :=
              Function.update m $k₁ (Function.update (m $k₁) $k₂ (Lsc.Amount.ofWord $v)) }))
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
  let name := mkIdent (`_root_ ++ ci.schema)
  `(def $name : Lsc.ContractSchema $S Lsc.ExtState $E $Er where
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
      err := ⟨fun $i $args => List.getD [$errBuilders,*] $i $errDefault $args⟩)

/-- `@[simp]` reductions for each storage field and event/error constructor.
`lsc_reify` includes them in the certificate `simp only` set. -/
def mkSchemaFieldCommands (ci : ContractInfo) : MetaM (Array (TSyntax `command)) := do
  let schema := mkIdent (`_root_ ++ ci.schema)
  let ns := ci.schema.getPrefix
  let σ := mkIdent `σ
  let m := mkIdent `m
  let k := mkIdent `k
  let tac ← `(Lean.Parser.Tactic.tacticSeq|
      simp [$schema:ident, Lsc.list_getD_cons_zero, Lsc.list_getD_cons_one,
        Lsc.list_getD_cons_two, Lsc.list_getD_cons_three, Lsc.list_getD_cons_four,
        Lsc.list_getD_cons_five, Lsc.list_getD_cons_six, Lsc.list_getD_cons_seven,
        Lsc.list_getD_cons_zero_app, Lsc.list_getD_pair_zero,
        Lsc.list_getElem?_cons_one, Lsc.list_getElem?_cons_two,
        Lsc.list_getElem?_cons_three, Lsc.list_getElem?_cons_four,
        Lsc.list_getElem?_cons_five, List.getElem?_cons_zero, Option.getD_some]
      <;> first | rfl | (funext; simp [$schema:ident,
        Lsc.list_getD_cons_zero, Lsc.list_getD_cons_one, Lsc.list_getD_cons_two,
        Lsc.list_getElem?_cons_one, Lsc.list_getElem?_cons_two,
        List.getElem?_cons_zero, Option.getD_some]))
  let mut cmds : Array (TSyntax `command) := #[]
  for f in ci.fields do
    let proj := mkIdent (`σ ++ f.name)
    let fld := mkIdent f.name
    let amt? ← isAmountTy f.valTy
    let ref? ← isRefTy f.valTy
    let readN := mkIdent (ns ++ Name.mkSimple s!"schema_read_{f.name.getString!}")
    let writeN := mkIdent (ns ++ Name.mkSimple s!"schema_write_{f.name.getString!}")
    let idx : Term := quote f.idx
    match f.kind with
    | .scalar =>
      let (readRhs, writeRhs) ←
        if amt? then
          pure (← `(fun $σ => Lsc.Amount.raw $proj),
            ← `(fun $σ $m => { $σ with $fld:ident := Lsc.Amount.ofWord $m }))
        else if ref? then
          pure (← `(fun $σ => Lsc.Address.toWord ($proj).addr),
            ← `(fun $σ $m => { $σ with $fld:ident := { addr := $m } }))
        else
          pure (← `(fun $σ => $proj),
            ← `(fun $σ $m => { $σ with $fld:ident := $m }))
      cmds := cmds.push (← `(command|
        @[simp] theorem $readN : ($schema).st.scalar $idx = $readRhs := by ($tac)))
      cmds := cmds.push (← `(command|
        @[simp] theorem $writeN : ($schema).st.scalarUpd $idx = $writeRhs := by ($tac)))
    | .map1 =>
      let (readRhs, writeRhs) ←
        if amt? then
          pure (← `(fun $σ $k => Lsc.Amount.raw ($proj $k)),
            ← `(fun $σ $m => { $σ with $fld:ident := fun $k => Lsc.Amount.ofWord ($m $k) }))
        else if ref? then
          pure (← `(fun $σ $k => Lsc.Address.toWord ($proj $k).addr),
            ← `(fun $σ $m => { $σ with $fld:ident := fun $k => { addr := $m $k } }))
        else
          pure (← `(fun $σ => $proj),
            ← `(fun $σ $m => { $σ with $fld:ident := $m }))
      cmds := cmds.push (← `(command|
        @[simp] theorem $readN : ($schema).st.map1 $idx = $readRhs := by ($tac)))
      cmds := cmds.push (← `(command|
        @[simp] theorem $writeN : ($schema).st.map1Upd $idx = $writeRhs := by ($tac)))
    | .map2 =>
      let k₁ := mkIdent `k₁; let k₂ := mkIdent `k₂
      let (readRhs, writeRhs) ←
        if amt? then
          pure (← `(fun $σ $k₁ $k₂ => Lsc.Amount.raw ($proj $k₁ $k₂)),
            ← `(fun $σ $m => { $σ with $fld:ident :=
              fun $k₁ $k₂ => Lsc.Amount.ofWord ($m $k₁ $k₂) }))
        else
          pure (← `(fun $σ => $proj),
            ← `(fun $σ $m => { $σ with $fld:ident := $m }))
      cmds := cmds.push (← `(command|
        @[simp] theorem $readN : ($schema).st.map2 $idx = $readRhs := by ($tac)))
      cmds := cmds.push (← `(command|
        @[simp] theorem $writeN : ($schema).st.map2Upd $idx = $writeRhs := by ($tac)))
  for i in [:ci.evCtors.size] do
    let ctor := ci.evCtors[i]!
    let builder ← ctorBuilder ctor
    let n := mkIdent (ns ++ Name.mkSimple s!"schema_ev_{ctor.getString!}")
    let idx : Term := quote i
    cmds := cmds.push (← `(command|
      @[simp] theorem $n : ($schema).ev.build $idx = $builder := by ($tac)))
  for i in [:ci.errCtors.size] do
    let ctor := ci.errCtors[i]!
    let builder ← ctorBuilder ctor
    let n := mkIdent (ns ++ Name.mkSimple s!"schema_err_{ctor.getString!}")
    let idx : Term := quote i
    cmds := cmds.push (← `(command|
      @[simp] theorem $n : ($schema).err.build $idx = $builder := by ($tac)))
  return cmds

def schemaLemmaNames (ci : ContractInfo) : Array Name := Id.run do
  let ns := ci.schema.getPrefix
  let mut acc : Array Name := #[]
  for f in ci.fields do
    let s := f.name.getString!
    acc := acc.push (ns ++ Name.mkSimple s!"schema_read_{s}")
    acc := acc.push (ns ++ Name.mkSimple s!"schema_write_{s}")
  for ctor in ci.evCtors do
    acc := acc.push (ns ++ Name.mkSimple s!"schema_ev_{ctor.getString!}")
  for ctor in ci.errCtors do
    acc := acc.push (ns ++ Name.mkSimple s!"schema_err_{ctor.getString!}")
  return acc

def existingIdents (names : Array Name) : MetaM (Array Ident) := do
  let env ← getEnv
  return names.filterMap fun n =>
    if env.contains n then some (mkIdent n) else none

def abiTyOf (ty : Expr) : MetaM AbiTy := do
  let ty ← whnfR ty
  if ← isRefTy ty then return .address
  match ty.getAppFn.constName? with
  | some ``Nat => pure .uint256
  | some ``Lsc.Address => pure .address
  | some ``Lsc.Flag => pure .bool
  | some ``Bool => pure .bool
  | some ``Lsc.Word | some ``Lsc.Amount | some ``Lsc.Fixed => pure .uint256
  | some n =>
    if n.getString! == "Ref" then pure .address
    else throwError "lsc_contract: unsupported ABI type `{ty}` (Nat, Address, Flag, Word, Amount, Fixed, Ref)"
  | _ => throwError "lsc_contract: unsupported ABI type `{ty}` (Nat, Address, Flag, Word, Amount, Fixed, Ref)"

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
  -- Amount / Ref / ABI boundary: Core stores the underlying word.
  if e.isAppOf ``Lsc.Amount.raw || e.isAppOf ``Lsc.Amount.ofWord
      || e.isAppOf ``Lsc.Amount.mk
      || e.isAppOf ``Lsc.Address.toWord
      || e.isAppOf ``Lsc.AbiType.encode then
    return (← atomOf env e.appArg!)
  if e.isConstOf ``Bool.true then return .lit 1
  if e.isConstOf ``Bool.false then return .lit 0
  if let some n := e.getAppFn.constName? then
    if n.getString! == "addr" && e.getAppNumArgs ≥ 1 then
      let recv := e.getArg! (e.getAppNumArgs - 1)
      if ← isRefTy (← inferType recv) then
        return (← atomOf env recv)
    if n.getString! == "mk" && e.getAppNumArgs ≥ 1 then
      let last := e.getArg! (e.getAppNumArgs - 1)
      -- `I.Ref.mk addr` / `{ addr := n }`
      if ← isRefTy (← inferType e) then
        return (← atomOf env last)
  if let .proj _ 0 s := e then
    let ty ← whnfD (← inferType s)
    if ty.isAppOf ``Lsc.Amount || (← isRefTy ty) then
      return (← atomOf env s)
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
      if body.isAppOf ``Lsc.Amount.raw then
        body.appArg!
      else
        let body :=
          if body.isAppOf ``Lsc.Address.toWord then body.appArg! else body
        if let some n := body.getAppFn.constName? then
          if n.getString! == "addr" && body.getAppNumArgs ≥ 1 then
            body.getArg! (body.getAppNumArgs - 1)
          else body
        else body
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
    let some mid := m.fvarId? |
      throwError "reify: `{upd}` is not a storage update"
    let idxs := (List.range ci.fields.size).filter fun i =>
      (args[ctor.numParams + i]!).containsFVar mid
    match idxs with
    | [i] => pure ci.fields[i]!
    | _ => throwError "reify: `{upd}` does not update exactly one field"

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

/-- Word-like types that may be compared: `Nat`, `Address`, `Word`, `Amount`, `Fixed`, `Flag`. -/
def isWordLike (ty : Expr) : Bool :=
  let n := ty.getAppFn.constName?
  n == some ``Nat || n == some ``Lsc.Address || n == some ``Lsc.Word
    || n == some ``Lsc.Amount
    || n == some ``Lsc.Flag || n == some ``Lsc.Fixed

partial def condOf (env : Env t) (e : Expr) : MetaM Cond := do
  let e := e.consumeMData
  let f := e.getAppFn
  let args := e.getAppArgs
  let atom := atomOf env
  let checkWord (ty : Expr) : MetaM Unit := do
    let ty ← whnfR ty
    unless isWordLike ty || ty.isConstOf ``Nat || ty.isConstOf ``Bool do
      throwError "reify: comparison on `{ty}` is not supported (use Nat, Address, Word, Amount, Flag, Bool)"
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

/-- `Amount a` / `Fixed d` / `Word` map to `Nat`. `Address`/`Flag` stay named. -/
partial def retTyOf (ρ : Expr) : MetaM RetTy := do
  let ρ ← whnfR ρ
  match ρ.getAppFn.constName?, ρ.getAppNumArgs with
  | some ``Unit, 0 | some ``PUnit, 0 => pure .unit
  | some ``Nat, 0 => pure .word
  | some ``Lsc.Address, 0 => pure .addr
  | some ``Lsc.Flag, 0 => pure .flag
  | some ``Bool, 0 => pure .flag
  | some ``Lsc.Word, 0 => pure .word
  | some ``Lsc.Amount, _ => pure .word
  | some ``Lsc.Fixed, 1 => pure .word
  | some ``Prod, 2 => return .pair (← retTyOf (ρ.getArg! 0)) (← retTyOf (ρ.getArg! 1))
  | _, _ =>
    match ← unfoldDefinition? ρ with
    | some ρ' => retTyOf ρ'
    | none => throwError "reify: unsupported return type `{ρ}` \
        (Unit, Nat, Address, Flag, Bool, Word, Amount, Fixed, or pairs)"

/-- Head constants that unfold to a `Tx` primitive (`Amount.add` → `addChecked`,
`IERC20.Ref.transfer` → `Tx.call`, …). Compared as names so Reify need not import
`Stdlib.ERC20`. -/
def isRefMethod : Name → Bool
  | .str (.str _ "Ref") s =>
      s != "addr" && s != "try" && s != "impl" && s != "mk" && s != "rec"
  | _ => false

/-- `I.Try.f` / `Tx.tryCall` / `Tx.tryView` — not yet in the compilable fragment. -/
def isTryHead : Name → Bool
  | ``Lsc.Tx.tryCall | ``Lsc.Tx.tryView => true
  | .str (.str _ "Try") _ => true
  | .str (.str _ "Ref") "try" => true
  | _ => false

/-- Head constants that unfold to a `Tx` primitive (`Amount.add` → `addChecked`,
`I.Ref.transfer` → `Tx.call`, …). Compared as names so Reify need not import
`Stdlib.ERC20`. -/
def isSurfaceOp : Name → Bool
  | ``Lsc.Tx.HAddChecked.hAdd | ``Lsc.Tx.HSubChecked.hSub
  | ``Lsc.Tx.HMulChecked.hMul | ``Lsc.Tx.HDivChecked.hDiv
  | ``Lsc.Tx.HMulDivDown.hMulDivDown | ``Lsc.Tx.HMulDivUp.hMulDivUp => true
  | .str (.str `Lsc "Amount") s =>
      s == "add" || s == "sub" || s == "mulScalar" || s == "divScalar"
        || s == "mulDivDown" || s == "mulDivUp" || s == "rescale"
  | .str (.str `Lsc "Fixed") s =>
      s == "mulDown" || s == "mulUp" || s == "divDown" || s == "divUp"
  | n =>
      isRefMethod n ||
        match n with
        | .str p "1" =>
            let s := p.getString!
            s.startsWith "instHAdd" || s.startsWith "instHSub"
              || s.startsWith "instHMul" || s.startsWith "instHDiv"
              || s.startsWith "instHMulDiv"
        | _ => false

/-- `Rounding` must be a literal constructor so the reifier can pick `mulDivDown` vs `mulDivUp`. -/
def roundingOf (e : Expr) : MetaM Rounding := do
  let e := e.consumeMData
  match e.getAppFn.constName? with
  | some ``Lsc.Rounding.down => return .down
  | some ``Lsc.Rounding.up => return .up
  | _ => throwError "reify: rounding `{e}` must be a literal `.down` or `.up`"

/-- Heads that `deltaUnfold` must not unfold past (primitives and `do` combinators). -/
def isDeltaStop : Name → Bool
  | ``Lsc.Tx.addChecked | ``Lsc.Tx.subChecked | ``Lsc.Tx.mulChecked | ``Lsc.Tx.divChecked
  | ``Lsc.Tx.mulDivDown | ``Lsc.Tx.mulDivUp | ``Lsc.Tx.pow10
  | ``Lsc.Tx.HMulDivDown.hMulDivDown | ``Lsc.Tx.HMulDivUp.hMulDivUp
  | ``Lsc.Tx.call | ``Lsc.Tx.view | ``Lsc.Tx.callAsNat | ``Lsc.Tx.viewAsNat
  | ``Lsc.Tx.tryCall | ``Lsc.Tx.tryView
  | ``Lsc.Tx.load | ``Lsc.Tx.loadMap | ``Lsc.Tx.loadMap2
  | ``Lsc.Tx.store | ``Lsc.Tx.storeMap | ``Lsc.Tx.storeMap2
  | ``Lsc.Tx.require | ``Lsc.Tx.emit | ``Lsc.Tx.revert
  | ``Lsc.Tx.sender | ``Lsc.Tx.value | ``Lsc.Tx.timestamp | ``Lsc.Tx.blockNumber
  | ``Lsc.Tx.selfAddress
  | ``Bind.bind | ``Pure.pure | ``ite
  | ``Lsc.Amount.add | ``Lsc.Amount.sub
  | ``Lsc.Amount.mulScalar | ``Lsc.Amount.divScalar
  | ``Lsc.Amount.mulDivDown | ``Lsc.Amount.mulDivUp
  | ``Lsc.Tx.HAddChecked.hAdd | ``Lsc.Tx.HSubChecked.hSub
  | ``Lsc.Tx.HMulChecked.hMul | ``Lsc.Tx.HDivChecked.hDiv =>
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
Before unfolding `rescale`, `roundingOf` requires a literal `.down`/`.up`. -/
partial def deltaUnfold (e : Expr) (fuel : Nat := 8) : MetaM (Expr × Option Name) := do
  let rec go (e : Expr) (fuel : Nat) (seen : Option Name) : MetaM (Expr × Option Name) := do
    let e := e.consumeMData
    if fuel = 0 then return (e, seen)
    let n? := e.getAppFn.constName?
    if n?.any isDeltaStop then return (e, seen)
    if let some n := n? then
      let tagged ← isLscInline n
      if tagged || isSurfaceOp n then
        if n == (.str (.str `Lsc "Word") "rescale")
            || n == (.str (.str `Lsc "Amount") "rescale")
            || n == ``Lsc.Tx.rescale then
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

/-- TODO: `Tx.tryCall` / `I.Try` are not in the compilable fragment yet. -/
def throwTryCall {α : Type} (_e : Expr) : MetaM α :=
  throwError "reify: try-calls are not compilable yet"

/-- ABI return kind of a `Tx.call`/`Tx.view` result type. -/
def abiRetOfTy (α : Expr) : MetaM AbiRet := do
  let α ← whnfR α
  if α.isConstOf ``Bool then return .boolOpt
  if α.isConstOf ``Unit || α.isConstOf ``PUnit then return .none
  return .word

/-- Closed `AbiRet` constructor (the `callAsNat` / `viewAsNat` argument). -/
def abiRetLit (e : Expr) : MetaM AbiRet := do
  let e ← whnfR e.consumeMData
  match e.getAppFn.constName? with
  | some ``Lsc.AbiRet.word => return .word
  | some ``Lsc.AbiRet.boolOpt => return .boolOpt
  | some ``Lsc.AbiRet.none => return .none
  | _ => throwError "reify: CALL return kind `{e}` must be a closed `AbiRet`"

/-- Selector nat of an elaborated `Tx.call`/`Tx.view`. -/
def selectorLit (e : Expr) : MetaM Nat := do
  match ← closedNat? e with
  | some n => return n
  | none => throwError "reify: CALL selector `{e}` must be a closed Nat"

/-- Result type of a `Tx … α` (unfolds `M` / similar abbrevs, not `ReaderT`). -/
partial def txRet? (ty : Expr) : MetaM (Option Expr) := do
  let ty := ty.consumeMData
  if ty.isAppOfArity ``Lsc.Tx 5 then return some (ty.getArg! 4)
  match ← unfoldDefinition? ty with
  | some ty' => txRet? ty'
  | none => return none

/-- Parse `Tx.call` / `Tx.view` / `callAsNat` / `viewAsNat` into a Core op. -/
def extCallOp (env : Env t) (isView : Bool) (x : Expr) (args : Array Expr)
    (retOverride : Option AbiRet := none) : MetaM (Option Op) := do
  if args.size < 3 then return none
  let addr ← atomOf env args[args.size - 3]!
  let sel ← selectorLit args[args.size - 2]!
  let as ← atomsOfList env args[args.size - 1]!
  let ret ←
    match retOverride with
    | some r => pure r
    | none => do
      let some α ← txRet? (← inferType x) |
        throwError "reify: CALL/view `{x}` is not a `Tx`"
      abiRetOfTy α
  if isView then return some (.view addr sel as ret)
  else return some (.call addr sel as ret)

/-- `getAppFn` / `getAppArgs` that skip intervening `MData`. -/
partial def flattenApp (e : Expr) : Expr × Array Expr :=
  let e := e.consumeMData
  match e with
  | .app f a =>
    let (fn, args) := flattenApp f
    (fn, args.push a)
  | _ => (e, #[])

/-- True when `e` is `Amount.ofWord` / `Amount.mk`, possibly η-expanded. -/
partial def isOfWordFn (e : Expr) : Bool :=
  let e := e.consumeMData
  if e.isAppOf ``Lsc.Amount.ofWord || e.isConstOf ``Lsc.Amount.ofWord
      || e.isAppOf ``Lsc.Amount.mk || e.isConstOf ``Lsc.Amount.mk then
    true
  else if e.isLambda then
    isOfWordFn e.bindingBody!
  else false

/-- `I.Ref.mk`, possibly η-expanded (`fun n => { addr := n }`). -/
partial def isRefMkFn (e : Expr) : Bool :=
  let e := e.consumeMData
  if let some n := e.getAppFn.constName? then
    if n.getString! == "mk" then
      -- `I.Ref.mk` — last component of the parent is `Ref`
      match n.getPrefix with
      | .str _ "Ref" => true
      | _ => e.isLambda && isRefMkFn e.bindingBody!
    else e.isLambda && isRefMkFn e.bindingBody!
  else if e.isLambda then
    isRefMkFn e.bindingBody!
  else false

/-- `Tx.natToBool`, possibly η-expanded. -/
partial def isNatToBoolFn (e : Expr) : Bool :=
  let e := e.consumeMData
  if e.isAppOf ``Lsc.Tx.natToBool || e.isConstOf ``Lsc.Tx.natToBool then
    true
  else if e.isLambda then
    isNatToBoolFn e.bindingBody!
  else false

/-- Drop `ofWord <$> tx` / `Ref.mk <$> tx` / `natToBool <$> tx`. Do not peel when the last argument
is itself an `Amount` or `Ref` (e.g. `mulDivDown a (ofWord scale) x`). `Tx`
unfolds to `ReaderT`, so the guard is "not an Amount/Ref", not `isAppOf Tx`. -/
partial def peelAmountWrap (e : Expr) : MetaM Expr := do
  let (_, args) := flattenApp e
  if args.size ≥ 2 && (isOfWordFn args[args.size - 2]! || isRefMkFn args[args.size - 2]!
      || isNatToBoolFn args[args.size - 2]!) then
    let x := args[args.size - 1]!
    let ty ← inferType x
    if (← isAmountTy ty) || (← isRefTy ty) then
      return e
    else
      peelAmountWrap x
  else
    return e

/-- Drop unused `{Type}` binders (`fun {S X E ε} => Amount.add`). -/
partial def dropUnusedTypeLams (e : Expr) : Expr :=
  let e := e.consumeMData
  match e with
  | .lam _ d b _ =>
    if d.isSort && !b.hasLooseBVars then dropUnusedTypeLams b else e
  | _ => e

/-- Unfold surface / inline / instance-projection heads, then peel `ofWord <$>`. -/
partial def prepOp (x : Expr) (fuel : Nat := 8) : MetaM Expr := do
  if fuel = 0 then return x
  let x ← peelAmountWrap x.consumeMData
  let (f0, args) := flattenApp x
  let f := dropUnusedTypeLams f0
  let x := mkAppN f args
  if f.constName?.any isDeltaStop then return x
  if let some n := f.constName? then
    if (← isLscInline n) || isSurfaceOp n then
      return (← prepOp (← deltaUnfold x).1 (fuel - 1))
  if let some x' ← unfoldProjInst? x then
    return (← prepOp x' (fuel - 1))
  match f with
  | .proj .. =>
    let f' := dropUnusedTypeLams (← whnfR f)
    if f' != f then
      return (← prepOp (mkAppN f' args) (fuel - 1))
    match ← reduceProj? f with
    | some f' => prepOp (mkAppN (dropUnusedTypeLams f') args) (fuel - 1)
    | none =>
      match ← unfoldDefinition? x with
      | some x' => prepOp x' (fuel - 1)
      | none => return x
  | .lam .. =>
    let x' := f.beta args
    if x' == x then return x
    else prepOp x' (fuel - 1)
  | _ =>
    match ← unfoldDefinition? x with
    | some x' => prepOp x' (fuel - 1)
    | none => return x

/-- Word-valued primitives. -/
def opOf (ci : ContractInfo) (env : Env t) (x : Expr) : MetaM (Option Op) := do
  let x ← prepOp x
  let (fn, args) := flattenApp x
  if let some n := fn.constName? then
    if isTryHead n then throwTryCall x
  let atom := atomOf env
  match fn.constName?, args.size with
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
  | some ``Lsc.Tx.HAddChecked.hAdd, n =>
    return some (.addChecked (← atom args[n - 2]!) (← atom args[n - 1]!))
  | some ``Lsc.Tx.HSubChecked.hSub, n =>
    return some (.subChecked (← atom args[n - 2]!) (← atom args[n - 1]!))
  | some ``Lsc.Tx.HMulChecked.hMul, n =>
    return some (.mulChecked (← atom args[n - 2]!) (← atom args[n - 1]!))
  | some ``Lsc.Tx.HDivChecked.hDiv, n =>
    return some (.divChecked (← atom args[n - 2]!) (← atom args[n - 1]!))
  | some ``Lsc.Tx.mulDivDown, 7 =>
    return some (.mulDivDown (← atom args[4]!) (← atom args[5]!) (← atom args[6]!))
  | some ``Lsc.Tx.mulDivUp, 7 =>
    return some (.mulDivUp (← atom args[4]!) (← atom args[5]!) (← atom args[6]!))
  | some ``Lsc.Tx.pow10, 5 =>
    return some (.pow10 (← atom args[4]!))
  | some ``Lsc.Tx.call, _ =>
    extCallOp env false x args
  | some ``Lsc.Tx.callAsNat, n =>
    if n < 4 then return none
    extCallOp env false x args (← abiRetLit args[n - 4]!)
  | some ``Lsc.Tx.view, _ =>
    extCallOp env true x args
  | some ``Lsc.Tx.viewAsNat, n =>
    if n < 4 then return none
    extCallOp env true x args (← abiRetLit args[n - 4]!)
  | some ``Lsc.Amount.add, n =>
    return some (.addChecked (← atom args[n - 2]!) (← atom args[n - 1]!))
  | some ``Lsc.Amount.sub, n =>
    return some (.subChecked (← atom args[n - 2]!) (← atom args[n - 1]!))
  | some ``Lsc.Amount.mulScalar, n =>
    return some (.mulChecked (← atom args[n - 2]!) (← atom args[n - 1]!))
  | some ``Lsc.Amount.divScalar, n =>
    return some (.divChecked (← atom args[n - 2]!) (← atom args[n - 1]!))
  | some ``Lsc.Amount.mulDivDown, n =>
    return some (.mulDivDown (← atom args[n - 3]!) (← atom args[n - 2]!) (← atom args[n - 1]!))
  | some ``Lsc.Amount.mulDivUp, n =>
    return some (.mulDivUp (← atom args[n - 3]!) (← atom args[n - 2]!) (← atom args[n - 1]!))
  | some ``Lsc.Tx.HMulDivDown.hMulDivDown, n =>
    if n < 3 then return none
    return some (.mulDivDown (← atom args[n - 3]!) (← atom args[n - 2]!) (← atom args[n - 1]!))
  | some ``Lsc.Tx.HMulDivUp.hMulDivUp, n =>
    if n < 3 then return none
    return some (.mulDivUp (← atom args[n - 3]!) (← atom args[n - 2]!) (← atom args[n - 1]!))
  | some ``Pure.pure, 4 => return some (.pure (← atom args[3]!))
  | _, _ => return none

/-- Unit-valued primitives. -/
def stmtOf (ci : ContractInfo) (env : Env t) (x : Expr) : MetaM (Option Stmt) := do
  let x ← prepOp x
  let (fn, args) := flattenApp x
  if let some n := fn.constName? then
    if isTryHead n then throwTryCall x
  let atom := atomOf env
  match fn.constName?, args.size with
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
  | some ``Lsc.Tx.call, _ =>
    match ← extCallOp env false x args with
    | some (.call t sel as ret) => return some (.call t sel as ret)
    | some (.view t sel as ret) => return some (.view t sel as ret)
    | _ => return none
  | some ``Lsc.Tx.callAsNat, n =>
    if n < 4 then return none
    match ← extCallOp env false x args (← abiRetLit args[n - 4]!) with
    | some (.call t sel as ret) => return some (.call t sel as ret)
    | some (.view t sel as ret) => return some (.view t sel as ret)
    | _ => return none
  | some ``Lsc.Tx.view, _ =>
    match ← extCallOp env true x args with
    | some (.call t sel as ret) => return some (.call t sel as ret)
    | some (.view t sel as ret) => return some (.view t sel as ret)
    | _ => return none
  | some ``Lsc.Tx.viewAsNat, n =>
    if n < 4 then return none
    match ← extCallOp env true x args (← abiRetLit args[n - 4]!) with
    | some (.call t sel as ret) => return some (.call t sel as ret)
    | some (.view t sel as ret) => return some (.view t sel as ret)
    | _ => return none
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
  let e ← peelAmountWrap e.consumeMData
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
      if isTryHead name then throwTryCall e
      match name, args.size with
      | ``Bind.bind, 6 =>
        let x0 ← peelAmountWrap args[4]!
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
        else if let some n := x.getAppFn.constName? then
          if isTryHead n then throwTryCall x
          else throwInlineOr inline? x m!"reify: `{x0}` is not a contract primitive"
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
    | _ =>
      let e' ← prepOp e
      if e' != e then
        reify ci t env e' inline?
      else if let some op ← opOf ci env e then
        match opTailCore t op with
        | some c => return c
        | none =>
            throwInlineOr inline? e m!"reify: `{e}` returns a word but the function does not"
      else if let some s ← stmtOf ci env e then
        match stmtTailCore t s with
        | some c => return c
        | none =>
            throwInlineOr inline? e m!"reify: `{e}` returns Unit but the function does not"
      else
        throwInlineOr inline? e m!"reify: `{e}` is outside the reifiable fragment"

/-! ## Commands -/

/-- `@[lsc_inline]` helpers and generated `I.Ref.f` methods reachable from `fn`. -/
def isCertUnfold (env : Environment) (n : Name) : Bool :=
  Lsc.lscInlineAttr.hasTag env n || isRefMethod n

/-- `@[lsc_inline]` names and `I.Ref` methods reachable from `fn`. -/
def inlinesUsedBy (fn : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let info ← getConstInfoDefn fn
  let mut acc : Array Name := #[]
  let mut seen : NameSet := {}
  let mut work : Array Name := #[]
  for n in info.value.getUsedConstants do
    if isCertUnfold env n then
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
        if isCertUnfold env m && !seen.contains m then
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
  | some ``Core.denote =>
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

The certificate tactic is `first | rfl | (push Amount/Bool wrap through Core
constructors; simp only [Core.denote, inlines, monad laws, schema field
lemmas]; rfl)`.
`rfl` is the fast path when no inlines are used. With inlines the `rfl`
attempt is skipped (it times out on a large non-matching `do` block).
An outer `Amount.ofWord <$>` / `natToBool <$>` wrapper is pushed inward by
`map_denote_*` (matching `Core` constructors, not `do`/`bind` pretty-printing)
before `Core.denote` unfolds. `map_eq_pure_bind` is not in the `simp only`
set (it would hide `map_callAsNat_bool`). A propositional certificate is not a
trust extension: the reifier is still untrusted MetaM, and the kernel checks
`Core.denote (reify f) = f`.
-/
def certifyDenote (fn : Name) (ci : ContractInfo) (lhs lhsRaw rhs coreE : Expr) :
    TermElabM Expr := do
  let eq ← mkEq lhs rhs
  let inlines ← inlinesUsedBy fn
  -- `isDefEq` on a large non-matching `do` block (inlined helper mid-body)
  -- burns the heartbeat budget; skip it when inlines are present.
  if inlines.isEmpty then
    -- Default `isDefEq` on a large mismatched `do` block burns heartbeats.
    -- Reducible equality is the fast path; otherwise fall through to simp.
    if ← withNewMCtxDepth (withReducible (isDefEq lhs rhs)) then
      return (← mkEqRefl lhs)
  -- Do not include `map_eq_pure_bind`: it rewrites `f <$> callAsNat` to a
  -- bind and hides `map_callAsNat_bool` / `map_viewAsNat_amount`.
  let mut idsAmount : Array Ident := #[
    mkIdent ``Lsc.Tx.bind_assoc,
    mkIdent ``Lsc.Tx.bind_assoc_pure,
    mkIdent ``Lsc.Tx.discard_bind_pure,
    mkIdent ``Lsc.Tx.require_iff,
    mkIdent ``Lsc.Tx.pure_bind,
    mkIdent ``Lsc.Tx.bind_pure,
    mkIdent ``Lsc.Tx.map_pure,
    mkIdent ``Lsc.Tx.map_ite,
    mkIdent ``Lsc.Tx.bind_ite,
    mkIdent ``Lsc.Tx.map_bind,
    mkIdent ``Lsc.Tx.bind_map,
    mkIdent ``Lsc.Tx.map_bind_ofWord,
    mkIdent ``Lsc.Tx.map_bind_natToBool,
    mkIdent ``Lsc.Tx.map_bind_viewAsNat_amount,
    mkIdent ``Lsc.Tx.bind_load_inner_viewAsNat_amount,
    mkIdent ``Lsc.Tx.bind_load_inner_viewAsNat_amount_addr,
    mkIdent ``Lsc.Tx.bind_load_getD_inner_viewAsNat_amount,
    mkIdent ``Lsc.Tx.bind_load_getD_pair_addr_view_amount,
    mkIdent ``Lsc.Tx.load_selfAddress_view_amount,
    mkIdent ``Lsc.Tx.view_toWord_arg,
    mkIdent ``Lsc.load_getD_cons,
    mkIdent ``Lsc.load_getD_cons_one,
    mkIdent ``Lsc.load_getD_cons_two,
    mkIdent ``Lsc.Tx.map_callAsNat_bool,
    mkIdent ``Lsc.Tx.map_viewAsNat_bool,
    mkIdent ``Lsc.Tx.map_callAsNat_amount,
    mkIdent ``Lsc.Tx.map_viewAsNat_amount,
    mkIdent ``Lsc.Tx.bind_callAsNat_bool,
    mkIdent ``Lsc.Tx.bind_viewAsNat_bool,
    mkIdent ``Lsc.Tx.bind_callAsNat_amount,
    mkIdent ``Lsc.Tx.bind_viewAsNat_amount,
    mkIdent ``Lsc.Tx.callAsNat_bool_bind_require,
    mkIdent ``Lsc.Tx.viewAsNat_bool_bind_require,
    mkIdent ``Lsc.Tx.callAsNat_bool_bind_require_bind,
    mkIdent ``Lsc.Tx.viewAsNat_bool_bind_require_bind,
    mkIdent ``Lsc.Tx.callAsNat_bool_bind_unit,
    mkIdent ``Lsc.Tx.viewAsNat_bool_bind_unit,
    mkIdent ``Lsc.Tx.viewAsNat_word_bind_const,
    mkIdent ``Lsc.Tx.callAsNat_word_bind_const,
    mkIdent ``Lsc.Tx.natToBool_one,
    mkIdent ``Lsc.Tx.map_discard,
    mkIdent ``Lsc.Address.toWord,
    mkIdent ``Lsc.Flag.off_eq_zero,
    mkIdent ``Lsc.Flag.on_eq_one,
    mkIdent ``Lsc.Tx.encode_address,
    mkIdent ``Lsc.Tx.encode_amount,
    mkIdent ``Lsc.Tx.encode_word,
    mkIdent ``Lsc.Tx.callAsNat_addr,
    mkIdent ``Lsc.Tx.viewAsNat_addr,
    mkIdent ``Lsc.AbiType.encode,
    mkIdent ``Lsc.Core.denote,
    mkIdent ``Lsc.Op.denote,
    mkIdent ``Lsc.Stmt.denote,
    mkIdent ``Lsc.Atom.eval_lit,
    mkIdent ``Lsc.Atom.eval_var_0,
    mkIdent ``Lsc.Atom.eval_var_0_addr,
    mkIdent ``Lsc.Atom.eval_var_1_addr,
    mkIdent ``Lsc.Atom.eval_var_2_addr,
    mkIdent ``Lsc.Atom.eval_var_3_addr,
    mkIdent ``Lsc.Atom.eval_var_succ_addr,
    mkIdent ``Lsc.Atom.eval_var_1,
    mkIdent ``Lsc.Atom.eval_var_2,
    mkIdent ``Lsc.Atom.eval_var_3,
    mkIdent ``Lsc.Atom.eval_var_4,
    mkIdent ``Lsc.Atom.eval_var_5,
    mkIdent ``Lsc.Atom.eval_var_succ,
    mkIdent ``Lsc.Atom.eval_var_6,
    mkIdent ``Lsc.Atom.eval_var_7,
    mkIdent ``Lsc.Atom.eval_var_8,
    mkIdent ``Lsc.Atom.eval_var_9,
    mkIdent ``Lsc.Atom.eval_var_10,
    mkIdent ``Lsc.Atom.eval_var_11,
    mkIdent ``Lsc.Atom.eval_var_12,
    mkIdent ``Lsc.Cond.denote,
    mkIdent ``Lsc.Cond.denote_eq,
    mkIdent ``Lsc.Cond.denote_ne,
    mkIdent ``Lsc.Cond.denote_lt,
    mkIdent ``Lsc.Cond.denote_le,
    mkIdent ``List.map_cons,
    mkIdent ``List.map_nil,
    mkIdent ``Lsc.list_getD_cons_zero,
    mkIdent ``Lsc.list_getD_cons_one,
    mkIdent ``Lsc.list_getD_cons_two,
    mkIdent ``Lsc.list_getD_cons_three,
    mkIdent ``Lsc.list_getD_cons_four,
    mkIdent ``Lsc.list_getD_cons_five,
    mkIdent ``Lsc.list_getD_cons_six,
    mkIdent ``Lsc.list_getD_cons_seven,
    mkIdent ``Lsc.list_getD_cons_succ,
    mkIdent ``Lsc.list_getD_cons_zero_app,
    mkIdent ``Lsc.list_getD_pair_zero,
    mkIdent ``Option.getD_some,
    mkIdent ``Option.getD_none,
    mkIdent ``Lsc.Amount.ofWord_eq_zero,
    mkIdent ``Lsc.Amount.ofWord_raw,
    mkIdent ``Lsc.Amount.raw_ofWord,
    mkIdent ``Lsc.Amount.load_bind_ofWord,
    mkIdent ``Lsc.Amount.loadMap_bind_ofWord,
    mkIdent ``Lsc.Amount.loadMap2_bind_ofWord,
    mkIdent ``Lsc.Amount.add_bind_ofWord,
    mkIdent ``Lsc.Amount.sub_bind_ofWord,
    mkIdent ``Lsc.Amount.mulDivDown_bind_ofWord,
    mkIdent ``Lsc.Amount.mulDivUp_bind_ofWord,
    mkIdent ``Lsc.Amount.add,
    mkIdent ``Lsc.Amount.sub,
    mkIdent ``Lsc.Amount.mulScalar,
    mkIdent ``Lsc.Amount.divScalar,
    mkIdent ``Lsc.Amount.mulDivDown,
    mkIdent ``Lsc.Amount.mulDivUp,
    mkIdent ``Lsc.Amount.hMulDivDown_def,
    mkIdent ``Lsc.Amount.hMulDivUp_def,
    mkIdent ``Lsc.Amount.eq_iff,
    mkIdent ``Lsc.Amount.ne_iff,
    mkIdent ``Lsc.Amount.lt_iff,
    mkIdent ``Lsc.Amount.le_iff,
    mkIdent ``Lsc.Amount.require_lt_ofWord,
    mkIdent ``Lsc.Amount.require_le_ofWord,
    mkIdent ``Lsc.Amount.require_eq_zero_ofWord,
    mkIdent ``Lsc.Amount.ite_eq_zero_ofWord,
    mkIdent ``Lsc.Amount.raw_ofNat,
    mkIdent ``Lsc.Amount.raw_zero,
    mkIdent ``Lsc.Amount.mk_raw,
    mkIdent ``Lsc.Tx.HAddChecked.hAdd,
    mkIdent ``Lsc.Tx.HSubChecked.hSub,
    mkIdent ``Lsc.Tx.HMulChecked.hMul,
    mkIdent ``Lsc.Tx.HDivChecked.hDiv,
    mkIdent ``Lsc.Tx.HMulDivDown.hMulDivDown,
    mkIdent ``Lsc.Tx.HMulDivUp.hMulDivUp,
    mkIdent ``Lsc.Amount.raw,
    mkIdent ``Lsc.Prim.eval_id,
    mkIdent ``Lsc.RetExpr.eval_word,
    mkIdent ``Lsc.RetExpr.eval_flag,
    mkIdent ``Lsc.list_getElem?_cons_one,
    mkIdent ``Lsc.list_getElem?_cons_two,
    mkIdent ``Lsc.list_getElem?_cons_three,
    mkIdent ``Lsc.list_getElem?_cons_four,
    mkIdent ``Lsc.list_getElem?_cons_five,
    mkIdent ``List.getElem?_cons_zero,
    mkIdent fn]
  let schemaIds ← existingIdents (schemaLemmaNames ci)
  idsAmount := idsAmount ++ schemaIds
  for n in inlines do
    idsAmount := idsAmount.push (mkIdent n)
  -- `lhsRaw` inlines `f.core`. `simp` of `Core.denote` equation lemmas gives
  -- the `Tx` `>>=` spine without unfolding into ReaderT.
  let eqRaw ← mkEq lhsRaw rhs
  let tacAmt ← `(by
    -- Push `ofWord <$>` / `natToBool <$>` through Core constructors *before*
    -- unfolding `Core.denote` (unfolding yields a `do`/`bind` spine that
    -- `map_bind` does not match on large programs). Constructor lemmas are
    -- first-order. Then unfold primitives / schema / inlines.
    -- Do not `simp` `map_eq_pure_bind`: it hides `map_callAsNat_bool`.
    try (conv =>
      lhs
      simp (config := { maxSteps := 20000 }) only
        [Lsc.map_denote_letOp_ofWord, Lsc.map_denote_seq_ofWord,
          Lsc.map_denote_ret_ofWord, Lsc.map_denote_ite_ofWord,
          Lsc.map_denote_letPure_ofWord, Lsc.map_denote_letOp_natToBool,
          Lsc.map_denote_seq_natToBool, Lsc.map_denote_ret_natToBool,
          Lsc.map_denote_ite_natToBool, Lsc.map_denote_letPure_natToBool,
          Lsc.map_denote_letOp, Lsc.map_denote_seq, Lsc.map_denote_ret,
          Lsc.map_denote_ite, Lsc.map_denote_letPure, Lsc.map_denote_opTail,
          Lsc.map_denote_opTailFlag, Lsc.map_denote_opTailAddr,
          Lsc.map_denote_stmtTail, Lsc.map_denote_revertTail,
          Lsc.Tx.map_pure, Lsc.Tx.natToBool_one])
    simp only [$[$idsAmount:ident],*]
    try (conv =>
      lhs
      simp (config := { maxSteps := 20000 }) only
        [Lsc.Tx.map_bind_ofWord, Lsc.Tx.map_bind_natToBool, Lsc.Tx.map_bind,
          Lsc.Tx.map_discard, Lsc.Tx.map_pure, Lsc.Tx.map_ite, Lsc.Tx.bind_ite])
    try simp only [Lsc.list_getD_cons_zero, Lsc.list_getD_cons_one,
      Lsc.list_getD_cons_two, Lsc.list_getD_cons_three, Lsc.list_getD_cons_four,
      Lsc.list_getD_cons_five, Lsc.list_getD_cons_six, Lsc.list_getD_cons_seven,
      Lsc.list_getD_cons_succ, Lsc.list_getD_cons_zero_app,
      Lsc.list_getD_pair_zero, Option.getD_some, Lsc.load_getD_cons,
      Lsc.load_getD_cons_one, Lsc.load_getD_cons_two,
      Lsc.list_getElem?_cons_one, Lsc.list_getElem?_cons_two,
      Lsc.list_getElem?_cons_three, Lsc.list_getElem?_cons_four,
      Lsc.list_getElem?_cons_five, List.getElem?_cons_zero,
      Lsc.Atom.eval_var_0, Lsc.Atom.eval_var_0_addr, Lsc.Atom.eval_var_1,
      Lsc.Atom.eval_var_1_addr, Lsc.Atom.eval_var_2, Lsc.Atom.eval_var_2_addr,
      Lsc.Atom.eval_var_3, Lsc.Atom.eval_var_3_addr, Lsc.Atom.eval_var_succ,
      Lsc.Atom.eval_var_succ_addr]
    try simp only [Lsc.Tx.map_callAsNat_bool, Lsc.Tx.map_viewAsNat_bool,
      Lsc.Tx.map_callAsNat_amount, Lsc.Tx.map_viewAsNat_amount,
      Lsc.Tx.bind_callAsNat_bool, Lsc.Tx.bind_viewAsNat_bool,
      Lsc.Tx.bind_callAsNat_amount, Lsc.Tx.bind_viewAsNat_amount,
      Lsc.Tx.callAsNat_bool_bind_require, Lsc.Tx.viewAsNat_bool_bind_require,
      Lsc.Tx.callAsNat_bool_bind_require_bind,
      Lsc.Tx.viewAsNat_bool_bind_require_bind,
      Lsc.Tx.map_bind, Lsc.Tx.bind_map, Lsc.Tx.map_bind_ofWord,
      Lsc.Tx.map_bind_natToBool, Lsc.Tx.map_bind_viewAsNat_amount,
      Lsc.Tx.bind_load_inner_viewAsNat_amount,
      Lsc.Tx.bind_load_inner_viewAsNat_amount_addr,
      Lsc.Tx.bind_load_getD_inner_viewAsNat_amount,
      Lsc.Tx.bind_load_getD_pair_addr_view_amount,
      Lsc.Tx.load_selfAddress_view_amount, Lsc.Tx.view_toWord_arg,
      Lsc.Amount.load_bind_ofWord, Lsc.Amount.loadMap_bind_ofWord,
      Lsc.Amount.add_bind_ofWord, Lsc.Amount.sub_bind_ofWord,
      Lsc.Amount.mulDivDown_bind_ofWord, Lsc.Amount.mulDivUp_bind_ofWord,
      Lsc.Amount.require_lt_ofWord, Lsc.Amount.require_le_ofWord,
      Lsc.Amount.require_eq_zero_ofWord, Lsc.Amount.ite_eq_zero_ofWord,
      Lsc.Tx.bind_assoc, Lsc.Tx.bind_assoc_pure, Lsc.Tx.discard_bind_pure,
      Lsc.Tx.pure_bind, Lsc.Tx.bind_pure, Lsc.Tx.map_pure,
      Lsc.Address.toWord, Lsc.Flag.off_eq_zero, Lsc.Flag.on_eq_one,
      Lsc.Tx.natToBool_one]
    try (exact Lsc.Tx.bind_load_getD_pair_addr_view_amount _ _ _)
    try (exact Lsc.Tx.bind_load_getD_inner_viewAsNat_amount _ _ _ _)
    try (exact Lsc.Tx.bind_load_inner_viewAsNat_amount_addr _ _)
    try (exact Lsc.Tx.bind_load_inner_viewAsNat_amount _ _)
    all_goals rfl)
  try
    withoutErrToSorry (elabTermAndSynthesize tacAmt eqRaw)
  catch e =>
    let extra ← do
      if let some (l, r) ← firstDifferingBind lhsRaw rhs then
        pure m!"\nFirst differing bind:{indentExpr l}\nversus:{indentExpr r}"
      else pure m!""
    throwError "reify: certificate failed — denotation of the reified term is not \
      equal to the original function (even after Tx monad laws).{indentExpr eq}{extra}\n\
      Reified Core:{indentExpr coreE}\nTactic:{e.toMessageData}"

/-- Unfold `abbrev`s such as `C.M` until the head is `Lsc.Tx`. -/
partial def whnfToTx (ty : Expr) : MetaM Expr := do
  let ty := ty.consumeMData
  if ty.isAppOfArity ``Lsc.Tx 5 then return ty
  match ← unfoldDefinition? ty with
  | some ty' => whnfToTx ty'
  | none => throwError "reify: `{ty}` is not a `Tx` type"

/-- Reconstruct a surface `Amount` / `Bool` / `Ref` / pair from a Core word. -/
partial def wrapValue (ty : Expr) (e : Expr) : MetaM Expr := do
  let ty ← whnfR ty
  if ty.isAppOf ``Lsc.Amount then
    mkAppOptM ``Lsc.Amount.ofWord #[ty.getArg! 0, some e]
  else if ty.isConstOf ``Bool then
    mkAppM ``Lsc.Tx.natToBool #[e]
  else if ← isRefTy ty then
    let some n := ty.getAppFn.constName? | pure e
    return mkAppN (mkConst (n ++ `mk)) (ty.getAppArgs.push e)
  else if ty.isAppOfArity ``Prod 2 then
    let α := ty.getArg! 0
    let β := ty.getArg! 1
    let fst ← mkAppOptM ``Prod.fst #[none, none, some e]
    let snd ← mkAppOptM ``Prod.snd #[none, none, some e]
    let x ← wrapValue α fst
    let y ← wrapValue β snd
    mkAppM ``Prod.mk #[x, y]
  else
    pure e

/-- `Amount.ofWord <$> core` (and Bool / Ref / pair analogues) when Core returns a word.
Pass the named function, not `fun v => f v`, so certificate `simp` matches
`map_callAsNat_bool` / `map_viewAsNat_amount`. -/
def wrapDenote (ρ : Expr) (core : Expr) : MetaM Expr := do
  let ρ ← whnfR ρ
  if ρ.isConstOf ``Unit || ρ.isConstOf ``PUnit
      || ρ.isConstOf ``Nat || ρ.isConstOf ``Lsc.Word
      || ρ.isConstOf ``Lsc.Address || ρ.isConstOf ``Lsc.Flag then
    return core
  unless ρ.isAppOf ``Lsc.Amount || ρ.isAppOf ``Prod || ρ.isConstOf ``Bool
      || (← isRefTy ρ) do
    return core
  let txTy ← inferType core
  let txTy ← whnfToTx txTy
  let α := txTy.getArg! 4
  if ← isDefEq α ρ then return core
  if ρ.isConstOf ``Bool then
    mkAppM ``Functor.map #[mkConst ``Lsc.Tx.natToBool, core]
  else if ρ.isAppOf ``Lsc.Amount then
    let f ← mkAppOptM ``Lsc.Amount.ofWord #[ρ.getArg! 0]
    mkAppM ``Functor.map #[f, core]
  else if ← isRefTy ρ then
    let some n := ρ.getAppFn.constName? | return core
    let f := mkAppN (mkConst (n ++ `mk)) ρ.getAppArgs
    mkAppM ``Functor.map #[f, core]
  else
    withLocalDeclD `v α fun v => do
      let body ← wrapValue ρ v
      let f ← mkLambdaFVars #[v] body
      mkAppM ``Functor.map #[f, core]

/-- Core env atom: `.raw` / `.addr` for Amount / Ref parameters. -/
def encodeEnvAtom (p : Expr) : MetaM Expr := do
  let ty ← inferType p
  if ← isAmountTy ty then mkAppM ``Lsc.Amount.raw #[p]
  else if ← isRefTy ty then
    mkAppM ``Lsc.Address.toWord (#[(← mkProjection p `addr)])
  else if (← whnfR ty).isConstOf ``Lsc.Address then mkAppM ``Lsc.Address.toWord #[p]
  else pure p

/-- Reify `fn` and add `fn.core` and `fn.core_denote` to the environment. -/
def reifyFunction (fn : Name) : TermElabM Unit := do
  let info ← getConstInfoDefn fn
  for n in info.value.getUsedConstants do
    if isTryHead n then
      throwTryCall (mkConst n)
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
    -- Certificate: `Core.denote schema core env = f`, or `ofWord <$> Core.denote = f`
    -- when the surface returns `Amount`.
    let schema := Lean.mkConst ci.schema
    let envAtoms : List Expr ← params.toList.reverse.mapM fun p => encodeEnvAtom p
    let envList ← mkListLit (Lean.mkConst ``Nat) envAtoms
    let coreDenote :=
      mkAppN (Lean.mkConst ``Core.denote)
        #[S, X, E, ε, schema, toExpr t, Lean.mkConst coreName, envList]
    let coreDenoteRaw :=
      mkAppN (Lean.mkConst ``Core.denote)
        #[S, X, E, ε, schema, toExpr t, core.toExpr, envList]
    let lhs ← wrapDenote ρ coreDenote
    let lhsRaw ← wrapDenote ρ coreDenoteRaw
    let rhs := mkAppN (Lean.mkConst fn) params
    let eq ← mkEq lhs rhs
    let pf ← withDeclName (fn ++ `core_denote) <|
      certifyDenote fn ci lhs lhsRaw rhs core.toExpr
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

def fnKindOf (fn : Name) : MetaM FnKind := do
  if fn.getString! == "constructor" then
    return .constructor
  unless (← getEnv).contains (fn ++ `core) do
    throwError "reify: `{fn}.core` missing when classifying function kind"
  let e ← mkAppM ``Core.isPureRead #[mkConst (fn ++ `core)]
  let e ← reduce (skipTypes := true) e
  if e.isConstOf ``Bool.true then return .view else return .tx

def fnMeta (fn : Name) : MetaM (List Param × RetTy × FnKind) := do
  let info ← getConstInfoDefn fn
  forallTelescope info.type fun xs body => do
    let txTy ← whnfToTx body
    let t ← retTyOf (txTy.getArg! 4)
    let params ← xs.toList.mapM fun x => do
      let n := (← x.fvarId!.getUserName).getString!
      let abi ← abiTyOf (← inferType x)
      pure { name := n, ty := abi }
    let kind ← fnKindOf fn
    pure (params, t, kind)

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
  let contractTy := Lean.mkConst ``ContractDef
  let contractVal := mkAppN (Lean.mkConst ``ContractDef.mk) #[
    toExpr ns.getString!, toExpr fields, fnList, ctorE, toExpr events, toExpr errors]
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
      let X := Lean.mkConst ``Lsc.ExtState
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

/-! ## `implements` (`C.impl_<I>` / `C.impl`) -/

/-- One `implements I args` clause from `lsc_contract`. -/
structure ImplementsClause where
  ifaceIdent : Ident
  ifaceName : Name
  args : Array Term
  deriving Inhabited

/-- ABI name of a surface type (same cases as `deriving Interface`). -/
def abiNameOf (ty : Expr) : MetaM String := do
  let ty ← withReducible (whnf ty)
  if ty.isConstOf ``Lsc.Address then return "address"
  if ty.isConstOf ``Bool then return "bool"
  if ty.isAppOf ``Lsc.Amount then return "uint256"
  if ty.isConstOf ``Lsc.Word || ty.isConstOf ``Nat then return "uint256"
  throwError "implements: unsupported ABI argument type{indentD ty}"

def peelFnView (ty : Expr) : MetaM (Bool × Expr) := do
  let ty ← whnf ty
  if ty.isAppOfArity ``Lsc.Fn 1 then return (false, ty.appArg!)
  if ty.isAppOfArity ``Lsc.View 1 then return (true, ty.appArg!)
  throwError "implements: interface fields must have type `Fn _` or `View _`{indentD ty}"

structure IfaceMethod where
  name : Name
  isView : Bool
  sel : Nat
  arity : Nat
  retKind : AbiRet
  argTys : Array Expr
  retTy : Expr

def collectIfaceMethods (I : Expr) : MetaM (Array IfaceMethod) := do
  let I ← whnfD I
  let some structName := I.getAppFn.constName? |
    throwError "implements: `{I}` is not an interface type"
  unless isStructure (← getEnv) structName do
    throwError "implements: `{structName}` is not a structure"
  let _ ← synthInstance (mkApp (mkConst ``Lsc.Interface) I)
  let params := I.getAppArgs
  let env ← getEnv
  let mut out : Array IfaceMethod := #[]
  for fieldName in getStructureFields env structName do
    let projTy ← inferType (mkAppN (mkConst (structName ++ fieldName)) params)
    let m ← forallBoundedTelescope projTy (some 1) fun _ fieldTy => do
      let (isView, inner) ← peelFnView fieldTy
      forallTelescope inner fun args ret => do
        let mut abiNames : Array String := #[]
        let mut argTys : Array Expr := #[]
        for x in args do
          let ty ← inferType x
          argTys := argTys.push ty
          abiNames := abiNames.push (← abiNameOf ty)
        let retKind ← abiRetOfTy ret
        let sel := methodSelector fieldName.getString! abiNames.toList
        return {
          name := fieldName, isView, sel, arity := args.size, retKind
          argTys, retTy := ret }
    out := out.push m
  return out

def checkImplementsTypes (ns : Name) (iface : Name) (m : IfaceMethod) : MetaM Unit := do
  let fn := ns ++ m.name
  unless (← getEnv).contains fn do
    throwError "implements {iface.getString!}: `{ns}` has no function `{m.name}`"
  let surf ← fnSurface fn
  unless surf.params.size == m.arity do
    throwError "implements {iface.getString!}: method `{m.name}` expects {m.arity} \
      argument(s), `{fn}` has {surf.params.size}"
  for i in [:m.arity] do
    unless ← isDefEq surf.params[i]!.2 m.argTys[i]! do
      throwError "implements {iface.getString!}: method `{m.name}` argument {i} has type\
{indentExpr m.argTys[i]!}\nbut `{fn}` has{indentExpr surf.params[i]!.2}"
  unless ← isDefEq surf.ρ m.retTy do
    throwError "implements {iface.getString!}: method `{m.name}` returns\
      {indentExpr m.retTy} but `{fn}` returns{indentExpr surf.ρ}"

def checkImplementsView (ns : Name) (iface : Name) (m : IfaceMethod) : MetaM Unit := do
  unless m.isView do return
  let fn := ns ++ m.name
  unless (← getEnv).contains (fn ++ `core) do
    throwError "implements {iface.getString!}: `{fn}` is not reified"
  let e ← mkAppM ``Core.isPureRead #[mkConst (fn ++ `core)]
  let e ← reduce (skipTypes := true) e
  unless e.isConstOf ``Bool.true do
    throwError "implements {iface.getString!}: `{m.name}` is a View but `{fn}` \
      writes, emits, or makes a non-view CALL"

def checkImplementsMethod (ns : Name) (iface : Name) (m : IfaceMethod) : MetaM Unit := do
  checkImplementsTypes ns iface m
  checkImplementsView ns iface m

def checkSelectorClash (clauses : Array (Name × Array IfaceMethod)) : MetaM Unit := do
  let mut acc : List (Nat × String × String × Nat × Bool × AbiRet) := []
  for (iname, methods) in clauses do
    for m in methods do
      match acc.find? (fun p => p.1 == m.sel) with
      | some (_, in0, mn0, ar, iv, r) =>
        unless ar == m.arity && iv == m.isView && r == m.retKind do
          throwError "implements: selector clash {m.sel} between `{in0}.{mn0}` \
            and `{iname.getString!}.{m.name}` (different signatures)"
      | none =>
        acc := (m.sel, iname.getString!, m.name.getString!, m.arity, m.isView, m.retKind) :: acc

/-- Name/arity/argument and return types, plus selector-clash. Independent of
reify, so a signature mismatch can abort `lsc_contract` before `core_denote`. -/
def checkImplementsTypesClauses (ns : Name) (clauses : Array ImplementsClause) :
    TermElabM Unit := do
  let mut collected : Array (Name × Array IfaceMethod) := #[]
  for c in clauses do
    let ifaceApp : Term ← `($(mkIdent c.ifaceName) $c.args*)
    let I ← elabTerm ifaceApp none
    let I ← instantiateMVars I
    let methods ← collectIfaceMethods I
    for m in methods do
      checkImplementsTypes ns c.ifaceName m
    collected := collected.push (c.ifaceName, methods)
  checkSelectorClash collected

/-- View methods must reify to a `Core.isPureRead` program. -/
def checkImplementsViewClauses (ns : Name) (clauses : Array ImplementsClause) :
    TermElabM Unit := do
  for c in clauses do
    let ifaceApp : Term ← `($(mkIdent c.ifaceName) $c.args*)
    let I ← elabTerm ifaceApp none
    let I ← instantiateMVars I
    let methods ← collectIfaceMethods I
    for m in methods do
      checkImplementsView ns c.ifaceName m

/-- Name/arity/type/view checks plus selector-clash. After reify (Views need
`f.core`), before `C.Fn`/`C.spec`, so a mismatch does not leave a half-generated
contract. -/
def checkImplementsClauses (ns : Name) (clauses : Array ImplementsClause) :
    TermElabM Unit := do
  checkImplementsTypesClauses ns clauses
  checkImplementsViewClauses ns clauses

def implMethodBody (ns : Name) (m : IfaceMethod) : MetaM Term := do
  let fn := ns ++ m.name
  let surf ← fnSurface fn
  let ids : Array Ident := surf.params.map fun (n, _) => mkIdent n
  let f : Term := ⟨mkIdent fn⟩
  if m.isView then
    let w := mkIdent `w
    let run ←
      if ids.size == 0 then
        `(Lsc.Tx.run $f { sender := (0 : Lsc.Address) } $w)
      else
        `(Lsc.Tx.run ($f $ids*) { sender := (0 : Lsc.Address) } $w)
    let inner ←
      `(match ($run) with
        | Except.ok (v, _) => v
        | Except.error _ => default)
    let mut acc ← `(fun $w => $inner)
    for id in ids.reverse do
      acc ← `(fun $id => $acc)
    return acc
  else
    let ctx := mkIdent `ctx
    let w := mkIdent `w
    let run ←
      if ids.size == 0 then
        `(Lsc.Tx.run $f $ctx $w)
      else
        `(Lsc.Tx.run ($f $ids*) $ctx $w)
    let mut acc ← `(fun $ctx $w => $run)
    for id in ids.reverse do
      acc ← `(fun $id => $acc)
    return acc

def worldTyTerm (ci : ContractInfo) : MetaM Term := do
  let S := mkIdent ci.storage
  let E := mkIdent ci.event
  `(Lsc.World $S Lsc.ExtState $E)

/-- `C.impl_<I>` (and `C.impl` when there is exactly one clause). -/
def mkImplCommands (ns : Name) (clauses : Array ImplementsClause) :
    TermElabM (Array (TSyntax `command)) := do
  if clauses.isEmpty then return #[]
  let ci ← contractInfo ns
  let W ← worldTyTerm ci
  let ε : Term := ⟨mkIdent ci.error⟩
  let specId : Term := ⟨mkIdent (ns ++ `spec)⟩
  let fnTy : Term := ⟨mkIdent (ns ++ `Fn)⟩
  let mut cmds : Array (TSyntax `command) := #[]
  let mut collected : Array (Name × Array IfaceMethod) := #[]
  let mut implNames : Array Name := #[]
  for c in clauses do
    let ifaceApp : Term ← `($(mkIdent c.ifaceName) $c.args*)
    let I ← elabTerm ifaceApp none
    let I ← instantiateMVars I
    let methods ← collectIfaceMethods I
    for m in methods do
      checkImplementsMethod ns c.ifaceName m
    collected := collected.push (c.ifaceName, methods)
    let implTy ← `($(mkIdent (c.ifaceName ++ `Impl)) $c.args* $W $ε)
    let fields : Array (TSyntax ``Parser.Term.structInstField) ←
      methods.mapM fun m => do
        let n := mkIdent m.name
        let body ← implMethodBody ns m
        `(Parser.Term.structInstField| $n:ident := $body)
    let step ←
      `(fun ctx w w' =>
          ∃ (fn : $fnTy), ∃ (args : Lsc.Spec.Args $specId fn),
            ∃ r, Lsc.Tx.run (Lsc.Spec.exec $specId fn args) ctx w = .ok (r, w'))
    let implName := ns ++ Name.mkSimple s!"impl_{c.ifaceName.getString!}"
    implNames := implNames.push implName
    let implId := mkIdent (`_root_ ++ implName)
    let stepField ← `(Parser.Term.structInstField| step := $step)
    let allFields := fields.push stepField
    let body ← `({ $[$allFields:structInstField],* })
    let cmd ← `(command| def $implId : $implTy := $body)
    cmds := cmds.push cmd
  checkSelectorClash collected
  if clauses.size = 1 then
    let c := clauses[0]!
    let implTy ← `($(mkIdent (c.ifaceName ++ `Impl)) $c.args* $W $ε)
    let implAlias := mkIdent (`_root_ ++ ns ++ `impl)
    let rhs : Term := ⟨mkIdent (`_root_ ++ implNames[0]!)⟩
    cmds := cmds.push (← `(command| def $implAlias : $implTy := $rhs))
  return cmds

def parseImplements (impls : Syntax) : Array (Ident × Array Term) := Id.run do
  let mut out : Array (Ident × Array Term) := #[]
  for g in impls.getArgs do
    -- `implements I args (, J args)*`
    out := out.push (⟨g[1]⟩, g[2].getArgs.map fun t => ⟨t⟩)
    for rest in g[3].getArgs do
      out := out.push (⟨rest[1]⟩, rest[2].getArgs.map fun t => ⟨t⟩)
  return out

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

def isWordTy (ty : Expr) : MetaM Bool := do
  let ty ← whnfR ty
  return ty.isConstOf ``Lsc.Word

def isFlagTy (ty : Expr) : MetaM Bool := do
  let ty ← whnfR ty
  return ty.isConstOf ``Lsc.Flag

def isBoolTy (ty : Expr) : MetaM Bool := do
  let ty ← whnfR ty
  return ty.isConstOf ``Bool

def encodeWordTerm (ty : Expr) (x : Term) : MetaM Term := do
  if ← isAmountTy ty then `(Lsc.Amount.raw $x)
  else if ← isRefTy ty then `(($x).addr)
  else if ← isAddressTy ty then `(Lsc.Address.toWord $x)
  else if ← isWordTy ty then `(($x : Nat))
  else pure x

def decodeWordTerm (ty : Expr) (n : Term) : MetaM Term := do
  if ← isAmountTy ty then
    let ty ← whnfD ty
    let aT ← exprToTerm (ty.getArg! 0)
    `(Lsc.Amount.ofWord (a := $aT) $n)
  else if ← isRefTy ty then
    `({ addr := $n })
  else if ← isWordTy ty then
    `(($n : Lsc.Word))
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
  let wrapMap : TSyntax ``Lean.Parser.Tactic.tacticSeq ←
    if ← isAmountTy surf.ρ then
      let ρ ← whnfD surf.ρ
      let aT ← exprToTerm (ρ.getArg! 0)
      `(Lean.Parser.Tactic.tacticSeq|
          apply Lsc.Lang.worldAfter_wrap_eq
            (f := Lsc.Amount.ofWord (a := $aT))
          rw [$specExec:ident]
          apply $coreDenote)
    else if ← isBoolTy surf.ρ then
      `(Lean.Parser.Tactic.tacticSeq|
          apply Lsc.Lang.worldAfter_wrap_eq (f := Lsc.Tx.natToBool)
          rw [$specExec:ident]
          apply $coreDenote)
    else if ← isRefTy surf.ρ then
      let ρT ← exprToTerm surf.ρ
      `(Lean.Parser.Tactic.tacticSeq|
          apply Lsc.Lang.worldAfter_wrap_eq
            (f := fun n => ({ addr := n } : $ρT))
          rw [$specExec:ident]
          apply $coreDenote)
    else if ← isProdTy surf.ρ then
      let ρ ← whnfD surf.ρ
      let α ← whnfD (ρ.getArg! 0)
      let β ← whnfD (ρ.getArg! 1)
      unless α.isAppOf ``Lsc.Amount && β.isAppOf ``Lsc.Amount do
        throwError "lsc_contract: pair return must be Amount × Amount"
      let aT ← exprToTerm (α.getArg! 0)
      let bT ← exprToTerm (β.getArg! 0)
      `(Lean.Parser.Tactic.tacticSeq|
          apply Lsc.Lang.worldAfter_wrap_eq
            (f := fun v => (Lsc.Amount.ofWord (a := $aT) v.1,
              Lsc.Amount.ofWord (a := $bT) v.2))
          rw [$specExec:ident]
          apply $coreDenote)
    else
      -- Flag/Nat/Unit views: `simp only` can leave `worldAfter f = worldAfter f`.
      -- `all_goals try rfl` is a no-op when simp already closed.
      `(Lean.Parser.Tactic.tacticSeq|
          simp only [$coreDenote:ident, $specExec:ident]
          all_goals try rfl)
  let tac ←
    match n with
    | 0 =>
      `(Lean.Parser.Tactic.tacticSeq|
          cases $argsId:ident
          dsimp [$fnDefId:ident, $encodeId:ident]
          change Lsc.Lang.worldAfter (Lsc.Core.denote $schemaId $coreId []) $ctxId $wId =
            Lsc.Lang.worldAfter (Lsc.Spec.exec $specId .$ctor:ident ()) $ctxId $wId
          ($wrapMap))
    | 1 => do
      let enc ← encodeWordTerm surf.params[0]!.2 ⟨argsId⟩
      `(Lean.Parser.Tactic.tacticSeq|
          dsimp [$fnDefId:ident, $encodeId:ident, Lsc.Address.toWord]
          change Lsc.Lang.worldAfter (Lsc.Core.denote $schemaId $coreId [$enc]) $ctxId $wId =
            Lsc.Lang.worldAfter (Lsc.Spec.exec $specId .$ctor:ident $argsId) $ctxId $wId
          ($wrapMap))
    | 2 => do
      let b0 := binders[0]!; let b1 := binders[1]!
      let e0 ← encodeWordTerm surf.params[0]!.2 ⟨b0⟩
      let e1 ← encodeWordTerm surf.params[1]!.2 ⟨b1⟩
      `(Lean.Parser.Tactic.tacticSeq|
          rcases $argsId:ident with ⟨$b0, $b1⟩
          dsimp [$fnDefId:ident, $encodeId:ident, Lsc.Address.toWord]
          change Lsc.Lang.worldAfter (Lsc.Core.denote $schemaId $coreId [$e1, $e0]) $ctxId $wId =
            Lsc.Lang.worldAfter (Lsc.Spec.exec $specId .$ctor:ident ($b0, $b1)) $ctxId $wId
          ($wrapMap))
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
          ($wrapMap))
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
        cases fn <;> simp [$encodeId:ident, $fnDefId:ident, Lsc.Address.toWord] <;> rfl)
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

def obligationsMissing (ns : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut missing : Array Name := #[]
  for s in #[`Inv, `claim, `Auth, `inflow, `holdings] do
    unless env.contains (ns ++ s) do
      missing := missing.push (ns ++ s)
  return missing

/-- Copy-pasteable security theorems for `C`'s generated `Fn` (not imported from Security). -/
def obligationsText (ns : Name) (ctors : List Name) (_extName : String) : String :=
  let C := ns.toString
  let leaf (n : Name) : String := n.getString!
  let world := s!"Lsc.World {C}.Storage Lsc.ExtState {C}.Event"
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
  let rely := s!"{C}.rely"
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
    let (schema, lawful, fields) ← liftTermElabM do
      let ci ← contractInfo ns
      let schema ← mkSchemaCommand ci
      let lawful ← mkSchemaLawfulCommand ci
      let fields ← mkSchemaFieldCommands ci
      pure (schema, lawful, fields)
    elabCommand schema
    elabCommand lawful
    for cmd in fields do elabCommand cmd
  | _ => throwUnsupportedSyntax

/-- `lsc_reify C.f` reifies a contract function and certifies the result. -/
syntax (name := lscReify) "lsc_reify " ident+ : command

@[command_elab lscReify] def elabLscReify : CommandElab
  | `(lsc_reify $fns:ident*) => do
    for fn in fns do
      let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo fn
      liftTermElabM <| withRef fn <| reifyFunction n
  | _ => throwUnsupportedSyntax

/-- `lsc_contract C f₁ … fₙ implements I args, …` reifies each `C.fᵢ` if needed, then
defines `C.contract`, `C.Fn` / `C.entry` / `C.spec`, the transport codec, and
`C.impl_<I>` (`C.impl` when there is exactly one `implements` clause). A function
named `constructor` is the constructor; otherwise the kind is `view` when
`Core.isPureRead` (no writes, emits, or CALLs) and `tx` otherwise. -/
syntax (name := lscContract)
  "lsc_contract " ident ident+
    ("implements " ident term:arg* (", " ident term:arg*)*)* : command

@[command_elab lscContract] def elabLscContract : CommandElab
  | stx => do
    unless stx.getKind == ``lscContract do throwUnsupportedSyntax
    let ns : Ident := ⟨stx[1]⟩
    let fnNode := stx[2]
    let fns := if fnNode.getKind == nullKind then fnNode.getArgs else #[fnNode]
    let nsName ← liftCoreM <|
      realizeGlobalConstNoOverloadWithInfo (mkIdent (ns.getId ++ `Storage))
    let nsName := nsName.getPrefix
    let mut resolved : Array Name := #[]
    for fn in fns do
      let n ← liftCoreM <|
        realizeGlobalConstNoOverloadWithInfo (mkIdent (nsName ++ fn.getId))
      resolved := resolved.push n
    let mut clauses : Array ImplementsClause := #[]
    for (id, args) in parseImplements stx[3] do
      let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
      clauses := clauses.push { ifaceIdent := id, ifaceName := n, args }
    match ← liftTermElabM (_root_.observing
        (checkImplementsTypesClauses nsName clauses)) with
    | .error e =>
      logError e.toMessageData
      return
    | .ok () => pure ()
    liftTermElabM <| assembleContract nsName resolved
    match ← liftTermElabM (_root_.observing
        (checkImplementsViewClauses nsName clauses)) with
    | .error e =>
      logError e.toMessageData
      return
    | .ok () => pure ()
    let cmds ← liftTermElabM <| mkSpecCommands nsName resolved
    for cmd in cmds do
      elabCommand cmd
    let codecCmds ← liftTermElabM do mkCodecCommands nsName resolved
    for cmd in codecCmds do
      elabCommand cmd
    let implCmds ← liftTermElabM <| mkImplCommands nsName clauses
    for cmd in implCmds do
      elabCommand cmd

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
      logInfo m!"{obligationsText nsName info.ctors ""}"
  | _ => throwUnsupportedSyntax

end Lsc.Reify

