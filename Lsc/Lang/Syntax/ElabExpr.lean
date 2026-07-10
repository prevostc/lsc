import Lsc.Lang.Syntax.Params

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Meta Lean.Parser.Term

namespace Lsc.Syntax

/-! ## Elaboration -/

/-- If `stx` is literally a bare numeral (`lscExprNum`), return its value — used by `+?`/`-?`
to detect the bare-`Nat` right-hand side (`Wei.addCheckedNat`) without first elaborating it as
a full `CoreExpr .uint256`. -/
def lscExprAsNatLit? (stx : TSyntax `lscExpr) : Option Nat :=
  match stx with
  | `(lscExpr| $n:num) => some n.getNat
  | _ => none

/-- Look up a storage field's `FieldKind` against the real storage `structure`, reusing
`Lsc.Deriving.getStructureFieldKinds` directly (no reimplementation). -/
def storageFieldKind (storageName : Name) (field : String) : TermElabM Lsc.Deriving.FieldKind := do
  let kinds ← Lsc.Deriving.getStructureFieldKinds storageName
  match kinds.find? (fun p => p.1.toString == field) with
  | some (_, k) => return k
  | none => throwError "Syntax: unknown storage field `{field}` on `{storageName}`"

def isMappingField (k : Lsc.Deriving.FieldKind) : Bool :=
  match k with | .mapping _ => true | _ => false

/-- Elaborate a `σ.field[key]`/`σ.field[key] = e;` node's `key` sub-`lscExpr` into a
`Lsc.MapKey`-valued `Term` — only `msg.sender` or a bare local identifier are supported
(see `lscExprMapGet`'s docstring). -/
def elabMapKey (key : TSyntax `lscExpr) : TermElabM Term :=
  match key with
  | `(lscExpr| msg.sender) => `(Lsc.MapKey.caller)
  | `(lscExpr| $x:ident) =>
    match Lsc.sigmaFieldName? x.getId with
    | some _ => throwErrorAt x "a mapping key cannot itself be a `σ.field` read"
    | none => `(Lsc.MapKey.var $(quote x.getId.toString))
  | stx => throwErrorAt stx "unsupported mapping key `{stx}` — expected `msg.sender` or a \
bare local identifier"

mutual

/-- Elaborate one `lscExpr` node into a `Lsc.Expr`-valued `Term`, alongside the `FieldKind`
tag it was resolved at (needed by callers, e.g. `require`/`if`'s `Bool`-kind check, `emit`'s
expected-argument-kind check, and `+?`/`-?`'s own dispatch). -/
partial def elabLscExpr (storageName : Name) (locals : List (String × Lsc.Deriving.FieldKind)) :
    TSyntax `lscExpr → TermElabM (Term × Lsc.Deriving.FieldKind)
  | `(lscExpr| ($e)) => elabLscExpr storageName locals e
  | `(lscExpr| msg.sender) => do
      return (← `(Lsc.CoreExpr.txField Lsc.TxField.caller), .address)
  | `(lscExpr| true) => do
      return (← `(Lsc.CoreExpr.lit Lsc.Ty.bool (Lsc.Lit.bool true)), .bool)
  | `(lscExpr| false) => do
      return (← `(Lsc.CoreExpr.lit Lsc.Ty.bool (Lsc.Lit.bool false)), .bool)
  | `(lscExpr| ! $e) => do
      let (t, k) ← elabLscExpr storageName locals e
      unless k == .bool do
        throwError "`!` expects a `Bool`-kind `lscExpr`, got a `{repr k}`-kind one"
      return (← `(Lsc.CoreExpr.not $t), .bool)
  | `(lscExpr| $a +? $b) => do
      let (at_, ak) ← elabLscExpr storageName locals a
      elabCheckedAddWith storageName locals at_ ak b
  | `(lscExpr| $a -? $b) => do
      let (at_, ak) ← elabLscExpr storageName locals a
      elabCheckedSubWith storageName locals at_ ak b
  | `(lscExpr| $a ⸢*⸣? $b) => do
      let (at_, ak) ← elabLscExpr storageName locals a
      unless ak == .wad do
        throwError "`⸢*⸣?`'s left-hand side must be `Wad`-kind, got `{repr ak}`"
      let (bt, bk) ← elabLscExpr storageName locals b
      unless bk == .wad do
        throwError "`⸢*⸣?`'s right-hand side must be `Wad`-kind, got `{repr bk}`"
      return (← `(Lsc.Wad.Expr.mulHalfUpChecked $at_ $bt), .wad)
  | `(lscExpr| $a ⌊/⌋? $b) => do
      let (at_, ak) ← elabLscExpr storageName locals a
      unless ak == .wad do
        throwError "`⌊/⌋?`'s left-hand side must be `Wad`-kind, got `{repr ak}`"
      let (bt, bk) ← elabLscExpr storageName locals b
      unless bk == .wad do
        throwError "`⌊/⌋?`'s right-hand side must be `Wad`-kind, got `{repr bk}`"
      return (← `(Lsc.Wad.Expr.divDownChecked $at_ $bt), .wad)
  | `(lscExpr| $a == $b) => do
      let (at_, ak) ← elabLscExpr storageName locals a
      let (bt, bk) ← elabLscExpr storageName locals b
      unless ak == bk do
        throwError "`==` between mismatched kinds `{repr ak}` and `{repr bk}`"
      if ak == .wei || ak == .wad then
        throwError "`==` is not yet supported on `{repr ak}`-kind expressions"
      -- Explicit `t` (rather than `eqAuto`'s implicit-`t` inference from `a`) avoids the same
      -- defeq-but-not-syntactic-equality trap the hand-written `pause`/`unpause` needed
      -- `@CoreExpr.eqAuto Ty.address ...` to route around (e.g. `msg.sender : CoreExpr
      -- (txFieldTy .caller)` vs `σ.owner : CoreExpr Ty.address`): `ak`'s `tyConst` is always
      -- the concrete `Ty` literal (from `storageFieldKind`/`Lit`/local `FieldKind`s), never an
      -- unreduced type-family application, so pinning `t` to it keeps the result syntactically
      -- `Ty`-headed rather than stuck on whichever operand happened to be elaborated first.
      let tyConst ← ak.tyConst
      return (← `(@Lsc.CoreExpr.eqAuto $tyConst $at_ $bt), .bool)
  | `(lscExpr| $n:num) => do
      let litTerm ← `(Lsc.Lit.u256 $(quote n.getNat))
      return (← `(Lsc.CoreExpr.lit Lsc.Ty.uint256 $litTerm), .uint256)
  | `(lscExpr| $x:ident [ $key ]) => do
      match Lsc.sigmaFieldName? x.getId with
      | some field => do
          let k ← storageFieldKind storageName field
          unless isMappingField k do
            throwErrorAt x "`{field}` is not a mapping field, cannot index it with `[..]`"
          let keyTerm ← elabMapKey key
          return (← `(Lsc.Wad.Expr.mapGet $(quote field) $keyTerm), .wad)
      | none => throwErrorAt x "expected `σ.field[key]`, got `{x.getId}[..]`"
  | `(lscExpr| $x:ident) => do
      let name := x.getId
      match Lsc.sigmaFieldName? name with
      | some field => do
          let k ← storageFieldKind storageName field
          let (k', t) ← match k with
            | .interface _ =>
              let t ← `(Lsc.CoreExpr.storageGet Lsc.Ty.address $(quote field))
              pure (.address, t)
            | _ =>
              let t ← k.storageGetStx field
              pure (k, t)
          return (t, k')
      | none =>
          let nameStr := name.toString
          match locals.find? (·.1 == nameStr) with
          | some (_, k) =>
              let nameLit := quote nameStr
              let (t, k') ← match k with
                | .wei => do
                  let t ← `(Lsc.Wei.Expr.var $nameLit)
                  pure (t, k)
                | .wad => do
                  let t ← `(Lsc.Wad.Expr.var $nameLit)
                  pure (t, k)
                | .bool => do
                  let t ← `(Lsc.CoreExpr.var Lsc.Ty.bool $nameLit)
                  pure (t, k)
                | .address => do
                  let t ← `(Lsc.CoreExpr.var Lsc.Ty.address $nameLit)
                  pure (t, k)
                | .uint256 => do
                  let t ← `(Lsc.CoreExpr.var Lsc.Ty.uint256 $nameLit)
                  pure (t, k)
                | .mapping _ => throwErrorAt x "`{nameStr}` is a mapping field, not a local value"
                | .interface _ => do
                  let t ← `(Lsc.CoreExpr.var Lsc.Ty.address $nameLit)
                  pure (t, Lsc.Deriving.FieldKind.address)
              return (t, k')
          | none => throwErrorAt x "unbound identifier `{nameStr}` in `lscExpr`"
  | stx => throwErrorAt stx "Syntax.elabLscExpr: unsupported `lscExpr` node"

/-- Checked addition, given the already-elaborated left-hand side (`at_`/`ak`) — shared by
`+?`'s own `lscExpr` production and the `+=?` compound-assignment statement sugar
(`lscMapAssignAdd`/`lscAssignAdd`), which both need to build "current value +? rhs" without
re-parsing a synthetic `lscExpr` node. -/
partial def elabCheckedAddWith (storageName : Name) (locals : List (String × Lsc.Deriving.FieldKind))
    (at_ : Term) (ak : Lsc.Deriving.FieldKind) (b : TSyntax `lscExpr) :
    TermElabM (Term × Lsc.Deriving.FieldKind) := do
  match ak with
  | .wei =>
    match lscExprAsNatLit? b with
    | some n => return (← `(Lsc.Wei.Expr.addCheckedNat $at_ $(quote n)), .wei)
    | none =>
        let (bt, bk) ← elabLscExpr storageName locals b
        unless bk == .wei do
          throwError "`+?`'s right-hand side must be `Wei`-kind or a numeral, got `{repr bk}`"
        return (← `(Lsc.Wei.Expr.addChecked $at_ $bt), .wei)
  | .wad =>
    match lscExprAsNatLit? b with
    | some n => return (← `(Lsc.Wad.Expr.addCheckedNat $at_ $(quote n)), .wad)
    | none =>
        let (bt, bk) ← elabLscExpr storageName locals b
        unless bk == .wad do
          throwError "`+?`'s right-hand side must be `Wad`-kind or a numeral, got `{repr bk}`"
        return (← `(Lsc.Wad.Expr.addChecked $at_ $bt), .wad)
  | _ => throwError "`+?`'s left-hand side must be `Wei`- or `Wad`-kind, got `{repr ak}`"

/-- Checked subtraction — the `-?`/`-=?` counterpart of `elabCheckedAddWith`. -/
partial def elabCheckedSubWith (storageName : Name) (locals : List (String × Lsc.Deriving.FieldKind))
    (at_ : Term) (ak : Lsc.Deriving.FieldKind) (b : TSyntax `lscExpr) :
    TermElabM (Term × Lsc.Deriving.FieldKind) := do
  match ak with
  | .wei =>
    let bt ← match lscExprAsNatLit? b with
      | some n => `(Lsc.Wei.Expr.lit $(quote n))
      | none => do
          let (bt, bk) ← elabLscExpr storageName locals b
          unless bk == .wei do
            throwError "`-?`'s right-hand side must be `Wei`-kind or a numeral, got `{repr bk}`"
          pure bt
    return (← `(Lsc.Wei.Expr.subChecked $at_ $bt), .wei)
  | .wad =>
    let bt ← match lscExprAsNatLit? b with
      | some n => `(Lsc.Wad.Expr.lit $(quote n))
      | none => do
          let (bt, bk) ← elabLscExpr storageName locals b
          unless bk == .wad do
            throwError "`-?`'s right-hand side must be `Wad`-kind or a numeral, got `{repr bk}`"
          pure bt
    return (← `(Lsc.Wad.Expr.subChecked $at_ $bt), .wad)
  | _ => throwError "`-?`'s left-hand side must be `Wei`- or `Wad`-kind, got `{repr ak}`"

end

end Lsc.Syntax
