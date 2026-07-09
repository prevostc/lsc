import Lsc.Lang.Syntax.Grammar

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Meta Lean.Parser.Term

namespace Lsc.Syntax

/-! ## `tx` parameters -/

/-- One `tx` parameter declaration: `name : ty`, e.g. `amount : Wad`. `ty` is parsed as a
plain `ident` (not a dedicated keyword-token grammar) purely to avoid reserving `UInt256`/
`Bool`/`Address`/`Wei`/`Wad` as global tokens (see `elabLscTyIdent` below, which resolves the
five supported spellings by string match, the same style `emit $ctor:ident`/`revert
$errCtor:ident` already use for resolving *their* idents against real declarations). Declared
as its own `lscTxParam` syntax category so a comma-separated `lscTxParam,*` list can be wrapped
in a single, optional pair of parens on `tx`'s own `elab` declaration below — giving
`tx foo { .. }` (no parens) and `tx foo(a : ty1, b : ty2) { .. }` (one paren group, comma-
separated) the same shape/ergonomics as Solidity's (and most other languages') parameter
lists. -/
declare_syntax_cat lscTxParam
syntax (name := lscTxParamDecl) ident " : " ident : lscTxParam

/-- Resolve a `tx` parameter's `ty` identifier to a `FieldKind`, by string match against the
five supported spellings — the same five `Lsc.Deriving.FieldKind` already supports for storage
fields/`let`-locals, so a `tx` parameter is usable inside the body exactly like a `let`-bound
local (see this file's module docstring's "`let x = e;`" section: a parameter and a `let`-local
are structurally the same kind of thing, just supplied by the caller instead of computed by an
expression). Spelled capitalized (`UInt256`/`Bool`/`Address`/`Wei`/`Wad`) to match the real Lean
type names these already have everywhere else (storage fields, event payloads, `leanTypeStx`),
rather than a separate lowercase-only convention just for `tx` parameters. -/
def elabLscTyIdent (ty : Lean.Ident) : TermElabM Lsc.Deriving.FieldKind :=
  match ty.getId.toString with
  | "UInt256" => return .uint256
  | "Bool" => return .bool
  | "Address" => return .address
  | "Wei" => return .wei
  | "Wad" => return .wad
  | _ => do
    -- Not one of the five fixed keywords — try resolving `ty` as a named `Wad`(`= Fixed 18`)-
    -- shaped alias (e.g. `Token.Amount`, declared as `abbrev Token.Amount := Lsc.Wad` right next
    -- to a token's own storage) via the same alias resolution `Lsc.Deriving.fieldKindOfExprM`
    -- already uses for storage struct fields — so a `tx` parameter (e.g. `Escrow.release`'s
    -- `amount`) can name the specific token it moves, instead of the generic `Wad`. Only ever
    -- accepts a `Fixed 18` alias, never another `d` (`fieldKindOfExprM`/`fieldKindOfExpr`'s own
    -- docstrings explain why: this DSL's `.wad`-kind pipeline hardcodes the 18-decimals `WAD`
    -- scale, so accepting e.g. `Fixed 6` here would silently mis-scale `⸢*⸣?`/`⌊/⌋?` instead of
    -- rejecting it) — a genuinely non-18-decimals token must be authored as a hand-written
    -- `ContractM` contract (bypassing this grammar entirely), same as `Escrow.release` already
    -- does for its cross-contract `exec` call. -/
    let e ← Lean.Elab.Term.elabType ty
    match ← Lsc.Deriving.fieldKindOfExprM e with
    | some (.interface iface) => return .interface iface
    | some .wad => return .wad
    | _ => throwErrorAt ty "unsupported `tx` parameter type `{ty.getId}` \
        — expected one of `UInt256`/`Bool`/`Address`/`Wei`/`Wad`, or an alias resolving to \
        `Wad`/`Fixed 18` exactly (e.g. `Token.Amount`)"

/-- Elaborate one `(name : ty)` parameter group into `(paramNameString, FieldKind)`. -/
def elabTxParam : TSyntax `lscTxParam → TermElabM (String × Lsc.Deriving.FieldKind)
  | `(lscTxParam| $x:ident : $ty:ident) => do
      let k ← elabLscTyIdent ty
      return (x.getId.toString, k)
  | stx => throwErrorAt stx "Syntax.elabTxParam: unsupported `lscTxParam` node"

/-- The companion half of `elabTxParam`: pulls out the parameter's *un-resolved* `(name, ty)`
syntax pair verbatim (no `FieldKind` resolution at all) — used only by a cross-contract `tx`'s
`flushContractTxs` branch (`Lsc.Deriving.contractTxParamTyExt`, below) so it can rebuild the real
callable `def`'s parameter binder with the author's *exact* declared type (e.g. `Token.Amount`),
not `FieldKind.leanTypeStx`'s generic `Lsc.Wad` — see `Fixed`'s docstring
(`Lsc/Lib/Wad/Syntax.lean`) for why that distinction is exactly what makes mixing up two
different tokens' amounts a compile error at an `exec`/`read` call site. -/
def txParamNameAndTyIdent : TSyntax `lscTxParam → Option (String × Lean.Ident)
  | `(lscTxParam| $x:ident : $ty:ident) => some (x.getId.toString, ty)
  | _ => none

/-- Stash `fnName`'s parameters' declared types, resolved to their fully-qualified `Name`s, into
`Lsc.Deriving.contractParamTyExt` — shared by `tx`'s and `view`'s elaborators (both use the same
`lscTxParam` parameter grammar), see that extension's docstring for who consults this, why a
fully-qualified `Name` (rather than the raw `ty` syntax as written) is stored, and why. -/
def stashParamTys (fnName : Name) (paramsStx : Array (TSyntax `lscTxParam)) : CommandElabM Unit := do
  let paramTys ← liftTermElabM <|
    (paramsStx.toList.filterMap txParamNameAndTyIdent).mapM fun (n, ty) => do
      let e ← Lean.Elab.Term.elabType ty
      let some tyName := e.constName?
        | throwErrorAt ty "Syntax.stashParamTys: expected `{ty}` to resolve to a named type"
      return (n, tyName)
  modifyEnv fun env =>
    Lsc.Deriving.contractParamTyExt.modifyState env fun m => m.insert fnName paramTys

end Lsc.Syntax
