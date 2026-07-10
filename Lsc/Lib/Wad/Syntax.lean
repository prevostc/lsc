import Lsc.Core.UInt256
import Lsc.Core.MapKey
import Lsc.Types
import Lean

namespace Lsc.Wad

/-- Fixed-point scale: 18 decimal places, mirroring Solidity's `WAD` convention.
`1.0` is represented as `WAD` raw units. -/
def WAD : Nat := 1000000000000000000

/-- `scale d = 10^d` — the raw-unit count representing `1.0` at `d` decimal places. `WAD` is
just `scale 18`, kept as its own `def` for the many existing call sites/proofs that already
name it directly. -/
def scale (d : Nat) : Nat := 10 ^ d

@[simp] theorem scale_eighteen : scale 18 = WAD := rfl

/-- The default, generic "no specific token" tag — `Wad` (below) uses this, so every existing
untagged use of `Wad`/`Fixed d` (internal math, `Interest`'s accounting, storage-internal
mappings, ...) keeps meaning exactly what it always did: "some `d`-decimals fixed-point
quantity, not tied to any one token." Uninhabited (zero constructors) since no value of this
type is ever actually constructed — it only ever appears as a phantom type-level marker, never
as real data (see `Fixed`'s docstring). -/
inductive Untagged where

/-- A decimals-*and*-token-indexed fixed-point number: `Fixed d tag` represents a value scaled by
`10^d`, the same raw-`UInt256`-under-the-hood representation regardless of `d`/`tag` (EVM
storage/ABI encoding is completely unit-agnostic — every `Fixed _ _` is a wire-identical 32-byte
word; both `d` and `tag` are purely Lean-type-level markers, carrying no runtime data of their
own). This is what makes both load-bearing for safety without costing anything at codegen time:

- Two `Fixed d1 _`/`Fixed d2 _` values are simply *different Lean types* whenever `d1 ≠ d2`, so
  passing one where the other is expected (e.g. a caller's own accounting unit vs. a specific
  ERC20-shaped token's declared `decimals`) is a compile error, not a silent runtime bug — see
  `Fixed.convert` below for the one sanctioned, explicit way to cross between two different `d`s
  (same `tag` only).
- Two `Fixed _ tag1`/`Fixed _ tag2` values are likewise different Lean types whenever `tag1` and
  `tag2` are different nominal marker types (typically one fresh, uninhabited `inductive Tag`
  declared per token via `declare_token_amount`, below) — so mixing up *which token* an amount
  belongs to (even between two tokens that happen to share the same `decimals`) is *also* a
  compile error, not just a differently-named `abbrev` for the same underlying type. There is
  deliberately no generic `tag1 → tag2` conversion (unlike `Fixed.convert`'s decimals-crossing):
  swapping one token's amount for another's isn't a scaling operation, it needs real
  exchange-rate/business logic that has no place in this framework — see `Fixed.retag`'s
  docstring for the one, very restricted, compiler-internal exception.

`Wad` (below) is exactly `Fixed 18 Untagged`; every existing `Wad`-typed field/proof in this
codebase keeps working unchanged, since `Wad` is a plain `abbrev`, not a new type. -/
structure Fixed (decimals : Nat) (tag : Type) where
  raw : UInt256

/-- Hand-written rather than `deriving` — every auto-derived handler below would ask for the
corresponding instance (`[Repr tag]`/`[BEq tag]`/...) on the purely phantom `tag` parameter, as
if it carried real data, which fails for every uninhabited tag (`Untagged`, or any token's own
generated `Tag`, see `declare_token_amount`) that has no such instance. Each of these only ever
needs to look at `raw` — `tag` never holds any data at all. -/
instance {d : Nat} {tag : Type} : Repr (Fixed d tag) := ⟨fun a _ => reprPrec a.raw 0⟩

instance {d : Nat} {tag : Type} : BEq (Fixed d tag) := ⟨fun a b => a.raw == b.raw⟩

instance {d : Nat} {tag : Type} : DecidableEq (Fixed d tag) := fun a b =>
  decidable_of_iff (a.raw = b.raw) (by constructor <;> (intro h; cases a; cases b; simp_all))

/-- `w.raw.toNat` under a shorter name — proofs about `Fixed`/`Wad` values constantly need to
state arithmetic side-conditions and derived-storage equations in terms of this plain `Nat`
(overflow/underflow bounds, `Mapping` update laws, ...), and the repeated `.raw.toNat` projection
chain hurts readability at that volume. `@[reducible]` (like `Wad`/`mkNat` above) so it stays
fully transparent to `omega`/`simp`/`rfl`/`apply` — this only ever abbreviates the exact same
`Nat`, never a new opaque projection. -/
abbrev Fixed.n {d : Nat} {tag : Type} (w : Fixed d tag) : Nat := w.raw.toNat

/-- `1 Wad = 1e18` raw units, generically tagged (see `Untagged`'s docstring) — the original,
18-decimals-specific fixed-point type most of this codebase's `Wad`-kind storage fields/`tx`
parameters use. Kept as a plain `abbrev` (fully reducible/interchangeable with `Fixed 18
Untagged`) rather than a fresh `structure`, so every existing `Wad`-typed declaration, proof, and
the `Lang/Derive.lean` `FieldKind.wad` detection continue to work with zero changes. -/
abbrev Wad := Fixed 18 Untagged

def mkNat {d : Nat} {tag : Type} (n : Nat) : Fixed d tag := ⟨BitVec.ofNat 256 n⟩

/-- Round-tripping a `Fixed d tag`'s own raw `Nat` back through `mkNat` is the identity — needed
whenever a checked op's result happens to land back on a value's *original* raw representation
(e.g. the degenerate self-transfer case in `EscrowProofs.runTransferOk`/`TokenProofs.runTransferOk`
below). Generic over `d`/`tag` so both `Wad` and every `declare_token_amount`-declared `Amount`
share the one proof. -/
@[simp] theorem Fixed.mkNat_self {d : Nat} {tag : Type} (w : Fixed d tag) :
    mkNat w.n = w := by
  simp [mkNat, Fixed.n, BitVec.ofNat_toNat]

/-- `1.0` at any `d`/`tag`, i.e. `scale d` raw units — `Wad.one` (`d = 18`, `tag = Untagged`) is
the original spelling, kept as its own `def` for existing call sites. -/
def Fixed.one {d : Nat} {tag : Type} : Fixed d tag := mkNat (scale d)

/-- `1.0` as a `Wad` (`WAD` raw units). -/
def one : Wad := mkNat WAD

/-- The **only** sanctioned way to move a value from one decimals-scale to another, *for the same
token* (`tag` is fixed on both sides — see `Fixed`'s docstring for why crossing `tag`s has no
generic equivalent at all) — deliberately not a `Coe`/`CoeTC` instance (an implicit coercion here
would silently reintroduce exactly the "tokens can have different decimals than Wad" bug this
type exists to rule out: every crossing between two different `d`s must be a visible, explicit
call site). Scales up by `10^(d2-d1)` (checked for overflow) when widening, or truncates down by
`10^(d1-d2)` (exact, cannot overflow) when narrowing — matching how real-world decimals
conversions between ERC20s are done (e.g. USDC's 6 decimals into an 18-decimals internal
ledger). -/
def Fixed.convert {d1 d2 : Nat} {tag : Type} (a : Fixed d1 tag) : Except ArithError (Fixed d2 tag) :=
  if d2 ≥ d1 then
    let factor := scale (d2 - d1)
    let widened := a.raw.toNat * factor
    if widened < 2 ^ 256 then .ok (mkNat widened)
    else .error .Overflow
  else
    let factor := scale (d1 - d2)
    .ok (mkNat (a.raw.toNat / factor))

/-- Reinterpret a `Fixed d t1` as a `Fixed d t2` — a raw bit-for-bit reinterpretation with **no**
general soundness guarantee of its own (unlike `Fixed.convert`, which actually rescales the raw
value; this changes nothing about `raw` at all). Deliberately **not** meant to be called directly
by DSL authors — it exists only as the one internal primitive `Lang/Syntax.lean`'s generated
`view` wrapper uses to re-attach a token's own declared `RetTy` tag (e.g. `Token.Amount`) onto a
value that came back from the tag-erased `Val Ty.wad` plumbing, which is sound *there* only
because the compiler statically knows, from the `view`'s own return-type annotation, exactly
which token's amount it just computed — see that call site for the only sanctioned use. Any other
use silently reintroduces the exact "which token is this amount really for" bug `Fixed`'s `tag`
parameter exists to rule out, so this is intentionally undocumented in user-facing reference
material and unnamed in any DSL grammar. -/
def Fixed.retag {d : Nat} {t1 t2 : Type} (a : Fixed d t1) : Fixed d t2 := ⟨a.raw⟩

/-- `declare_token_amount Amount` — run inside `namespace Foo`, right next to `Foo`'s storage
declaration — declares both a fresh, uninhabited nominal marker `Foo.Tag` and the requested
`Foo.Amount := Lsc.Wad.Fixed 18 Foo.Tag` `abbrev` in one step (see `Fixed`'s docstring for why a
*fresh* `Tag` per token, rather than the shared `Untagged` every plain `Wad` uses, is exactly what
makes `Foo.Amount` a genuinely different Lean type from every other token's own `Amount`, even
one with the exact same `18` decimals). The generated `Tag` is never meant to be referenced
directly by name anywhere else — only `Foo.Amount` (the `abbrev` this expands to) is part of a
token's public surface. -/
elab "declare_token_amount " id:ident : command => do
  let tagId := Lean.mkIdent (Lean.Name.mkSimple "Tag")
  Lean.Elab.Command.elabCommand (← `(
    inductive $tagId))
  Lean.Elab.Command.elabCommand (← `(abbrev $id := Lsc.Wad.Fixed 18 $tagId))
  Lean.Elab.Command.elabCommand (← `(
    instance : Inhabited $id where default := ⟨0⟩))

/--
Wad-domain expression fragment (`Expr .wad`), mirroring `Wei.Expr`'s shape
exactly — `Ty.wad`/`Val.wad` are registered in the core `Ty`/`Val`/
`ContractDSL` machinery (`Lsc/Lang/AST.lean`/`Lsc/Core/ContractM.lean`)
alongside `Ty.wei`/`Val.wei`, so `Wad.Expr` has the same `.var`/`.storageGet`
cases `Wei.Expr` does, letting a `Wad`-typed field be declared in a
contract's `storage:` block and read/written from a `tx { }` body exactly
like a `Wei` field. `.mapGet` additionally supports reading one entry of a
`Lsc.Mapping` storage field (see `Lsc/Core/Mapping.lean`). -/
inductive Expr where
  | lit : Nat → Expr
  | var : Ident → Expr
  | storageGet : Ident → Expr
  | mapGet : Ident → MapKey → Expr
  | addChecked : Expr → Expr → Expr
  | addCheckedNat : Expr → Nat → Expr
  | subChecked : Expr → Expr → Expr
  | mulHalfUpChecked : Expr → Expr → Expr
  | divDownChecked : Expr → Expr → Expr
  deriving Repr

/-- The `ArithError`s a given top-level `Expr` node can raise, mirroring
`Wei.arithErrors`. Used (once wired up, see the follow-up note above) by
`Lang.Checks.checkArithErrorCoverage`-style coverage checks. -/
def arithErrors : Expr → List ArithError
  | .addChecked _ _ => [.Overflow]
  | .addCheckedNat _ _ => [.Overflow]
  | .subChecked _ _ => [.Underflow]
  | .mulHalfUpChecked _ _ => [.Overflow]
  | .divDownChecked _ _ => [.DivisionByZero, .Overflow]
  | .lit _ => []
  | .var _ => []
  | .storageGet _ => []
  | .mapGet _ _ => []

end Lsc.Wad
