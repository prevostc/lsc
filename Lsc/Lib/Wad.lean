import Lsc.Lib.Wad.Syntax
import Lsc.Lib.Wad.Eval
import Lsc.Lib.Wad.Optimize

/-!
# `Wad`: 18-decimal fixed-point arithmetic

`Wad` wraps a raw `UInt256`, interpreted as a fixed-point decimal with 18
places (`1.0` is `10^18` raw units) — the same convention Solidity DeFi code
uses, and the type `docs/reference/AMM.md` uses for AMM reserve/fee storage.

Structurally this mirrors `Lsc.Wei` exactly: `Syntax.lean` holds the
structure, the `Expr` AST fragment and `arithErrors`; `Eval.lean` holds the
checked arithmetic operations and the `Expr` evaluator; `Optimize.lean` holds
IR lowering.

`Wad` adds two checked operations beyond what `Wei` needs, because
multiplying/dividing *scaled* fixed-point numbers isn't plain integer
multiply/divide:

* `mulHalfUpChecked` (surface syntax `⸢*⸣?`, per `docs/reference/AMM.md`) —
  multiplies two `Wad`s and divides the (36-decimal) product back down by
  `WAD`, rounding half-up.
* `divDownChecked` (surface syntax `⌊/⌋?`) — scales the numerator up by `WAD`
  before dividing, rounding down, so the quotient keeps 18 decimals instead
  of collapsing to an integer.

These operator names/notation are picked to match `docs/extensions/MATH.md`'s
`Wad.mulHalfUp`/`Wad.divDown` naming (with a `Checked` suffix on the `Expr`
constructors, mirroring `Fixed.Expr.addChecked`/`.subChecked`).

## First-class wiring (on par with `Wei`)

`Ty.wad`/`Val.wad` are registered in the core `Ty`/`Val`/`ContractDSL`
machinery (`Lsc/Lang/AST.lean`/`Lsc/Core/ContractM.lean`) alongside
`Ty.wei`/`Val.wei`, so a `Wad`-typed field can be declared in a
`deriving ContractStorage` structure and read/written from a `tx { }` body
exactly like a `Wei` field: `σ.field +? 1` / `σ.field -? 1` (checked
add/sub, shared with `Wei`) and `σ.field ⸢*⸣? other` / `σ.field ⌊/⌋? other`
(checked half-up multiply / round-down divide, `Wad`-only) all elaborate via
`Lsc/Lang/Syntax.lean`'s `lscExpr` grammar. `Wad.eval` is `ContractM`-based
(`Lsc/Lib/Wad/Eval.lean`), mirroring `Wei.eval` exactly.

`Lsc.Compile.IR.Expr` has `mul`/`div` primitives (lowering to EVM's native
`MUL`/`DIV` opcodes), and `Wad.Optimize.lowerExpr` uses them for
`.mulHalfUpChecked`/`.divDownChecked` — see that file's docstring for the
one accepted limitation (no synthesized 512-bit overflow guard on the
intermediate `a.raw * b.raw` product, mirroring the same lack of an
IR-level overflow guard `Wei.lowerExpr`'s `.addChecked`/`.subChecked` cases
already have).

`Lang.Checks.checkArithErrorCoverage` consults `Wad.arithErrors` via
`visitWadExpr`, mirroring `visitWeiExpr`, so a contract using `Wad`
arithmetic gets the same build-time "every arithmetic error variant must be
handled" enforcement `Wei` contracts get.
-/
