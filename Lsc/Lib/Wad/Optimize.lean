import Lsc.Lib.Wad.Syntax
import Lsc.Compile.IR

namespace Lsc.Wad

open Lsc.Compile.IR (Expr Stmt)

/-- Lower a `Wad.Expr` to flat IR, mirroring `Wei.lowerExpr`.

`.addChecked`/`.addCheckedNat`/`.subChecked` lower onto the same integer
add/sub primitives `Wei` uses — at the raw-`UInt256` level these are
identical; only the *decoding* of the raw value into a decimal differs, and
IR doesn't need to know about that.

`.mulHalfUpChecked a b` lowers to `(a * b + WAD / 2) / WAD` using the new
`Compile.IR.Expr.mul`/`.div` primitives (which lower straight onto EVM's
native `MUL`/`DIV` opcodes, see `Bytecode/Codegen.lean`/`Yul.lean`).
`.divDownChecked a b` lowers to `(a * WAD) / b`.

**Accepted overflow limitation (mirrors `Wei`'s existing precedent):** just
like `Wei.lowerExpr`'s `.addChecked`/`.subChecked` cases lower straight onto
raw `IR.Expr.add`/`.sub` with no IR-level overflow guard (only the
specialised `lowerAddCheckedNatStorage`/`lowerLetBind` path emits an
`ifRevert` check), this lowering does not synthesize a 512-bit-safe
overflow check for `a.raw * b.raw` either. EVM's `MUL` computes the product
mod 2^256, so if the *true* (unbounded) product of two `Wad`s' raw
`UInt256`s exceeds 2^256, the lowered bytecode silently wraps instead of
reverting with `Overflow` the way `Wad.mulHalfUpChecked`'s `Except`-based
pure evaluator (`Eval.lean`, used by `Wad.eval`/off-chain simulation) does.
Closing this gap fully requires a 512-bit "full-precision" multiply
technique (e.g. the standard `MULMOD`-based `mulDiv` idiom used by
OpenZeppelin/Solady) synthesized at the `IR.Stmt` level (extra `letBind`s +
`ifRevert`s), which is a separate, larger follow-up — tracked here rather
than silently shipped: any `Wad` contract whose multiplicands can realistically
reach the ~2^128 range (i.e. large enough that `raw_a * raw_b` can exceed
2^256) needs that follow-up before its bytecode can be trusted for
overflow-safety; today's lowering is exact for the common case where the
product itself fits in 256 bits (true for any realistic token/interest-rate
Wad values, e.g. both operands well under 10^39). -/
partial def lowerExpr (fieldSlot mapFieldSlot : Ident → Option Nat) (e : Expr) : Except String Compile.IR.Expr :=
  match e with
  | .lit n => .ok (Compile.IR.Expr.lit n)
  | .var name => .ok (Compile.IR.Expr.local name)
  | .storageGet field =>
    match fieldSlot field with
    | some s => .ok (Compile.IR.Expr.sload s)
    | none => .error s!"unknown storage field {field}"
  | .mapGet field key => do
    match mapFieldSlot field with
    | none => .error s!"unknown mapping field {field}"
    | some base =>
      let keyIr ← match key with
        | .caller => .ok (Compile.IR.Expr.local "caller")
        | .var name => .ok (Compile.IR.Expr.local name)
      .ok (Compile.IR.Expr.dynSload (Compile.IR.Expr.mapSlot base keyIr))
  | .addChecked a b => do
    let a' ← lowerExpr fieldSlot mapFieldSlot a
    let b' ← lowerExpr fieldSlot mapFieldSlot b
    .ok (Compile.IR.Expr.add a' b')
  | .addCheckedNat e n => do
    let e' ← lowerExpr fieldSlot mapFieldSlot e
    .ok (Compile.IR.Expr.add e' (Compile.IR.Expr.lit n))
  | .subChecked a b => do
    let a' ← lowerExpr fieldSlot mapFieldSlot a
    let b' ← lowerExpr fieldSlot mapFieldSlot b
    .ok (Compile.IR.Expr.sub a' b')
  | .mulHalfUpChecked a b => do
    let a' ← lowerExpr fieldSlot mapFieldSlot a
    let b' ← lowerExpr fieldSlot mapFieldSlot b
    let product := Compile.IR.Expr.mul a' b'
    let rounded := Compile.IR.Expr.add product (Compile.IR.Expr.lit (WAD / 2))
    .ok (Compile.IR.Expr.div rounded (Compile.IR.Expr.lit WAD))
  | .divDownChecked a b => do
    let a' ← lowerExpr fieldSlot mapFieldSlot a
    let b' ← lowerExpr fieldSlot mapFieldSlot b
    let scaledNumer := Compile.IR.Expr.mul a' (Compile.IR.Expr.lit WAD)
    .ok (Compile.IR.Expr.div scaledNumer b')

end Lsc.Wad
