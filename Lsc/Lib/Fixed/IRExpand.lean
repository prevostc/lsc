import Lsc.Compile.IR
import Lsc.Compile.IR.Builder
import Lsc.Lib.Math.SqrtAlgo

/-!
# Expand fixed-point `sqrtDown` / `min` into primitive IR

User-space `Fixed.Expr.sqrtDownChecked` and `.min` lower to primitive IR (no `sqrtDown` / `min`
IR nodes). Sqrt instantiates the same representation-polymorphic implementation used by the
library's executable semantics. -/

namespace Lsc.Fixed.IRExpand

open Lsc.Compile.IR
open Lsc.Compile.IR.Builder

private abbrev E := Expr

def irOps : Lsc.Math.SqrtAlgo.Ops Expr where
  lit := .lit
  add := .add
  sub := .sub
  mul := .mul
  div := .div
  gt := .gt
  shr := .shr

/-- `floor(sqrt(x * scale))` at raw-word level. -/
def expandSqrtDown (scale : Nat) (x : E) : E :=
  let a := if scale == 1 then x else .mul x (.lit scale)
  Lsc.Math.SqrtAlgo.sqrt irOps a

def irSharing : Lsc.Math.SqrtAlgo.Sharing Build Expr where
  bind build tag value := build.bind tag value

/-- Interpret the single shared sqrt program as linear primitive-IR bindings. -/
def sqrtBinds (a : E) (build : Build) : Build × E :=
  Lsc.Math.SqrtAlgo.sqrtWith irOps irSharing build a

/-- Linear statement-level `floor(sqrt(x * scale))`, ending in `tail result`. -/
def expandSqrtDownStmt (scale : Nat) (x : E) (fresh : Fresh) (tail : E → Stmt) : Stmt :=
  let a := if scale == 1 then x else .mul x (.lit scale)
  let (build, result) := sqrtBinds a { fresh }
  build.finish (tail result)

/-- Solady branchless minimum on raw words. -/
def expandMin (a b : E) : E :=
  .xor a (.mul (.xor a b) (.lt b a))

end Lsc.Fixed.IRExpand
