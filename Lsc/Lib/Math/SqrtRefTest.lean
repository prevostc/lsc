import Lsc.Lib.Math.SqrtRef
import Mathlib.Data.Nat.Sqrt

namespace Lsc.Math.SqrtRefTest

open Lsc.Math.SqrtRef

example : ozSqrt 0 = 0 := by native_decide
example : ozSqrt 1 = 1 := by native_decide
example : ozSqrt 10 = Nat.sqrt 10 := by native_decide
example : ozSqrt 100 = Nat.sqrt 100 := by native_decide
example : ozSqrt 255 = Nat.sqrt 255 := by native_decide
example : ozSqrt 256 = Nat.sqrt 256 := by native_decide
example : ozSqrt 65535 = Nat.sqrt 65535 := by native_decide
example : ozSqrtEvm evmMaxWord = Nat.sqrt evmMaxWord := by native_decide

end Lsc.Math.SqrtRefTest
