import Examples.Amm
import Lsc.Stdlib.ERC20
import Lsc.Compiler.Externals

/-!
AMM binding package used by the multi-binding `toYulFn_correct_ext` instance.
-/

namespace Lsc.Compiler

open Lsc.Stdlib

@[reducible] def ammBs (α : Abs IERC20.Ghost) : List (BindEnv IERC20 Amm.Storage Amm.Ext) :=
  [⟨α, Amm.token0B⟩, ⟨α, Amm.token1B⟩]

end Lsc.Compiler
