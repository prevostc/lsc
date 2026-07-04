import Lsc.Arithmetic

/-!
  Wad fixed-point lib — stub until AMM milestone.
  See `docs/extensions/MATH.md`.
-/

namespace Lsc.Lib.Wad

structure Wad where
  raw : UInt256
  deriving Repr, DecidableEq

end Lsc.Lib.Wad
