import LscV2.Arithmetic

/-!
  Wad fixed-point lib — stub until AMM milestone.
  See `docs/spec_idea_2/extensions/MATH.md`.
-/

namespace LscV2.Lib.Wad

structure Wad where
  raw : UInt256
  deriving Repr, DecidableEq

end LscV2.Lib.Wad
