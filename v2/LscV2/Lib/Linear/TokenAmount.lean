import LscV2.Types

/-!
  Linear type lib stub — see `docs/spec_idea_2/extensions/linear-types/`.
-/

namespace LscV2.Lib.Linear

structure TokenAmount where
  raw : UInt256
  deriving Repr, DecidableEq, Inhabited

end LscV2.Lib.Linear
