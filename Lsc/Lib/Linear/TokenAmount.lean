import Lsc.Types

/-!
  Linear type lib stub — see `docs/extensions/linear-types/`.
-/

namespace Lsc.Lib.Linear

structure TokenAmount where
  raw : UInt256
  deriving Repr, DecidableEq, Inhabited

end Lsc.Lib.Linear
