import Stdlib.ERC20
import Stdlib.SafeERC20
import Stdlib.Scales

/-!
# Stdlib — user-importable features above the language

`Stdlib` sits between `Lsc` (language, compiler, security model) and `Examples`
(protocol instances). It must not import `Examples`. `Lsc` must not import `Stdlib`.
-/
