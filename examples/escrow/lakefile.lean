import Lake
open Lake DSL

package escrow where
  version := v!"0.1.0"

require lsc from "../.."

-- `Token` lives in this same package (not a separate sibling example) since `Escrow` is its one
-- and only real caller — `exec Token.transfer(..);`, see `src/Escrow.lean`'s `import Token`.
-- Kept as its own `lean_lib`/`lean_lib ... Theorem` pair (rather than folded into `Escrow`'s),
-- exactly mirroring the module boundaries `Token` had as a separate sibling package, just
-- without the extra package indirection.
lean_lib Token where
  srcDir := "src"
  roots := #[`Token]

lean_lib TokenProofs where
  srcDir := "test"
  roots := #[`TokenProofs]

lean_lib TokenTheorem where
  srcDir := "test"
  roots := #[`TokenTheorem]

lean_lib Escrow where
  srcDir := "src"
  roots := #[`Escrow]

lean_lib EscrowProofs where
  srcDir := "test"
  roots := #[`EscrowProofs]

lean_lib EscrowTheorem where
  srcDir := "test"
  roots := #[`EscrowTheorem]
