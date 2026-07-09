import Lake
open Lake DSL

package token where
  version := v!"0.1.0"

require lsc from "../.."

lean_lib Token where
  srcDir := "src"
  roots := #[`Token]

lean_lib TokenProofs where
  srcDir := "test"
  roots := #[`TokenProofs]

lean_lib TokenTheorem where
  srcDir := "test"
  roots := #[`TokenTheorem]
