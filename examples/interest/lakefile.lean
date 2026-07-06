import Lake
open Lake DSL

package interest where
  version := v!"0.1.0"

require lsc from "../.."

lean_lib Interest where
  srcDir := "src"
  roots := #[`Interest]

lean_lib InterestProofs where
  srcDir := "test"
  roots := #[`InterestProofs]

lean_lib InterestTheorems where
  srcDir := "test"
  roots := #[`InterestTheorems]
