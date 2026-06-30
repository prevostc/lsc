import Lake
open Lake DSL

package counter where
  version := v!"0.1.0"

require lscV2 from "../.."

lean_lib Counter where
  srcDir := "src"
  roots := #[`Counter]

lean_lib CounterDSL where
  srcDir := "src"
  roots := #[`CounterDSL]

lean_lib CounterProofs where
  srcDir := "test"
  roots := #[`CounterProofs]

lean_lib CounterTheorem where
  srcDir := "test"
  roots := #[`CounterTheorem]
