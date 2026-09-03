import Lake
open Lake DSL

package fixedmath where
  version := v!"0.1.0"

require lsc from "../.."

lean_lib FixedMath where
  srcDir := "src"
  roots := #[`FixedMath]

lean_lib FixedMathTheorem where
  srcDir := "test"
  roots := #[`FixedMathTheorem]

lean_exe review where
  root := `ReviewMain
  supportInterpreter := true
