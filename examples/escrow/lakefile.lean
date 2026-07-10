import Lake
open Lake DSL

package escrow where
  version := v!"0.1.0"

require lsc from "../.."

lean_lib Escrow where
  srcDir := "src"
  roots := #[`Escrow]

lean_lib EscrowProofs where
  srcDir := "test"
  roots := #[`EscrowProofs]

lean_lib EscrowTheorem where
  srcDir := "test"
  roots := #[`EscrowTheorem]

lean_lib EscrowCompileTest where
  srcDir := "test"
  roots := #[`EscrowCompileTest]

lean_exe review where
  root := `ReviewMain
  supportInterpreter := true
