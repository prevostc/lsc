import LscV2.Checks
import LscV2.AST
import LscV2.Syntax
import LscV2.Eval
import Lean

/-!
  Contract command elaboration (IMPLEMENTATION Step 7).

  Generic `contract $name where …` generators live here. Counter-specific
  codegen belongs in `examples/counter/`, not in this module.
-/

namespace LscV2.ContractElab

/-- Placeholder until generic generators are wired; see strategy-reset plan Phase 2. -/
def contractElabPending : String := "contract command elaboration not yet implemented"

end LscV2.ContractElab
