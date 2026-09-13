-- slice 4: Example imports restored when Examples compile on the oracle model.
-- import Examples.Counter.Theorems
-- import Examples.Token.Theorems
-- import Examples.Vault.Theorems
-- import Examples.Amm.Theorems
-- import Examples.Cpamm.Theorems
import Lsc.Security.WealthTheorems
import Lsc.Compiler.DispatchTheorems
import Lsc.Compiler.CoreTheorems
import Lsc.Compiler.CoreExtSimTheorems
import Lsc.Compiler.EndToEndTheorems
import Lsc.Compiler.EndToEndExtTheorems
import Lsc.Compiler.DispatchExtTheorems
import Lsc.Compiler.ProgressCoreTheorems
import Lsc.Compiler.ConstructorTheorems
import Lsc.Compiler.DeployTheorems

/-!
# Axiom footprint checks

Every certificate and end-to-end theorem must depend on nothing beyond the three standard
axioms. `#guard_msgs` turns a widened footprint into a build error (see
`docs/internals/TRUSTED_COMPUTING_BASE.md`).
-/

/-- info: 'Lsc.Security.no_unauthorized_extraction' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lsc.Security.no_unauthorized_extraction

-- slice 4: Counter / Token / Vault / Amm / Cpamm example pins.

/-- info: 'Lsc.Compiler.toYulFn_correct_callFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.toYulFn_correct_callFree

/-- info: 'Lsc.Compiler.toYulFn_correct_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.toYulFn_correct_ext

/-- info: 'Lsc.Compiler.core_sim_ext_callFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.core_sim_ext_callFree

/-- info: 'Lsc.Compiler.runtimeBlock_correct_callFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.runtimeBlock_correct_callFree

/-- info: 'Lsc.Compiler.bytecode_call_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.bytecode_call_correct

/-- info: 'Lsc.Compiler.runtimeBlock_correct_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.runtimeBlock_correct_ext

/-- info: 'Lsc.Compiler.bytecode_call_correct_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.bytecode_call_correct_ext

/-- info: 'Lsc.Compiler.yul_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.yul_progress

/-- info: 'Lsc.Compiler.evmCallRunExtAll_of_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.evmCallRunExtAll_of_progress

/-- info: 'Lsc.Compiler.constructor_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.constructor_correct

/-- info: 'Lsc.Compiler.bytecode_deploy_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.bytecode_deploy_correct
