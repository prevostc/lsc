import Examples.Counter.Theorems
import Examples.Token.Theorems
import Examples.Vault.Theorems
import Examples.Cpamm.Theorems
import Examples.WETH.Theorems
import Lsc.Security.WealthTheorems
import Lsc.Security.InvariantTheorems
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
`docs/internals/TRUSTED_COMPUTING_BASE.md`). Agents update this file when a
pinned theorem is added or renamed; the commit message records what moved.
-/

/-- info: 'Lsc.Security.no_unauthorized_extraction' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lsc.Security.no_unauthorized_extraction

/-- info: 'Counter.increment_adds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Counter.increment_adds

/-- info: 'Token.transfer_conserves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Token.transfer_conserves

/-- info: 'Token.token_no_unauthorized_extraction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Token.token_no_unauthorized_extraction

/-- info: 'Token.token_solvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Token.token_solvent

/-- info: 'Token.erc20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Token.erc20

/-- info: 'Vault.vault_solvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Vault.vault_solvent

/-- info: 'Vault.vault_no_unauthorized_extraction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Vault.vault_no_unauthorized_extraction

/-- info: 'Vault.deposit_holdings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Vault.deposit_holdings

/-- info: 'Vault.withdraw_holdings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Vault.withdraw_holdings

/-- info: 'Cpamm.swap0for1_k' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Cpamm.swap0for1_k

/-- info: 'Cpamm.cpamm_solvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cpamm.cpamm_solvent

/-- info: 'Cpamm.cpamm_no_unauthorized_extraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cpamm.cpamm_no_unauthorized_extraction

/-- info: 'WETH.weth_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WETH.weth_exact

/-- info: 'WETH.weth_backed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WETH.weth_backed

/-- info: 'WETH.weth_no_unauthorized_extraction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms WETH.weth_no_unauthorized_extraction

/-- info: 'Lsc.Security.inv_of_reachable' does not depend on any axioms -/
#guard_msgs in #print axioms Lsc.Security.inv_of_reachable

/-- info: 'WETH.deposit_delta' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms WETH.deposit_delta

/-- info: 'WETH.withdraw_delta' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms WETH.withdraw_delta

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
