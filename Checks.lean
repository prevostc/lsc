import Examples.Counter
import Examples.Token
import Examples.TokenProofsTheorems
import Examples.TokenSecurityTheorems
import Examples.VaultSecurityTheorems
import Lsc.Security.WealthTheorems
import Examples.CounterCompileTheorems
import Examples.TokenCompileTheorems
import Lsc.Compiler.DispatchTheorems
import Lsc.Compiler.CoreTheorems
import Lsc.Compiler.CoreExtSimTheorems
import Examples.VaultCompileTheorems
import Examples.AmmCompileTheorems
import Lsc.Compiler.EndToEndTheorems
import Lsc.Compiler.EndToEndExtTheorems
import Lsc.Compiler.DispatchExtTheorems
import Examples.TokenEndToEndTheorems
import Examples.VaultEndToEndTheorems
import Examples.AmmEndToEndTheorems
import Lsc.Compiler.ProgressCoreTheorems
import Lsc.Compiler.ConstructorTheorems
import Lsc.Compiler.DeployTheorems

/-!
# Axiom footprint checks

Every certificate and end-to-end theorem must depend on nothing beyond the three standard
axioms. `#guard_msgs` turns a widened footprint into a build error (see
`docs/architecture/TRUSTED_COMPUTING_BASE.md`).
-/

/-- info: 'Counter.increment.core_denote' depends on axioms: [propext] -/
#guard_msgs in #print axioms Counter.increment.core_denote

/-- info: 'Token.transfer.core_denote' depends on axioms: [propext] -/
#guard_msgs in #print axioms Token.transfer.core_denote

/-- info: 'Token.transfer_conserves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Token.transfer_conserves

/-- info: 'Token.token_no_unauthorized_extraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Token.token_no_unauthorized_extraction

/-- info: 'Token.token_solvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Token.token_solvent

/-- info: 'Vault.vault_solvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Vault.vault_solvent

/-- info: 'Lsc.Security.no_unauthorized_extraction' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lsc.Security.no_unauthorized_extraction

/-- info: 'Vault.vault_no_unauthorized_extraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Vault.vault_no_unauthorized_extraction

/-- info: 'Lsc.Compiler.counter_increment_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.counter_increment_correct

/-- info: 'Lsc.Compiler.counter_incrementBy_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.counter_incrementBy_correct

/-- info: 'Lsc.Compiler.counter_decrement_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.counter_decrement_correct

/-- info: 'Lsc.Compiler.counter_get_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.counter_get_correct

/-- info: 'Lsc.Compiler.counter_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.counter_correct

/-- info: 'Lsc.Compiler.token_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.token_correct

/-- info: 'Lsc.Compiler.toYulFn_correct_callFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.toYulFn_correct_callFree

/-- info: 'Lsc.Compiler.toYulFn_correct_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.toYulFn_correct_ext

/-- info: 'Lsc.Compiler.vault_correct_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.vault_correct_ext

/-- info: 'Lsc.Compiler.core_sim_ext_callFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.core_sim_ext_callFree

/-- info: 'Lsc.Compiler.runtimeBlock_correct_callFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.runtimeBlock_correct_callFree

/-- info: 'Lsc.Compiler.counter_dispatch_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.counter_dispatch_correct

/-- info: 'Lsc.Compiler.token_dispatch_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.token_dispatch_correct

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

/-- info: 'Vault.vault_abs_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Vault.vault_abs_nonvacuous

/-- info: 'Vault.vault_bytecode_no_unauthorized_extraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Vault.vault_bytecode_no_unauthorized_extraction

/-- info: 'Vault.vault_bytecode_no_unauthorized_extraction_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Vault.vault_bytecode_no_unauthorized_extraction_exists

/-- info: 'Vault.vault_bytecode_solvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Vault.vault_bytecode_solvent

/-- info: 'Vault.vault_bytecode_solvent_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Vault.vault_bytecode_solvent_exists

/-- info: 'Token.token_bytecode_no_unauthorized_extraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Token.token_bytecode_no_unauthorized_extraction

/-- info: 'Token.token_bytecode_no_unauthorized_extraction_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Token.token_bytecode_no_unauthorized_extraction_exists

/-- info: 'Token.token_bytecode_solvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Token.token_bytecode_solvent

/-- info: 'Token.token_bytecode_solvent_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Token.token_bytecode_solvent_exists

/-- info: 'Lsc.Compiler.constructor_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.constructor_correct

/-- info: 'Lsc.Compiler.bytecode_deploy_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.bytecode_deploy_correct

/-- info: 'Token.token_deploy_then_no_unauthorized_extraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Token.token_deploy_then_no_unauthorized_extraction

/-! ### Multi-binding S2 / AMM bytecode (appended) -/

/-- info: 'Lsc.Compiler.amm_correct_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.amm_correct_ext

/-- info: 'Amm.amm_bytecode_no_unauthorized_extraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Amm.amm_bytecode_no_unauthorized_extraction
