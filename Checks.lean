import Lsc.Examples.Counter
import Lsc.Examples.Token
import Lsc.Examples.TokenProofs
import Lsc.Examples.TokenSecurity
import Lsc.Examples.VaultSecurity
import Lsc.Security.Wealth
import Lsc.Compiler.Proof.Counter
import Lsc.Compiler.Proof.Token
import Lsc.Compiler.Proof.Dispatch
import Lsc.Compiler.Proof.CoreExt
import Lsc.Compiler.Proof.CoreExtSim
import Lsc.Compiler.Proof.Vault
import Lsc.Compiler.EndToEnd
import Lsc.Compiler.EndToEndExt
import Lsc.Compiler.Proof.DispatchExt
import Lsc.Examples.TokenEndToEnd
import Lsc.Examples.VaultEndToEnd
import Lsc.Compiler.Proof.ProgressCore

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
