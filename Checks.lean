import Lsc.Examples.Counter
import Lsc.Examples.Token
import Lsc.Examples.TokenProofs
import Lsc.Examples.TokenSecurity
import Lsc.Examples.VaultSecurity
import Lsc.Security.Wealth

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
