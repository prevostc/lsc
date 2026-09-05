import Lsc

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

/-- info: 'Vault.deposit.core_denote' depends on axioms: [propext] -/
#guard_msgs in #print axioms Vault.deposit.core_denote

/-- info: 'Token.transfer_conserves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Token.transfer_conserves
