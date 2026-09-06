import Lsc.Compiler.Proof.Core
import Lsc.Examples.Vault

set_option linter.unusedSimpArgs false

/-!
`CallFree` for Vault entrypoints that do not `call`. `deposit` / `withdraw` still contain
`Stmt.call`; `constructor` is excluded by `f.kind ≠ .constructor`.
-/

namespace Lsc.Compiler

open Lsc

theorem vault_previewDeposit_callFree : CallFree Vault.previewDeposit.core := by
  simp [CallFree, M1Frag, M1Op, M1Stmt, M1Cond, Vault.previewDeposit.core]

theorem vault_previewRedeem_callFree : CallFree Vault.previewRedeem.core := by
  simp [CallFree, M1Frag, M1Op, M1Stmt, M1Cond, Vault.previewRedeem.core]

theorem vault_pause_callFree : CallFree Vault.pause.core := by
  simp [CallFree, M1Frag, M1Op, M1Stmt, M1Cond, Vault.pause.core]

theorem vault_unpause_callFree : CallFree Vault.unpause.core := by
  simp [CallFree, M1Frag, M1Op, M1Stmt, M1Cond, Vault.unpause.core]

theorem vault_paused?_callFree : CallFree Vault.paused?.core := by
  simp [CallFree, M1Frag, M1Op, M1Stmt, M1Cond, Vault.paused?.core]

theorem vault_decimals_callFree : CallFree Vault.decimals.core := by
  simp [CallFree, M1Frag, M1Op, M1Stmt, M1Cond, Vault.decimals.core]

end Lsc.Compiler
