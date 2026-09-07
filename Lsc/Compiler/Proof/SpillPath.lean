import Lsc.Compiler.Bytecode
import Lsc.Compiler.Proof.Layout
import YulEvmCompiler.Optimizer.Spec.MemoryGuard
import YulEvmCompiler.Optimizer.Implementation.MemorySpillStateSound

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
`compileBlock` path split and scratch transport for powdr spilling.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open YulEvmCompiler.Optimizer
open YulEvmCompiler.Optimizer.MemorySpillSelect

/-- If `compileRuntime` emitted `is`, that list is either the memoryguard-erased
compile of the runtime or a successful powdr spill of the uniquified runtime
when erasure is rejected (`DUP17+`). The disjuncts are exclusive. -/
theorem compileInstr_elim {b : YBlock} {is : List Instr}
    (h : (compileErased b <|> compileSpilled b) = some is) :
    compileErased b = some is ∨
      (compileErased b = none ∧ compileSpilled b = some is) := by
  cases he : compileErased b with
  | some is0 =>
    have : some is0 = some is := by
      simpa [he] using h
    cases this
    exact Or.inl rfl
  | none =>
    exact Or.inr ⟨rfl, by simpa [he] using h⟩

/-- `compileBlock` is the erase path used by exported bytecode theorems. -/
theorem compileBlock_elim {b : YBlock} {is : List Instr}
    (h : compileBlock b = some is) :
    compileErased b = some is := by
  simpa [compileBlock] using h

/-- A spilled compile is a `spillBlock?` of the uniquified runtime together
with an ordinary compile of that spilled block. Storage, logs, halt, and
environment of a matching Yul run agree with the guarded source except on
compiler scratch (`R_of_scratchRel`). -/
theorem compileSpilled_inv {b : YBlock} {is : List Instr}
    (h : compileSpilled b = some is) :
    ∃ r, spillRuntime? b = some r ∧ compile r.block = some is := by
  unfold compileSpilled at h
  split at h
  · next r hr => exact ⟨r, hr, h⟩
  · cases h

theorem guardedExternals_none (base reserved : Nat) :
    GuardedExternals ExternalCalls.none ExternalCreates.none base reserved where
  calls_insensitive := by
    intro req left right response hrel
    simp [ExternalCalls.none]
  creates_insensitive := by
    intro req left right response hrel
    simp [ExternalCreates.none]

theorem R_of_scratchRel {S X E ε} {c : ContractDef} {Γ : ContractSchema S X E ε}
    {κ : List UInt8 → U256} {w : World S X E} {base reserved : Nat}
    {st st' : EvmState} (hR : R c Γ κ w st)
    (h : ScratchRel base reserved st st') : R c Γ κ w st' := by
  rcases hR with ⟨hs, hlog, hκ, hwf⟩
  refine ⟨?_, ?_, ?_, hwf⟩
  · simpa [MemorySpillStateSound.ScratchRel.storage_eq h] using hs
  · have henv := MemorySpillStateSound.ScratchRel.env_eq h
    have hlogs := MemorySpillStateSound.ScratchRel.logs_eq h
    unfold logsRel selfLogs at hlog ⊢
    simpa [henv, hlogs] using hlog
  · have henv := MemorySpillStateSound.ScratchRel.env_eq h
    simpa [henv] using hκ

end Lsc.Compiler
