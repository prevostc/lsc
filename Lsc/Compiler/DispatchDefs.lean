import Lsc.Compiler.Correctness
import Lsc.Compiler.Yul
import YulEvmCompiler.Optimizer.Implementation.MemorySpill

/-!
S1 dispatcher conclusion and inversion of `runtimeBlock`.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc

/-- Dispatcher for the S1 call-free fragment: size guard, selector `switch`, then
the selected function's Yul (or `revert(0,0)`). The `Run` is of the
memoryguard-erased block (`if k {}` then the dispatcher): the raw AST
contains a parser-level `memoryguard` call that is not a Yul function. -/
def RuntimeBlockCorrectCallFree {S X E ε : Type} (c : ContractDef)
    (Γ : ContractSchema S X E ε) (κ : List UInt8 → U256)
    (yul : YBlock) (ctx : Ctx) (w : World S X E) (st0 : EvmState) : Prop :=
  ∃ stObs, RunCommitted (YulEvmCompiler.Optimizer.MemorySpill.eraseMemoryGuardStmts yul)
      st0 [] stObs .halt ∧
    match selectedFn c st0.env.calldata with
    | none => stObs.halted = some (.revert, []) ∧ R c Γ κ w stObs
    | some f =>
      match Tx.run (Core.denote Γ f.core (decodeArgs f st0.env.calldata).reverse) ctx w with
      | .ok (v, w') => haltSuccess f.ret v stObs.halted ∧ R c Γ κ w' stObs
      | .error e =>
        ∃ bytes, stObs.halted = some (.revert, bytes) ∧
          haltError c Γ e bytes ∧ R c Γ κ w stObs

/-- `runtimeBlock` is a `memoryguard` marker, a calldata-size guard, and a selector
`switch`. Used by the dispatcher proofs and by ABI transport (selector uniqueness). -/
theorem runtimeBlock_inv {c yul} (h : runtimeBlock c = some yul) :
    selectorsNodup c = true ∧
    ∃ cases, c.functions.mapM (entryCase c) = some cases ∧
      yul = memoryGuardStmt ::
        [YulSemantics.Stmt.block (emitGuardLt {} 4).stmts,
          YulSemantics.Stmt.switch
            (bop Op.shr [lit 224, bop Op.calldataload [lit 0]])
            cases (some [revert00])] := by
  unfold runtimeBlock at h
  cases hsel : selectorsNodup c
  · simp [hsel] at h
  · simp [hsel] at h
    cases hmap : c.functions.mapM (entryCase c) with
    | none => simp [hmap, Option.bind] at h
    | some cs =>
      simp [hmap, Option.bind] at h
      exact ⟨rfl, cs, rfl, h.symm⟩

end Lsc.Compiler
