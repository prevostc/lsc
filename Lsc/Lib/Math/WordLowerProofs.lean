import Lsc.Compile.IR.WordEvalLemmas
import Lsc.Lib.Math.LowerProofs

namespace Lsc.Math.WordLowerProofs

open Lsc.Compile.IR
open Lsc.Compile.IR.Builder
open Lsc.Math

/-- Word-level returned-value semantics for the compiler-seeded linear sqrt lowering.
The concrete used-name invariant justifies generated locals, while `StmtNoWrap` justifies
interpreting the Nat operations as EVM `UInt256` operations. -/
theorem eval_sqrtBinds_seeded_word (st : IRState) (word : WordState)
    (fresh : Fresh) (a : Expr)
    (build : Build) (result : Expr)
    (hbuild : Lsc.Fixed.IRExpand.sqrtBinds a { fresh } = (build, result))
    (ha : NameSafe { fresh } a)
    (hst : word.Agrees st) (hhalt : word.halt = .running)
    (hnw : StmtNoWrap { state := st } (build.finish (.ret result))) :
    ∃ wordResult value,
      evalStmtWord word (build.finish (.ret result)) = some wordResult ∧
      wordResult.halt = .returned value ∧
      value.toNat = SqrtAlgo.sqrtNat (evalExpr st a) := by
  obtain ⟨wordResult, value, hword, hreturned, hvalue⟩ :=
    evalStmtWord_seqLets_returns st word build.binds result hst hhalt
      (by simpa [Build.finish] using hnw)
  refine ⟨wordResult, value, by simpa [Build.finish] using hword, hreturned, ?_⟩
  rw [hvalue]
  have hnat := LowerProofs.eval_sqrtBinds_seeded st fresh a ha
  simp only [hbuild] at hnat
  simpa [Builder.run, Build.finish] using hnat

end Lsc.Math.WordLowerProofs
