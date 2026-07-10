import Lsc.Lang.TxM

/-!
Smoke tests for the `TxM` builder (step 1 of the Lean-first DSL redesign).
Builds the same `Stmt` shapes as `examples/counter/src/Counter.lean`'s
hand-written `incrementAst`/`pauseAst`/`unpauseAst`, but via `do`-notation
over `TxM` instead of writing out `Stmt.seq`/`Stmt.require`/... by hand.

This does *not* type-check against a real generated `CounterStorage`/
`CounterError`/`CounterEvent` (those come from the later `deriving`-handler
step) — it only proves the builder mechanics (sequencing, `require`,
storage reads/writes, `emitEvent`, checked arithmetic, `ifE`) work end-to-end.

Uses the low-level `weiField`/`boolField`/`addrField`/`CoreExpr.eqAuto`/
`CoreExpr.not`/`CoreExpr.txField` primitives directly (rather than the
`wei σ.field`/`===`/`!`/`msg.sender` term-level notations, or the
`revert .Ctor`/`require ... else revert .Ctor` real-constructor sugar in
`Lang/Derive.lean`) — those notations were removed once `Lang/Syntax.lean`'s
`tx { ... }` grammar took over as the contract-author-facing surface; this
file exercises the raw builder mechanics without going through a real
`derive_contract_dsl`-derived contract, see this file's module docstring. -/

namespace Lsc.TxMTest

open Lsc

/-- `increment`: require not paused, `number +?= 1`, emit. -/
def incrementTxM : TxM Unit := do
  requireE (CoreExpr.not (boolField "paused")) "Paused"
  let n := Wei.Expr.addCheckedNat (weiField "number") 1
  setWei "number" n
  emitEvent "Incremented" [⟨Ty.wei, n⟩]

/-- `pause`: require caller is owner, require not paused, set paused. -/
def pauseTxM : TxM Unit := do
  requireE (CoreExpr.eqAuto (CoreExpr.txField TxField.caller) (addrField "owner")) "NotOwner"
  requireE (CoreExpr.not (boolField "paused")) "Paused"
  setBool "paused" (CoreExpr.lit Ty.bool (.bool true))
  emitEvent "Paused" []

/-- `unpause`: require caller is owner, require paused, clear paused. -/
def unpauseTxM : TxM Unit := do
  requireE (CoreExpr.eqAuto (CoreExpr.txField TxField.caller) (addrField "owner")) "NotOwner"
  requireE (boolField "paused") "Paused"
  setBool "paused" (CoreExpr.lit Ty.bool (.bool false))
  emitEvent "Unpaused" []

/-- Exercises `ifE`: two branches each emitting a different event. -/
def branchingTxM : TxM Unit := do
  ifE (boolField "paused")
    (emitEvent "WasPaused" [])
    (emitEvent "WasNotPaused" [])

/-- `TxM.run` extracts a plain `Stmt` — proves the builder produces real
data, not just a deferred computation. -/
def incrementAst : Stmt := TxM.run incrementTxM
def pauseAst : Stmt := TxM.run pauseTxM
def unpauseAst : Stmt := TxM.run unpauseTxM
def branchingAst : Stmt := TxM.run branchingTxM

/-- A trivial pretty-printer just for these smoke tests (`Stmt` has no
`Repr` instance upstream; not needed by the compile pipeline either). -/
partial def _root_.Lsc.Stmt.summary : Stmt → String
  | .skip => "skip"
  | .seq a b => s!"{a.summary}; {b.summary}"
  | .letBind n _ => s!"let {n}"
  | .storageSet n _ => s!"σ.{n} := _"
  | .mapSet n _ _ => s!"σ.{n}[_] := _"
  | .require _ err => s!"require _ else revert {err}"
  | .ifThenElse _ t e => s!"if _ then ({t.summary}) else ({e.summary})"
  | .emit n _ => s!"emit {n}"
  | .revert err => s!"revert {err}"
  | .ret _ => "return _"
  | .externalExec _ _ _ => "externalExec"
  | .letExecBind _ _ _ _ _ => "letExecBind"
  | .externalRead _ _ _ _ => "externalRead"
  | .letReadBind _ _ _ _ _ _ => "letReadBind"
  | .reentrancyGuard b => s!"reentrancyGuard ({b.summary})"

#eval incrementAst.summary
#eval pauseAst.summary
#eval unpauseAst.summary
#eval branchingAst.summary

example : incrementAst =
    (Stmt.require (CoreExpr.not (CoreExpr.storageGet Ty.bool "paused")) "Paused").seq
      ((Stmt.storageSet "number" ⟨Ty.wei, (Wei.Expr.storageGet "number").addCheckedNat 1⟩).seq
        (Stmt.emit "Incremented" [⟨Ty.wei, (Wei.Expr.storageGet "number").addCheckedNat 1⟩])) := rfl

example : pauseAst =
    (Stmt.require (CoreExpr.eqAuto (CoreExpr.txField TxField.caller)
      (CoreExpr.storageGet Ty.address "owner")) "NotOwner").seq
      ((Stmt.require (CoreExpr.not (CoreExpr.storageGet Ty.bool "paused")) "Paused").seq
        ((Stmt.storageSet "paused" ⟨Ty.bool, CoreExpr.lit Ty.bool (Lit.bool true)⟩).seq
          (Stmt.emit "Paused" []))) := rfl

example : branchingAst =
    Stmt.ifThenElse (CoreExpr.storageGet Ty.bool "paused") (Stmt.emit "WasPaused" [])
      (Stmt.emit "WasNotPaused" []) := rfl

end Lsc.TxMTest
