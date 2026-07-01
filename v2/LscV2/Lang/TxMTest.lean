import LscV2.Lang.TxM

/-!
Smoke tests for the `TxM` builder (step 1 of the Lean-first DSL redesign).
Builds the same `Stmt` shapes as `examples/counter/src/Counter.lean`'s
hand-written `incrementAst`/`pauseAst`/`unpauseAst`, but via `do`-notation
over `TxM` instead of writing out `Stmt.seq`/`Stmt.require`/... by hand.

This does *not* type-check against a real generated `CounterStorage`/
`CounterError`/`CounterEvent` (those come from the later `deriving`-handler
step) — it only proves the builder mechanics (sequencing, `require`,
storage reads/writes, `emit`, checked arithmetic, `ifE`) work end-to-end.
-/

namespace LscV2.TxMTest

open LscV2

/-- `increment`: require not paused, `number +?= 1`, emit. -/
def incrementTxM : TxM Unit := do
  require !(bool σ.paused) else revert Paused
  let n := wei σ.number +? 1
  setWei "number" n
  emit "Incremented" [⟨Ty.wei, n⟩]

/-- `pause`: require caller is owner, require not paused, set paused. -/
def pauseTxM : TxM Unit := do
  require (msg.sender === addr σ.owner) else revert NotOwner
  require !(bool σ.paused) else revert Paused
  setBool "paused" (CoreExpr.lit Ty.bool (.bool true))
  emit "Paused" []

/-- `unpause`: require caller is owner, require paused, clear paused. -/
def unpauseTxM : TxM Unit := do
  require (msg.sender === addr σ.owner) else revert NotOwner
  require (bool σ.paused) else revert Paused
  setBool "paused" (CoreExpr.lit Ty.bool (.bool false))
  emit "Unpaused" []

/-- Exercises `ifE`: two branches each emitting a different event. -/
def branchingTxM : TxM Unit := do
  ifE (bool σ.paused)
    (emit "WasPaused" [])
    (emit "WasNotPaused" [])

/-- `TxM.run` extracts a plain `Stmt` — proves the builder produces real
data, not just a deferred computation. -/
def incrementAst : Stmt := TxM.run incrementTxM
def pauseAst : Stmt := TxM.run pauseTxM
def unpauseAst : Stmt := TxM.run unpauseTxM
def branchingAst : Stmt := TxM.run branchingTxM

/-- A trivial pretty-printer just for these smoke tests (`Stmt` has no
`Repr` instance upstream; not needed by the compile pipeline either). -/
partial def _root_.LscV2.Stmt.summary : Stmt → String
  | .skip => "skip"
  | .seq a b => s!"{a.summary}; {b.summary}"
  | .letBind n _ => s!"let {n}"
  | .storageSet n _ => s!"σ.{n} := _"
  | .require _ err => s!"require _ else revert {err}"
  | .ifThenElse _ t e => s!"if _ then ({t.summary}) else ({e.summary})"
  | .emit n _ => s!"emit {n}"
  | .revert err => s!"revert {err}"

#eval incrementAst.summary
#eval pauseAst.summary
#eval unpauseAst.summary
#eval branchingAst.summary

example : incrementAst =
    (Stmt.require (!(CoreExpr.storageGet Ty.bool "paused")) "Paused").seq
      ((Stmt.storageSet "number" ⟨Ty.wei, (Wei.Expr.storageGet "number").addCheckedNat 1⟩).seq
        (Stmt.emit "Incremented" [⟨Ty.wei, (Wei.Expr.storageGet "number").addCheckedNat 1⟩])) := rfl

example : pauseAst =
    (Stmt.require (msg.sender === CoreExpr.storageGet Ty.address "owner") "NotOwner").seq
      ((Stmt.require (!(CoreExpr.storageGet Ty.bool "paused")) "Paused").seq
        ((Stmt.storageSet "paused" ⟨Ty.bool, CoreExpr.lit Ty.bool (Lit.bool true)⟩).seq
          (Stmt.emit "Paused" []))) := rfl

example : branchingAst =
    Stmt.ifThenElse (CoreExpr.storageGet Ty.bool "paused") (Stmt.emit "WasPaused" [])
      (Stmt.emit "WasNotPaused" []) := rfl

end LscV2.TxMTest
