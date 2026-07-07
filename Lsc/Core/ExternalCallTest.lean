import Lsc.Core.ContractM

/-!
Focused tests for `ContractM.PairM.exec`/`PairM.read`, the black-box cross-contract call
primitives (AST/eval-layer semantics only — no `@nonreentrant` decorator, no `Checks.lean`
enforcement, no real multi-contract dispatch; see `Core/ContractM.lean`'s `PairM` section
docstring for the full scope boundary).

Uses trivial `Nat` storages and minimal test-only `Err`/`ContractErrors` instances for both
"sides" of the pair, mirroring the pattern other `Lsc.*Test` files use to exercise `ContractM`
primitives without a real derived contract. -/

namespace Lsc.ExternalCallTest

open Lsc

inductive CallerErr
  | Reentrant
  | ExternalCallFailed
  | Other
  deriving Repr, DecidableEq

instance : ContractErrors CallerErr where
  arith := fun _ => .Other
  fromFramework := fun
    | .Reentrant => .Reentrant
    | .ExternalCallFailed => .ExternalCallFailed
    | .Unauthorized | .InvalidSelector => .Other

inductive CalleeErr
  | Boom
  deriving Repr, DecidableEq

instance : ContractErrors CalleeErr where
  arith := fun _ => .Boom
  fromFramework := fun _ => .Boom

abbrev CallerM := ContractM Nat Unit CallerErr
abbrev CalleeM := ContractM Nat Unit CalleeErr

def mkCallerState (locked : Bool := false) : ContractState Nat :=
  { storage := 0, context := default, locked := locked }

def mkCalleeState : ContractState Nat :=
  { storage := 0, context := default, locked := false }

/-- (a) A well-behaved callee, run via `exec`, succeeds: the caller observes the return value,
its lock is released afterward, and the callee's real state change is threaded through. -/
def wellBehavedCallee : CalleeM Nat := fun s =>
  .ok (42, { s with storage := s.storage + 1 }, [])

example :
    (ContractM.PairM.exec (S := Nat) (T := Nat) (E := Unit) (Err := CallerErr) wellBehavedCallee)
      (mkCallerState) (mkCalleeState) =
      .ok (42, { mkCallerState with locked := false }, { mkCalleeState with storage := 1 }, []) := by
  rfl

/-- (b) A callee that fails is observed by the caller only as the opaque
`ExternalCallFailed`, never the callee's real error. -/
def failingCallee : CalleeM Nat := fun _ => .error .Boom

example :
    (ContractM.PairM.exec (S := Nat) (T := Nat) (E := Unit) (Err := CallerErr) failingCallee)
      (mkCallerState) (mkCalleeState) = .error .ExternalCallFailed := by
  rfl

/-- (c) `exec`, run while the caller is already `locked`, is rejected with `Reentrant` —
covers the one residual reentrancy scenario `exec`'s guard rules out (see `PairM.exec`'s
docstring): real reentrancy through the callee itself is structurally impossible, since
`CalleeM`'s type has no way to mention `CallerM`/`PairM`/`exec` at all. -/
example :
    (ContractM.PairM.exec (S := Nat) (T := Nat) (E := Unit) (Err := CallerErr) wellBehavedCallee)
      (mkCallerState (locked := true)) (mkCalleeState) = .error .Reentrant := by
  rfl

/-- (d) Sequencing two `exec`s in the same transaction: both succeed (the lock from the first
doesn't spuriously leak into the second), and both real state changes are threaded through. -/
def twoSequentialExecs : ContractM.PairM Nat Nat Unit CallerErr Nat := do
  let a ← ContractM.PairM.exec wellBehavedCallee
  let b ← ContractM.PairM.exec wellBehavedCallee
  pure (a + b)

example :
    (ContractM.PairM.run twoSequentialExecs (mkCallerState) (mkCalleeState)).map
      (fun (a, s, t, _) => (a, s.locked, t.storage)) =
      .ok (84, false, 2) := by
  rfl

/-- (e) `read`, on a well-behaved callee, returns the same value `exec` would — but the
callee's state change is **discarded**: the caller observes the callee's storage unchanged. -/
example :
    (ContractM.PairM.read (S := Nat) (T := Nat) (E := Unit) (Err := CallerErr) wellBehavedCallee)
      (mkCallerState) (mkCalleeState) =
      .ok (42, { mkCallerState with locked := false }, mkCalleeState, []) := by
  rfl

/-- (f) `read` still surfaces callee failure as the same opaque `ExternalCallFailed`. -/
example :
    (ContractM.PairM.read (S := Nat) (T := Nat) (E := Unit) (Err := CallerErr) failingCallee)
      (mkCallerState) (mkCalleeState) = .error .ExternalCallFailed := by
  rfl

/-- (g) `read`, like `exec`, is rejected with `Reentrant` when the caller is already locked. -/
example :
    (ContractM.PairM.read (S := Nat) (T := Nat) (E := Unit) (Err := CallerErr) wellBehavedCallee)
      (mkCallerState (locked := true)) (mkCalleeState) = .error .Reentrant := by
  rfl

end Lsc.ExternalCallTest
