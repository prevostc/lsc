import Mathlib.Logic.Equiv.Defs
import Lsc.Lang.Tx

/-!
# External-contract interface: `Interface`, `Binding`, `Tx.call`

A declared interface is a deterministic may-model plus ABI metadata. A `Binding` names
the storage field that holds the callee address and the ghost field that the model
updates. `Tx.call` takes no address: the compiled call `sload`s the bound field.
-/

namespace Lsc

/-- How the compiler lowers a successful CALL's return data. -/
inductive AbiRet
  | word
  | boolOpt
  | none
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Compiler-only ABI of one interface method. -/
structure AbiSpec where
  selector : Nat
  arity : Nat
  ret : AbiRet
  deriving DecidableEq, Repr, Lean.ToExpr

/-- A foreign-contract may-model. `n` is the method count (`idx : Method ≃ Fin n`). -/
structure Interface where
  Ghost : Type
  Method : Type
  n : Nat
  model : Method → Address → List Nat → Ghost → Option (Nat × Ghost)
  abi : Method → AbiSpec
  idx : Method ≃ Fin n

/-- Static binding of an interface: address lives in our storage, ghost in `World.ext`. -/
structure Binding (I : Interface) (S X : Type) where
  addr : S → Address
  get : X → I.Ghost
  set : X → I.Ghost → X

namespace Tx

variable {I : Interface} {S X E ε : Type}

/-- CALL through a binding. Faults and model-`none` revert the caller (`callFailed`).
The model sees `ctx.self` (our address, the token's `msg.sender`); the callee is
implicit in the binding's ghost. The compiler `sload`s `b.addr` for the EVM CALL. -/
def call (b : Binding I S X) (m : I.Method) (args : List Nat) : Tx S X E ε Nat :=
  fun ctx w =>
    if w.faults w.ncalls then .error .callFailed
    else
      match I.model m ctx.self args (b.get w.ext) with
      | none => .error .callFailed
      | some (ret, g') =>
          .ok (ret, { w with ext := b.set w.ext g', ncalls := w.ncalls + 1 })

/-- Statement-position CALL (discard the returned word). -/
def callUnit (b : Binding I S X) (m : I.Method) (args : List Nat) : Tx S X E ε Unit :=
  fun ctx w =>
    match Tx.run (Tx.call b m args) ctx w with
    | .ok (_, w') => .ok ((), w')
    | .error e => .error e

@[simp] theorem run_call (b : Binding I S X) (m : I.Method) (args : List Nat)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (Tx.call (E := E) (ε := ε) b m args) ctx w =
      if w.faults w.ncalls then .error .callFailed
      else
        match I.model m ctx.self args (b.get w.ext) with
        | none => .error .callFailed
        | some (ret, g') =>
            .ok (ret, { w with ext := b.set w.ext g', ncalls := w.ncalls + 1 }) :=
  rfl

/-- `simp` after a `do` block leaves `ReaderT.run` (`.run`), which does not match `Tx.run_call`. -/
@[simp] theorem call_run (b : Binding I S X) (m : I.Method) (args : List Nat)
    (ctx : Ctx) (w : World S X E) :
    (Tx.call (E := E) (ε := ε) b m args).run ctx w =
      if w.faults w.ncalls then .error .callFailed
      else
        match I.model m ctx.self args (b.get w.ext) with
        | none => .error .callFailed
        | some (ret, g') =>
            .ok (ret, { w with ext := b.set w.ext g', ncalls := w.ncalls + 1 }) :=
  rfl

@[simp] theorem run_callUnit (b : Binding I S X) (m : I.Method) (args : List Nat)
    (ctx : Ctx) (w : World S X E) :
    Tx.run (Tx.callUnit (E := E) (ε := ε) b m args) ctx w =
      match Tx.run (Tx.call (E := E) (ε := ε) b m args) ctx w with
      | .ok (_, w') => .ok ((), w')
      | .error e => .error e :=
  rfl

end Tx

end Lsc
