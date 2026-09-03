import Lsc3.Examples.Counter
import Lsc3.Compile.GetBody
import Lsc3.Compile.GetContract
import Lsc3.Compile.IncBody
import Lsc3.Compile.IncContract
import Lsc3.Compile.Codegen

/-!
# Counter.get — Lean, Core, codegen, and compiler bytecode

`get` is `read count`. Reification yields `opTail (.load 0)`; codegen of that term
encodes to `GetBody.code`. The one-function compiler contract with the same Core
encodes to `GetContract.code`, and `GetContract.getOnly_hit sel n` is the machine
certificate (any `sel`, including `selectorOf "get" []`). Instantiating that proof
at a concrete Keccak selector exceeds `maxRecDepth`; apply it rather than
specializing it here.

`increment` is load / checked `+ 1` / store / emit. The one-function compiler
contract encodes to `IncContract.code`; `IncContract.incOnly_hit sel n h` is the
matching-selector machine certificate (STOP with slot 0 equal to `n + 1`).
-/

open Lsc3 Lsc3.Compile Counter

namespace Counter

/-- `get` is `read count`. -/
theorem get_run (ctx : Lsc3.Ctx) (w : World Storage Event) :
    Tx.run get ctx w = .ok (w.self.count, w) := by
  simp [get]

/-- Reification of `get` is a tail load of slot 0. -/
theorem get_core_eq : get.core = Core.opTail (.load 0) := rfl

/-- The get-only compiler contract uses the same Core term. -/
theorem get_core_getOnly : get.core = GetContract.getFn.core := by
  rw [get_core_eq, GetContract.getFn_core]

/-- `Core.denote` of the reified term is the user function. -/
theorem get_denote : Core.denote schema get.core [] = get :=
  get.core_denote

/-- Codegen of `get.core` is the `GetBody` instruction list. -/
theorem get_codegen (ctx : Lsc3.Compile.Ctx) :
    match Codegen.genCore ctx contract get.core with
    | .ok (instrs, _) => encode instrs = .ok GetBody.code
    | .error _ => False := by
  rw [get_core_eq]
  exact GetBody.encode_genCore_load0 ctx contract

/-- The compiler's one-function `get` contract encodes to `GetContract.code`. -/
theorem getOnly_compile :
    compileContract GetContract.getOnly =
      .ok (GetContract.code (FnDef.selector GetContract.getFn)) :=
  GetContract.compile_getOnly

/-- `increment` is load, checked `+ 1`, store, emit. -/
theorem increment_run (ctx : Lsc3.Ctx) (w : World Storage Event)
    (h : w.self.count + 1 < wordBound) :
    Tx.run increment ctx w =
      .ok ((), { self := { w.self with count := w.self.count + 1 },
                 log := w.log ++ [.Incremented 1] }) := by
  simp [increment, h]

theorem increment_core_eq :
    increment.core =
      Core.letOp (.load 0)
        (Core.letOp (.addChecked (.var 0) (.lit 1))
          (Core.seq (.store 0 (.var 0))
            (Core.stmtTail (.emit 0 [.lit 1])))) :=
  rfl

/-- Codegen of `increment.core` encodes to `IncBody.code`. -/
theorem increment_codegen :
    match Codegen.genCore {} contract increment.core with
    | .ok (instrs, _) => encode instrs = .ok IncBody.code
    | .error _ => False := by
  rw [increment_core_eq, IncBody.increment_genCore]
  exact IncBody.encode_inc

/-- The increment-only compiler contract uses the same Core term. -/
theorem increment_core_incOnly : increment.core = IncContract.incFn.core := by
  rw [increment_core_eq, IncContract.incFn_core]

/-- The compiler's one-function `increment` contract encodes to `IncContract.code`. -/
theorem incrementOnly_compile :
    compileContract IncContract.incOnly =
      .ok (IncContract.code (FnDef.selector IncContract.incFn)) :=
  IncContract.compile_incOnly

end Counter
