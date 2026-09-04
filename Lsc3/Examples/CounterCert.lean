import Lsc3.Examples.Counter
import Lsc3.Compile.GetBody
import Lsc3.Compile.GetContract
import Lsc3.Compile.IncBody
import Lsc3.Compile.IncByBody
import Lsc3.Compile.DecBody
import Lsc3.Compile.IncContract
import Lsc3.Compile.GetInc
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

The two-function compiler `GetInc.getInc` encodes to `GetInc.code`. Apply
`GetInc.getInc_get_hit` / `GetInc.getInc_inc_hit`; do not instantiate them here.
Checked-add jump targets are `incPc + 1` plus the isolated body's local PCs
(`GetInc.bodyRevPc_eq`), not a second hand-placed numeral.

Isolated `incrementBy` encodes to `IncByBody.code`. Apply `IncByBody.incBy_hit` /
`IncByBody.incBy_zero` / `IncByBody.incBy_overflow`; do not instantiate them here.

Isolated `decrement` encodes to `DecBody.code`. Apply `DecBody.dec_hit` /
`DecBody.dec_zero`; do not instantiate them here.

`lsc_contract Counter … get` is the generic compiler: the last function is the
same `opTail (.load 0)` body as `GetContract`, and the dispatcher is
`dispatchByteSize 4` bytes.
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
      .ok ((), { w with self := { w.self with count := w.self.count + 1 }, log := w.log ++ [.Incremented 1] }) := by
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

/-- The compiler's two-function `get` + `increment` contract encodes to `GetInc.code`. -/
theorem getInc_compile :
    compileContract GetInc.getInc =
      .ok (GetInc.code (FnDef.selector GetContract.getFn) (FnDef.selector IncContract.incFn)) :=
  GetInc.compile_getInc

/-- `incrementBy n` requires `n ≠ 0`, then checked-adds `n` onto `count`. -/
theorem incrementBy_run (n : Nat) (ctx : Lsc3.Ctx) (w : World Storage Event)
    (hnz : n ≠ 0) (h : w.self.count + n < wordBound) :
    Tx.run (incrementBy n) ctx w =
      .ok ((), { w with self := { w.self with count := w.self.count + n }, log := w.log ++ [.Incremented n] }) := by
  simp [incrementBy, hnz, h]

/-- `incrementBy 0` reverts with `Error.Zero`. -/
theorem incrementBy_zero (ctx : Lsc3.Ctx) (w : World Storage Event) :
    Tx.run (incrementBy 0) ctx w = .error (.user .Zero) := by
  simp [incrementBy]

theorem incrementBy_core_eq :
    incrementBy.core =
      Core.seq (.require (.ne (.var 0) (.lit 0)) 0 [])
        (Core.letOp (.load 0)
          (Core.letOp (.addChecked (.var 0) (.var 1))
            (Core.seq (.store 0 (.var 0))
              (Core.stmtTail (.emit 0 [.var 2]))))) :=
  rfl

/-- The isolated `incrementBy` codegen function uses the same Core term. -/
theorem incrementBy_core_incBy : incrementBy.core = IncByBody.incByFn.core := by
  rw [incrementBy_core_eq, IncByBody.incByFn_core]

/-- Codegen of isolated `incrementBy` encodes to `IncByBody.code`. -/
theorem incrementBy_codegen :
    match Codegen.genFunction contract IncByBody.incByFn {} with
    | .ok (instrs, _) => encode instrs = .ok IncByBody.code
    | .error _ => False := by
  rw [IncByBody.incrementBy_genFunction]
  exact IncByBody.encode_incBy

/-- `Core.denote` of the reified `incrementBy` term is the user function. -/
theorem incrementBy_denote (n : Nat) :
    Core.denote schema incrementBy.core [n] = incrementBy n :=
  incrementBy.core_denote n

/-- Saturating decrement: `count = 0` stays `0`. -/
theorem decrement_zero (ctx : Lsc3.Ctx) (w : World Storage Event)
    (h : w.self.count = 0) :
    Tx.run decrement ctx w =
      .ok ((), { w with self := { w.self with count := 0 } }) := by
  simp [decrement, h]

/-- Saturating decrement: `count ≠ 0` stores `count - 1`. -/
theorem decrement_run (ctx : Lsc3.Ctx) (w : World Storage Event)
    (h : 0 < w.self.count) :
    Tx.run decrement ctx w =
      .ok ((), { w with self := { w.self with count := w.self.count - 1 } }) := by
  have hne : ¬ w.self.count = 0 := Nat.pos_iff_ne_zero.mp h
  have hle : 1 ≤ w.self.count := h
  simp [decrement, hne, hle]

theorem decrement_core_eq :
    decrement.core =
      Core.letOp (.load 0)
        (Core.ite (.eq (.var 0) (.lit 0))
          (Core.letOp (.pure (.lit 0))
            (Core.stmtTail (.store 0 (.var 0))))
          (Core.letOp (.subChecked (.var 0) (.lit 1))
            (Core.stmtTail (.store 0 (.var 0))))) :=
  rfl

/-- Codegen of isolated `decrement` encodes to `DecBody.code`. -/
theorem decrement_codegen :
    match Codegen.genFunction contract DecBody.decFn {} with
    | .ok (instrs, _) => encode instrs = .ok DecBody.code
    | .error _ => False := by
  rw [DecBody.decrement_genFunction]
  exact DecBody.encode_dec

/-- Dispatch order is the `lsc_contract` argument order. -/
theorem contract_fn_names :
    contract.functions.map (fun f => f.name) =
      ["increment", "incrementBy", "decrement", "get"] :=
  rfl

theorem contract_nFns : contract.functions.length = 4 := rfl

theorem contract_get_core :
    (contract.functions.get ⟨3, by decide⟩).core = Core.opTail (.load 0) :=
  rfl

theorem contract_get_params :
    (contract.functions.get ⟨3, by decide⟩).params = [] :=
  rfl

theorem contract_get_name :
    (contract.functions.get ⟨3, by decide⟩).name = "get" :=
  rfl

/-- The production Counter `get` is the generic load-0 body, not a hand-written clone. -/
theorem genFunction_contract_get (ctx : Lsc3.Compile.Ctx) :
    Codegen.genFunction contract (contract.functions.get ⟨3, by decide⟩) ctx =
      .ok (GetContract.bodyInstrs,
        Ctx.afterFunction (Ctx.forFunction ctx "get" 0)) := by
  unfold Codegen.genFunction
  rw [contract_get_params, contract_get_core, contract_get_name]
  simp [List.length_nil, bind, Except.bind, GetContract.bodyInstrs]
  have hcore :
      Codegen.genCore (ctx.forFunction "get" 0) contract (Core.opTail (.load 0)) =
        .ok (GetContract.bodyInstrs, ctx.forFunction "get" 0) :=
    GetBody.genCore_opTail_load0 _ _
  let k : Except String (List Asm × Lsc3.Compile.Ctx) → Except String (List Asm × Lsc3.Compile.Ctx) :=
    fun x =>
      match x with
      | Except.error err => Except.error err
      | Except.ok v => Except.ok (v.1, v.2.afterFunction)
  exact (congrArg k hcore).trans rfl

/-- Four selector branches; first function `JUMPDEST` sits at `dispatchByteSize 4`. -/
theorem counter_dispatch_size (ctx : Lsc3.Compile.Ctx) :
    match selectorDispatch contract ctx with
    | .ok (instrs, _) => asmListSize instrs = dispatchByteSize 4
    | .error _ => False := by
  have hne : contract.functions ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [contract_nFns] at this
  have h := selectorDispatch_size (c := contract) (ctx := ctx) hne
  simpa [contract_nFns] using h

end Counter
