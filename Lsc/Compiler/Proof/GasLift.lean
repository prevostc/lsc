import Lsc.Compiler.Proof.Lift

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
A `Run` in `gas := .none` never executes `gas()` (`ExternalGas.none.Gas` is
`False`), so it is also a `Run` in `gas := .any`. Exported S2 theorems keep
`openModel` at `.none`; spilling glue uses this lift internally.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D0" => yulExt calls creates ExternalGas.none
local notation "DA" => yulExt calls creates ExternalGas.any

theorem yulExt_op_gas :
    (yulExt calls creates ExternalGas.none).Op =
      (yulExt calls creates ExternalGas.any).Op := rfl

/-- `gas()` cannot succeed under `.none`; every other built-in ignores the oracle. -/
theorem builtin_none_to_any {op : Op} {args : List U256} {st : EvmState}
    {r : BuiltinResult U256 EvmState}
    (h : builtinWithExternal calls creates ExternalGas.none op args st r) :
    builtinWithExternal calls creates ExternalGas.any op args st r := by
  cases op with
  | gas =>
    cases args with
    | nil =>
      simp [builtinWithExternal] at h
      obtain ⟨g, hg, _⟩ := h
      exact False.elim hg
    | cons _ _ =>
      simp [builtinWithExternal] at h
  | _ => exact h

def eresCastGas : EResult D0 → EResult DA
  | .vals vs st => .vals vs st
  | .halt st => .halt st

def resCastGas : Res D0 → Res DA
  | .eres r => .eres (eresCastGas r)
  | .sres V st o => .sres V st o

theorem hoist_cast_gas (body : Block Op) :
    hoist DA body = fscopeCast yulExt_op_gas (hoist D0 body) := by
  induction body with
  | nil => rfl
  | cons s rest ih =>
    cases s with
    | funDef n ps rs b =>
      rw [show hoist DA (Stmt.funDef n ps rs b :: rest) =
            (n, { params := ps, rets := rs, body := b }) :: hoist DA rest from rfl,
          show hoist D0 (Stmt.funDef n ps rs b :: rest) =
            (n, { params := ps, rets := rs, body := b }) :: hoist D0 rest from rfl, ih]
      simp [fscopeCast, fdeclCast]
    | block b =>
      simpa [hoist] using ih
    | letDecl vs e => simpa [hoist] using ih
    | assign vs e => simpa [hoist] using ih
    | cond c b => simpa [hoist] using ih
    | switch c cases dflt => simpa [hoist] using ih
    | forLoop init c post body => simpa [hoist] using ih
    | exprStmt e => simpa [hoist] using ih
    | «break» => simpa [hoist] using ih
    | «continue» => simpa [hoist] using ih
    | leave => simpa [hoist] using ih

theorem find?_fscopeCast_gas (scope : FScope D0) (fn : Ident) :
    (fscopeCast yulExt_op_gas scope).find?
      (fun p : Ident × FDecl DA => p.1 = fn) =
      (scope.find? (fun p => p.1 = fn)).map fun p =>
        (p.1, fdeclCast yulExt_op_gas p.2) := by
  induction scope with
  | nil => rfl
  | cons p rest ih =>
    by_cases hp : p.1 = fn
    · simp [fscopeCast, List.find?, hp]
    · have hdec : decide (p.1 = fn) = false := decide_eq_false hp
      simp only [fscopeCast, List.map_cons, List.find?, hdec]
      rw [List.find?_map]
      congr 1

theorem lookupFun_cast_gas (funs : FunEnv D0) (fn : Ident) :
    lookupFun (funEnvCast yulExt_op_gas funs) fn =
      (lookupFun funs fn).map fun p =>
        (fdeclCast yulExt_op_gas p.1, funEnvCast yulExt_op_gas p.2) := by
  induction funs with
  | nil => rfl
  | cons scope rest ih =>
    simp only [lookupFun, funEnvCast_cons, find?_fscopeCast_gas]
    cases hfind : scope.find? (fun p => p.1 = fn) <;> simp [ih]

theorem bindZeros_cast_gas (xs : List Ident) :
    bindZeros DA xs = bindZeros D0 xs := rfl

theorem set_cast_gas (V : VEnv D0) (x : Ident) (v : U256) :
    VEnv.set (D := DA) V x v = VEnv.set (D := D0) V x v := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
    by_cases hx : p.1 = x
    · simp [VEnv.set, hx]
    · simp [VEnv.set, hx, ih]

theorem setMany_cast_gas (V : VEnv D0) (xs : List Ident) (vs : List U256) :
    VEnv.setMany (D := DA) V xs vs = VEnv.setMany (D := D0) V xs vs := by
  unfold VEnv.setMany
  have hfun :
      (fun (acc : VEnv D0) (p : Ident × U256) => VEnv.set (D := DA) acc p.1 p.2) =
        fun acc p => VEnv.set (D := D0) acc p.1 p.2 := by
    funext acc p
    exact set_cast_gas acc p.1 p.2
  rw [hfun]

private theorem decide_eq_of_iff {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    decide p = decide q := by
  by_cases hp : p
  · simp [hp, h.mp hp]
  · simp [hp, mt h.mpr hp]

theorem litValue_gas :
    (yulExt calls creates ExternalGas.any).litValue =
      (yulExt calls creates ExternalGas.none).litValue := rfl

theorem selectSwitch_cast_gas (cv : U256)
    (cases : List (Literal × Block Op)) (dflt : Option (Block Op)) :
    selectSwitch DA cv cases dflt = selectSwitch D0 cv cases dflt := by
  induction cases with
  | nil => simp [selectSwitch, List.find?]
  | cons p rest ih =>
    have hdec :
        decide (cv = (yulExt calls creates ExternalGas.any).litValue p.1) =
          decide (cv = (yulExt calls creates ExternalGas.none).litValue p.1) :=
      decide_eq_of_iff (by simp [litValue_gas])
    simp [selectSwitch, List.find?, hdec]
    cases h : decide (cv = (yulExt calls creates ExternalGas.none).litValue p.1)
    · change selectSwitch DA cv rest dflt = selectSwitch D0 cv rest dflt
      exact ih
    · rfl

theorem restore_cast_gas (outer inner : VEnv D0) :
    restore (D := DA) outer inner = restore (D := D0) outer inner := rfl

theorem zero_cast_gas : Dialect.zero DA = Dialect.zero D0 := rfl

theorem fdeclCast_body_gas (d : FDecl D0) :
    (fdeclCast yulExt_op_gas d).body = d.body := rfl

/-- Every `.none`-oracle derivation is an `.any`-oracle derivation. -/
theorem step_none_to_any {funs : FunEnv D0} {V : VEnv D0} {st : EvmState}
    {code : Code Op} {res : Res D0}
    (h : Step D0 funs V st code res) :
    Step DA (funEnvCast yulExt_op_gas funs) V st code (resCastGas res) := by
  induction h with
  | lit => exact Step.lit (D := DA)
  | var hv => exact Step.var (D := DA) hv
  | builtinOk hargs hop ih =>
    exact Step.builtinOk (D := DA) ih (builtin_none_to_any hop)
  | builtinHalt hargs hop ih =>
    exact Step.builtinHalt (D := DA) ih (builtin_none_to_any hop)
  | builtinArgsHalt hargs ih => exact Step.builtinArgsHalt (D := DA) ih
  | callOk hargs hlu hlen hbody ho ihargs ihbody =>
    rename_i funs V st fn args argvals st1 decl cenv Vend st2 o
    have hlu' :
        lookupFun (funEnvCast yulExt_op_gas funs) fn =
          some (fdeclCast yulExt_op_gas decl, funEnvCast yulExt_op_gas cenv) := by
      rw [lookupFun_cast_gas, hlu]; rfl
    refine Step.callOk (D := DA) (Vend := Vend) ihargs hlu' ?_ ?_ ho
    · simpa [fdeclCast_params] using hlen
    · simpa [fdeclCast_body_gas, bindZeros_cast_gas, resCastGas] using ihbody
  | callHalt hargs hlu hlen hbody ihargs ihbody =>
    rename_i funs V st fn args argvals st1 decl cenv Vend st2
    have hlu' :
        lookupFun (funEnvCast yulExt_op_gas funs) fn =
          some (fdeclCast yulExt_op_gas decl, funEnvCast yulExt_op_gas cenv) := by
      rw [lookupFun_cast_gas, hlu]; rfl
    refine Step.callHalt (D := DA) (Vend := Vend) ihargs hlu' ?_ ?_
    · simpa [fdeclCast_params] using hlen
    · simpa [fdeclCast_body_gas, bindZeros_cast_gas, resCastGas] using ihbody
  | callArgsHalt hargs ih => exact Step.callArgsHalt (D := DA) ih
  | argsNil => exact Step.argsNil (D := DA)
  | argsCons hr hh ihr ihh => exact Step.argsCons (D := DA) ihr ihh
  | argsRestHalt hr ih => exact Step.argsRestHalt (D := DA) ih
  | argsHeadHalt hr hh ihr ihh => exact Step.argsHeadHalt (D := DA) ihr ihh
  | funDef => exact Step.funDef (D := DA)
  | block hb ih =>
    rename_i funs V st body Vb stb o
    have ih' :
        Step DA (hoist DA body :: funEnvCast yulExt_op_gas funs)
          V st (.stmts body) (resCastGas (.sres Vb stb o)) := by
      have h := ih
      rw [funEnvCast_cons] at h
      rwa [← hoist_cast_gas] at h
    exact Step.block (D := DA) (by simpa [resCastGas] using ih')
  | letZero => exact Step.letZero (D := DA)
  | letVal he hl ih => exact Step.letVal (D := DA) ih hl
  | letHalt he ih => exact Step.letHalt (D := DA) ih
  | assignVal he hl ih =>
    simpa [resCastGas, setMany_cast_gas] using Step.assignVal (D := DA) ih hl
  | assignHalt he ih => exact Step.assignHalt (D := DA) ih
  | exprStmt he ih => exact Step.exprStmt (D := DA) ih
  | exprStmtHalt he ih => exact Step.exprStmtHalt (D := DA) ih
  | ifTrue he hn hb ihc ihb =>
    exact Step.ifTrue (D := DA) ihc (by simpa [Dialect.zero] using hn) ihb
  | ifFalse he hz ih =>
    exact Step.ifFalse (D := DA) ih (by simpa [Dialect.zero] using hz)
  | ifHalt he ih => exact Step.ifHalt (D := DA) ih
  | switchExec he hb ihc ihb =>
    exact Step.switchExec (D := DA) ihc (by simpa [selectSwitch_cast_gas, resCastGas] using ihb)
  | switchHalt he ih => exact Step.switchHalt (D := DA) ih
  | forLoop hi hl ihi ihl =>
    have ihi' := ihi
    rw [funEnvCast_cons] at ihi'
    rw [← hoist_cast_gas] at ihi'
    have ihl' := ihl
    rw [funEnvCast_cons] at ihl'
    rw [← hoist_cast_gas] at ihl'
    exact Step.forLoop (D := DA) ihi' ihl'
  | forInitHalt hi ih =>
    have ih' := ih
    rw [funEnvCast_cons] at ih'
    rw [← hoist_cast_gas] at ih'
    exact Step.forInitHalt (D := DA) ih'
  | «break» => exact Step.break (D := DA)
  | «continue» => exact Step.continue (D := DA)
  | leave => exact Step.leave (D := DA)
  | seqNil => exact Step.seqNil (D := DA)
  | seqCons hh hr ihh ihr => exact Step.seqCons (D := DA) ihh ihr
  | seqStop hh hne ih => exact Step.seqStop (D := DA) ih hne
  | loopDone he hz ih =>
    exact Step.loopDone (D := DA) ih (by simpa [Dialect.zero] using hz)
  | loopCondHalt he ih => exact Step.loopCondHalt (D := DA) ih
  | loopStep he hn hb ho hp hl ihc ihb ihp ihl =>
    exact Step.loopStep (D := DA) ihc (by simpa [Dialect.zero] using hn) ihb ho ihp ihl
  | loopPostHalt he hn hb ho hp ihc ihb ihp =>
    exact Step.loopPostHalt (D := DA) ihc (by simpa [Dialect.zero] using hn) ihb ho ihp
  | loopBreak he hn hb ihc ihb =>
    exact Step.loopBreak (D := DA) ihc (by simpa [Dialect.zero] using hn) ihb
  | loopLeave he hn hb ihc ihb =>
    exact Step.loopLeave (D := DA) ihc (by simpa [Dialect.zero] using hn) ihb
  | loopBodyHalt he hn hb ihc ihb =>
    exact Step.loopBodyHalt (D := DA) ihc (by simpa [Dialect.zero] using hn) ihb

theorem run_none_to_any {prog : Block Op} {st0 : EvmState} {V' : VEnv D0}
    {st' : EvmState} {o : Outcome} (h : Run D0 prog st0 V' st' o) :
    Run DA prog st0 V' st' o := by
  simpa [Run, funEnvCast_nil, resCastGas] using step_none_to_any h

end Lsc.Compiler
