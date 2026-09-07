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

/-! ## `gas := .any` → `gas := .none` when the program never mentions `gas()` -/

def noGasOp : Op → Bool
  | .gas => false
  | _ => true

mutual
def noGasExpr : Expr Op → Bool
  | .lit _ | .var _ => true
  | .builtin op args => noGasOp op && noGasExprs args
  | .call _ args => noGasExprs args

def noGasExprs : List (Expr Op) → Bool
  | [] => true
  | e :: es => noGasExpr e && noGasExprs es

def noGasStmt : Stmt Op → Bool
  | .block b | .funDef _ _ _ b => noGasStmts b
  | .letDecl _ none => true
  | .letDecl _ (some e) => noGasExpr e
  | .assign _ e | .exprStmt e => noGasExpr e
  | .cond c b => noGasExpr c && noGasStmts b
  | .switch c cases dflt =>
      noGasExpr c && noGasCases cases && noGasDflt dflt
  | .forLoop init c post body =>
      noGasStmts init && noGasExpr c && noGasStmts post && noGasStmts body
  | .break | .continue | .leave => true

def noGasStmts : Block Op → Bool
  | [] => true
  | s :: rest => noGasStmt s && noGasStmts rest

def noGasCases : List (Literal × Block Op) → Bool
  | [] => true
  | (_, b) :: rest => noGasStmts b && noGasCases rest

def noGasDflt : Option (Block Op) → Bool
  | none => true
  | some b => noGasStmts b
end

def noGasCode : Code Op → Bool
  | .expr e => noGasExpr e
  | .args es => noGasExprs es
  | .stmt s => noGasStmt s
  | .stmts ss => noGasStmts ss
  | .loop c post body => noGasExpr c && noGasStmts post && noGasStmts body

def noGasDecl (d : FDecl DA) : Bool := noGasStmts d.body

def noGasScope : FScope DA → Bool
  | [] => true
  | p :: rest => noGasDecl p.2 && noGasScope rest

def noGasFuns : FunEnv DA → Bool
  | [] => true
  | scope :: rest => noGasScope scope && noGasFuns rest

theorem band_split {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem band3 {a b c : Bool} (h : (a && b && c) = true) :
    a = true ∧ b = true ∧ c = true := by
  have h1 := band_split (a := a && b) (b := c) (by simpa [Bool.and_assoc] using h)
  have h2 := band_split h1.1
  exact ⟨h2.1, h2.2, h1.2⟩

theorem band4 {a b c d : Bool} (h : (a && b && c && d) = true) :
    a = true ∧ b = true ∧ c = true ∧ d = true := by
  have h1 := band_split (a := a && b && c) (b := d) (by simpa [Bool.and_assoc] using h)
  have h2 := band3 h1.1
  exact ⟨h2.1, h2.2.1, h2.2.2, h1.2⟩

def eresCastGasInv : EResult DA → EResult D0
  | .vals vs st => .vals vs st
  | .halt st => .halt st

def resCastGasInv : Res DA → Res D0
  | .eres r => .eres (eresCastGasInv r)
  | .sres V st o => .sres V st o

theorem hoist_cast_gas_inv (body : Block Op) :
    hoist D0 body = fscopeCast (Eq.symm yulExt_op_gas) (hoist DA body) := by
  induction body with
  | nil => rfl
  | cons s rest ih =>
    cases s with
    | funDef n ps rs b =>
      rw [show hoist D0 (Stmt.funDef n ps rs b :: rest) =
            (n, { params := ps, rets := rs, body := b }) :: hoist D0 rest from rfl,
          show hoist DA (Stmt.funDef n ps rs b :: rest) =
            (n, { params := ps, rets := rs, body := b }) :: hoist DA rest from rfl, ih]
      simp [fscopeCast, fdeclCast]
    | block b => simpa [hoist] using ih
    | letDecl vs e => simpa [hoist] using ih
    | assign vs e => simpa [hoist] using ih
    | cond c b => simpa [hoist] using ih
    | switch c cases dflt => simpa [hoist] using ih
    | forLoop init c post body => simpa [hoist] using ih
    | exprStmt e => simpa [hoist] using ih
    | «break» => simpa [hoist] using ih
    | «continue» => simpa [hoist] using ih
    | leave => simpa [hoist] using ih

theorem find?_fscopeCast_gas_inv (scope : FScope DA) (fn : Ident) :
    (fscopeCast (Eq.symm yulExt_op_gas) scope).find?
      (fun p : Ident × FDecl D0 => p.1 = fn) =
      (scope.find? (fun p => p.1 = fn)).map fun p =>
        (p.1, fdeclCast (Eq.symm yulExt_op_gas) p.2) := by
  induction scope with
  | nil => rfl
  | cons p rest ih =>
    by_cases hp : p.1 = fn
    · simp [fscopeCast, List.find?, hp]
    · have hdec : decide (p.1 = fn) = false := decide_eq_false hp
      simp only [fscopeCast, List.map_cons, List.find?, hdec]
      rw [List.find?_map]
      congr 1

theorem lookupFun_cast_gas_inv (funs : FunEnv DA) (fn : Ident) :
    lookupFun (funEnvCast (Eq.symm yulExt_op_gas) funs) fn =
      (lookupFun funs fn).map fun p =>
        (fdeclCast (Eq.symm yulExt_op_gas) p.1,
          funEnvCast (Eq.symm yulExt_op_gas) p.2) := by
  induction funs with
  | nil => rfl
  | cons scope rest ih =>
    simp only [lookupFun, funEnvCast_cons, find?_fscopeCast_gas_inv]
    cases hfind : scope.find? (fun p => p.1 = fn) <;> simp [ih]

theorem fdeclCast_body_gas_inv (d : FDecl DA) :
    (fdeclCast (Eq.symm yulExt_op_gas) d).body = d.body := rfl

theorem noGasScope_find {scope : FScope DA} {fn : Ident} {p : Ident × FDecl DA}
    (hs : noGasScope scope = true)
    (h : scope.find? (fun q => q.1 = fn) = some p) :
    noGasDecl p.2 = true := by
  induction scope with
  | nil => simp [List.find?] at h
  | cons q rest ih =>
    simp [List.find?] at h
    by_cases hq : q.1 = fn
    · simp [hq] at h
      cases h
      simp only [noGasScope, Bool.and_eq_true] at hs
      exact hs.1
    · have hdec : decide (q.1 = fn) = false := decide_eq_false hq
      simp [hdec] at h
      simp only [noGasScope, Bool.and_eq_true] at hs
      exact ih hs.2 h

theorem lookupFun_noGas {funs : FunEnv DA} {fn : Ident}
    {decl : FDecl DA} {cenv : FunEnv DA}
    (hf : noGasFuns funs = true)
    (h : lookupFun funs fn = some (decl, cenv)) :
    noGasDecl decl = true ∧ noGasFuns cenv = true := by
  induction funs with
  | nil => simp [lookupFun] at h
  | cons scope rest ih =>
    simp only [lookupFun] at h
    cases hfind : scope.find? (fun p => p.1 = fn) with
    | none =>
      simp [hfind] at h
      simp only [noGasFuns, Bool.and_eq_true] at hf
      exact ih hf.2 h
    | some p =>
      simp [hfind] at h
      obtain ⟨rfl, rfl⟩ := h
      have hf' := hf
      simp only [noGasFuns, Bool.and_eq_true] at hf'
      exact ⟨noGasScope_find hf'.1 hfind, hf⟩

theorem noGas_hoist (body : Block Op)
    (h : noGasStmts body = true) : noGasScope (hoist DA body) = true := by
  induction body with
  | nil => rfl
  | cons s rest ih =>
    simp only [noGasStmts, Bool.and_eq_true] at h
    cases s with
    | funDef n ps rs b =>
      rw [show hoist DA (Stmt.funDef n ps rs b :: rest) =
            (n, { params := ps, rets := rs, body := b }) :: hoist DA rest from rfl]
      have hb : noGasStmts b = true := by simpa [noGasStmt] using h.1
      simp [noGasScope, noGasDecl, hb, ih h.2]
    | block b => simpa [hoist] using ih h.2
    | letDecl vs e => simpa [hoist] using ih h.2
    | assign vs e => simpa [hoist] using ih h.2
    | cond c b => simpa [hoist] using ih h.2
    | switch c cases dflt => simpa [hoist] using ih h.2
    | forLoop init c post body => simpa [hoist] using ih h.2
    | exprStmt e => simpa [hoist] using ih h.2
    | «break» => simpa [hoist] using ih h.2
    | «continue» => simpa [hoist] using ih h.2
    | leave => simpa [hoist] using ih h.2

theorem noGasFuns_hoist_cons {body : Block Op} {funs : FunEnv DA}
    (hb : noGasStmts body = true) (hf : noGasFuns funs = true) :
    noGasFuns (hoist DA body :: funs) = true := by
  simp [noGasFuns, noGas_hoist body hb, hf]

theorem noGas_selectSwitch (cv : U256) (cases : List (Literal × Block Op))
    (dflt : Option (Block Op))
    (hc : noGasCases cases = true)
    (hd : noGasDflt dflt = true) :
    noGasStmts (selectSwitch DA cv cases dflt) = true := by
  induction cases with
  | nil =>
    simp only [selectSwitch, List.find?]
    cases dflt with
    | none => simp [noGasStmts]
    | some b => simpa [Option.getD, noGasDflt] using hd
  | cons p rest ih =>
    have hc' := band_split (a := noGasStmts p.2) (b := noGasCases rest) (by
      simpa [noGasCases] using hc)
    cases hdec : decide (cv = Dialect.litValue DA p.1) with
    | false =>
      have : selectSwitch DA cv (p :: rest) dflt = selectSwitch DA cv rest dflt := by
        simp [selectSwitch, List.find?, hdec]
      rw [this]
      exact ih hc'.2
    | true =>
      have : selectSwitch DA cv (p :: rest) dflt = p.2 := by
        simp [selectSwitch, List.find?, hdec]
      rw [this]
      exact hc'.1

theorem builtin_any_to_none {op : Op} {args : List U256} {st : EvmState}
    {r : BuiltinResult U256 EvmState}
    (h : builtinWithExternal calls creates ExternalGas.any op args st r)
    (hne : noGasOp op = true) :
    builtinWithExternal calls creates ExternalGas.none op args st r := by
  cases op with
  | gas => simp [noGasOp] at hne
  | _ => exact h

theorem step_any_to_none {funs : FunEnv DA} {V : VEnv DA} {st : EvmState}
    {code : Code Op} {res : Res DA}
    (h : Step DA funs V st code res)
    (hng : noGasCode code = true) (hf : noGasFuns funs = true) :
    Step D0 (funEnvCast (Eq.symm yulExt_op_gas) funs) V st code (resCastGasInv res) := by
  revert hng hf
  induction h with
  | lit => intros; exact Step.lit (D := D0)
  | var hv => intros; exact Step.var (D := D0) hv
  | builtinOk hargs hop ih =>
    intro hng hf
    rename_i funs V st op args argvals st1 rets st2
    have hs : noGasOp op = true ∧ noGasExprs args = true := by
      simpa [noGasCode, noGasExpr, Bool.and_eq_true] using hng
    exact Step.builtinOk (D := D0) (ih (by simpa [noGasCode] using hs.2) hf)
      (builtin_any_to_none hop hs.1)
  | builtinHalt hargs hop ih =>
    intro hng hf
    rename_i funs V st op args argvals st1 st2
    have hs : noGasOp op = true ∧ noGasExprs args = true := by
      simpa [noGasCode, noGasExpr, Bool.and_eq_true] using hng
    exact Step.builtinHalt (D := D0) (ih (by simpa [noGasCode] using hs.2) hf)
      (builtin_any_to_none hop hs.1)
  | builtinArgsHalt hargs ih =>
    intro hng hf
    have hs := band_split (by simpa [noGasCode, noGasExpr] using hng)
    exact Step.builtinArgsHalt (D := D0)
      (ih (by simpa [noGasCode] using hs.2) hf)
  | callOk hargs hlu hlen hbody ho ihargs ihbody =>
    intro hng hf
    rename_i funs V st fn args argvals st1 decl cenv Vend st2 o
    have hlu' :
        lookupFun (funEnvCast (Eq.symm yulExt_op_gas) funs) fn =
          some (fdeclCast (Eq.symm yulExt_op_gas) decl,
            funEnvCast (Eq.symm yulExt_op_gas) cenv) := by
      rw [lookupFun_cast_gas_inv, hlu]; rfl
    obtain ⟨hdecl, hcenv⟩ := lookupFun_noGas hf hlu
    refine Step.callOk (D := D0) (Vend := Vend)
      (ihargs (by simpa [noGasCode, noGasExpr] using hng) hf) hlu' ?_ ?_ ho
    · simpa [fdeclCast_params] using hlen
    · simpa [fdeclCast_body_gas_inv, bindZeros_cast_gas, resCastGasInv] using
        ihbody (by simpa [noGasCode, noGasStmt, noGasDecl] using hdecl) hcenv
  | callHalt hargs hlu hlen hbody ihargs ihbody =>
    intro hng hf
    rename_i funs V st fn args argvals st1 decl cenv Vend st2
    have hlu' :
        lookupFun (funEnvCast (Eq.symm yulExt_op_gas) funs) fn =
          some (fdeclCast (Eq.symm yulExt_op_gas) decl,
            funEnvCast (Eq.symm yulExt_op_gas) cenv) := by
      rw [lookupFun_cast_gas_inv, hlu]; rfl
    obtain ⟨hdecl, hcenv⟩ := lookupFun_noGas hf hlu
    refine Step.callHalt (D := D0) (Vend := Vend)
      (ihargs (by simpa [noGasCode, noGasExpr] using hng) hf) hlu' ?_ ?_
    · simpa [fdeclCast_params] using hlen
    · simpa [fdeclCast_body_gas_inv, bindZeros_cast_gas, resCastGasInv] using
        ihbody (by simpa [noGasCode, noGasStmt, noGasDecl] using hdecl) hcenv
  | callArgsHalt hargs ih =>
    intro hng hf
    exact Step.callArgsHalt (D := D0)
      (ih (by simpa [noGasCode, noGasExpr] using hng) hf)
  | argsNil => intros; exact Step.argsNil (D := D0)
  | argsCons hr hh ihr ihh =>
    intro hng hf
    rename_i funs V st e rest restvals st1 v st2
    have hs := band_split (by simpa [noGasCode, noGasExprs] using hng)
    exact Step.argsCons (D := D0)
      (ihr (by simpa [noGasCode] using hs.2) hf)
      (ihh (by simpa [noGasCode] using hs.1) hf)
  | argsRestHalt hr ih =>
    intro hng hf
    have hs := band_split (by simpa [noGasCode, noGasExprs] using hng)
    exact Step.argsRestHalt (D := D0)
      (ih (by simpa [noGasCode] using hs.2) hf)
  | argsHeadHalt hr hh ihr ihh =>
    intro hng hf
    rename_i funs V st e rest restvals st1 st2
    have hs := band_split (by simpa [noGasCode, noGasExprs] using hng)
    exact Step.argsHeadHalt (D := D0)
      (ihr (by simpa [noGasCode] using hs.2) hf)
      (ihh (by simpa [noGasCode] using hs.1) hf)
  | funDef => intros; exact Step.funDef (D := D0)
  | block hb ih =>
    intro hng hf
    rename_i funs V st body Vb stb o
    have ih' :
        Step D0 (hoist D0 body :: funEnvCast (Eq.symm yulExt_op_gas) funs)
          V st (.stmts body) (resCastGasInv (.sres Vb stb o)) := by
      have h := ih (by simpa [noGasCode, noGasStmt] using hng)
        (noGasFuns_hoist_cons (by simpa [noGasCode, noGasStmt] using hng) hf)
      rw [funEnvCast_cons] at h
      rwa [← hoist_cast_gas_inv] at h
    exact Step.block (D := D0) (by simpa [resCastGasInv] using ih')
  | letZero => intros; exact Step.letZero (D := D0)
  | letVal he hl ih =>
    intro hng hf
    exact Step.letVal (D := D0) (ih (by simpa [noGasCode, noGasStmt] using hng) hf) hl
  | letHalt he ih =>
    intro hng hf
    exact Step.letHalt (D := D0) (ih (by simpa [noGasCode, noGasStmt] using hng) hf)
  | assignVal he hl ih =>
    intro hng hf
    simpa [resCastGasInv, setMany_cast_gas] using
      Step.assignVal (D := D0) (ih (by simpa [noGasCode, noGasStmt] using hng) hf) hl
  | assignHalt he ih =>
    intro hng hf
    exact Step.assignHalt (D := D0) (ih (by simpa [noGasCode, noGasStmt] using hng) hf)
  | exprStmt he ih =>
    intro hng hf
    exact Step.exprStmt (D := D0) (ih (by simpa [noGasCode, noGasStmt] using hng) hf)
  | exprStmtHalt he ih =>
    intro hng hf
    exact Step.exprStmtHalt (D := D0) (ih (by simpa [noGasCode, noGasStmt] using hng) hf)
  | ifTrue he hn hb ihc ihb =>
    intro hng hf
    rename_i funs V st c body cv st1 V' st2 o
    have hs := band_split (by simpa [noGasCode, noGasStmt] using hng)
    exact Step.ifTrue (D := D0) (ihc (by simpa [noGasCode] using hs.1) hf)
      (by simpa [Dialect.zero] using hn)
      (ihb (by simpa [noGasCode, noGasStmt] using hs.2) hf)
  | ifFalse he hz ih =>
    intro hng hf
    have hs := band_split (by simpa [noGasCode, noGasStmt] using hng)
    exact Step.ifFalse (D := D0)
      (ih (by simpa [noGasCode] using hs.1) hf)
      (by simpa [Dialect.zero] using hz)
  | ifHalt he ih =>
    intro hng hf
    have hs := band_split (by simpa [noGasCode, noGasStmt] using hng)
    exact Step.ifHalt (D := D0)
      (ih (by simpa [noGasCode] using hs.1) hf)
  | switchExec he hb ihc ihb =>
    intro hng hf
    rename_i funs V st c cases dflt cv st1 V' st2 o
    have hs := band3 (by simpa [noGasCode, noGasStmt] using hng)
    exact Step.switchExec (D := D0) (ihc (by simpa [noGasCode] using hs.1) hf)
      (by simpa [selectSwitch_cast_gas, resCastGasInv] using
        ihb (by
          simpa [noGasCode, noGasStmt] using
            noGas_selectSwitch cv cases dflt hs.2.1 hs.2.2) hf)
  | switchHalt he ih =>
    intro hng hf
    have hs := band3 (by simpa [noGasCode, noGasStmt] using hng)
    exact Step.switchHalt (D := D0)
      (ih (by simpa [noGasCode] using hs.1) hf)
  | forLoop hi hl ihi ihl =>
    intro hng hf
    rename_i funs V st init c post body Vinit stinit Vend stend o
    have hs := band4 (by simpa [noGasCode, noGasStmt] using hng)
    have hf' := noGasFuns_hoist_cons hs.1 hf
    have ihi' := ihi (by simpa [noGasCode] using hs.1) hf'
    rw [funEnvCast_cons] at ihi'
    rw [← hoist_cast_gas_inv] at ihi'
    have hloop : noGasCode (.loop c post body) = true := by
      simp [noGasCode, hs.2.1, hs.2.2.1, hs.2.2.2]
    have ihl' := ihl hloop hf'
    rw [funEnvCast_cons] at ihl'
    rw [← hoist_cast_gas_inv] at ihl'
    exact Step.forLoop (D := D0) ihi' ihl'
  | forInitHalt hi ih =>
    intro hng hf
    rename_i funs V st init c post body Vinit stinit
    have hs := band4 (by simpa [noGasCode, noGasStmt] using hng)
    have ih' := ih (by simpa [noGasCode] using hs.1) (noGasFuns_hoist_cons hs.1 hf)
    rw [funEnvCast_cons] at ih'
    rw [← hoist_cast_gas_inv] at ih'
    exact Step.forInitHalt (D := D0) ih'
  | «break» => intros; exact Step.break (D := D0)
  | «continue» => intros; exact Step.continue (D := D0)
  | leave => intros; exact Step.leave (D := D0)
  | seqNil => intros; exact Step.seqNil (D := D0)
  | seqCons hh hr ihh ihr =>
    intro hng hf
    rename_i funs V st s rest V1 st1 V2 st2 o
    have hs := band_split (by simpa [noGasCode, noGasStmts] using hng)
    exact Step.seqCons (D := D0)
      (ihh (by simpa [noGasCode] using hs.1) hf)
      (ihr (by simpa [noGasCode] using hs.2) hf)
  | seqStop hh hne ih =>
    intro hng hf
    have hs := band_split (by simpa [noGasCode, noGasStmts] using hng)
    exact Step.seqStop (D := D0)
      (ih (by simpa [noGasCode] using hs.1) hf) hne
  | loopDone he hz ih =>
    intro hng hf
    have hs := band3 (by simpa [noGasCode] using hng)
    exact Step.loopDone (D := D0)
      (ih (by simpa [noGasCode] using hs.1) hf)
      (by simpa [Dialect.zero] using hz)
  | loopCondHalt he ih =>
    intro hng hf
    have hs := band3 (by simpa [noGasCode] using hng)
    exact Step.loopCondHalt (D := D0)
      (ih (by simpa [noGasCode] using hs.1) hf)
  | loopStep he hn hb ho hp hl ihc ihb ihp ihl =>
    intro hng hf
    rename_i funs V st c post body cv st1 Vb stb ob Vp stp Vend stend o
    have hs := band3 (by simpa [noGasCode] using hng)
    exact Step.loopStep (D := D0) (ihc (by simpa [noGasCode] using hs.1) hf)
      (by simpa [Dialect.zero] using hn)
      (ihb (by simpa [noGasCode, noGasStmt] using hs.2.2) hf) ho
      (ihp (by simpa [noGasCode, noGasStmt] using hs.2.1) hf)
      (ihl (by simpa [noGasCode] using hng) hf)
  | loopPostHalt he hn hb ho hp ihc ihb ihp =>
    intro hng hf
    rename_i funs V st c post body cv st1 Vb stb ob Vp stp
    have hs := band3 (by simpa [noGasCode] using hng)
    exact Step.loopPostHalt (D := D0) (ihc (by simpa [noGasCode] using hs.1) hf)
      (by simpa [Dialect.zero] using hn)
      (ihb (by simpa [noGasCode, noGasStmt] using hs.2.2) hf) ho
      (ihp (by simpa [noGasCode, noGasStmt] using hs.2.1) hf)
  | loopBreak he hn hb ihc ihb =>
    intro hng hf
    rename_i funs V st c post body cv st1 Vb stb
    have hs := band3 (by simpa [noGasCode] using hng)
    exact Step.loopBreak (D := D0) (ihc (by simpa [noGasCode] using hs.1) hf)
      (by simpa [Dialect.zero] using hn)
      (ihb (by simpa [noGasCode, noGasStmt] using hs.2.2) hf)
  | loopLeave he hn hb ihc ihb =>
    intro hng hf
    rename_i funs V st c post body cv st1 Vb stb
    have hs := band3 (by simpa [noGasCode] using hng)
    exact Step.loopLeave (D := D0) (ihc (by simpa [noGasCode] using hs.1) hf)
      (by simpa [Dialect.zero] using hn)
      (ihb (by simpa [noGasCode, noGasStmt] using hs.2.2) hf)
  | loopBodyHalt he hn hb ihc ihb =>
    intro hng hf
    rename_i funs V st c post body cv st1 Vb stb
    have hs := band3 (by simpa [noGasCode] using hng)
    exact Step.loopBodyHalt (D := D0) (ihc (by simpa [noGasCode] using hs.1) hf)
      (by simpa [Dialect.zero] using hn)
      (ihb (by simpa [noGasCode, noGasStmt] using hs.2.2) hf)

theorem run_any_to_none {prog : Block Op} {st0 : EvmState} {V' : VEnv DA}
    {st' : EvmState} {o : Outcome}
    (hng : noGasStmts prog = true)
    (h : Run DA prog st0 V' st' o) :
    Run D0 prog st0 V' st' o := by
  simpa [Run, funEnvCast_nil, resCastGasInv] using
    step_any_to_none h (by simpa [noGasCode, noGasStmt] using hng) (by simp [noGasFuns])

end Lsc.Compiler
