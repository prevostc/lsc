import YulSemantics.BigStep
import YulSemantics.Dialect.EVM
import YulSemantics.Observation

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Lift `Step` / `Run` from the executable EVM dialect to `evmWithExternal`.
`FunEnv` and `Res` are indexed by the whole `Dialect`, so they are transported
explicitly. Call/`gas`/`create` never fire in `evm` (`stepOp` returns `none`).
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM

def fdeclCast {D1 D2 : Dialect} (h : D1.Op = D2.Op) (d : FDecl D1) : FDecl D2 where
  params := d.params
  rets := d.rets
  body := h ▸ d.body

def fscopeCast {D1 D2 : Dialect} (h : D1.Op = D2.Op) (s : FScope D1) : FScope D2 :=
  s.map fun p => (p.1, fdeclCast h p.2)

def funEnvCast {D1 D2 : Dialect} (h : D1.Op = D2.Op) : FunEnv D1 → FunEnv D2
  | [] => []
  | scope :: rest => fscopeCast h scope :: funEnvCast h rest

@[simp] theorem fdeclCast_params {D1 D2 : Dialect} (h : D1.Op = D2.Op) (d : FDecl D1) :
    (fdeclCast h d).params = d.params := rfl

@[simp] theorem fdeclCast_rets {D1 D2 : Dialect} (h : D1.Op = D2.Op) (d : FDecl D1) :
    (fdeclCast h d).rets = d.rets := rfl

@[simp] theorem funEnvCast_nil {D1 D2 : Dialect} (h : D1.Op = D2.Op) :
    funEnvCast h ([] : FunEnv D1) = [] := rfl

@[simp] theorem funEnvCast_cons {D1 D2 : Dialect} (h : D1.Op = D2.Op)
    (s : FScope D1) (rest : FunEnv D1) :
    funEnvCast h (s :: rest) = fscopeCast h s :: funEnvCast h rest := rfl

@[simp] theorem stepOp_call (args : List U256) (st : EvmState) :
    stepOp Op.call args st = none := rfl
@[simp] theorem stepOp_callcode (args : List U256) (st : EvmState) :
    stepOp Op.callcode args st = none := rfl
@[simp] theorem stepOp_delegatecall (args : List U256) (st : EvmState) :
    stepOp Op.delegatecall args st = none := rfl
@[simp] theorem stepOp_staticcall (args : List U256) (st : EvmState) :
    stepOp Op.staticcall args st = none := rfl
@[simp] theorem stepOp_create (args : List U256) (st : EvmState) :
    stepOp Op.create args st = none := rfl
@[simp] theorem stepOp_create2 (args : List U256) (st : EvmState) :
    stepOp Op.create2 args st = none := rfl
@[simp] theorem stepOp_gas (args : List U256) (st : EvmState) :
    stepOp Op.gas args st = none := rfl

theorem builtin_lift (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) {op : Op} {args : List U256} {st : EvmState}
    {r : BuiltinResult U256 EvmState} (h : stepOp op args st = some r) :
    builtinWithExternal calls creates gasOracle op args st r := by
  cases op <;> first | exact h | simp [stepOp] at h

@[reducible] def yulExt (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) : Dialect :=
  evmWithExternal calls creates gasOracle

theorem evm_op_eq (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) : evm.Op = (yulExt calls creates gasOracle).Op := rfl

theorem fdeclCast_body (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) (d : FDecl evm) :
    (fdeclCast (evm_op_eq calls creates gasOracle) d).body = d.body := rfl

def eresCast (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) : EResult evm → EResult (yulExt calls creates gasOracle)
  | .vals vs st => .vals vs st
  | .halt st => .halt st

def resCast (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) : Res evm → Res (yulExt calls creates gasOracle)
  | .eres r => .eres (eresCast calls creates gasOracle r)
  | .sres V st o => .sres V st o

@[simp] theorem eresCast_vals (calls creates gasOracle vs st) :
    eresCast calls creates gasOracle (.vals vs st) = .vals vs st := rfl

@[simp] theorem eresCast_halt (calls creates gasOracle st) :
    eresCast calls creates gasOracle (.halt st) = .halt st := rfl

@[simp] theorem resCast_eres (calls creates gasOracle r) :
    resCast calls creates gasOracle (.eres r) =
      .eres (eresCast calls creates gasOracle r) := rfl

@[simp] theorem resCast_sres (calls creates gasOracle V st o) :
    resCast calls creates gasOracle (.sres V st o) = .sres V st o := rfl

theorem hoist_cast (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) (body : Block Op) :
    hoist (yulExt calls creates gasOracle) body =
      fscopeCast (evm_op_eq calls creates gasOracle) (hoist evm body) := by
  induction body with
  | nil => rfl
  | cons s rest ih =>
    cases s with
    | funDef n ps rs b =>
      have h₁ :
          hoist (yulExt calls creates gasOracle) (Stmt.funDef n ps rs b :: rest) =
            (n, { params := ps, rets := rs, body := b }) ::
              hoist (yulExt calls creates gasOracle) rest := rfl
      have h₂ :
          hoist evm (Stmt.funDef n ps rs b :: rest) =
            (n, { params := ps, rets := rs, body := b }) :: hoist evm rest := rfl
      rw [h₁, h₂, ih]
      simp [fscopeCast, fdeclCast]
    | block b =>
      have h₁ : hoist (yulExt calls creates gasOracle) (Stmt.block b :: rest) =
          hoist (yulExt calls creates gasOracle) rest := rfl
      have h₂ : hoist evm (Stmt.block b :: rest) = hoist evm rest := rfl
      rw [h₁, h₂, ih]
    | letDecl vs e =>
      have h₁ : hoist (yulExt calls creates gasOracle) (Stmt.letDecl vs e :: rest) =
          hoist (yulExt calls creates gasOracle) rest := rfl
      have h₂ : hoist evm (Stmt.letDecl vs e :: rest) = hoist evm rest := rfl
      rw [h₁, h₂, ih]
    | assign vs e =>
      have h₁ : hoist (yulExt calls creates gasOracle) (Stmt.assign vs e :: rest) =
          hoist (yulExt calls creates gasOracle) rest := rfl
      have h₂ : hoist evm (Stmt.assign vs e :: rest) = hoist evm rest := rfl
      rw [h₁, h₂, ih]
    | cond c b =>
      have h₁ : hoist (yulExt calls creates gasOracle) (Stmt.cond c b :: rest) =
          hoist (yulExt calls creates gasOracle) rest := rfl
      have h₂ : hoist evm (Stmt.cond c b :: rest) = hoist evm rest := rfl
      rw [h₁, h₂, ih]
    | switch c cases dflt =>
      have h₁ : hoist (yulExt calls creates gasOracle) (Stmt.switch c cases dflt :: rest) =
          hoist (yulExt calls creates gasOracle) rest := rfl
      have h₂ : hoist evm (Stmt.switch c cases dflt :: rest) = hoist evm rest := rfl
      rw [h₁, h₂, ih]
    | forLoop init c post body =>
      have h₁ :
          hoist (yulExt calls creates gasOracle) (Stmt.forLoop init c post body :: rest) =
            hoist (yulExt calls creates gasOracle) rest := rfl
      have h₂ : hoist evm (Stmt.forLoop init c post body :: rest) = hoist evm rest := rfl
      rw [h₁, h₂, ih]
    | exprStmt e =>
      have h₁ : hoist (yulExt calls creates gasOracle) (Stmt.exprStmt e :: rest) =
          hoist (yulExt calls creates gasOracle) rest := rfl
      have h₂ : hoist evm (Stmt.exprStmt e :: rest) = hoist evm rest := rfl
      rw [h₁, h₂, ih]
    | «break» =>
      have h₁ : hoist (yulExt calls creates gasOracle) (Stmt.«break» :: rest) =
          hoist (yulExt calls creates gasOracle) rest := rfl
      have h₂ : hoist evm (Stmt.«break» :: rest) = hoist evm rest := rfl
      rw [h₁, h₂, ih]
    | «continue» =>
      have h₁ : hoist (yulExt calls creates gasOracle) (Stmt.«continue» :: rest) =
          hoist (yulExt calls creates gasOracle) rest := rfl
      have h₂ : hoist evm (Stmt.«continue» :: rest) = hoist evm rest := rfl
      rw [h₁, h₂, ih]
    | leave =>
      have h₁ : hoist (yulExt calls creates gasOracle) (Stmt.leave :: rest) =
          hoist (yulExt calls creates gasOracle) rest := rfl
      have h₂ : hoist evm (Stmt.leave :: rest) = hoist evm rest := rfl
      rw [h₁, h₂, ih]

theorem find?_fscopeCast (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) (scope : FScope evm) (fn : Ident) :
    (fscopeCast (evm_op_eq calls creates gasOracle) scope).find?
      (fun p : Ident × FDecl (yulExt calls creates gasOracle) => p.1 = fn) =
      (scope.find? (fun p => p.1 = fn)).map fun p =>
        (p.1, fdeclCast (evm_op_eq calls creates gasOracle) p.2) := by
  induction scope with
  | nil => rfl
  | cons p rest ih =>
    by_cases hp : p.1 = fn
    · simp [fscopeCast, List.find?, hp]
    · have hdec : decide (p.1 = fn) = false := decide_eq_false hp
      simp only [fscopeCast, List.map_cons, List.find?, hdec]
      rw [List.find?_map]
      congr 1

theorem lookupFun_cast (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) (funs : FunEnv evm) (fn : Ident) :
    lookupFun (funEnvCast (evm_op_eq calls creates gasOracle) funs) fn =
      (lookupFun funs fn).map fun p =>
        (fdeclCast (evm_op_eq calls creates gasOracle) p.1,
          funEnvCast (evm_op_eq calls creates gasOracle) p.2) := by
  induction funs with
  | nil => rfl
  | cons scope rest ih =>
    simp only [lookupFun, funEnvCast_cons, find?_fscopeCast]
    cases hfind : scope.find? (fun p => p.1 = fn) <;> simp [ih]

theorem bindZeros_cast (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) (xs : List Ident) :
    bindZeros (yulExt calls creates gasOracle) xs = bindZeros evm xs := rfl

theorem set_cast (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) (V : VEnv evm) (x : Ident) (v : U256) :
    VEnv.set (D := yulExt calls creates gasOracle) V x v =
      VEnv.set (D := evm) V x v := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
    by_cases hx : p.1 = x
    · simp [VEnv.set, hx]
    · simp [VEnv.set, hx, ih]

theorem setMany_cast (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) (V : VEnv evm) (xs : List Ident) (vs : List U256) :
    VEnv.setMany (D := yulExt calls creates gasOracle) V xs vs =
      VEnv.setMany (D := evm) V xs vs := by
  unfold VEnv.setMany
  have hfun :
      (fun (acc : VEnv evm) (p : Ident × U256) =>
        VEnv.set (D := yulExt calls creates gasOracle) acc p.1 p.2) =
        fun acc p => VEnv.set (D := evm) acc p.1 p.2 := by
    funext acc p
    exact set_cast calls creates gasOracle acc p.1 p.2
  rw [hfun]

theorem restore_cast (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) (outer inner : VEnv evm) :
    restore (D := yulExt calls creates gasOracle) outer inner =
      restore (D := evm) outer inner := rfl

theorem zero_cast (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) :
    Dialect.zero (yulExt calls creates gasOracle) = Dialect.zero evm := rfl

theorem litValue_cast (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) :
    (yulExt calls creates gasOracle).litValue = evm.litValue := rfl

private theorem decide_eq_of_iff {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    decide p = decide q := by
  by_cases hp : p
  · simp [hp, h.mp hp]
  · simp [hp, mt h.mpr hp]

theorem selectSwitch_cast (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) (cv : U256)
    (cases : List (Literal × Block Op)) (dflt : Option (Block Op)) :
    selectSwitch (yulExt calls creates gasOracle) cv cases dflt =
      selectSwitch evm cv cases dflt := by
  induction cases with
  | nil => simp [selectSwitch, List.find?]
  | cons p rest ih =>
    have hdec :
        decide (cv = (yulExt calls creates gasOracle).litValue p.1) =
          decide (cv = evm.litValue p.1) :=
      decide_eq_of_iff (by simp [litValue_cast])
    simp [selectSwitch, List.find?, hdec]
    cases h : decide (cv = evm.litValue p.1)
    · change selectSwitch (yulExt calls creates gasOracle) cv rest dflt =
        selectSwitch evm cv rest dflt
      exact ih
    · rfl

/-- Every executable-dialect derivation is an open-world derivation. -/
theorem step_lift (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) {funs : FunEnv evm} {V : VEnv evm} {st : EvmState}
    {code : Code Op} {res : Res evm}
    (h : Step evm funs V st code res) :
    Step (yulExt calls creates gasOracle)
      (funEnvCast (evm_op_eq calls creates gasOracle) funs) V st code
      (resCast calls creates gasOracle res) := by
  induction h with
  | lit => exact Step.lit (D := yulExt calls creates gasOracle)
  | var hv => exact Step.var (D := yulExt calls creates gasOracle) hv
  | builtinOk hargs hop ih =>
    exact Step.builtinOk (D := yulExt calls creates gasOracle) ih (builtin_lift calls creates gasOracle hop)
  | builtinHalt hargs hop ih =>
    exact Step.builtinHalt (D := yulExt calls creates gasOracle) ih (builtin_lift calls creates gasOracle hop)
  | builtinArgsHalt hargs ih => exact Step.builtinArgsHalt (D := yulExt calls creates gasOracle) ih
  | callOk hargs hlu hlen hbody ho ihargs ihbody =>
    rename_i funs V st fn args argvals st1 decl cenv Vend st2 o
    have hlu' :
        lookupFun (funEnvCast (evm_op_eq calls creates gasOracle) funs) fn =
          some (fdeclCast (evm_op_eq calls creates gasOracle) decl,
            funEnvCast (evm_op_eq calls creates gasOracle) cenv) := by
      rw [lookupFun_cast, hlu]; rfl
    refine Step.callOk (D := yulExt calls creates gasOracle) (Vend := Vend) ihargs hlu' ?_ ?_ ho
    · simpa [fdeclCast_params] using hlen
    · simpa [fdeclCast_body, bindZeros_cast] using ihbody
  | callHalt hargs hlu hlen hbody ihargs ihbody =>
    rename_i funs V st fn args argvals st1 decl cenv Vend st2
    have hlu' :
        lookupFun (funEnvCast (evm_op_eq calls creates gasOracle) funs) fn =
          some (fdeclCast (evm_op_eq calls creates gasOracle) decl,
            funEnvCast (evm_op_eq calls creates gasOracle) cenv) := by
      rw [lookupFun_cast, hlu]; rfl
    refine Step.callHalt (D := yulExt calls creates gasOracle) (Vend := Vend) ihargs hlu' ?_ ?_
    · simpa [fdeclCast_params] using hlen
    · simpa [fdeclCast_body, bindZeros_cast] using ihbody
  | callArgsHalt hargs ih => exact Step.callArgsHalt (D := yulExt calls creates gasOracle) ih
  | argsNil => exact Step.argsNil (D := yulExt calls creates gasOracle)
  | argsCons hrest he ihrest ihe => exact Step.argsCons (D := yulExt calls creates gasOracle) ihrest ihe
  | argsRestHalt hrest ih => exact Step.argsRestHalt (D := yulExt calls creates gasOracle) ih
  | argsHeadHalt hrest he ihrest ihe => exact Step.argsHeadHalt (D := yulExt calls creates gasOracle) ihrest ihe
  | funDef => exact Step.funDef (D := yulExt calls creates gasOracle)
  | block hbody ih =>
    rename_i funs V st body Vb stb o
    have ih' :
        Step (yulExt calls creates gasOracle)
          (hoist (yulExt calls creates gasOracle) body ::
            funEnvCast (evm_op_eq calls creates gasOracle) funs)
          V st (.stmts body) (resCast calls creates gasOracle (.sres Vb stb o)) := by
      have h := ih
      rw [funEnvCast_cons] at h
      rwa [← hoist_cast] at h
    exact Step.block (D := yulExt calls creates gasOracle) (by simpa [restore_cast] using ih')
  | letZero =>
    simpa [bindZeros_cast, resCast] using (Step.letZero (D := yulExt calls creates gasOracle))
  | letVal he hlen ih => simpa [resCast] using Step.letVal (D := yulExt calls creates gasOracle) ih hlen
  | letHalt he ih => simpa [resCast] using Step.letHalt (D := yulExt calls creates gasOracle) ih
  | assignVal he hlen ih => simpa [resCast, setMany_cast] using Step.assignVal (D := yulExt calls creates gasOracle) ih hlen
  | assignHalt he ih => simpa [resCast] using Step.assignHalt (D := yulExt calls creates gasOracle) ih
  | exprStmt he ih => exact Step.exprStmt (D := yulExt calls creates gasOracle) ih
  | exprStmtHalt he ih => exact Step.exprStmtHalt (D := yulExt calls creates gasOracle) ih
  | ifTrue he hne hbody ihc ihb =>
    exact Step.ifTrue (D := yulExt calls creates gasOracle) ihc (by simpa [zero_cast] using hne) ihb
  | ifFalse he hz ih =>
    exact Step.ifFalse (D := yulExt calls creates gasOracle) ih (by simpa [zero_cast] using hz)
  | ifHalt he ih => exact Step.ifHalt (D := yulExt calls creates gasOracle) ih
  | switchExec he hbody ihc ihb =>
    exact Step.switchExec (D := yulExt calls creates gasOracle) ihc (by simpa [selectSwitch_cast] using ihb)
  | switchHalt he ih => exact Step.switchHalt (D := yulExt calls creates gasOracle) ih
  | forLoop hinit hloop ihi ihl =>
    have ihi' := ihi
    rw [funEnvCast_cons] at ihi'
    rw [← hoist_cast] at ihi'
    have ihl' := ihl
    rw [funEnvCast_cons] at ihl'
    rw [← hoist_cast] at ihl'
    exact Step.forLoop (D := yulExt calls creates gasOracle) ihi' ihl'
  | forInitHalt hinit ih =>
    have ih' := ih
    rw [funEnvCast_cons] at ih'
    rw [← hoist_cast] at ih'
    exact Step.forInitHalt (D := yulExt calls creates gasOracle) ih'
  | «break» => exact Step.«break» (D := yulExt calls creates gasOracle)
  | «continue» => exact Step.«continue» (D := yulExt calls creates gasOracle)
  | leave => exact Step.leave (D := yulExt calls creates gasOracle)
  | seqNil => exact Step.seqNil (D := yulExt calls creates gasOracle)
  | seqCons hs hr ihs ihr => exact Step.seqCons (D := yulExt calls creates gasOracle) ihs ihr
  | seqStop hs hne ih => exact Step.seqStop (D := yulExt calls creates gasOracle) ih hne
  | loopDone he hz ih =>
    exact Step.loopDone (D := yulExt calls creates gasOracle) ih (by simpa [zero_cast] using hz)
  | loopCondHalt he ih => exact Step.loopCondHalt (D := yulExt calls creates gasOracle) ih
  | loopStep he hne hb ho hp hl ihc ihb ihp ihl =>
    exact Step.loopStep (D := yulExt calls creates gasOracle) ihc (by simpa [zero_cast] using hne) ihb ho ihp ihl
  | loopPostHalt he hne hb ho hp ihc ihb ihp =>
    exact Step.loopPostHalt (D := yulExt calls creates gasOracle) ihc (by simpa [zero_cast] using hne) ihb ho ihp
  | loopBreak he hne hb ihc ihb =>
    exact Step.loopBreak (D := yulExt calls creates gasOracle) ihc (by simpa [zero_cast] using hne) ihb
  | loopLeave he hne hb ihc ihb =>
    exact Step.loopLeave (D := yulExt calls creates gasOracle) ihc (by simpa [zero_cast] using hne) ihb
  | loopBodyHalt he hne hb ihc ihb =>
    exact Step.loopBodyHalt (D := yulExt calls creates gasOracle) ihc (by simpa [zero_cast] using hne) ihb

theorem run_lift (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) {prog : Block Op} {st0 : EvmState} {V' : VEnv evm}
    {st' : EvmState} {o : Outcome} (h : Run evm prog st0 V' st' o) :
    Run (yulExt calls creates gasOracle) prog st0 V' st' o := by
  simpa [Run, funEnvCast_nil] using step_lift calls creates gasOracle h

theorem runCommitted_lift_run (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) {prog : Block Op} {st0 : EvmState} {V' : VEnv evm}
    {stObs : EvmState} {o : Outcome} (h : RunCommitted prog st0 V' stObs o) :
    ∃ st', Run (yulExt calls creates gasOracle) prog st0 V' st' o ∧
      stObs = committedState st0 st' := by
  obtain ⟨st', hrun, rfl⟩ := h
  exact ⟨st', run_lift calls creates gasOracle hrun, rfl⟩

/-- S1 `ExecStmts evm` transports into any `evmWithExternal` (local ops never consult `calls`). -/
theorem execStmts_lift (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) {funs : FunEnv evm} {V : VEnv evm} {st : EvmState}
    {ss : Block Op} {V' : VEnv evm} {st' : EvmState} {o : Outcome}
    (h : ExecStmts evm funs V st ss V' st' o) :
    ExecStmts (yulExt calls creates gasOracle)
      (funEnvCast (evm_op_eq calls creates gasOracle) funs) V st ss V' st' o := by
  simpa [resCast] using step_lift calls creates gasOracle h

theorem evalExpr_lift (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) {funs : FunEnv evm} {V : VEnv evm} {st : EvmState}
    {e : Expr Op} {r : EResult evm}
    (h : EvalExpr evm funs V st e r) :
    EvalExpr (yulExt calls creates gasOracle)
      (funEnvCast (evm_op_eq calls creates gasOracle) funs) V st e
      (eresCast calls creates gasOracle r) := by
  simpa [resCast] using step_lift calls creates gasOracle h

theorem execStmt_lift (calls : ExternalCalls) (creates : ExternalCreates)
    (gasOracle : ExternalGas) {funs : FunEnv evm} {V : VEnv evm} {st : EvmState}
    {s : Stmt Op} {V' : VEnv evm} {st' : EvmState} {o : Outcome}
    (h : ExecStmt evm funs V st s V' st' o) :
    ExecStmt (yulExt calls creates gasOracle)
      (funEnvCast (evm_op_eq calls creates gasOracle) funs) V st s V' st' o := by
  simpa [resCast] using step_lift calls creates gasOracle h

/-- S2 specialization: `creates := .none`, `gas := .none`. -/
theorem execStmts_lift_open (calls : ExternalCalls)
    {funs : FunEnv evm} {V : VEnv evm} {st : EvmState}
    {ss : Block Op} {V' : VEnv evm} {st' : EvmState} {o : Outcome}
    (h : ExecStmts evm funs V st ss V' st' o) :
    ExecStmts (evmWithExternal calls .none .none)
      (funEnvCast (evm_op_eq calls .none .none) funs) V st ss V' st' o :=
  execStmts_lift calls .none .none h

end Lsc.Compiler
