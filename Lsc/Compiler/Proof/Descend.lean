import Lsc.Compiler.Proof.Lift
import Lsc.Compiler.Externals
import YulSemantics.Determinism

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Inverse of `step_lift` for Yul that contains no `call`/`create`/`gas` ops.
`builtinWithExternal` on those ops is definitionally `stepOp = some`.
Empty `FunEnv` (emitted code is `hoist`-free) makes the cast trivial.
-/

namespace Lsc.Compiler

open YulSemantics
open YulSemantics.EVM
open Lsc hiding Op Stmt

def noExtCode : Code YOp → Bool
  | .expr e => noExtExpr e
  | .args es => noExtExprs es
  | .stmt s => noExtStmt s
  | .stmts ss => noExtBlock ss
  | .loop c post body => noExtExpr c && noExtBlock post && noExtBlock body

/-- Decidable: `code` contains no `call`/`callcode`/`delegatecall`/`staticcall`/
`create`/`create2`/`gas`. Function bodies in scope are a separate `noExtFuns`. -/
def NoExternalOps (code : Code YOp) : Prop := noExtCode code = true

instance (code : Code YOp) : Decidable (NoExternalOps code) :=
  inferInstanceAs (Decidable (noExtCode code = true))

def noExtFuns {calls : ExternalCalls} (funs : FunEnv (yulD calls)) : Bool :=
  funs.all (fun scope => scope.all (fun p => noExtBlock p.2.body))

def funEnvUncast (calls : ExternalCalls) :
    FunEnv (yulD calls) → FunEnv evm :=
  funEnvCast (Eq.symm (evm_op_eq calls .none .none))

def eresUncast (calls : ExternalCalls) :
    EResult (yulD calls) → EResult evm
  | .vals vs st => .vals vs st
  | .halt st => .halt st

def resUncast (calls : ExternalCalls) : Res (yulD calls) → Res evm
  | .eres r => .eres (eresUncast calls r)
  | .sres V st o => .sres V st o

@[simp] theorem funEnvUncast_nil (calls : ExternalCalls) :
    funEnvUncast calls [] = [] := rfl

@[simp] theorem funEnvUncast_cons (calls : ExternalCalls)
    (s : FScope (yulD calls)) (rest : FunEnv (yulD calls)) :
    funEnvUncast calls (s :: rest) =
      fscopeCast (Eq.symm (evm_op_eq calls .none .none)) s ::
        funEnvUncast calls rest := rfl

@[simp] theorem eresUncast_vals (calls vs st) :
    eresUncast calls (.vals vs st) = .vals vs st := rfl

@[simp] theorem eresUncast_halt (calls st) :
    eresUncast calls (.halt st) = .halt st := rfl

@[simp] theorem resUncast_eres (calls r) :
    resUncast calls (.eres r) = .eres (eresUncast calls r) := rfl

@[simp] theorem resUncast_sres (calls V st o) :
    resUncast calls (.sres V st o) = .sres V st o := rfl

@[simp] theorem noExtFuns_nil {calls : ExternalCalls} :
    noExtFuns ([] : FunEnv (yulD calls)) = true := rfl

theorem noExtFuns_cons_nil {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    (h : noExtFuns funs = true) :
    noExtFuns (([] : FScope (yulD calls)) :: funs) = true := by
  simpa [noExtFuns] using h

/-- For a non-external `op`, the open-world built-in is exactly `stepOp`. -/
theorem builtin_nonext {calls : ExternalCalls} {op : YOp} {args : List U256}
    {st : EvmState} {r : BuiltinResult U256 EvmState}
    (h : noExtOp op = true) :
    builtinWithExternal calls .none .none op args st r ↔
      stepOp op args st = some r := by
  cases op <;> first
    | (simp only [noExtOp] at h; exact Bool.noConfusion h)
    | simp [builtinWithExternal]

theorem builtin_descend {calls : ExternalCalls} {op : YOp} {args : List U256}
    {st : EvmState} {r : BuiltinResult U256 EvmState}
    (h : noExtOp op = true)
    (hbu : builtinWithExternal calls .none .none op args st r) :
    stepOp op args st = some r :=
  (builtin_nonext (calls := calls) h).mp hbu

theorem noExt_expr_builtin {op args}
    (h : noExtExpr (.builtin op args) = true) :
    noExtOp op = true ∧ noExtExprs args = true := by
  simpa [noExtExpr, Bool.and_eq_true] using h

theorem noExt_expr_call {fn args}
    (h : noExtExpr (.call fn args) = true) :
    noExtExprs args = true := by
  simpa [noExtExpr] using h

theorem noExt_args_cons {e es}
    (h : noExtExprs (e :: es) = true) :
    noExtExpr e = true ∧ noExtExprs es = true := by
  simpa [noExtExprs, Bool.and_eq_true] using h

theorem noExt_block_cons {s ss}
    (h : noExtBlock (s :: ss) = true) :
    noExtStmt s = true ∧ noExtBlock ss = true := by
  simpa [noExtBlock, noExtStmts, Bool.and_eq_true] using h

theorem noExt_stmt_block {b} (h : noExtStmt (.block b) = true) :
    noExtBlock b = true := h

theorem noExt_stmt_let {xs e} (h : noExtStmt (.letDecl xs (some e)) = true) :
    noExtExpr e = true := h

theorem noExt_stmt_assign {xs e} (h : noExtStmt (.assign xs e) = true) :
    noExtExpr e = true := h

theorem noExt_stmt_expr {e} (h : noExtStmt (.exprStmt e) = true) :
    noExtExpr e = true := h

theorem noExt_stmt_cond {c b} (h : noExtStmt (.cond c b) = true) :
    noExtExpr c = true ∧ noExtBlock b = true := by
  simpa [noExtStmt, noExtBlock, Bool.and_eq_true] using h

theorem noExt_stmt_switch {c cases dflt} (h : noExtStmt (.switch c cases dflt) = true) :
    noExtExpr c = true ∧ noExtCases cases = true ∧ noExtBlock (dflt.getD []) = true := by
  cases dflt with
  | none =>
    simp [noExtStmt, noExtBlock, Bool.and_eq_true] at h
    exact ⟨h.1, h.2, rfl⟩
  | some b =>
    simp [noExtStmt, noExtBlock, Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2, h.2⟩

theorem noExt_stmt_for {init c post body}
    (h : noExtStmt (.forLoop init c post body) = true) :
    noExtBlock init = true ∧ noExtExpr c = true ∧
      noExtBlock post = true ∧ noExtBlock body = true := by
  simp only [noExtStmt, noExtBlock, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem noExt_code_expr {e} (h : NoExternalOps (.expr e)) : noExtExpr e = true := h
theorem noExt_code_args {es} (h : NoExternalOps (.args es)) : noExtExprs es = true := h
theorem noExt_code_stmt {s} (h : NoExternalOps (.stmt s)) : noExtStmt s = true := h
theorem noExt_code_stmts {ss} (h : NoExternalOps (.stmts ss)) : noExtBlock ss = true := h
theorem noExt_code_loop {c post body} (h : NoExternalOps (.loop c post body)) :
    noExtExpr c = true ∧ noExtBlock post = true ∧ noExtBlock body = true := by
  simp [NoExternalOps, noExtCode, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem noExt_all_args {es} (h : noExtExprs es = true) : NoExternalOps (.args es) := h
theorem noExt_all_expr {e} (h : noExtExpr e = true) : NoExternalOps (.expr e) := h
theorem noExt_all_stmt {s} (h : noExtStmt s = true) : NoExternalOps (.stmt s) := h
theorem noExt_all_stmts {ss} (h : noExtBlock ss = true) : NoExternalOps (.stmts ss) := h
theorem noExt_all_block_stmt {b} (h : noExtBlock b = true) :
    NoExternalOps (.stmt (.block b)) := h

theorem noExt_selectSwitch {calls : ExternalCalls} {cv : U256}
    (cases : List (Literal × YBlock)) (dflt : Option YBlock)
    (hc : noExtCases cases = true)
    (hd : noExtBlock (dflt.getD []) = true) :
    noExtBlock (selectSwitch (yulD calls) cv cases dflt) = true := by
  induction cases with
  | nil =>
    simp only [selectSwitch, List.find?]
    cases dflt with
    | none => simp [noExtBlock]
    | some b => simpa [noExtBlock] using hd
  | cons p rest ih =>
    have ⟨hp, hrest⟩ : noExtStmts p.2 = true ∧ noExtCases rest = true := by
      simpa [noExtCases, Bool.and_eq_true] using hc
    simp only [selectSwitch, List.find?]
    cases hdec : decide (cv = (yulD calls).litValue p.1)
    · exact ih hrest
    · simpa [noExtBlock] using hp

theorem noExt_hoist {calls : ExternalCalls} {body : YBlock}
    (h : noExtBlock body = true) :
    (hoist (yulD calls) body).all (fun p => noExtBlock p.2.body) = true := by
  induction body with
  | nil => simp [hoist]
  | cons s rest ih =>
    have ⟨hs, hrest⟩ := noExt_block_cons h
    have ih' := ih hrest
    cases s with
    | funDef n ps rs b =>
      have hb : noExtBlock b = true := hs
      simpa [hoist, hb] using ih'
    | _ => simpa [hoist] using ih'

theorem noExtFuns_hoist_cons {calls : ExternalCalls} {body : YBlock}
    {funs : FunEnv (yulD calls)}
    (hb : noExtBlock body = true) (hf : noExtFuns funs = true) :
    noExtFuns (hoist (yulD calls) body :: funs) = true := by
  have hh := noExt_hoist (calls := calls) hb
  simpa [noExtFuns, hh] using hf

theorem mem_of_find? {α} {p : α → Bool} {l : List α} {x : α}
    (h : l.find? p = some x) : x ∈ l := by
  induction l with
  | nil => cases h
  | cons y ys ih =>
    simp [List.find?] at h
    split at h
    · cases h; exact List.Mem.head _
    · exact List.Mem.tail _ (ih h)

theorem lookupFun_noExt {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {fn : Ident} {decl : FDecl (yulD calls)} {cenv : FunEnv (yulD calls)}
    (hf : noExtFuns funs = true)
    (h : lookupFun funs fn = some (decl, cenv)) :
    noExtBlock decl.body = true ∧ noExtFuns cenv = true := by
  induction funs with
  | nil => cases h
  | cons scope rest ih =>
    have ⟨hs, hr⟩ : scope.all (fun p => noExtBlock p.2.body) = true ∧ noExtFuns rest = true := by
      simpa [noExtFuns, List.all_cons, Bool.and_eq_true] using hf
    simp only [lookupFun] at h
    cases hfind : scope.find? (fun p => p.1 = fn) with
    | none =>
      simp [hfind] at h
      exact ih hr h
    | some p =>
      simp [hfind] at h
      obtain ⟨rfl, rfl⟩ := h
      have hp : noExtBlock p.2.body = true :=
        (List.all_eq_true.mp hs) p (mem_of_find? hfind)
      refine ⟨hp, ?_⟩
      simpa [noExtFuns, hs] using hr

theorem fdeclCast_symm_body (calls : ExternalCalls) (d : FDecl (yulD calls)) :
    (fdeclCast (Eq.symm (evm_op_eq calls .none .none)) d).body = d.body :=
  rfl

theorem fdeclCast_roundtrip (calls : ExternalCalls) (d : FDecl evm) :
    fdeclCast (Eq.symm (evm_op_eq calls .none .none))
      (fdeclCast (evm_op_eq calls .none .none) d) = d := by
  cases d
  simp [fdeclCast]

theorem fscopeCast_roundtrip (calls : ExternalCalls) (s : FScope evm) :
    fscopeCast (Eq.symm (evm_op_eq calls .none .none))
      (fscopeCast (evm_op_eq calls .none .none) s) = s := by
  induction s with
  | nil => rfl
  | cons p rest ih =>
    calc
      fscopeCast (Eq.symm (evm_op_eq calls .none .none))
          (fscopeCast (evm_op_eq calls .none .none) (p :: rest))
        = (p.1, fdeclCast (Eq.symm (evm_op_eq calls .none .none))
            (fdeclCast (evm_op_eq calls .none .none) p.2)) ::
          fscopeCast (Eq.symm (evm_op_eq calls .none .none))
            (fscopeCast (evm_op_eq calls .none .none) rest) := rfl
      _ = (p.1, p.2) :: rest := by rw [fdeclCast_roundtrip, ih]

theorem find?_fscopeUncast (calls : ExternalCalls) (scope : FScope (yulD calls))
    (fn : Ident) :
    (fscopeCast (Eq.symm (evm_op_eq calls .none .none)) scope).find?
      (fun p : Ident × FDecl evm => p.1 = fn) =
      (scope.find? (fun p => p.1 = fn)).map fun p =>
        (p.1, fdeclCast (Eq.symm (evm_op_eq calls .none .none)) p.2) := by
  induction scope with
  | nil => rfl
  | cons p rest ih =>
    by_cases hp : p.1 = fn
    · simp [fscopeCast, List.find?, hp]
    · have hdec : decide (p.1 = fn) = false := decide_eq_false hp
      simp only [fscopeCast, List.map_cons, List.find?, hdec]
      rw [List.find?_map]
      congr 1

theorem lookupFun_uncast (calls : ExternalCalls) (funs : FunEnv (yulD calls)) (fn : Ident) :
    lookupFun (funEnvUncast calls funs) fn =
      (lookupFun funs fn).map fun p =>
        (fdeclCast (Eq.symm (evm_op_eq calls .none .none)) p.1,
          funEnvUncast calls p.2) := by
  induction funs with
  | nil => rfl
  | cons scope rest ih =>
    simp only [lookupFun, funEnvUncast_cons, find?_fscopeUncast]
    cases hfind : scope.find? (fun p => p.1 = fn) <;> simp [ih]

theorem hoist_uncast (calls : ExternalCalls) (body : YBlock) :
    hoist evm body =
      fscopeCast (Eq.symm (evm_op_eq calls .none .none))
        (hoist (yulD calls) body) := by
  have h := hoist_cast calls .none .none body
  simp only [yulD, yulExt] at h ⊢
  rw [h, fscopeCast_roundtrip]

theorem bindZeros_uncast (calls : ExternalCalls) (xs : List Ident) :
    bindZeros (yulD calls) xs = bindZeros evm xs :=
  bindZeros_cast calls .none .none xs

theorem restore_uncast (calls : ExternalCalls) (outer inner : VEnv evm) :
    restore (D := yulD calls) outer inner = restore (D := evm) outer inner :=
  restore_cast calls .none .none outer inner

theorem setMany_uncast (calls : ExternalCalls) (V : VEnv evm) (xs : List Ident)
    (vs : List U256) :
    VEnv.setMany (D := yulD calls) V xs vs = VEnv.setMany (D := evm) V xs vs :=
  setMany_cast calls .none .none V xs vs

theorem yulD_zero_eq (calls : ExternalCalls) :
    (yulD calls).zero = evm.zero :=
  zero_cast calls .none .none

theorem selectSwitch_uncast (calls : ExternalCalls) (cv : U256)
    (cases : List (Literal × YBlock)) (dflt : Option YBlock) :
    selectSwitch (yulD calls) cv cases dflt = selectSwitch evm cv cases dflt :=
  selectSwitch_cast calls .none .none cv cases dflt

/-- Inverse of `step_lift` for code (and function bodies in scope) with no external ops. -/
theorem step_descend {calls : ExternalCalls} {funs' : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {code : Code YOp} {r : Res (yulD calls)}
    (hfuns : noExtFuns funs' = true) (hcode : NoExternalOps code)
    (h : Step (yulD calls) funs' V st code r) :
    Step evm (funEnvUncast calls funs') V st code (resUncast calls r) := by
  revert hfuns hcode
  induction h with
  | lit =>
    intro _ _; exact Step.lit
  | var hv =>
    intro _ _; exact Step.var hv
  | builtinOk hargs hop ih =>
    intro hfuns hcode
    have ⟨hop', hargs'⟩ := noExt_expr_builtin (noExt_code_expr hcode)
    exact Step.builtinOk (ih hfuns (noExt_all_args hargs'))
      (builtin_descend hop' hop)
  | builtinHalt hargs hop ih =>
    intro hfuns hcode
    have ⟨hop', hargs'⟩ := noExt_expr_builtin (noExt_code_expr hcode)
    exact Step.builtinHalt (ih hfuns (noExt_all_args hargs'))
      (builtin_descend hop' hop)
  | builtinArgsHalt hargs ih =>
    intro hfuns hcode
    have ⟨_, hargs'⟩ := noExt_expr_builtin (noExt_code_expr hcode)
    exact Step.builtinArgsHalt (ih hfuns (noExt_all_args hargs'))
  | callOk hargs hlu hlen hbody ho ihargs ihbody =>
    intro hfuns hcode
    rename_i funs V st fn args argvals st1 decl cenv Vend st2 o
    have hargs' := noExt_expr_call (noExt_code_expr hcode)
    obtain ⟨hbod, hcenv⟩ := lookupFun_noExt hfuns hlu
    have hlu' :
        lookupFun (funEnvUncast calls funs) fn =
          some (fdeclCast (Eq.symm (evm_op_eq calls .none .none)) decl,
            funEnvUncast calls cenv) := by
      rw [lookupFun_uncast, hlu]; rfl
    refine Step.callOk (D := evm) (Vend := Vend)
      (ihargs hfuns (noExt_all_args hargs')) hlu' ?_ ?_ ho
    · simpa [fdeclCast] using hlen
    · simpa [fdeclCast_symm_body, bindZeros_uncast] using
        ihbody hcenv (noExt_all_block_stmt hbod)
  | callHalt hargs hlu hlen hbody ihargs ihbody =>
    intro hfuns hcode
    rename_i funs V st fn args argvals st1 decl cenv Vend st2
    have hargs' := noExt_expr_call (noExt_code_expr hcode)
    obtain ⟨hbod, hcenv⟩ := lookupFun_noExt hfuns hlu
    have hlu' :
        lookupFun (funEnvUncast calls funs) fn =
          some (fdeclCast (Eq.symm (evm_op_eq calls .none .none)) decl,
            funEnvUncast calls cenv) := by
      rw [lookupFun_uncast, hlu]; rfl
    refine Step.callHalt (D := evm) (Vend := Vend)
      (ihargs hfuns (noExt_all_args hargs')) hlu' ?_ ?_
    · simpa [fdeclCast] using hlen
    · simpa [fdeclCast_symm_body, bindZeros_uncast] using
        ihbody hcenv (noExt_all_block_stmt hbod)
  | callArgsHalt hargs ih =>
    intro hfuns hcode
    have hargs' := noExt_expr_call (noExt_code_expr hcode)
    exact Step.callArgsHalt (ih hfuns (noExt_all_args hargs'))
  | argsNil =>
    intro _ _; exact Step.argsNil
  | argsCons hrest he ihrest ihe =>
    intro hfuns hcode
    have ⟨he', hrest'⟩ := noExt_args_cons (noExt_code_args hcode)
    exact Step.argsCons (ihrest hfuns (noExt_all_args hrest'))
      (ihe hfuns (noExt_all_expr he'))
  | argsRestHalt hrest ih =>
    intro hfuns hcode
    have ⟨_, hrest'⟩ := noExt_args_cons (noExt_code_args hcode)
    exact Step.argsRestHalt (ih hfuns (noExt_all_args hrest'))
  | argsHeadHalt hrest he ihrest ihe =>
    intro hfuns hcode
    have ⟨he', hrest'⟩ := noExt_args_cons (noExt_code_args hcode)
    exact Step.argsHeadHalt (ihrest hfuns (noExt_all_args hrest'))
      (ihe hfuns (noExt_all_expr he'))
  | funDef =>
    intro _ _; exact Step.funDef
  | block hbody ih =>
    intro hfuns hcode
    rename_i funs V st body Vb stb o
    have hb := noExt_stmt_block (noExt_code_stmt hcode)
    have hf' := noExtFuns_hoist_cons hb hfuns
    have ih' := ih hf' (noExt_all_stmts hb)
    rw [funEnvUncast_cons, ← hoist_uncast] at ih'
    exact Step.block (D := evm) (by simpa [restore_uncast] using ih')
  | letZero =>
    intro _ _; simpa [bindZeros_uncast] using Step.letZero (D := evm)
  | letVal he hlen ih =>
    intro hfuns hcode
    have he' := noExt_stmt_let (noExt_code_stmt hcode)
    simpa using Step.letVal (ih hfuns (noExt_all_expr he')) hlen
  | letHalt he ih =>
    intro hfuns hcode
    have he' := noExt_stmt_let (noExt_code_stmt hcode)
    simpa using Step.letHalt (ih hfuns (noExt_all_expr he'))
  | assignVal he hlen ih =>
    intro hfuns hcode
    have he' := noExt_stmt_assign (noExt_code_stmt hcode)
    simpa [setMany_uncast] using Step.assignVal (ih hfuns (noExt_all_expr he')) hlen
  | assignHalt he ih =>
    intro hfuns hcode
    have he' := noExt_stmt_assign (noExt_code_stmt hcode)
    simpa using Step.assignHalt (ih hfuns (noExt_all_expr he'))
  | exprStmt he ih =>
    intro hfuns hcode
    exact Step.exprStmt (ih hfuns (noExt_all_expr (noExt_stmt_expr (noExt_code_stmt hcode))))
  | exprStmtHalt he ih =>
    intro hfuns hcode
    exact Step.exprStmtHalt (ih hfuns (noExt_all_expr (noExt_stmt_expr (noExt_code_stmt hcode))))
  | ifTrue he hne hbody ihc ihb =>
    intro hfuns hcode
    have ⟨hc, hb⟩ := noExt_stmt_cond (noExt_code_stmt hcode)
    exact Step.ifTrue (ihc hfuns (noExt_all_expr hc))
      (by simpa [yulD_zero_eq] using hne)
      (ihb hfuns (noExt_all_block_stmt hb))
  | ifFalse he hz ih =>
    intro hfuns hcode
    have ⟨hc, _⟩ := noExt_stmt_cond (noExt_code_stmt hcode)
    exact Step.ifFalse (ih hfuns (noExt_all_expr hc))
      (by simpa [yulD_zero_eq] using hz)
  | ifHalt he ih =>
    intro hfuns hcode
    have ⟨hc, _⟩ := noExt_stmt_cond (noExt_code_stmt hcode)
    exact Step.ifHalt (ih hfuns (noExt_all_expr hc))
  | switchExec he hbody ihc ihb =>
    intro hfuns hcode
    rename_i funs V st c cases dflt cv st1 V' st2 o
    have ⟨hc, hcases, hd⟩ := noExt_stmt_switch (noExt_code_stmt hcode)
    have hsel := noExt_selectSwitch (calls := calls) (cv := cv) cases dflt hcases hd
    exact Step.switchExec (D := evm) (ihc hfuns (noExt_all_expr hc))
      (by
        have := ihb hfuns (noExt_all_block_stmt hsel)
        simpa [selectSwitch_uncast] using this)
  | switchHalt he ih =>
    intro hfuns hcode
    have ⟨hc, _, _⟩ := noExt_stmt_switch (noExt_code_stmt hcode)
    exact Step.switchHalt (D := evm) (ih hfuns (noExt_all_expr hc))
  | forLoop hinit hloop ihi ihl =>
    intro hfuns hcode
    rename_i funs V st init c post body Vinit stinit Vend stend o
    have ⟨hi, hc, hp, hb⟩ := noExt_stmt_for (noExt_code_stmt hcode)
    have hf' := noExtFuns_hoist_cons hi hfuns
    have ihi' := ihi hf' (noExt_all_stmts hi)
    have ihl' := ihl hf' (by
      change NoExternalOps (.loop c post body)
      simp [NoExternalOps, noExtCode, hc, hp, hb])
    rw [funEnvUncast_cons, ← hoist_uncast] at ihi' ihl'
    exact Step.forLoop (D := evm) ihi' ihl'
  | forInitHalt hinit ih =>
    intro hfuns hcode
    rename_i funs V st init c post body Vinit stinit
    have ⟨hi, _, _, _⟩ := noExt_stmt_for (noExt_code_stmt hcode)
    have hf' := noExtFuns_hoist_cons hi hfuns
    have ih' := ih hf' (noExt_all_stmts hi)
    rw [funEnvUncast_cons, ← hoist_uncast] at ih'
    exact Step.forInitHalt (D := evm) ih'
  | «break» =>
    intro _ _; exact Step.«break»
  | «continue» =>
    intro _ _; exact Step.«continue»
  | «leave» =>
    intro _ _; exact Step.leave
  | seqNil =>
    intro _ _; exact Step.seqNil
  | seqCons hs hr ihs ihr =>
    intro hfuns hcode
    have ⟨hs', hr'⟩ := noExt_block_cons (noExt_code_stmts hcode)
    exact Step.seqCons (ihs hfuns (noExt_all_stmt hs'))
      (ihr hfuns (noExt_all_stmts hr'))
  | seqStop hs hne ih =>
    intro hfuns hcode
    have ⟨hs', _⟩ := noExt_block_cons (noExt_code_stmts hcode)
    exact Step.seqStop (ih hfuns (noExt_all_stmt hs')) hne
  | loopDone he hz ih =>
    intro hfuns hcode
    have ⟨hc, _, _⟩ := noExt_code_loop hcode
    exact Step.loopDone (D := evm) (ih hfuns (noExt_all_expr hc))
      (by simpa [yulD_zero_eq] using hz)
  | loopCondHalt he ih =>
    intro hfuns hcode
    have ⟨hc, _, _⟩ := noExt_code_loop hcode
    exact Step.loopCondHalt (D := evm) (ih hfuns (noExt_all_expr hc))
  | loopStep he hne hb ho hp hl ihc ihb ihp ihl =>
    intro hfuns hcode
    have ⟨hc, hp', hb'⟩ := noExt_code_loop hcode
    exact Step.loopStep (D := evm) (ihc hfuns (noExt_all_expr hc))
      (by simpa [yulD_zero_eq] using hne)
      (ihb hfuns (noExt_all_block_stmt hb')) ho
      (ihp hfuns (noExt_all_block_stmt hp'))
      (ihl hfuns hcode)
  | loopPostHalt he hne hb ho hp ihc ihb ihp =>
    intro hfuns hcode
    have ⟨hc, hp', hb'⟩ := noExt_code_loop hcode
    exact Step.loopPostHalt (D := evm) (ihc hfuns (noExt_all_expr hc))
      (by simpa [yulD_zero_eq] using hne)
      (ihb hfuns (noExt_all_block_stmt hb')) ho
      (ihp hfuns (noExt_all_block_stmt hp'))
  | loopBreak he hne hb ihc ihb =>
    intro hfuns hcode
    have ⟨hc, _, hb'⟩ := noExt_code_loop hcode
    exact Step.loopBreak (D := evm) (ihc hfuns (noExt_all_expr hc))
      (by simpa [yulD_zero_eq] using hne)
      (ihb hfuns (noExt_all_block_stmt hb'))
  | loopLeave he hne hb ihc ihb =>
    intro hfuns hcode
    have ⟨hc, _, hb'⟩ := noExt_code_loop hcode
    exact Step.loopLeave (D := evm) (ihc hfuns (noExt_all_expr hc))
      (by simpa [yulD_zero_eq] using hne)
      (ihb hfuns (noExt_all_block_stmt hb'))
  | loopBodyHalt he hne hb ihc ihb =>
    intro hfuns hcode
    have ⟨hc, _, hb'⟩ := noExt_code_loop hcode
    exact Step.loopBodyHalt (D := evm) (ihc hfuns (noExt_all_expr hc))
      (by simpa [yulD_zero_eq] using hne)
      (ihb hfuns (noExt_all_block_stmt hb'))

theorem execStmts_descend {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {ss : YBlock}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hfuns : noExtFuns funs = true) (hss : noExtBlock ss = true)
    (h : ExecStmts (yulD calls) funs V st ss V' st' o) :
    ExecStmts evm (funEnvUncast calls funs) V st ss V' st' o := by
  simpa [resUncast] using step_descend hfuns (noExt_all_stmts hss) h

theorem evalExpr_descend {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {e : YExpr} {r : EResult (yulD calls)}
    (hfuns : noExtFuns funs = true) (he : noExtExpr e = true)
    (h : EvalExpr (yulD calls) funs V st e r) :
    EvalExpr evm (funEnvUncast calls funs) V st e (eresUncast calls r) := by
  simpa [resUncast] using step_descend hfuns (noExt_all_expr he) h

theorem execStmt_descend {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState} {s : YStmt}
    {V' : VEnv (yulD calls)} {st' : EvmState} {o : Outcome}
    (hfuns : noExtFuns funs = true) (hs : noExtStmt s = true)
    (h : ExecStmt (yulD calls) funs V st s V' st' o) :
    ExecStmt evm (funEnvUncast calls funs) V st s V' st' o := by
  simpa [resUncast] using step_descend hfuns (noExt_all_stmt hs) h

theorem step_det_evm {funs V st code r₁ r₂}
    (h₁ : Step evm funs V st code r₁) (h₂ : Step evm funs V st code r₂) :
    r₁ = r₂ :=
  Step.det EVM.evm_deterministic h₁ h₂

theorem execStmts_det_evm {funs V st ss V₁ st₁ o₁ V₂ st₂ o₂}
    (h₁ : ExecStmts evm funs V st ss V₁ st₁ o₁)
    (h₂ : ExecStmts evm funs V st ss V₂ st₂ o₂) :
    V₁ = V₂ ∧ st₁ = st₂ ∧ o₁ = o₂ :=
  ExecStmts.det EVM.evm_deterministic h₁ h₂

theorem evalExpr_det_evm {funs V st e r₁ r₂}
    (h₁ : EvalExpr evm funs V st e r₁) (h₂ : EvalExpr evm funs V st e r₂) :
    r₁ = r₂ :=
  EvalExpr.det EVM.evm_deterministic h₁ h₂

/-- Inverse of `ExecStmts.append`: a run of `a ++ b` is a halt of `a`, or `a` to `.normal`
then `b`. -/
theorem execStmts_cons_inv {D : Dialect} [DecidableEq D.Value]
    {funs : FunEnv D} {V : VEnv D} {st : D.State} {s : YulSemantics.Stmt D.Op}
    {ss : YulSemantics.Block D.Op} {V' : VEnv D} {st' : D.State} {o : Outcome}
    (h : ExecStmts D funs V st (s :: ss) V' st' o) :
    (∃ V1 st1, ExecStmt D funs V st s V1 st1 .normal ∧
      ExecStmts D funs V1 st1 ss V' st' o) ∨
    (o ≠ .normal ∧ ExecStmt D funs V st s V' st' o) := by
  cases h with
  | seqCons h1 h2 => exact .inl ⟨_, _, h1, h2⟩
  | seqStop hs hne => exact .inr ⟨hne, hs⟩

theorem execStmts_append_inv {D : Dialect} [DecidableEq D.Value]
    {funs : FunEnv D} {V : VEnv D} {st : D.State}
    {ss1 ss2 : YulSemantics.Block D.Op}
    {V' : VEnv D} {st' : D.State} {o : Outcome}
    (h : ExecStmts D funs V st (ss1 ++ ss2) V' st' o) :
    (∃ V1 st1, ExecStmts D funs V st ss1 V1 st1 .normal ∧
      ExecStmts D funs V1 st1 ss2 V' st' o) ∨
    (o ≠ .normal ∧ ExecStmts D funs V st ss1 V' st' o) := by
  induction ss1 generalizing V st with
  | nil => exact .inl ⟨V, st, Step.seqNil, h⟩
  | cons s rest ih =>
    rw [List.cons_append] at h
    cases execStmts_cons_inv h with
    | inl h =>
      obtain ⟨V1, st1, hs, ht⟩ := h
      cases ih ht with
      | inl h2 =>
        obtain ⟨V2, st2, hr, hss⟩ := h2
        exact .inl ⟨V2, st2, Step.seqCons hs hr, hss⟩
      | inr h2 =>
        obtain ⟨hne, hr⟩ := h2
        exact .inr ⟨hne, Step.seqCons hs hr⟩
    | inr h =>
      obtain ⟨hne, hs⟩ := h
      exact .inr ⟨hne, Step.seqStop hs hne⟩

theorem execStmts_append_open {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState}
    {ss1 : YBlock} {V1 : VEnv (yulD calls)} {st1 : EvmState} {ss2 : YBlock}
    {V2 : VEnv (yulD calls)} {st2 : EvmState} {o : Outcome}
    (h1 : ExecStmts (yulD calls) funs V st ss1 V1 st1 .normal)
    (h2 : ExecStmts (yulD calls) funs V1 st1 ss2 V2 st2 o) :
    ExecStmts (yulD calls) funs V st (ss1 ++ ss2) V2 st2 o := by
  induction ss1 generalizing V st V1 st1 with
  | nil => cases h1; exact h2
  | cons s rest ih =>
    cases h1 with
    | seqCons hhead htail => exact Step.seqCons hhead (ih htail h2)
    | seqStop _ hne => exact (hne rfl).elim

theorem execStmts_append_halt_open {calls : ExternalCalls} {funs : FunEnv (yulD calls)}
    {V : VEnv (yulD calls)} {st : EvmState}
    {ss1 : YBlock} {V1 : VEnv (yulD calls)} {st1 : EvmState} {ss2 : YBlock}
    (h1 : ExecStmts (yulD calls) funs V st ss1 V1 st1 .halt) :
    ExecStmts (yulD calls) funs V st (ss1 ++ ss2) V1 st1 .halt := by
  induction ss1 generalizing V st with
  | nil => cases h1
  | cons s rest ih =>
    cases h1 with
    | seqCons hhead htail => exact Step.seqCons hhead (ih htail)
    | seqStop hs ho => exact Step.seqStop hs ho

end Lsc.Compiler
