import Lsc.Compiler.Proof.MemFootprint
import Lsc.Compiler.Proof.MemFootprintEmit
import Lsc.Compiler.Proof.MemFootprintOpEval
import Lsc.Compiler.Proof.Words
import Lsc.Compiler.Bytecode
import YulEvmCompiler.Optimizer.Spec.MemoryGuard
import YulEvmCompiler.Optimizer.Implementation.MemorySpill
import YulEvmCompiler.Optimizer.Implementation.MemorySpillLayoutSound

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-!
`Run (evmWithExternal calls creates ExternalGas.any)` of a `staticSafeStmts` program is a `Run guardedEvm`: each memory
builtin is `OpMemorySafe` because pointer/size literals sit in `[0, base)`.
`GuardedRunOfErased` composes that lift with the identity-guard replacement
`if 256 {}` → `if reserved {}`.
-/

namespace Lsc.Compiler

open Lsc hiding Op Stmt
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer
open YulEvmCompiler.Optimizer.MemorySpill
open YulEvmCompiler.Optimizer.MemorySpillSelect

section GuardedLift
variable {calls : ExternalCalls} {creates : ExternalCreates}
variable {base reserved : Nat}

/-! ## FunEnv / Res cast `(evmWithExternal calls creates ExternalGas.any)` → `(guardedEvm calls creates base reserved)` -/

def toGuardedEResult : EResult (evmWithExternal calls creates ExternalGas.any) → EResult (guardedEvm calls creates base reserved)
  | .vals values state => .vals values state
  | .halt state => .halt state

def toGuardedRes : Res (evmWithExternal calls creates ExternalGas.any) → Res (guardedEvm calls creates base reserved)
  | .eres result => .eres (toGuardedEResult result)
  | .sres vars state outcome => .sres vars state outcome

def toGuardedDecl (decl : FDecl (evmWithExternal calls creates ExternalGas.any)) : FDecl (guardedEvm calls creates base reserved) :=
  { params := decl.params, rets := decl.rets, body := decl.body }

def toGuardedScope (scope : FScope (evmWithExternal calls creates ExternalGas.any)) : FScope (guardedEvm calls creates base reserved) :=
  scope.map fun item => (item.1, toGuardedDecl item.2)

def toGuardedFuns (funs : FunEnv (evmWithExternal calls creates ExternalGas.any)) : FunEnv (guardedEvm calls creates base reserved) :=
  funs.map toGuardedScope

@[simp] theorem toGuardedScope_hoist (body : YBlock) :
    toGuardedScope (hoist (evmWithExternal calls creates ExternalGas.any) body) = hoist (guardedEvm calls creates base reserved) body := by
  induction body with
  | nil => rfl
  | cons stmt rest ih =>
    cases stmt <;>
      simpa [hoist, toGuardedScope, toGuardedDecl] using ih

private theorem toGuardedScope_find (scope : FScope (evmWithExternal calls creates ExternalGas.any)) (fn : Ident) :
    (toGuardedScope (base := base) (reserved := reserved) scope).find? (fun item => item.1 = fn) =
      (scope.find? fun item => item.1 = fn).map
        (fun item => (item.1, toGuardedDecl (base := base) (reserved := reserved) item.2)) := by
  unfold toGuardedScope
  rw [List.find?_map]
  rfl

@[simp] theorem toGuardedFuns_lookup (funs : FunEnv (evmWithExternal calls creates ExternalGas.any)) (fn : Ident) :
    lookupFun (toGuardedFuns (base := base) (reserved := reserved) funs) fn =
      (lookupFun funs fn).map fun result =>
        (toGuardedDecl (base := base) (reserved := reserved) result.1,
          toGuardedFuns (base := base) (reserved := reserved) result.2) := by
  induction funs with
  | nil => rfl
  | cons scope rest ih =>
    simp only [toGuardedFuns, List.map_cons, lookupFun]
    rw [toGuardedScope_find (base := base) (reserved := reserved)]
    cases hfind : scope.find? (fun item => item.1 = fn) with
    | none =>
      simp only [Option.map_none]
      exact ih
    | some item =>
      simp only [Option.map_some]
      rfl

theorem toGuardedFuns_lookup_some {funs : FunEnv (evmWithExternal calls creates ExternalGas.any)} {fn : Ident}
    {decl : FDecl (evmWithExternal calls creates ExternalGas.any)} {closure : FunEnv (evmWithExternal calls creates ExternalGas.any)}
    (hlookup : lookupFun funs fn = some (decl, closure)) :
    lookupFun (toGuardedFuns (base := base) (reserved := reserved) funs) fn =
      some (toGuardedDecl (base := base) (reserved := reserved) decl,
        toGuardedFuns (base := base) (reserved := reserved) closure) := by
  rw [toGuardedFuns_lookup (base := base) (reserved := reserved), hlookup]
  rfl

@[simp] theorem guarded_bindZeros (names : List Ident) :
    bindZeros (guardedEvm calls creates base reserved) names = bindZeros (evmWithExternal calls creates ExternalGas.any) names := rfl

@[simp] theorem guarded_selectSwitch (value : U256)
    (cases : List (Literal × YBlock)) (dflt : Option YBlock) :
    selectSwitch (guardedEvm calls creates base reserved) value cases dflt = selectSwitch (evmWithExternal calls creates ExternalGas.any) value cases dflt := by
  have hp : (fun p : Literal × YBlock =>
      decide (value = Dialect.litValue (guardedEvm calls creates base reserved) p.1)) =
      (fun p : Literal × YBlock =>
        decide (value = Dialect.litValue (evmWithExternal calls creates ExternalGas.any) p.1)) := by
    funext p
    congr
  unfold selectSwitch
  rw [hp]
  cases List.find? (fun p => decide (value = Dialect.litValue (evmWithExternal calls creates ExternalGas.any) p.1)) cases <;> rfl

@[simp] theorem guarded_set (vars : VEnv (evmWithExternal calls creates ExternalGas.any)) (name : Ident) (value : U256) :
    @VEnv.set (guardedEvm calls creates base reserved) vars name value = @VEnv.set (evmWithExternal calls creates ExternalGas.any) vars name value := by
  induction vars with
  | nil => rfl
  | cons item rest ih =>
    obtain ⟨head, old⟩ := item
    by_cases hhead : head = name
    · simp [VEnv.set, hhead]
    · simp [VEnv.set, hhead, ih]

private theorem guarded_set_fold (items : List (Ident × U256)) (vars : VEnv (evmWithExternal calls creates ExternalGas.any)) :
    items.foldl (fun env item => @VEnv.set (guardedEvm calls creates base reserved) env item.1 item.2) vars =
      items.foldl (fun env item => @VEnv.set (evmWithExternal calls creates ExternalGas.any) env item.1 item.2) vars := by
  induction items generalizing vars with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.foldl_cons]
    rw [guarded_set]
    exact ih _

@[simp] theorem guarded_setMany (vars : VEnv (evmWithExternal calls creates ExternalGas.any)) (names : List Ident)
    (values : List U256) :
    @VEnv.setMany (guardedEvm calls creates base reserved) vars names values = @VEnv.setMany (evmWithExternal calls creates ExternalGas.any) vars names values := by
  unfold VEnv.setMany
  exact guarded_set_fold (names.zip values) vars

theorem guarded_zero : Dialect.zero (guardedEvm calls creates base reserved) = Dialect.zero (evmWithExternal calls creates ExternalGas.any) := rfl

/-! ## `staticSafe` of `Code` and `FunEnv` -/

def staticSafeCode (base : Nat) : Code YOp → Bool
  | .expr e => staticSafeExpr base e
  | .args es => staticSafeExprs base es
  | .stmt s => staticSafeStmt base s
  | .stmts ss => staticSafeStmts base ss
  | .loop c post body =>
      staticSafeExpr base c && staticSafeStmts base post && staticSafeStmts base body

@[simp] theorem staticSafeCode_expr (base : Nat) (e : YExpr) :
    staticSafeCode base (.expr e) = staticSafeExpr base e := rfl
@[simp] theorem staticSafeCode_args (base : Nat) (es : List YExpr) :
    staticSafeCode base (.args es) = staticSafeExprs base es := rfl
@[simp] theorem staticSafeCode_stmt (base : Nat) (s : YStmt) :
    staticSafeCode base (.stmt s) = staticSafeStmt base s := rfl
@[simp] theorem staticSafeCode_stmts (base : Nat) (ss : YBlock) :
    staticSafeCode base (.stmts ss) = staticSafeStmts base ss := rfl
@[simp] theorem staticSafeCode_loop (base : Nat) (c : YExpr) (post body : YBlock) :
    staticSafeCode base (.loop c post body) =
      (staticSafeExpr base c && staticSafeStmts base post &&
        staticSafeStmts base body) := rfl

def scopeSafe (base : Nat) (scope : FScope (evmWithExternal calls creates ExternalGas.any)) : Prop :=
  ∀ p ∈ scope, staticSafeStmts base p.2.body = true

def funsSafe (base : Nat) (funs : FunEnv (evmWithExternal calls creates ExternalGas.any)) : Prop :=
  ∀ s ∈ funs, scopeSafe base s

theorem funsSafe_nil : funsSafe base ([] : FunEnv (evmWithExternal calls creates ExternalGas.any)) := by
  intro s hs; cases hs

theorem staticSafeStmts_mem {ss : YBlock} {s : YStmt}
    (h : staticSafeStmts base ss = true) (hs : s ∈ ss) :
    staticSafeStmt base s = true := by
  induction ss with
  | nil => cases hs
  | cons x rest ih =>
    simp only [staticSafeStmts, Bool.and_eq_true] at h
    simp only [List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact h.1
    · exact ih h.2 hs

theorem scopeSafe_hoist {body : YBlock} (h : staticSafeStmts base body = true) :
    scopeSafe base (hoist (evmWithExternal calls creates ExternalGas.any) body) := by
  induction body with
  | nil =>
    intro p hp
    simp [hoist] at hp
  | cons s rest ih =>
    simp only [staticSafeStmts, Bool.and_eq_true] at h
    intro p hp
    cases s with
    | funDef n ps rs b =>
      simp [hoist] at hp
      rcases hp with hpeq | hp
      · cases hpeq
        simpa [staticSafeStmt] using h.1
      · exact ih h.2 p (List.mem_filterMap.mpr hp)
    | block _ | letDecl _ _ | assign _ _ | cond _ _ | «switch» _ _ _
    | «forLoop» _ _ _ _ | «break» | «continue» | «leave» | exprStmt _ =>
      simp [hoist] at hp
      exact ih h.2 p (List.mem_filterMap.mpr hp)

theorem funsSafe_cons_hoist {body : YBlock} {funs : FunEnv (evmWithExternal calls creates ExternalGas.any)}
    (h : staticSafeStmts base body = true) (hf : funsSafe base funs) :
    funsSafe base (hoist (evmWithExternal calls creates ExternalGas.any) body :: funs) := by
  intro s hs
  simp only [List.mem_cons] at hs
  rcases hs with rfl | hs
  · exact scopeSafe_hoist h
  · exact hf s hs

theorem find?_mem_of_eq_some {α} {p : α → Bool} {l : List α} {x : α}
    (h : l.find? p = some x) : x ∈ l := by
  induction l with
  | nil => simp [List.find?] at h
  | cons y rest ih =>
    simp only [List.find?] at h
    split at h
    · next hp =>
      cases h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem funsSafe_lookup {funs : FunEnv (evmWithExternal calls creates ExternalGas.any)} {fn : Ident} {decl : FDecl (evmWithExternal calls creates ExternalGas.any)}
    {cenv : FunEnv (evmWithExternal calls creates ExternalGas.any)} (hf : funsSafe base funs)
    (h : lookupFun funs fn = some (decl, cenv)) :
    staticSafeStmts base decl.body = true ∧ funsSafe base cenv := by
  induction funs with
  | nil => cases h
  | cons scope rest ih =>
    simp only [lookupFun] at h
    cases hfind : scope.find? (fun p => p.1 = fn) with
    | none =>
      simp [hfind] at h
      exact ih (fun s hs => hf s (List.mem_cons_of_mem _ hs)) h
    | some item =>
      simp [hfind] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, ?_⟩
      · have hmem := find?_mem_of_eq_some hfind
        exact hf scope List.mem_cons_self item hmem
      · intro s hs
        exact hf s hs

def staticSafeDflt (base : Nat) : Option YBlock → Bool
  | none => true
  | some b => staticSafeStmts base b

theorem staticSafe_switch_parts {c : YExpr} {cases : List (Literal × YBlock)}
    {dflt : Option YBlock}
    (h : staticSafeStmt base (.switch c cases dflt) = true) :
    staticSafeExpr base c = true ∧
      staticSafeCases base cases = true ∧
      staticSafeDflt base dflt = true := by
  cases dflt with
  | none =>
    simp [staticSafeStmt, staticSafeDflt, Bool.and_eq_true] at h
    exact ⟨h.1, h.2, rfl⟩
  | some b =>
    simp [staticSafeStmt, staticSafeDflt, Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2, h.2⟩

theorem staticSafe_selectSwitch {cv : U256}
    {cases : List (Literal × YBlock)} {dflt : Option YBlock}
    (hc : staticSafeCases base cases = true)
    (hd : staticSafeDflt base dflt = true) :
    staticSafeStmts base (selectSwitch (evmWithExternal calls creates ExternalGas.any) cv cases dflt) = true := by
  induction cases with
  | nil =>
    simp [selectSwitch, List.find?] at hc ⊢
    cases dflt with
    | none => simp [staticSafeStmts]
    | some b => simpa [staticSafeDflt] using hd
  | cons p rest ih =>
    simp only [staticSafeCases, Bool.and_eq_true] at hc
    simp [selectSwitch, List.find?]
    cases hdec : decide (cv = Dialect.litValue (evmWithExternal calls creates ExternalGas.any) p.1)
    · exact ih hc.2
    · exact hc.1

/-! ## Step lift -/

theorem step_to_guarded {funs : FunEnv (evmWithExternal calls creates ExternalGas.any)} {V : VEnv (evmWithExternal calls creates ExternalGas.any)} {st : EvmState}
    {code : Code YOp} {result : Res (evmWithExternal calls creates ExternalGas.any)} (hbase : base < wordBound)
    (hstep : Step (evmWithExternal calls creates ExternalGas.any) funs V st code result)
    (hs : staticSafeCode base code = true)
    (hf : funsSafe base funs) :
    Step (guardedEvm calls creates base reserved) (toGuardedFuns funs) V st code (toGuardedRes result) := by
  induction hstep with
  | lit => exact .lit
  | var hget => exact .var hget
  | builtinOk hargs hop ih =>
    simp only [staticSafeCode, staticSafeExpr, Bool.and_eq_true] at hs
    exact .builtinOk (ih hs.2 hf) ⟨hop, staticSafeOp_eval hbase hs.1 hargs⟩
  | builtinHalt hargs hop ih =>
    simp only [staticSafeCode, staticSafeExpr, Bool.and_eq_true] at hs
    exact .builtinHalt (ih hs.2 hf) ⟨hop, staticSafeOp_eval hbase hs.1 hargs⟩
  | builtinArgsHalt hargs ih =>
    simp only [staticSafeCode, staticSafeExpr, Bool.and_eq_true] at hs
    exact .builtinArgsHalt (ih hs.2 hf)
  | callOk hargs hlookup hlen hbody hout ihArgs ihBody =>
    simp only [staticSafeCode, staticSafeExpr] at hs
    obtain ⟨hb, hcenv⟩ := funsSafe_lookup hf hlookup
    exact .callOk (ihArgs hs hf) (toGuardedFuns_lookup_some hlookup) hlen
      (by simpa [toGuardedRes, toGuardedDecl] using
        ihBody (by simp [staticSafeCode, staticSafeStmt, hb]) hcenv) hout
  | callHalt hargs hlookup hlen hbody ihArgs ihBody =>
    simp only [staticSafeCode, staticSafeExpr] at hs
    obtain ⟨hb, hcenv⟩ := funsSafe_lookup hf hlookup
    exact .callHalt (ihArgs hs hf) (toGuardedFuns_lookup_some hlookup) hlen
      (by simpa [toGuardedRes, toGuardedDecl] using
        ihBody (by simp [staticSafeCode, staticSafeStmt, hb]) hcenv)
  | callArgsHalt hargs ih =>
    simp only [staticSafeCode, staticSafeExpr] at hs
    exact .callArgsHalt (ih hs hf)
  | argsNil => exact .argsNil
  | argsCons hrest hhead ihRest ihHead =>
    simp only [staticSafeCode, staticSafeExprs, Bool.and_eq_true] at hs
    exact .argsCons (ihRest hs.2 hf) (ihHead (by simp [staticSafeCode, hs.1]) hf)
  | argsRestHalt hrest ih =>
    simp only [staticSafeCode, staticSafeExprs, Bool.and_eq_true] at hs
    exact .argsRestHalt (ih hs.2 hf)
  | argsHeadHalt hrest hhead ihRest ihHead =>
    simp only [staticSafeCode, staticSafeExprs, Bool.and_eq_true] at hs
    exact .argsHeadHalt (ihRest hs.2 hf) (ihHead (by simp [staticSafeCode, hs.1]) hf)
  | funDef => exact .funDef
  | block hbody ih =>
    simp only [staticSafeCode, staticSafeStmt] at hs
    apply Step.block
    simpa [toGuardedFuns, toGuardedRes] using
      ih (by simp [staticSafeCode, hs]) (funsSafe_cons_hoist hs hf)
  | letZero => exact .letZero
  | letVal heval hlen ih =>
    simp only [staticSafeCode, staticSafeStmt] at hs
    exact .letVal (ih (by simp [staticSafeCode, hs]) hf) hlen
  | letHalt heval ih =>
    simp only [staticSafeCode, staticSafeStmt] at hs
    exact .letHalt (ih (by simp [staticSafeCode, hs]) hf)
  | assignVal heval hlen ih =>
    simp only [staticSafeCode, staticSafeStmt] at hs
    simpa [toGuardedRes, guarded_setMany] using
      Step.assignVal (ih (by simp [staticSafeCode, hs]) hf) hlen
  | assignHalt heval ih =>
    simp only [staticSafeCode, staticSafeStmt] at hs
    exact .assignHalt (ih (by simp [staticSafeCode, hs]) hf)
  | exprStmt heval ih =>
    simp only [staticSafeCode, staticSafeStmt] at hs
    exact .exprStmt (ih (by simp [staticSafeCode, hs]) hf)
  | exprStmtHalt heval ih =>
    simp only [staticSafeCode, staticSafeStmt] at hs
    exact .exprStmtHalt (ih (by simp [staticSafeCode, hs]) hf)
  | ifTrue hcond hnzero hbody ihCond ihBody =>
    simp only [staticSafeCode, staticSafeStmt, Bool.and_eq_true] at hs
    exact .ifTrue (ihCond (by simp [staticSafeCode, hs.1]) hf)
      (by simpa [guarded_zero] using hnzero)
      (ihBody (by simp [staticSafeCode, staticSafeStmt, hs.2]) hf)
  | ifFalse hcond hzero ih =>
    simp only [staticSafeCode, staticSafeStmt, Bool.and_eq_true] at hs
    exact .ifFalse (ih (by simp [staticSafeCode, hs.1]) hf)
      (by simpa [guarded_zero] using hzero)
  | ifHalt hcond ih =>
    simp only [staticSafeCode, staticSafeStmt, Bool.and_eq_true] at hs
    exact .ifHalt (ih (by simp [staticSafeCode, hs.1]) hf)
  | switchExec hcond hbody ihCond ihBody =>
    have hparts := staticSafe_switch_parts hs
    exact .switchExec (ihCond (by simp [staticSafeCode, hparts.1]) hf)
      (by simpa [toGuardedRes, guarded_selectSwitch] using
        ihBody (by
          change staticSafeCode base (.stmt (.block _)) = true
          exact staticSafe_selectSwitch (calls := calls) (creates := creates) (base := base)
            hparts.2.1 hparts.2.2) hf)
  | switchHalt hcond ih =>
    have hparts := staticSafe_switch_parts hs
    exact .switchHalt (ih (by simp [staticSafeCode, hparts.1]) hf)
  | forLoop hinit hloop ihInit ihLoop =>
    simp only [staticSafeCode, staticSafeStmt, Bool.and_eq_true] at hs
    have hf' := funsSafe_cons_hoist hs.1.1.1 hf
    apply Step.forLoop
    · simpa [toGuardedFuns, toGuardedRes] using
        ihInit (by simp [staticSafeCode, hs.1.1.1]) hf'
    · simpa [toGuardedFuns, toGuardedRes] using
        ihLoop (by simp [staticSafeCode, hs.1.1.2, hs.1.2, hs.2]) hf'
  | forInitHalt hinit ih =>
    simp only [staticSafeCode, staticSafeStmt, Bool.and_eq_true] at hs
    apply Step.forInitHalt
    simpa [toGuardedFuns, toGuardedRes] using
      ih (by simp [staticSafeCode, hs.1.1.1]) (funsSafe_cons_hoist hs.1.1.1 hf)
  | «break» => exact .break
  | «continue» => exact .continue
  | «leave» => exact .leave
  | seqNil => exact .seqNil
  | seqCons hhead hrest ihHead ihRest =>
    simp only [staticSafeCode, staticSafeStmts, Bool.and_eq_true] at hs
    exact .seqCons (ihHead (by simp [staticSafeCode, hs.1]) hf)
      (ihRest (by simp [staticSafeCode, hs.2]) hf)
  | seqStop hhead hne ih =>
    simp only [staticSafeCode, staticSafeStmts, Bool.and_eq_true] at hs
    exact .seqStop (ih (by simp [staticSafeCode, hs.1]) hf) hne
  | loopDone hcond hzero ih =>
    simp only [staticSafeCode, Bool.and_eq_true] at hs
    exact .loopDone (ih (by simp [staticSafeCode, hs.1.1]) hf)
      (by simpa [guarded_zero] using hzero)
  | loopCondHalt hcond ih =>
    simp only [staticSafeCode, Bool.and_eq_true] at hs
    exact .loopCondHalt (ih (by simp [staticSafeCode, hs.1.1]) hf)
  | loopStep hcond hnzero hbody hout hpost hloop ihCond ihBody ihPost ihLoop =>
    simp only [staticSafeCode, Bool.and_eq_true] at hs
    exact .loopStep (ihCond (by simp [staticSafeCode, hs.1.1]) hf)
      (by simpa [guarded_zero] using hnzero)
      (ihBody (by simp [staticSafeCode, staticSafeStmt, hs.2]) hf) hout
      (ihPost (by simp [staticSafeCode, staticSafeStmt, hs.1.2]) hf)
      (ihLoop (by simp [staticSafeCode, hs]) hf)
  | loopPostHalt hcond hnzero hbody hout hpost ihCond ihBody ihPost =>
    simp only [staticSafeCode, Bool.and_eq_true] at hs
    exact .loopPostHalt (ihCond (by simp [staticSafeCode, hs.1.1]) hf)
      (by simpa [guarded_zero] using hnzero)
      (ihBody (by simp [staticSafeCode, staticSafeStmt, hs.2]) hf) hout
      (ihPost (by simp [staticSafeCode, staticSafeStmt, hs.1.2]) hf)
  | loopBreak hcond hnzero hbody ihCond ihBody =>
    simp only [staticSafeCode, Bool.and_eq_true] at hs
    exact .loopBreak (ihCond (by simp [staticSafeCode, hs.1.1]) hf)
      (by simpa [guarded_zero] using hnzero)
      (ihBody (by simp [staticSafeCode, staticSafeStmt, hs.2]) hf)
  | loopLeave hcond hnzero hbody ihCond ihBody =>
    simp only [staticSafeCode, Bool.and_eq_true] at hs
    exact .loopLeave (ihCond (by simp [staticSafeCode, hs.1.1]) hf)
      (by simpa [guarded_zero] using hnzero)
      (ihBody (by simp [staticSafeCode, staticSafeStmt, hs.2]) hf)
  | loopBodyHalt hcond hnzero hbody ihCond ihBody =>
    simp only [staticSafeCode, Bool.and_eq_true] at hs
    exact .loopBodyHalt (ihCond (by simp [staticSafeCode, hs.1.1]) hf)
      (by simpa [guarded_zero] using hnzero)
      (ihBody (by simp [staticSafeCode, staticSafeStmt, hs.2]) hf)

theorem run_to_guarded {prog : YBlock} {st0 : EvmState} {V' : VEnv (evmWithExternal calls creates ExternalGas.any)}
    {st' : EvmState} {o : Outcome} (hbase : base < wordBound)
    (hs : staticSafeStmts base prog = true)
    (h : Run (evmWithExternal calls creates ExternalGas.any) prog st0 V' st' o) :
    Run (guardedEvm calls creates base reserved) prog st0 V' st' o := by
  simpa [Run, toGuardedFuns, toGuardedRes] using
    step_to_guarded hbase h (by simp [staticSafeCode, staticSafeStmt, hs]) funsSafe_nil

end GuardedLift

/-! ## Identity-guard replacement -/

theorem evalExpr_lit_number {D : Dialect} [DecidableEq D.Value]
    {funs : FunEnv D} {V : VEnv D} {st : D.State} {n : Nat} {r : EResult D}
    (h : EvalExpr D funs V st (.lit (.number n)) r) :
    r = .vals [D.litValue (.number n)] st := by
  cases h
  rfl

theorem exec_block_nil {D : Dialect} [DecidableEq D.Value]
    {funs : FunEnv D} {V : VEnv D} {st : D.State} :
    ExecStmt D funs V st (.block []) V st .normal := by
  have hb : ExecStmt D funs V st (.block []) (restore V V) st .normal :=
    Step.block (D := D) (by
      change ExecStmts D (hoist D [] :: funs) V st [] V st .normal
      exact Step.seqNil)
  simpa [restore] using hb

theorem exec_cond_lit_empty_inv {D : Dialect} [DecidableEq D.Value]
    {funs : FunEnv D} {V V' : VEnv D} {st st' : D.State} {n : Nat} {o : Outcome}
    (hne : D.litValue (.number n) ≠ D.zero)
    (h : ExecStmt D funs V st (.cond (.lit (.number n)) []) V' st' o) :
    V' = V ∧ st' = st ∧ o = .normal := by
  cases h with
  | ifTrue hc hn hb =>
    have hr := evalExpr_lit_number hc
    injection hr with hvs hst
    injection hvs with hv
    subst hv; subst hst
    cases hb with
    | block hbody =>
      cases hbody
      simp [restore]
  | ifFalse hc hz =>
    have hr := evalExpr_lit_number hc
    injection hr with hvs
    injection hvs with hv
    subst hv
    exact absurd hz hne
  | ifHalt hc =>
    have hr := evalExpr_lit_number hc
    injection hr

theorem execStmts_replace_identity_guard {D : Dialect} [DecidableEq D.Value]
    {funs : FunEnv D} {V V' : VEnv D} {st st' : D.State} {n m : Nat}
    {tail : Block D.Op} {o : Outcome}
    (hn : D.litValue (.number n) ≠ D.zero)
    (hm : D.litValue (.number m) ≠ D.zero)
    (h : ExecStmts D funs V st (.cond (.lit (.number n)) [] :: tail) V' st' o) :
    ExecStmts D funs V st (.cond (.lit (.number m)) [] :: tail) V' st' o := by
  cases h with
  | seqCons hh hr =>
    obtain ⟨rfl, rfl, ho⟩ := exec_cond_lit_empty_inv hn hh
    cases ho
    exact Step.seqCons (exec_cond_lit_empty hm) hr
  | seqStop hh hne =>
    obtain ⟨_, _, ho⟩ := exec_cond_lit_empty_inv hn hh
    cases ho
    exact absurd rfl hne

theorem hoist_cons_cond (D : Dialect) (c : Expr D.Op) (b tail : Block D.Op) :
    hoist D (.cond c b :: tail) = hoist D tail := rfl

theorem run_replace_identity_guard {D : Dialect} [DecidableEq D.Value]
    {n m : Nat} {tail : Block D.Op} {st0 : D.State} {V' : VEnv D}
    {st' : D.State} {o : Outcome}
    (hn : D.litValue (.number n) ≠ D.zero)
    (hm : D.litValue (.number m) ≠ D.zero)
    (h : Run D (.cond (.lit (.number n)) [] :: tail) st0 V' st' o) :
    Run D (.cond (.lit (.number m)) [] :: tail) st0 V' st' o := by
  cases h with
  | block hbody =>
    rw [hoist_cons_cond] at hbody
    refine Step.block ?_
    rw [hoist_cons_cond]
    exact execStmts_replace_identity_guard hn hm hbody

/-! ## `collectMemoryGuards` of a `runtimeBlock` -/

mutual
theorem collect_noYulCallExpr (e : YExpr) (h : noYulCallExpr e = true) :
    collectMemoryGuardsExpr? e = some [] := by
  cases e with
  | lit _ | var _ => simp [collectMemoryGuardsExpr?]
  | builtin op args =>
    simp only [noYulCallExpr] at h
    simp [collectMemoryGuardsExpr?, collect_noYulCallArgs args h]
  | call _ _ =>
    simp [noYulCallExpr] at h
termination_by sizeOf e

theorem collect_noYulCallArgs (args : List YExpr) (h : noYulCallExprs args = true) :
    collectMemoryGuardsArgs? args = some [] := by
  cases args with
  | nil => simp [collectMemoryGuardsArgs?]
  | cons e es =>
    simp only [noYulCallExprs, Bool.and_eq_true] at h
    simp [collectMemoryGuardsArgs?, collect_noYulCallExpr e h.1,
      collect_noYulCallArgs es h.2]
termination_by sizeOf args
end

mutual
theorem collect_noYulCallStmt (s : YStmt) (h : noYulCallStmt s = true) :
    collectMemoryGuardsStmt? s = some [] := by
  cases s with
  | block b =>
    simp [collectMemoryGuardsStmt?, collect_noYulCallStmts b h]
  | funDef n ps rs b =>
    simp [collectMemoryGuardsStmt?, collect_noYulCallStmts b h]
  | letDecl xs val =>
    cases val with
    | none => simp [collectMemoryGuardsStmt?]
    | some e =>
      simp only [noYulCallStmt] at h
      simp [collectMemoryGuardsStmt?, collect_noYulCallExpr e h]
  | assign xs e =>
    simp only [noYulCallStmt] at h
    simp [collectMemoryGuardsStmt?, collect_noYulCallExpr e h]
  | cond c b =>
    simp only [noYulCallStmt, Bool.and_eq_true] at h
    simp [collectMemoryGuardsStmt?, collect_noYulCallExpr c h.1,
      collect_noYulCallStmts b h.2]
  | «switch» c cases dflt =>
    cases dflt with
    | none =>
      simp only [noYulCallStmt, Bool.and_eq_true] at h
      simp [collectMemoryGuardsStmt?, collect_noYulCallExpr c h.1.1,
        collect_noYulCallCases cases h.1.2]
    | some b =>
      simp only [noYulCallStmt, Bool.and_eq_true] at h
      simp [collectMemoryGuardsStmt?, collect_noYulCallExpr c h.1.1,
        collect_noYulCallCases cases h.1.2, collect_noYulCallStmts b h.2]
  | «forLoop» init c post body =>
    simp only [noYulCallStmt, Bool.and_eq_true] at h
    simp [collectMemoryGuardsStmt?, collect_noYulCallStmts init h.1.1.1,
      collect_noYulCallExpr c h.1.1.2, collect_noYulCallStmts post h.1.2,
      collect_noYulCallStmts body h.2]
  | «break» => simp [collectMemoryGuardsStmt?]
  | «continue» => simp [collectMemoryGuardsStmt?]
  | «leave» => simp [collectMemoryGuardsStmt?]
  | exprStmt e =>
    simp only [noYulCallStmt] at h
    simp [collectMemoryGuardsStmt?, collect_noYulCallExpr e h]
termination_by sizeOf s

theorem collect_noYulCallStmts (b : YBlock) (h : noYulCallStmts b = true) :
    collectMemoryGuardsStmts? b = some [] := by
  cases b with
  | nil => simp [collectMemoryGuardsStmts?]
  | cons s rest =>
    simp only [noYulCallStmts, Bool.and_eq_true] at h
    simp [collectMemoryGuardsStmts?, collect_noYulCallStmt s h.1,
      collect_noYulCallStmts rest h.2]
termination_by sizeOf b

theorem collect_noYulCallCases (cases : List (Literal × YBlock))
    (h : noYulCallCases cases = true) :
    collectMemoryGuardsCases? cases = some [] := by
  cases cases with
  | nil => simp [collectMemoryGuardsCases?]
  | cons p rest =>
    cases p with
    | mk l b =>
      simp only [noYulCallCases, Bool.and_eq_true] at h
      simp [collectMemoryGuardsCases?, collect_noYulCallStmts b h.1,
        collect_noYulCallCases rest h.2]
termination_by sizeOf cases
end

theorem collect_memoryGuardStmt :
    collectMemoryGuardsStmt? memoryGuardStmt = some [memoryGuardK] := by
  simp [memoryGuardStmt, collectMemoryGuardsStmt?, collectMemoryGuardsExpr?,
    collectMemoryGuardsStmts?, lit]

theorem collect_runtimeBlock {c yul} (h : runtimeBlock c = some yul) :
    collectMemoryGuardsStmts? yul = some [memoryGuardK] := by
  obtain ⟨_, cs, hmap, hy⟩ := runtimeBlock_inv h
  subst yul
  have htail := noYulCall_dispatchTail (emitGuardLt {} 4).stmts _ cs
    (noYulCall_guardLt 4) noYulCall_selector (mapM_entryCase_noYulCall hmap)
  simp [collectMemoryGuardsStmts?, collect_memoryGuardStmt,
    collect_noYulCallStmts _ htail]

theorem spillRuntime_base {c rt r} (hrt : runtimeBlock c = some rt)
    (hsp : spillRuntime? rt = some r) : r.base = memoryGuardK := by
  unfold spillRuntime? at hsp
  obtain ⟨guards, hf⟩ := spillBlock_facts hsp
  have hcol := collect_runtimeBlock hrt
  have hguards : guards = [memoryGuardK] :=
    Option.some.inj (hf.guards_collected.symm.trans hcol)
  have hhead := hf.guards_head
  simp [hguards] at hhead
  exact hhead.symm

theorem spillRuntime_reserved_facts {rt r} (hsp : spillRuntime? rt = some r) :
    r.reserved ≠ 0 ∧ r.reserved < wordBound := by
  unfold spillRuntime? at hsp
  obtain ⟨guards, hf⟩ := spillBlock_facts hsp
  refine ⟨?_, ?_⟩
  · intro hz
    have hres := hf.reserved_eq
    have hw := hf.words_nonzero
    have : r.base + 32 * r.layout.words = 0 := by
      simpa [hres] using hz
    omega
  · simpa [wordBound] using hf.reserved_lt

theorem memoryGuardK_pos : memoryGuardK ≠ 0 := by
  simp [memoryGuardK]

theorem guarded_litValue_ne_zero {calls : ExternalCalls} {creates : ExternalCreates}
    {base reserved n : Nat} (hn : n ≠ 0) (hlt : n < wordBound) :
    (guardedEvm calls creates base reserved).litValue (.number n) ≠
      Dialect.zero (guardedEvm calls creates base reserved) := by
  intro heq
  have h1 : (BitVec.ofNat 256 n).toNat = n := toNat_ofNat_of_lt hlt
  have h0 : (BitVec.ofNat 256 0).toNat = 0 := by simp
  have : n = 0 := by
    simp [Dialect.zero, litValue] at heq
    exact h1.symm.trans ((congrArg BitVec.toNat heq).trans h0)
  exact hn this

/-- A `Run` of the memoryguard-erased runtime in the ordinary dialect is a
`GuardedRun` of the raw runtime: every executed memory builtin stays in
`[0, memoryGuardK)`, and the discarded `if 256 {}` is replaced by
`if reserved {}`. Parametric in the call/create oracles (`run_to_guarded`
already is); S1 instantiates `.none`, S2 the open CALL oracle. -/
theorem GuardedRunOfErased {calls : ExternalCalls} {creates : ExternalCreates}
    {c : ContractDef} {rt : YBlock}
    {r : MemorySpillSelect.Result} {yst0 yst' : EvmState} {o : Outcome}
    (hrt : runtimeBlock c = some rt) (hsp : spillRuntime? rt = some r)
    (h : Run (evmWithExternal calls creates ExternalGas.any)
      (eraseMemoryGuardStmts rt) yst0 [] yst' o) :
    GuardedRun calls creates rt r.base r.reserved
      yst0 [] yst' o := by
  have hbase : r.base = memoryGuardK := spillRuntime_base hrt hsp
  have ⟨hneR, hltR⟩ := spillRuntime_reserved_facts hsp
  have hG :
      Run (guardedEvm calls creates memoryGuardK r.reserved)
        (eraseMemoryGuardStmts rt) yst0 [] yst' o :=
    run_to_guarded (calls := calls) (creates := creates) (base := memoryGuardK)
      (reserved := r.reserved) memoryGuardK_lt_wordBound (staticSafe_erase_runtime hrt) h
  obtain ⟨cs, hmapE, hE⟩ := erase_runtimeBlock hrt
  obtain ⟨cs', hmapR, hR⟩ := resolve_runtimeBlock hrt r.reserved
  have hcs : cs' = cs := Option.some.inj (hmapR.symm.trans hmapE)
  subst hcs
  rw [hE] at hG
  have hG' :=
    run_replace_identity_guard
      (D := guardedEvm calls creates memoryGuardK r.reserved)
      (n := memoryGuardK) (m := r.reserved)
      (guarded_litValue_ne_zero (calls := calls) (creates := creates)
        (base := memoryGuardK) (reserved := r.reserved)
        memoryGuardK_pos memoryGuardK_lt_wordBound)
      (guarded_litValue_ne_zero (calls := calls) (creates := creates)
        (base := memoryGuardK) (reserved := r.reserved) hneR hltR)
      (by simpa [memoryGuardErased, lit] using hG)
  show Run (guardedEvm calls creates r.base r.reserved)
      (resolveMemoryGuardStmts r.base r.reserved rt) yst0 [] yst' o
  rw [hbase, hR]
  simpa [lit] using hG'

end Lsc.Compiler
