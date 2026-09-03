import Lsc.Compile.IR.Builder
import Lsc.Compile.IR.EvalLemmas

namespace Lsc.Compile.IR.Builder

/-- Execute the bindings accumulated by a builder. -/
def run (st : IRState) (build : Build) : IRState :=
  evalStmt st (build.finish .skip)

theorem eval_seqLets_append (st : IRState) (xs ys : List (Lsc.Ident × Expr)) (tail : Stmt) :
    evalStmt st (seqLets (xs ++ ys) tail) =
      evalStmt (evalStmt st (seqLets xs .skip)) (seqLets ys tail) := by
  induction xs generalizing st with
  | nil => rfl
  | cons bind rest ih =>
      rcases bind with ⟨name, value⟩
      simp only [List.cons_append, seqLets, evalStmt_seq, evalStmt_letBind]
      exact ih (st.setLocal name (evalExpr st value))

/-- A newly returned local denotes the value passed to `Build.bind` after executing the
accumulated linear bindings.  This fact does not need a freshness assumption; freshness is only
needed to ensure that the new local does not change older expressions. -/
theorem eval_bind_result (st : IRState) (build : Build) (tag : String) (value : Expr) :
    let result := build.bind tag value
    evalExpr (run st result.1) result.2 = evalExpr (run st build) value := by
  simp only [Build.bind]
  simp only [run, Build.finish]
  rw [eval_seqLets_append]
  simp [seqLets, evalStmt]

theorem run_bind (st : IRState) (build : Build) (tag : String) (value : Expr) :
    run st (build.bind tag value).1 =
      (run st build).setLocal (build.fresh.take tag).1 (evalExpr (run st build) value) := by
  simp only [Build.bind, run, Build.finish]
  rw [eval_seqLets_append]
  rfl

/-- Expressions safe to carry through a builder mention only names reserved in its supply. -/
def NameSafe (build : Build) (e : Expr) : Prop :=
  ∀ name ∈ freeVarsExpr e, name ∈ build.fresh.used

theorem nameSafe_bind_result (build : Build) (tag : String) (value : Expr) :
    NameSafe (build.bind tag value).1 (build.bind tag value).2 := by
  intro name h
  simp only [Build.bind, freeVarsExpr, List.mem_singleton] at h
  subst name
  exact take_name_used build.fresh tag

theorem nameSafe_bind_old (build : Build) (tag : String) (value old : Expr)
    (h : NameSafe build old) :
    NameSafe (build.bind tag value).1 old := by
  intro name hfree
  exact take_used_extends build.fresh tag (h name hfree)

/-- A generated binding cannot affect an older expression whose free variables were seeded in
the builder's used-name list. -/
theorem eval_bind_noninterference (st : IRState) (build : Build) (tag : String)
    (value old : Expr) (h : NameSafe build old) :
    evalExpr (run st (build.bind tag value).1) old = evalExpr (run st build) old := by
  rw [run_bind]
  apply evalExpr_setLocal_unused
  intro hfree
  exact take_name_not_used build.fresh tag (h _ hfree)

/-- The explicit freshness invariant needed to interpret a linear `Build` compositionally.
`Safe build e` means that `e` may be carried across the next sharing point.  The operation fields
say that primitive expressions preserve safety.  `bind` states both parts of freshness: the
returned local is safe, and adding it preserves every previously-safe expression's denotation.

The concrete `nameFreshnessInvariant` below instantiates this interface from `Fresh.used`; the
structure remains useful to the generic sharing simulation. -/
structure FreshnessInvariant (st : IRState) where
  Safe : Build → Expr → Prop
  lit : ∀ build n, Safe build (.lit n)
  add : ∀ {build a b}, Safe build a → Safe build b → Safe build (.add a b)
  sub : ∀ {build a b}, Safe build a → Safe build b → Safe build (.sub a b)
  mul : ∀ {build a b}, Safe build a → Safe build b → Safe build (.mul a b)
  div : ∀ {build a b}, Safe build a → Safe build b → Safe build (.div a b)
  gt : ∀ {build a b}, Safe build a → Safe build b → Safe build (.gt a b)
  shr : ∀ {build a b}, Safe build a → Safe build b → Safe build (.shr a b)
  bind : ∀ {build value}, Safe build value → ∀ tag,
    let result := build.bind tag value
    Safe result.1 result.2 ∧
      ∀ {old}, Safe build old →
        Safe result.1 old ∧ evalExpr (run st result.1) old = evalExpr (run st build) old

/-- The name-supply invariant used by compiler-seeded builders, with no abstract assumptions. -/
def nameFreshnessInvariant (st : IRState) : FreshnessInvariant st where
  Safe := NameSafe
  lit _ _ := by simp [NameSafe, freeVarsExpr]
  add ha hb := by
    intro name h
    simp only [freeVarsExpr, List.mem_append] at h
    exact h.elim (ha name) (hb name)
  sub ha hb := by
    intro name h
    simp only [freeVarsExpr, List.mem_append] at h
    exact h.elim (ha name) (hb name)
  mul ha hb := by
    intro name h
    simp only [freeVarsExpr, List.mem_append] at h
    exact h.elim (ha name) (hb name)
  div ha hb := by
    intro name h
    simp only [freeVarsExpr, List.mem_append] at h
    exact h.elim (ha name) (hb name)
  gt ha hb := by
    intro name h
    simp only [freeVarsExpr, List.mem_append] at h
    exact h.elim (ha name) (hb name)
  shr ha hb := by
    intro name h
    simp only [freeVarsExpr, List.mem_append] at h
    exact h.elim (ha name) (hb name)
  bind hv tag :=
    ⟨nameSafe_bind_result _ tag _,
      fun hold => ⟨nameSafe_bind_old _ tag _ _ hold,
        eval_bind_noninterference st _ tag _ _ hold⟩⟩

end Lsc.Compile.IR.Builder
