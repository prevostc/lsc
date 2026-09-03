import Lsc.Compile.Bytecode.CodegenProofs
import Lsc.Compile.IR.BuilderSemantics

namespace Lsc.Compile.Bytecode

open Lsc.Compile.IR
open Lsc.Compile.IR.Builder

/-- A compositional account of a linear SSA binding list.  Each step records the word denoted by
its source and the freshness/reload obligations needed when the source is retained by codegen. -/
inductive BindingTrace : Ctx → WordState → List (Lsc.Ident × Expr) → Ctx → WordState → Prop
  | nil (ctx word) : BindingTrace ctx word [] ctx word
  | cons (ctx word name source bound rest finalCtx finalWord)
      (hview : ViewExpr source)
      (heval : evalExprWord word source = some bound)
      (hsafe : BindReloadSafe { ctx with stackDepth := ctx.stackDepth + 1 }
        word name bound source)
      (hrest : BindingTrace
        (({ ctx with stackDepth := ctx.stackDepth + 1 }).bindLocal name (some source))
        (word.setLocal name bound) rest finalCtx finalWord) :
      BindingTrace ctx word ((name, source) :: rest) finalCtx finalWord

theorem BindingTrace.snoc
    {ctx word binds midCtx midWord finalCtx finalWord name source bound}
    (hbinds : BindingTrace ctx word binds midCtx midWord)
    (hview : ViewExpr source)
    (heval : evalExprWord midWord source = some bound)
    (hsafe : BindReloadSafe { midCtx with stackDepth := midCtx.stackDepth + 1 }
      midWord name bound source)
    (hfinal : BindingTrace
      (({ midCtx with stackDepth := midCtx.stackDepth + 1 }).bindLocal name (some source))
      (midWord.setLocal name bound) [] finalCtx finalWord) :
    BindingTrace ctx word (binds ++ [(name, source)]) finalCtx finalWord := by
  induction hbinds with
  | nil =>
      simpa using BindingTrace.cons _ _ _ _ _ _ _ _
        hview heval hsafe hfinal
  | cons ctx word oldName oldSource oldBound rest restCtx restWord
      oldView oldEval oldSafe oldRest ih =>
      simp only [List.cons_append]
      exact BindingTrace.cons _ _ _ _ _ _ _ _
        oldView oldEval oldSafe (ih heval hsafe hfinal)

/-- A valid binding trace turns a return expression into a `ViewProgram`, without inspecting the
concrete binding list. -/
theorem BindingTrace.viewProgram
    {ctx word binds finalCtx finalWord result value}
    (hbinds : BindingTrace ctx word binds finalCtx finalWord)
    (hresult : ViewExpr result)
    (heval : evalExprWord finalWord result = some value) :
    ViewProgram word (Builder.seqLets binds (.ret result)) value := by
  induction hbinds with
  | nil =>
      exact ViewProgram.ret _ _ _ hresult heval
  | cons ctx word name source bound rest finalCtx finalWord
      hview hsource hsafe hrest ih =>
      exact ViewProgram.letSeq _ _ _ _ _ _ hview hsource (ih heval)

/-- The same trace supplies every context-indexed reload obligation for the generated program. -/
theorem BindingTrace.viewProgramReloadSafe
    {ctx word binds finalCtx finalWord}
    (hbinds : BindingTrace ctx word binds finalCtx finalWord) :
    ViewProgramReloadSafe ctx word (Builder.seqLets binds (.ret result)) := by
  induction hbinds with
  | nil => exact ViewProgramReloadSafe.ret _ _ _
  | cons ctx word name source bound rest finalCtx finalWord
      hview hsource hsafe hrest ih =>
      exact ViewProgramReloadSafe.letSeq _ _ _ _ _ _ hsafe ih

/-- Combined generic entry point used by linear builder clients. -/
theorem BindingTrace.viewProgram_and_reloadSafe
    {ctx word binds finalCtx finalWord result value}
    (hbinds : BindingTrace ctx word binds finalCtx finalWord)
    (hresult : ViewExpr result)
    (heval : evalExprWord finalWord result = some value) :
    ViewProgram word (Builder.seqLets binds (.ret result)) value ∧
      ViewProgramReloadSafe ctx word (Builder.seqLets binds (.ret result)) :=
  ⟨hbinds.viewProgram hresult heval, hbinds.viewProgramReloadSafe⟩

theorem evalExprWord_setLocal_unused (word : WordState) (name : Lsc.Ident)
    (bound : EWord) (e : Expr) (hunused : name ∉ freeVarsExpr e) :
    evalExprWord (word.setLocal name bound) e = evalExprWord word e := by
  induction e with
  | lit | sload | calldataWord => rfl
  | «local» other =>
      simp only [freeVarsExpr, List.mem_singleton] at hunused
      have hne : other ≠ name := Ne.symm hunused
      simp [evalExprWord, WordState.lookupLocal, WordState.setLocal, hne]
  | mapSlot | mapSlot2 => rfl
  | dynSload slot ih =>
      simp only [freeVarsExpr] at hunused
      simp only [evalExprWord]
      rw [ih hunused]
      rfl
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb | div a b iha ihb
  | lt a b iha ihb | eq a b iha ihb | gt a b iha ihb | xor a b iha ihb =>
      simp only [freeVarsExpr, List.mem_append] at hunused
      have ha : name ∉ freeVarsExpr a := fun h => hunused (Or.inl h)
      have hb : name ∉ freeVarsExpr b := fun h => hunused (Or.inr h)
      simp [evalExprWord, iha ha, ihb hb]
  | isZero a ih =>
      simp only [freeVarsExpr] at hunused
      simp [evalExprWord, ih hunused]
  | shr amount value ihAmount ihValue =>
      simp only [freeVarsExpr, List.mem_append] at hunused
      have ha : name ∉ freeVarsExpr amount := fun h => hunused (Or.inl h)
      have hv : name ∉ freeVarsExpr value := fun h => hunused (Or.inr h)
      simp [evalExprWord, ihAmount ha, ihValue hv]

theorem ReloadableViewExpr.succ
    (fuel : Nat) {locals : List (Lsc.Ident × LocalBinding)} {word : WordState} {e : Expr}
    (h : ReloadableViewExpr fuel locals word e) :
    ReloadableViewExpr (fuel + 1) locals word e := by
  induction fuel using Nat.strong_induction_on generalizing e with
  | h fuel ihFuel =>
      induction e with
      | lit n | calldataWord n => simpa [ReloadableViewExpr] using h
      | «local» name =>
          simp only [ReloadableViewExpr] at h ⊢
          rcases h with ⟨hcaller, binding, source, hlookup, hsource, heval, hrec⟩
          cases fuel with
          | zero => contradiction
          | succ next =>
              refine ⟨hcaller, binding, source, hlookup, hsource, heval, ?_⟩
              simpa [Nat.add_assoc] using
                ihFuel next (Nat.lt_succ_self next) hrec
      | add a b iha ihb | sub a b iha ihb | mul a b iha ihb | div a b iha ihb
      | gt a b iha ihb | shr a b iha ihb | xor a b iha ihb =>
          simp only [ReloadableViewExpr] at h ⊢
          exact ⟨iha h.1, ihb h.2⟩
      | sload | mapSlot | mapSlot2 | dynSload | lt | eq | isZero =>
          simp [ReloadableViewExpr] at h

/-- Extend a reload proof through a fresh binding that cannot occur in the expression or in any
previously recorded source. -/
theorem ReloadableViewExpr.bindFresh
    {fuel : Nat} {ctx : Ctx} {word : WordState} {e : Expr}
    {name : Lsc.Ident} {bound : EWord} {newSource : Expr}
    (hname : name ∉ freeVarsExpr e)
    (holdSources : ∀ queried binding source,
      ctx.lookupBinding queried = some binding →
      binding.src = some source →
      name ∉ freeVarsExpr source)
    (h : ReloadableViewExpr fuel ctx.locals word e) :
    ReloadableViewExpr fuel
      ((name, { absPos := ctx.stackDepth, src := some newSource }) :: ctx.locals)
      (word.setLocal name bound) e := by
  induction fuel using Nat.strong_induction_on generalizing e with
  | h fuel ihFuel =>
      induction e with
      | lit n | calldataWord n => simpa [ReloadableViewExpr] using h
      | «local» queried =>
          simp only [freeVarsExpr, List.mem_singleton] at hname
          simp only [ReloadableViewExpr] at h ⊢
          rcases h with
            ⟨hcaller, binding, source, hlookup, hsource, heval, hrec⟩
          have hne : queried ≠ name := by
            intro heq
            exact hname heq.symm
          have hlookup' :
              ({ locals :=
                (name, { absPos := ctx.stackDepth, src := some newSource }) :: ctx.locals } :
                Ctx).lookupBinding queried = some binding := by
            have hne' : name ≠ queried := Ne.symm hne
            simpa [Ctx.lookupBinding, hne, hne'] using hlookup
          have hsourceUnused : name ∉ freeVarsExpr source :=
            holdSources queried binding source hlookup hsource
          refine ⟨hcaller, binding, source, hlookup', hsource, ?_, ?_⟩
          · rw [evalExprWord_setLocal_unused _ _ _ _ hsourceUnused, heval]
            simp [WordState.lookupLocal, WordState.setLocal, hne]
          · cases fuel with
            | zero => contradiction
            | succ next =>
                exact ihFuel next (Nat.lt_succ_self next)
                  hsourceUnused hrec
      | add a b iha ihb | sub a b iha ihb | mul a b iha ihb | div a b iha ihb
      | gt a b iha ihb | shr a b iha ihb | xor a b iha ihb =>
          simp only [freeVarsExpr, List.mem_append] at hname
          simp only [ReloadableViewExpr] at h ⊢
          exact ⟨
            iha (fun ha => hname (Or.inl ha)) h.1,
            ihb (fun hb => hname (Or.inr hb)) h.2⟩
      | sload | mapSlot | mapSlot2 | dynSload | lt | eq | isZero =>
          simp [ReloadableViewExpr] at h

theorem Fresh.take_name_ne_caller (fresh : Fresh) (tag : String) :
    (fresh.take tag).1 ≠ "caller" := by
  simp only [Fresh.take, generatedName]
  intro h
  have hl := congrArg String.toList h
  simp at hl

/-- Expressions carried through a linear view builder: all names are supply-reserved, the reload
graph is valid in the current codegen context, and evaluation yields the indexed word. -/
structure BuilderViewValue (build : Build) (ctx : Ctx) (word : WordState)
    (e : Expr) (value : EWord) : Prop where
  nameSafe : NameSafe build e
  reloadable : ReloadableViewExpr ctx.locals.length ctx.locals word e
  eval : evalExprWord word e = some value

/-- State invariant connecting a total `Fresh` supply, its accumulated binding list, and the
context/word state obtained by replaying those bindings. -/
structure BuilderBindingInvariant (startCtx : Ctx) (startWord : WordState)
    (build : Build) (ctx : Ctx) (word : WordState) : Prop where
  trace : BindingTrace startCtx startWord build.binds ctx word
  sourceNameSafe : ∀ queried binding source,
    ctx.lookupBinding queried = some binding →
    binding.src = some source →
    NameSafe build source
  reloadSources : ReloadableSources ctx word

theorem BuilderBindingInvariant.empty (ctx : Ctx) (word : WordState) (fresh : Fresh)
    (hempty : ctx.locals = []) :
    BuilderBindingInvariant ctx word ({ fresh } : Build) ctx word := by
  constructor
  · exact BindingTrace.nil _ _
  · intro queried binding source hlookup
    simp [Ctx.lookupBinding, hempty] at hlookup
  · intro queried binding source hlookup
    simp [Ctx.lookupBinding, hempty] at hlookup

/-- `Build.bind` is the single compositional extension rule.  Total name freshness makes the new
source stable, lifts all old source graphs, and validates the reload plan for the returned local. -/
theorem BuilderBindingInvariant.bind
    {startCtx : Ctx} {startWord : WordState} {build : Build}
    {ctx : Ctx} {word : WordState} {source : Expr} {bound : EWord}
    (hinv : BuilderBindingInvariant startCtx startWord build ctx word)
    (hsource : BuilderViewValue build ctx word source bound)
    (tag : String) :
    let result := build.bind tag source
    let name := result.2
    let nextCtx :=
      ({ ctx with stackDepth := ctx.stackDepth + 1 }).bindLocal
        (build.fresh.take tag).1 (some source)
    let nextWord := word.setLocal (build.fresh.take tag).1 bound
    BuilderBindingInvariant startCtx startWord result.1 nextCtx nextWord ∧
      BuilderViewValue result.1 nextCtx nextWord name bound ∧
      ∀ {old oldValue}, BuilderViewValue build ctx word old oldValue →
        BuilderViewValue result.1 nextCtx nextWord old oldValue := by
  let name := (build.fresh.take tag).1
  let pushed : Ctx := { ctx with stackDepth := ctx.stackDepth + 1 }
  let nextCtx := pushed.bindLocal name (some source)
  let nextWord := word.setLocal name bound
  have hnameFresh : name ∉ build.fresh.used :=
    take_name_not_used build.fresh tag
  have hsourceUnused : name ∉ freeVarsExpr source := by
    intro hmem
    exact hnameFresh (hsource.nameSafe name hmem)
  have holdUnused : ∀ queried binding oldSource,
      ctx.lookupBinding queried = some binding →
      binding.src = some oldSource →
      name ∉ freeVarsExpr oldSource := by
    intro queried binding oldSource hlookup hsrc hmem
    exact hnameFresh (hinv.sourceNameSafe queried binding oldSource hlookup hsrc name hmem)
  have hsourceLift :
      ReloadableViewExpr ctx.locals.length nextCtx.locals nextWord source := by
    change ReloadableViewExpr ctx.locals.length
      ((name, { absPos := pushed.stackDepth, src := some source }) :: ctx.locals)
      nextWord source
    exact hsource.reloadable.bindFresh hsourceUnused holdUnused
  have hstable :
      evalExprWord nextWord source = evalExprWord word source :=
    evalExprWord_setLocal_unused word name bound source hsourceUnused
  have hsafe : BindReloadSafe pushed word name bound source := by
    constructor
    · exact hstable
    · exact hstable.trans hsource.eval
    · intro queried binding oldSource hlookup hsrc
      exact evalExprWord_setLocal_unused word name bound oldSource
        (holdUnused queried binding oldSource hlookup hsrc)
    · change ReloadableViewExpr (ctx.locals.length + 1) nextCtx.locals nextWord source
      exact hsourceLift.succ ctx.locals.length
    · intro queried binding oldSource hlookup hsrc hplan
      have hlift : ReloadableViewExpr ctx.locals.length nextCtx.locals nextWord oldSource := by
        change ReloadableViewExpr ctx.locals.length
          ((name, { absPos := pushed.stackDepth, src := some source }) :: ctx.locals)
          nextWord oldSource
        exact hplan.bindFresh (holdUnused queried binding oldSource hlookup hsrc) holdUnused
      simpa [nextCtx, pushed, Ctx.bindLocal] using hlift.succ ctx.locals.length
  have htrace :
      BindingTrace startCtx startWord (build.bind tag source).1.binds nextCtx nextWord := by
    simp only [Build.bind]
    exact hinv.trace.snoc hsource.reloadable.view hsource.eval hsafe
      (BindingTrace.nil _ _)
  have hnextSourceSafe : ∀ queried binding oldSource,
      nextCtx.lookupBinding queried = some binding →
      binding.src = some oldSource →
      NameSafe (build.bind tag source).1 oldSource := by
    intro queried binding oldSource hlookup hsrc
    by_cases hname : queried = name
    · subst queried
      simp [nextCtx, pushed, Ctx.bindLocal, Ctx.lookupBinding] at hlookup
      subst binding
      simp only [Option.some.injEq] at hsrc
      subst oldSource
      exact nameSafe_bind_old build tag source source hsource.nameSafe
    · have hold : ctx.lookupBinding queried = some binding := by
        have hname' : name ≠ queried := Ne.symm hname
        simpa [nextCtx, pushed, Ctx.bindLocal, Ctx.lookupBinding, hname, hname'] using hlookup
      exact nameSafe_bind_old build tag source oldSource
        (hinv.sourceNameSafe queried binding oldSource hold hsrc)
  have hnextReload : ReloadableSources nextCtx nextWord := by
    intro queried binding oldSource hlookup hsrc
    by_cases hname : queried = name
    · subst queried
      simp [nextCtx, pushed, Ctx.bindLocal, Ctx.lookupBinding] at hlookup
      subst binding
      simp only [Option.some.injEq] at hsrc
      subst oldSource
      exact hsafe.sourcePlan
    · have hold : ctx.lookupBinding queried = some binding := by
        have hname' : name ≠ queried := Ne.symm hname
        simpa [nextCtx, pushed, Ctx.bindLocal, Ctx.lookupBinding, hname, hname'] using hlookup
      exact hsafe.oldPlans queried binding oldSource hold hsrc
        (hinv.reloadSources queried binding oldSource hold hsrc)
  have hresultValue :
      BuilderViewValue (build.bind tag source).1 nextCtx nextWord (.local name) bound := by
    constructor
    · simpa [name] using nameSafe_bind_result build tag source
    · simp only [ReloadableViewExpr]
      refine ⟨Fresh.take_name_ne_caller build.fresh tag, ?_⟩
      refine ⟨{ absPos := pushed.stackDepth, src := some source }, source, ?_, rfl, ?_, ?_⟩
      · simp [nextCtx, pushed, Ctx.bindLocal, Ctx.lookupBinding]
      · rw [hstable, hsource.eval]
        simp [nextWord, name, WordState.lookupLocal, WordState.setLocal]
      · simpa [nextCtx, Ctx.bindLocal] using hsourceLift
    · simp [nextWord, name, evalExprWord, WordState.lookupLocal, WordState.setLocal]
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨htrace, hnextSourceSafe, hnextReload⟩
  · simpa [Build.bind, name, nextCtx, nextWord, pushed] using hresultValue
  · intro old oldValue hold
    have holdUnused' : name ∉ freeVarsExpr old := by
      intro hmem
      exact hnameFresh (hold.nameSafe name hmem)
    have hlift : ReloadableViewExpr ctx.locals.length nextCtx.locals nextWord old := by
      change ReloadableViewExpr ctx.locals.length
        ((name, { absPos := pushed.stackDepth, src := some source }) :: ctx.locals)
        nextWord old
      exact hold.reloadable.bindFresh holdUnused' holdUnused
    constructor
    · exact nameSafe_bind_old build tag source old hold.nameSafe
    · simpa [nextCtx, Ctx.bindLocal] using hlift.succ ctx.locals.length
    · exact (evalExprWord_setLocal_unused word name bound old holdUnused').trans hold.eval

end Lsc.Compile.Bytecode
