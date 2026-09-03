import Lsc.Compile.Bytecode.BuilderProofs
import Lsc.Lib.Fixed.IRExpand

namespace Lsc.Math.BytecodeProofs

open Lsc.Compile.IR
open Lsc.Compile.IR.Builder
open Lsc.Compile.Bytecode
open Lsc.Math

private theorem value_lit (build : Build) (ctx : Ctx) (word : WordState) (n : Nat)
    (hwidth : pushWidth n ≤ 32) :
    BuilderViewValue build ctx word (.lit n) (.ofNat n) := by
  constructor
  · exact (nameFreshnessInvariant {}).lit build n
  · simpa [ReloadableViewExpr] using hwidth
  · rfl

private theorem value_add {build ctx word a b x y}
    (ha : BuilderViewValue build ctx word a x)
    (hb : BuilderViewValue build ctx word b y) :
    BuilderViewValue build ctx word (.add a b) (EvmYul.UInt256.add x y) := by
  constructor
  · exact (nameFreshnessInvariant {}).add ha.nameSafe hb.nameSafe
  · simpa only [ReloadableViewExpr] using And.intro ha.reloadable hb.reloadable
  · simp [evalExprWord, ha.eval, hb.eval]

private theorem value_sub {build ctx word a b x y}
    (ha : BuilderViewValue build ctx word a x)
    (hb : BuilderViewValue build ctx word b y) :
    BuilderViewValue build ctx word (.sub a b) (EvmYul.UInt256.sub x y) := by
  constructor
  · exact (nameFreshnessInvariant {}).sub ha.nameSafe hb.nameSafe
  · simpa only [ReloadableViewExpr] using And.intro ha.reloadable hb.reloadable
  · simp [evalExprWord, ha.eval, hb.eval]

private theorem value_mul {build ctx word a b x y}
    (ha : BuilderViewValue build ctx word a x)
    (hb : BuilderViewValue build ctx word b y) :
    BuilderViewValue build ctx word (.mul a b) (EvmYul.UInt256.mul x y) := by
  constructor
  · exact (nameFreshnessInvariant {}).mul ha.nameSafe hb.nameSafe
  · simpa only [ReloadableViewExpr] using And.intro ha.reloadable hb.reloadable
  · simp [evalExprWord, ha.eval, hb.eval]

private theorem value_div {build ctx word a b x y}
    (ha : BuilderViewValue build ctx word a x)
    (hb : BuilderViewValue build ctx word b y) :
    BuilderViewValue build ctx word (.div a b) (EvmYul.UInt256.div x y) := by
  constructor
  · exact (nameFreshnessInvariant {}).div ha.nameSafe hb.nameSafe
  · simpa only [ReloadableViewExpr] using And.intro ha.reloadable hb.reloadable
  · simp [evalExprWord, ha.eval, hb.eval]

private theorem value_gt {build ctx word a b x y}
    (ha : BuilderViewValue build ctx word a x)
    (hb : BuilderViewValue build ctx word b y) :
    BuilderViewValue build ctx word (.gt a b) (boolWord (x > y)) := by
  constructor
  · exact (nameFreshnessInvariant {}).gt ha.nameSafe hb.nameSafe
  · simpa only [ReloadableViewExpr] using And.intro ha.reloadable hb.reloadable
  · simp [evalExprWord, ha.eval, hb.eval]

private theorem value_shr {build ctx word amount value x y}
    (ha : BuilderViewValue build ctx word amount x)
    (hv : BuilderViewValue build ctx word value y) :
    BuilderViewValue build ctx word (.shr amount value) (EvmYul.UInt256.shiftRight y x) := by
  constructor
  · exact (nameFreshnessInvariant {}).shr ha.nameSafe hv.nameSafe
  · simpa only [ReloadableViewExpr] using And.intro ha.reloadable hv.reloadable
  · simp [evalExprWord, ha.eval, hv.eval]

private theorem magnitudeStep_value
    {build ctx word aa xn aaValue xnValue}
    (haa : BuilderViewValue build ctx word aa aaValue)
    (hxn : BuilderViewValue build ctx word xn xnValue)
    (threshold shift factor : Nat)
    (hthreshold : pushWidth (threshold - 1) ≤ 32)
    (hshift : pushWidth shift ≤ 32)
    (hfactor : pushWidth (factor - 1) ≤ 32) :
    ∃ aaValue' xnValue',
      BuilderViewValue build ctx word
        (SqrtAlgo.magnitudeStep Lsc.Fixed.IRExpand.irOps threshold shift factor (aa, xn)).1
        aaValue' ∧
      BuilderViewValue build ctx word
        (SqrtAlgo.magnitudeStep Lsc.Fixed.IRExpand.irOps threshold shift factor (aa, xn)).2
        xnValue' := by
  let htake := value_gt haa (value_lit build ctx word (threshold - 1) hthreshold)
  let haa' := value_shr
    (value_mul htake (value_lit build ctx word shift hshift)) haa
  let hfactor' := value_add (value_lit build ctx word 1 (by decide))
    (value_mul htake (value_lit build ctx word (factor - 1) hfactor))
  exact ⟨_, _, haa', value_mul hxn hfactor'⟩

private theorem magnitudeFold_value
    {startCtx startWord build ctx word aa xn anchor aaValue xnValue anchorValue}
    (steps : List (Nat × Nat × Nat))
    (hsteps : ∀ step ∈ steps,
      pushWidth (step.1 - 1) ≤ 32 ∧
      pushWidth step.2.1 ≤ 32 ∧
      pushWidth (step.2.2 - 1) ≤ 32)
    (hinv : BuilderBindingInvariant startCtx startWord build ctx word)
    (haa : BuilderViewValue build ctx word aa aaValue)
    (hxn : BuilderViewValue build ctx word xn xnValue)
    (hanchor : BuilderViewValue build ctx word anchor anchorValue) :
    let result := steps.foldl
      (fun (s, state) step =>
        let next := SqrtAlgo.magnitudeStep Lsc.Fixed.IRExpand.irOps
          step.1 step.2.1 step.2.2 state
        let (s, aa) := s.bind "sqrt_aa" next.1
        let (s, xn) := s.bind "sqrt_xn" next.2
        (s, (aa, xn)))
      (build, (aa, xn))
    ∃ finalCtx finalWord aaValue' xnValue' anchorValue',
      BuilderBindingInvariant startCtx startWord result.1 finalCtx finalWord ∧
      BuilderViewValue result.1 finalCtx finalWord result.2.1 aaValue' ∧
      BuilderViewValue result.1 finalCtx finalWord result.2.2 xnValue' ∧
      BuilderViewValue result.1 finalCtx finalWord anchor anchorValue' := by
  induction steps generalizing build ctx word aa xn aaValue xnValue anchorValue with
  | nil => exact ⟨ctx, word, aaValue, xnValue, anchorValue, hinv, haa, hxn, hanchor⟩
  | cons step rest ih =>
      simp only [List.foldl]
      have hs := hsteps step (by simp)
      obtain ⟨aaNextValue, xnNextValue, haaNext, hxnNext⟩ :=
        magnitudeStep_value haa hxn step.1 step.2.1 step.2.2 hs.1 hs.2.1 hs.2.2
      obtain ⟨hinv1, haa1, preserve1⟩ := hinv.bind haaNext "sqrt_aa"
      obtain ⟨hinv2, hxn2, preserve2⟩ :=
        hinv1.bind (preserve1 hxnNext) "sqrt_xn"
      apply ih (fun candidate hmem => hsteps candidate (by simp [hmem]))
        hinv2 (preserve2 haa1) hxn2 (preserve2 (preserve1 hanchor))

private theorem sixFold_value
    {startCtx startWord build ctx word a x aValue xValue}
    (steps : List Nat)
    (hinv : BuilderBindingInvariant startCtx startWord build ctx word)
    (ha : BuilderViewValue build ctx word a aValue)
    (hx : BuilderViewValue build ctx word x xValue) :
    let result := steps.foldl
      (fun (s, xn) _ =>
        s.bind "sqrt_x"
          (SqrtAlgo.newtonStep Lsc.Fixed.IRExpand.irOps a xn))
      (build, x)
    ∃ finalCtx finalWord aValue' xValue',
      BuilderBindingInvariant startCtx startWord result.1 finalCtx finalWord ∧
      BuilderViewValue result.1 finalCtx finalWord a aValue' ∧
      BuilderViewValue result.1 finalCtx finalWord result.2 xValue' := by
  induction steps generalizing build ctx word x aValue xValue with
  | nil => exact ⟨ctx, word, aValue, xValue, hinv, ha, hx⟩
  | cons _ rest ih =>
      simp only [List.foldl]
      have hstep := value_shr (value_lit build ctx word 1 (by decide))
        (value_add hx (value_div ha hx))
      obtain ⟨hinv1, hx1, preserve⟩ := hinv.bind hstep "sqrt_x"
      exact ih hinv1 (preserve ha) hx1

/-- Generic compositional instantiation for the SSA bindings emitted by `sqrtWith`/`sqrtBinds`.
The proof follows sharing points and never expands the concrete binding list. -/
theorem sqrtBinds_bindingInvariant
    {startCtx startWord build ctx word a aValue}
    (hinv : BuilderBindingInvariant startCtx startWord build ctx word)
    (ha : BuilderViewValue build ctx word a aValue) :
    let result := Lsc.Fixed.IRExpand.sqrtBinds a build
    ∃ (finalCtx : Ctx) (finalWord : WordState) (resultValue : EWord),
      BuilderBindingInvariant startCtx startWord result.1 finalCtx finalWord ∧
      BuilderViewValue result.1 finalCtx finalWord result.2 resultValue := by
  simp only [Lsc.Fixed.IRExpand.sqrtBinds, SqrtAlgo.sqrtWith, SqrtAlgo.initWith,
    SqrtAlgo.magnitudeInitWith, SqrtAlgo.sixStepsWith]
  obtain ⟨magCtx, magWord, aaValue, xnValue, anchorValue, hinvMag, haa, hxn, haMag⟩ :=
    magnitudeFold_value SqrtAlgo.magnitudeSchedule (by
      intro step hmem
      simp [SqrtAlgo.magnitudeSchedule] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      hinv ha (value_lit build ctx word 1 (by decide)) ha
  have hinit := value_shr (value_lit _ _ _ 1 (by decide))
    (value_mul (value_lit _ _ _ 3 (by decide)) hxn)
  obtain ⟨hinvInit, hx0, preserveInit⟩ := hinvMag.bind hinit "sqrt_x"
  obtain ⟨sixCtx, sixWord, aValue', xValue, hinvSix, haSix, hxSix⟩ :=
    sixFold_value (List.range 6) hinvInit (preserveInit haMag) hx0
  have hfloor := value_sub hxSix (value_gt hxSix (value_div haSix hxSix))
  obtain ⟨hinvFloor, hresult, _⟩ := hinvSix.bind hfloor "sqrt_floor"
  exact ⟨_, _, _, hinvFloor, hresult⟩

/-- Empty-context compiler specialization using the total `Fresh` supply. -/
theorem sqrtBinds_seeded_bindingInvariant
    (word : WordState) (fresh : Fresh) (a : Expr) (aValue : EWord)
    (ha : BuilderViewValue ({ fresh } : Build) ({} : Ctx) word a aValue) :
    let result := Lsc.Fixed.IRExpand.sqrtBinds a ({ fresh } : Build)
    ∃ finalCtx finalWord resultValue,
      BuilderBindingInvariant ({} : Ctx) word result.1 finalCtx finalWord ∧
      BuilderViewValue result.1 finalCtx finalWord result.2 resultValue := by
  exact sqrtBinds_bindingInvariant (BuilderBindingInvariant.empty {} word fresh rfl) ha

/-- The generated sqrt return program immediately instantiates the two generic program lemmas.
The supplied empty binding invariant lets callers start after an independently-proved prologue
(notably ABI parameter bindings), without rebuilding the sqrt trace. -/
theorem sqrtBinds_seeded_viewProgram
    (ctx : Ctx) (word : WordState) (fresh : Fresh) (a : Expr) (aValue : EWord)
    (hinv : BuilderBindingInvariant ctx word ({ fresh } : Build) ctx word)
    (ha : BuilderViewValue ({ fresh } : Build) ctx word a aValue) :
    let result := Lsc.Fixed.IRExpand.sqrtBinds a ({ fresh } : Build)
    ∃ resultValue,
      ViewProgram word (Builder.seqLets result.1.binds (.ret result.2)) resultValue ∧
      ViewProgramReloadSafe ctx word
        (Builder.seqLets result.1.binds (.ret result.2)) := by
  obtain ⟨finalCtx, finalWord, resultValue, hinv, hresult⟩ :=
    sqrtBinds_bindingInvariant hinv ha
  exact ⟨resultValue,
    hinv.trace.viewProgram hresult.reloadable.view hresult.eval,
    hinv.trace.viewProgramReloadSafe⟩

/-- The exact, unoptimized statement chain emitted by `sqrtBinds` compiles and runs as a view.
This consumes `sqrtBinds_seeded_viewProgram` directly; no optimizer-shape transport theorem is
needed between the single-source builder proof and bytecode codegen. -/
theorem sqrtBinds_seeded_runView_correct
    (word : WordState) (fresh : Fresh) (a : Expr) (aValue : EWord)
    (ha : BuilderViewValue ({ fresh } : Build) ({} : Ctx) word a aValue)
    (st : EvmYul.EVM.State) (hctx : ContextAgrees ({} : Ctx) st word)
    (hmemory : st.memory = ByteArray.empty)
    (instrs : List Instr) (out : Ctx)
    (hgen :
      let result := Lsc.Fixed.IRExpand.sqrtBinds a ({ fresh } : Build)
      Codegen.stmt ({} : Ctx)
        (Builder.seqLets result.1.binds (.ret result.2)) = .ok (instrs, out)) :
    ∃ (resultValue : EWord) (final : EvmYul.EVM.State),
      runView instrs st = .ok final ∧
      final.H_return = resultValue.toByteArray ∧
      EvmYulBridge.EncodablePlainInstrs instrs := by
  obtain ⟨resultValue, hspec⟩ :=
    sqrtBinds_seeded_viewProgram ({} : Ctx) word fresh a aValue
      (BuilderBindingInvariant.empty {} word fresh rfl) ha
  obtain ⟨final, hrun, hreturn, hencodable⟩ :=
    codegenViewProgram_runView_correct_of_spec hspec st hctx hmemory instrs out hgen
  exact ⟨resultValue, final, hrun, hreturn, hencodable⟩

end Lsc.Math.BytecodeProofs
