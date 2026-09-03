import Lsc.Lib.Math.SqrtAlgo

namespace Lsc.Math.SqrtAlgo

/-- A persistent relational interpretation of the operations and sharing points used by
`sqrtWith`.  `bind` must relate the newly shared value and preserve every value that was already
related.  This persistence is the key property needed by linear builders: adding a fresh local
must not change the meanings of expressions built before it. -/
structure SharingSimulation (opsA : Ops α) (sharingA : Sharing σ α)
    (opsB : Ops β) (sharingB : Sharing τ β) where
  StateRel : σ → τ → Prop
  ValRel : σ → τ → α → β → Prop
  lit : ∀ {sa sb}, StateRel sa sb → ∀ n, ValRel sa sb (opsA.lit n) (opsB.lit n)
  add : ∀ {sa sb x x' y y'}, StateRel sa sb →
    ValRel sa sb x x' → ValRel sa sb y y' →
    ValRel sa sb (opsA.add x y) (opsB.add x' y')
  sub : ∀ {sa sb x x' y y'}, StateRel sa sb →
    ValRel sa sb x x' → ValRel sa sb y y' →
    ValRel sa sb (opsA.sub x y) (opsB.sub x' y')
  mul : ∀ {sa sb x x' y y'}, StateRel sa sb →
    ValRel sa sb x x' → ValRel sa sb y y' →
    ValRel sa sb (opsA.mul x y) (opsB.mul x' y')
  div : ∀ {sa sb x x' y y'}, StateRel sa sb →
    ValRel sa sb x x' → ValRel sa sb y y' →
    ValRel sa sb (opsA.div x y) (opsB.div x' y')
  gt : ∀ {sa sb x x' y y'}, StateRel sa sb →
    ValRel sa sb x x' → ValRel sa sb y y' →
    ValRel sa sb (opsA.gt x y) (opsB.gt x' y')
  shr : ∀ {sa sb x x' y y'}, StateRel sa sb →
    ValRel sa sb x x' → ValRel sa sb y y' →
    ValRel sa sb (opsA.shr x y) (opsB.shr x' y')
  bind : ∀ {sa sb x y}, StateRel sa sb → ValRel sa sb x y → ∀ tag,
    let ra := sharingA.bind sa tag x
    let rb := sharingB.bind sb tag y
    StateRel ra.1 rb.1 ∧
      ValRel ra.1 rb.1 ra.2 rb.2 ∧
      ∀ {old old'}, ValRel sa sb old old' → ValRel ra.1 rb.1 old old'

variable {α β σ τ : Type} {opsA : Ops α} {opsB : Ops β}
  {sharingA : Sharing σ α} {sharingB : Sharing τ β}

private theorem magnitudeStep_rel
    (sim : SharingSimulation opsA sharingA opsB sharingB)
    {sa sb aa aa' xn xn'} (hs : sim.StateRel sa sb)
    (haa : sim.ValRel sa sb aa aa') (hxn : sim.ValRel sa sb xn xn')
    (threshold shift factor : Nat) :
    sim.ValRel sa sb
      (magnitudeStep opsA threshold shift factor (aa, xn)).1
      (magnitudeStep opsB threshold shift factor (aa', xn')).1 ∧
    sim.ValRel sa sb
      (magnitudeStep opsA threshold shift factor (aa, xn)).2
      (magnitudeStep opsB threshold shift factor (aa', xn')).2 := by
  let htake := sim.gt hs haa (sim.lit hs (threshold - 1))
  let haaNext := sim.shr hs
    (sim.mul hs htake (sim.lit hs shift)) haa
  let hfactor := sim.add hs (sim.lit hs 1)
    (sim.mul hs htake (sim.lit hs (factor - 1)))
  exact ⟨haaNext, sim.mul hs hxn hfactor⟩

private theorem magnitudeFold_rel
    (sim : SharingSimulation opsA sharingA opsB sharingB)
    (steps : List (Nat × Nat × Nat))
    {sa sb aa aa' xn xn' anchor anchor'}
    (hs : sim.StateRel sa sb)
    (haa : sim.ValRel sa sb aa aa') (hxn : sim.ValRel sa sb xn xn')
    (hanchor : sim.ValRel sa sb anchor anchor') :
    let ra := steps.foldl
      (fun (s, state) step =>
        let next := magnitudeStep opsA step.1 step.2.1 step.2.2 state
        let (s, aa) := sharingA.bind s "sqrt_aa" next.1
        let (s, xn) := sharingA.bind s "sqrt_xn" next.2
        (s, (aa, xn)))
      (sa, (aa, xn))
    let rb := steps.foldl
      (fun (s, state) step =>
        let next := magnitudeStep opsB step.1 step.2.1 step.2.2 state
        let (s, aa) := sharingB.bind s "sqrt_aa" next.1
        let (s, xn) := sharingB.bind s "sqrt_xn" next.2
        (s, (aa, xn)))
      (sb, (aa', xn'))
    sim.StateRel ra.1 rb.1 ∧
      sim.ValRel ra.1 rb.1 ra.2.1 rb.2.1 ∧
      sim.ValRel ra.1 rb.1 ra.2.2 rb.2.2 ∧
      sim.ValRel ra.1 rb.1 anchor anchor' := by
  induction steps generalizing sa sb aa aa' xn xn' with
  | nil => exact ⟨hs, haa, hxn, hanchor⟩
  | cons step rest ih =>
      simp only [List.foldl]
      obtain ⟨haaNext, hxnNext⟩ :=
        magnitudeStep_rel sim hs haa hxn step.1 step.2.1 step.2.2
      obtain ⟨hs1, haa1, preserve1⟩ := sim.bind hs haaNext "sqrt_aa"
      obtain ⟨hs2, hxn2, preserve2⟩ :=
        sim.bind hs1 (preserve1 hxnNext) "sqrt_xn"
      exact ih hs2 (preserve2 haa1) hxn2 (preserve2 (preserve1 hanchor))

private theorem sixFold_rel
    (sim : SharingSimulation opsA sharingA opsB sharingB)
    (steps : List Nat) {sa sb a a' x x'}
    (hs : sim.StateRel sa sb)
    (ha : sim.ValRel sa sb a a') (hx : sim.ValRel sa sb x x') :
    let ra := steps.foldl
      (fun (s, xn) _ => sharingA.bind s "sqrt_x" (newtonStep opsA a xn)) (sa, x)
    let rb := steps.foldl
      (fun (s, xn) _ => sharingB.bind s "sqrt_x" (newtonStep opsB a' xn)) (sb, x')
    sim.StateRel ra.1 rb.1 ∧
      sim.ValRel ra.1 rb.1 a a' ∧
      sim.ValRel ra.1 rb.1 ra.2 rb.2 := by
  induction steps generalizing sa sb x x' with
  | nil => exact ⟨hs, ha, hx⟩
  | cons _ rest ih =>
      simp only [List.foldl]
      have hstep := sim.shr hs (sim.lit hs 1)
        (sim.add hs hx (sim.div hs ha hx))
      obtain ⟨hs1, hx1, preserve⟩ := sim.bind hs hstep "sqrt_x"
      exact ih hs1 (preserve ha) hx1

/-- `sqrtWith` is preserved by every persistent relational interpretation of its primitive
operations and explicit sharing points. -/
theorem sqrtWith_rel
    (sim : SharingSimulation opsA sharingA opsB sharingB)
    {sa sb a a'} (hs : sim.StateRel sa sb) (ha : sim.ValRel sa sb a a') :
    let ra := sqrtWith opsA sharingA sa a
    let rb := sqrtWith opsB sharingB sb a'
    sim.StateRel ra.1 rb.1 ∧ sim.ValRel ra.1 rb.1 ra.2 rb.2 := by
  simp only [sqrtWith, initWith, magnitudeInitWith, sixStepsWith]
  obtain ⟨hsMag, haa, hxn, haMag⟩ :=
    magnitudeFold_rel sim magnitudeSchedule hs ha (sim.lit hs 1) ha
  have hinit := sim.shr hsMag (sim.lit hsMag 1)
    (sim.mul hsMag (sim.lit hsMag 3) hxn)
  obtain ⟨hsInit, hx0, preserveInit⟩ := sim.bind hsMag hinit "sqrt_x"
  obtain ⟨hsSix, haSix, hxSix⟩ :=
    sixFold_rel sim (List.range 6) hsInit (preserveInit haMag) hx0
  have hfloor := sim.sub hsSix hxSix (sim.gt hsSix hxSix (sim.div hsSix haSix hxSix))
  obtain ⟨hsFloor, hresult, _⟩ := sim.bind hsSix hfloor "sqrt_floor"
  exact ⟨hsFloor, hresult⟩

end Lsc.Math.SqrtAlgo
