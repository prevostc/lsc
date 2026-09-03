/-!
# Integer square-root algorithm

This module contains the single, representation-polymorphic implementation used by both the
executable `Nat` semantics and the primitive IR expansion.  An `Ops α` supplies precisely the
EVM operations needed by the algorithm; no square-root primitive is assumed.
-/

namespace Lsc.Math.SqrtAlgo

structure Ops (α : Type) where
  lit : Nat → α
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  div : α → α → α
  gt : α → α → α
  shr : α → α → α

/-- Interpretation of the algorithm's explicit sharing points. The value semantics uses the
identity interpretation; IR lowering records each shared value as a local binding. -/
structure Sharing (σ α : Type) where
  bind : σ → String → α → σ × α

def Sharing.identity : Sharing Unit α where
  bind state _ value := (state, value)

/-- A semantics-preserving map between two interpretations of the sqrt operations. -/
structure OpsHom (a : Ops α) (b : Ops β) (f : α → β) : Prop where
  lit : ∀ n, f (a.lit n) = b.lit n
  add : ∀ x y, f (a.add x y) = b.add (f x) (f y)
  sub : ∀ x y, f (a.sub x y) = b.sub (f x) (f y)
  mul : ∀ x y, f (a.mul x y) = b.mul (f x) (f y)
  div : ∀ x y, f (a.div x y) = b.div (f x) (f y)
  gt : ∀ x y, f (a.gt x y) = b.gt (f x) (f y)
  shr : ∀ x y, f (a.shr x y) = b.shr (f x) (f y)

def magnitudeStep (ops : Ops α) (threshold shift factor : Nat)
    (state : α × α) : α × α :=
  let (aa, xn) := state
  let take := ops.gt aa (ops.lit (threshold - 1))
  let aa' := ops.shr (ops.mul take (ops.lit shift)) aa
  let factor' := ops.add (ops.lit 1) (ops.mul take (ops.lit (factor - 1)))
  (aa', ops.mul xn factor')

/-- The magnitude schedule shared by the semantic implementation and linear IR lowering. -/
def magnitudeSchedule : List (Nat × Nat × Nat) :=
  [(2 ^ 128, 128, 2 ^ 64), (2 ^ 64, 64, 2 ^ 32), (2 ^ 32, 32, 2 ^ 16),
   (2 ^ 16, 16, 2 ^ 8), (2 ^ 8, 8, 2 ^ 4), (2 ^ 4, 4, 2 ^ 2), (2 ^ 2, 0, 2)]

def magnitudeInitWith (ops : Ops α) (sharing : Sharing σ α) (s : σ) (a : α) :
    σ × (α × α) :=
  magnitudeSchedule.foldl
    (fun (s, state) step =>
      let next := magnitudeStep ops step.1 step.2.1 step.2.2 state
      let (s, aa) := sharing.bind s "sqrt_aa" next.1
      let (s, xn) := sharing.bind s "sqrt_xn" next.2
      (s, (aa, xn)))
    (s, (a, ops.lit 1))

def magnitudeInit (ops : Ops α) (a : α) : α × α :=
  (magnitudeInitWith ops Sharing.identity () a).2

/-- Initial Newton estimate from an already-computed magnitude state. -/
def initFromMagnitude (ops : Ops α) (state : α × α) : α :=
  ops.shr (ops.lit 1) (ops.mul (ops.lit 3) state.2)

def initWith (ops : Ops α) (sharing : Sharing σ α) (s : σ) (a : α) : σ × α :=
  let (s, state) := magnitudeInitWith ops sharing s a
  sharing.bind s "sqrt_x" (initFromMagnitude ops state)

def init (ops : Ops α) (a : α) : α :=
  (initWith ops Sharing.identity () a).2

def newtonStep (ops : Ops α) (a xn : α) : α :=
  ops.shr (ops.lit 1) (ops.add xn (ops.div a xn))

def sixStepsWith (ops : Ops α) (sharing : Sharing σ α) (s : σ) (a x0 : α) : σ × α :=
  List.range 6 |>.foldl
    (fun (s, xn) _ => sharing.bind s "sqrt_x" (newtonStep ops a xn))
    (s, x0)

def sixSteps (ops : Ops α) (a x0 : α) : α :=
  (sixStepsWith ops Sharing.identity () a x0).2

def preFix (ops : Ops α) (a : α) : α :=
  sixSteps ops a (init ops a)

/-- One-bit correction that turns the Newton pre-fixpoint into floor sqrt. -/
def floorFix (ops : Ops α) (a x : α) : α :=
  ops.sub x (ops.gt x (ops.div a x))

/-- The single executable sqrt program, parameterized only by primitive operations and the
interpretation of explicit sharing points. -/
def sqrtWith (ops : Ops α) (sharing : Sharing σ α) (s : σ) (a : α) : σ × α :=
  let (s, x0) := initWith ops sharing s a
  let (s, x) := sixStepsWith ops sharing s a x0
  sharing.bind s "sqrt_floor" (floorFix ops a x)

/-- Six Newton steps followed by the one-bit floor correction. -/
def sqrt (ops : Ops α) (a : α) : α :=
  (sqrtWith ops Sharing.identity () a).2

private def mapPair (f : α → β) (state : α × α) : β × β :=
  (f state.1, f state.2)

variable {α β : Type} {a : Ops α} {b : Ops β} {f : α → β}

private theorem magnitudeInitWith_identity_aux (ops : Ops α)
    (steps : List (Nat × Nat × Nat)) (state : α × α) :
    (steps.foldl
      (fun (s, state) step =>
        let next := magnitudeStep ops step.1 step.2.1 step.2.2 state
        let (s, aa) := Sharing.identity.bind s "sqrt_aa" next.1
        let (s, xn) := Sharing.identity.bind s "sqrt_xn" next.2
        (s, (aa, xn)))
      ((), state)).2 =
      steps.foldl
        (fun state step => magnitudeStep ops step.1 step.2.1 step.2.2 state) state := by
  induction steps generalizing state with
  | nil => rfl
  | cons step steps ih =>
      simp only [List.foldl, Sharing.identity]
      exact ih (magnitudeStep ops step.1 step.2.1 step.2.2 state)

theorem magnitudeInit_eq_fold (ops : Ops α) (x : α) :
    magnitudeInit ops x =
      magnitudeSchedule.foldl
        (fun state step => magnitudeStep ops step.1 step.2.1 step.2.2 state)
        (x, ops.lit 1) := by
  exact magnitudeInitWith_identity_aux ops magnitudeSchedule (x, ops.lit 1)

theorem map_magnitudeStep (h : OpsHom a b f) (threshold shift factor : Nat)
    (state : α × α) :
    mapPair f (magnitudeStep a threshold shift factor state) =
      magnitudeStep b threshold shift factor (mapPair f state) := by
  rcases state with ⟨aa, xn⟩
  simp [mapPair, magnitudeStep, h.lit, h.add, h.mul, h.gt, h.shr]

private theorem map_magnitudeFold (h : OpsHom a b f)
    (steps : List (Nat × Nat × Nat)) (state : α × α) :
    mapPair f
        (steps.foldl
          (fun state step => magnitudeStep a step.1 step.2.1 step.2.2 state) state) =
      steps.foldl
        (fun state step => magnitudeStep b step.1 step.2.1 step.2.2 state)
        (mapPair f state) := by
  induction steps generalizing state with
  | nil => rfl
  | cons step steps ih =>
      simp only [List.foldl]
      rw [ih, map_magnitudeStep h]

theorem map_magnitudeInit (h : OpsHom a b f) (x : α) :
    mapPair f (magnitudeInit a x) = magnitudeInit b (f x) := by
  rw [magnitudeInit_eq_fold, magnitudeInit_eq_fold]
  rw [map_magnitudeFold h]
  simp [mapPair, h.lit]

theorem init_eq_fromMagnitude (ops : Ops α) (x : α) :
    init ops x = initFromMagnitude ops (magnitudeInit ops x) := by
  simp only [init, initWith]
  rw [magnitudeInit_eq_fold]
  rfl

theorem map_init (h : OpsHom a b f) (x : α) :
    f (init a x) = init b (f x) := by
  rw [init_eq_fromMagnitude, init_eq_fromMagnitude]
  simp only [initFromMagnitude]
  rw [h.shr, h.lit, h.mul, h.lit]
  have hm := congrArg Prod.snd (map_magnitudeInit h x)
  have hm' : f (magnitudeInit a x).2 = (magnitudeInit b (f x)).2 := by
    simpa [mapPair] using hm
  exact congrArg (fun z => b.shr (b.lit 1) (b.mul (b.lit 3) z)) hm'

theorem map_newtonStep (h : OpsHom a b f) (x y : α) :
    f (newtonStep a x y) = newtonStep b (f x) (f y) := by
  simp [newtonStep, h.lit, h.add, h.div, h.shr]

private theorem map_newtonFold (h : OpsHom a b f) (steps : List Nat) (x y : α) :
    f (steps.foldl (fun xn _ => newtonStep a x xn) y) =
      steps.foldl (fun xn _ => newtonStep b (f x) xn) (f y) := by
  induction steps generalizing y with
  | nil => rfl
  | cons step steps ih =>
      simp only [List.foldl]
      rw [ih, map_newtonStep h]

theorem sixSteps_eq_fold (ops : Ops α) (x y : α) :
    sixSteps ops x y =
      (List.range 6).foldl (fun xn _ => newtonStep ops x xn) y := by
  rfl

theorem map_sixSteps (h : OpsHom a b f) (x y : α) :
    f (sixSteps a x y) = sixSteps b (f x) (f y) := by
  rw [sixSteps_eq_fold, sixSteps_eq_fold]
  exact map_newtonFold h (List.range 6) x y

theorem map_preFix (h : OpsHom a b f) (x : α) :
    f (preFix a x) = preFix b (f x) := by
  simp only [preFix]
  rw [map_sixSteps h, map_init h]

theorem sqrt_eq_floorFix (ops : Ops α) (x : α) :
    sqrt ops x = floorFix ops x (preFix ops x) := by
  simp only [sqrt, sqrtWith, preFix]
  rw [init_eq_fromMagnitude, sixSteps_eq_fold]
  rfl

theorem map_sqrt (h : OpsHom a b f) (x : α) :
    f (sqrt a x) = sqrt b (f x) := by
  rw [sqrt_eq_floorFix, sqrt_eq_floorFix]
  simp [floorFix, h.sub, h.gt, h.div, map_preFix h]

def natOps : Ops Nat where
  lit := id
  add := Nat.add
  sub := Nat.sub
  mul := Nat.mul
  div := Nat.div
  gt := fun a b => if a > b then 1 else 0
  shr := fun amount value => value / 2 ^ amount

def sqrtNat (a : Nat) : Nat := sqrt natOps a

end Lsc.Math.SqrtAlgo
