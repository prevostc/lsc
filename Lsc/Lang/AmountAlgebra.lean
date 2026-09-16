import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Defs
import Lsc.Lang.Amount

/-!
`AddCommMonoid` for `Amount`, kept out of `Amount.lean` / `AmountTheorems.lean`
so Mathlib `^` lemmas do not leak into the compiler's `simp` set.
-/

namespace Lsc.Amount

/-- So `∑ a ∈ A, amounts a` type-checks on `Amount`. -/
instance {a : Asset} : AddCommMonoid (Amount a) where
  add := Add.add
  add_assoc := fun x y z => Amount.ext (Nat.add_assoc x.raw y.raw z.raw)
  zero := ⟨0⟩
  zero_add := Amount.zero_add
  add_zero := Amount.add_zero
  nsmul := nsmulRec
  add_comm := fun x y => Amount.ext (Nat.add_comm x.raw y.raw)

/-- Finite sums commute with `.raw`. -/
theorem sum_raw {a : Asset} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Amount a) :
    (∑ x ∈ s, f x).raw = ∑ x ∈ s, (f x).raw := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro x s hx ih
  simp [Finset.sum_insert hx, Amount.raw_add, ih]

end Lsc.Amount
