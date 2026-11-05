import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem FCA_chap_D_4_5_2
    (g : E → ℝ)
    (A : E →ₗ[ℝ] F)
    (x : F)
    (hg_convex : ConvexOn ℝ Set.univ g)
    (hg_bounded : BddBelow (Set.image g {y | A y = x}))
    (hA_surjective : Function.Surjective A) :
    let Ag := fun x => sInf (Set.image g {y | A y = x})
    let Yx := {y | (A y = x) ∧ (g y = Ag x)}
    (Set.Nonempty Yx) → (∃ y ∈ Yx, DifferentiableAt ℝ g y) →
    (DifferentiableAt ℝ Ag x) := by
  sorry
