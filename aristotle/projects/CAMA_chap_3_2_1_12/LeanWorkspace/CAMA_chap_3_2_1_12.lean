import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem CAMA_chap_3_2_1_12
  (A : AffineMap ℝ E F)
  (C : Set E)
  (D : Set F)
  (hC : Convex ℝ C)
  (hD₀ : Convex ℝ D)
  (hD₁ : Set.Nonempty (Set.preimage A (intrinsicInterior ℝ D))) :
  (intrinsicInterior ℝ (Set.image A C) = Set.image A (intrinsicInterior ℝ C)) ∧
  (intrinsicInterior ℝ (Set.preimage A D) = Set.preimage A (intrinsicInterior ℝ D)) := by
  sorry
