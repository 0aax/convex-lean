import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem CAMA_chap_3_1_2_4
  (A : AffineMap ℝ E F)
  (C : Set E)
  (D : Set F)
  (hC : Convex ℝ C)
  (hD : Convex ℝ D) :
  Convex ℝ (Set.image A C) ∧
  (Convex ℝ (Set.preimage A D)) := by
  sorry
