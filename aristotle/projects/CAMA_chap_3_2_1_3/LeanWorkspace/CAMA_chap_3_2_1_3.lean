import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_2_1_3
  (C : Set E)
  (hC₀ : Nonempty C)
  (hC₁ : Convex ℝ C) :
  (Set.Nonempty (intrinsicInterior ℝ C)) ∧
  (Module.finrank ℝ (affineSpan ℝ C).direction) =
  (Module.finrank ℝ (affineSpan ℝ (intrinsicInterior ℝ C)).direction) := by
  sorry
