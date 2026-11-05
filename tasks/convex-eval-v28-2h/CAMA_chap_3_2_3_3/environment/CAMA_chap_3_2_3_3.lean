import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_2_3_3
  (C : Set E)
  (hC₀ : Set.Nonempty C)
  (hC₁ : Convex ℝ C)
  (hC₂ : IsCompact C) :
  Set.Nonempty (Set.extremePoints ℝ C) := by
  sorry
