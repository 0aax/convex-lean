import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_A_ex_11
  (S : Set E) :
  ∀ x ∈ Set.extremePoints ℝ (convexHull ℝ S), x ∈ S := by
  sorry
