import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_1_2_7
  (C : Set E)
  (hC : Convex ℝ C) :
  Convex ℝ (interior C) ∧ Convex ℝ (closure C) := by
  sorry
