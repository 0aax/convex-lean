import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_1_4_3
  (S : Set E) :
  (Bornology.IsBounded S → Bornology.IsBounded (convexHull ℝ S)) ∧
  (IsCompact S → IsCompact (convexHull ℝ S)) := by
  sorry
