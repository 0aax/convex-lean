import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_2_3_4
    (C : Set E)
    (hC₀ : C.Nonempty)
    (hC₁ : Convex ℝ C)
    (hC₂ : IsCompact C) :
    C = convexHull ℝ (Set.extremePoints ℝ C) := by
  sorry
