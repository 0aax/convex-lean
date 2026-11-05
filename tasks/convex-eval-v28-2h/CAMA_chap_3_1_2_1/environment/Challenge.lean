import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_1_2_1 {ι : Type*}
  (J : Set ι)
  (C : ι → Set E)
  (hC : ∀ i, Convex ℝ (C i)) :
  Convex ℝ (⋂ (j : ι) (_ : j ∈ J), (C j)) := by
  sorry
