import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_D_1_3_3
  (g : E → ℝ)
  (hg_convex : ConvexOn ℝ Set.univ g)
  (hg_neg : ∃ (x₀ : E), g x₀ < 0):
  (closure {z | g z < 0} = {z | g z ≤ 0}) ∧
  ({z | g z < 0} = interior {z | g z ≤ 0}) ∧
  (frontier {z | g z ≤ 0} = {z | g z = 0}) := by
  sorry
