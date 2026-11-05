import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_C_ex14
  (S : ℕ → Set E)
  (hS_nested : ∀ k, S (k + 1) ⊆ S k)
  (hS_compact : ∀ k, IsCompact (S k)) :
  convexHull ℝ (⋂ k, S k) = ⋂ k, convexHull ℝ (S k) := by
  sorry
