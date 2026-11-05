import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_A_ex_22
  (C : Set E)
  (hC_convex : Convex ℝ C) :
  IsClosed C ↔
  (∀ (a d : E), d ≠ 0 →
    IsClosed (C ∩ {x | ∃ t : ℝ, x = a + t • d})) := by
  sorry
