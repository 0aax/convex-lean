import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_A_ex_20
  (S : Set E)
  (hS_bounded : Bornology.IsBounded S) :
  sSup {v | ∃ x y, (x ∈ S) ∧ (y ∈ S) ∧ (v = ‖y - x‖)} =
  sSup {v | ∃ x y, (x ∈ convexHull ℝ S) ∧ (y ∈ convexHull ℝ S) ∧ (v = ‖y - x‖)} := by
  sorry
