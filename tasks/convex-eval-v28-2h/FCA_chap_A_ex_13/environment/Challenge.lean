import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def projectionMapping {E : Type*} [NormedAddCommGroup E] (C : Set E) (x : E) : Set E :=
  {w : E | w ∈ C ∧ ∀ z ∈ C, ‖w - x‖ ≤ ‖z - x‖}

theorem FCA_chap_A_ex_13
  (C : Set E)
  (x yC : E)
  (hC_nonempty : Set.Nonempty C)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C)
  (hyC : yC ∈ C) :
  yC ∈ projectionMapping C x ↔
  (∀ y ∈ C, inner ℝ (x - y) (y - yC) ≤ 0) := by
  sorry
