import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def hyperplaneHalfspace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (s : E) (t : ℝ) : Set E :=
  {x | inner ℝ s x ≤ t}

theorem BC_chap_7_12
  (C : Set E)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C) :
  C = ⋂ (u : E) (η : ℝ) (_ : C ⊆ hyperplaneHalfspace u η), hyperplaneHalfspace u η := by
  sorry
