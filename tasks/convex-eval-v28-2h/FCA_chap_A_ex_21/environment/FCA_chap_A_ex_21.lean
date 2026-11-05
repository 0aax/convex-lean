import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def setAdd {E : Type*} [NormedAddCommGroup E]
    (C : Set E) (K : Set E)
    : Set E
    := {v : E | ∃ c ∈ C, ∃ k ∈ K, v = c + k}

theorem FCA_chap_A_ex_21
  (S₁ S₂ : Set E) :
  convexHull ℝ (S₁ ∩ S₂) ⊆ convexHull ℝ S₁ ∩ convexHull ℝ S₂ ∧
  convexHull ℝ (setAdd S₁ S₂) = setAdd (convexHull ℝ S₁) (convexHull ℝ S₂) ∧
  convexHull ℝ (S₁ ∪ S₂) = convexHull ℝ (convexHull ℝ S₁ ∪ convexHull ℝ S₂) := by
  sorry
