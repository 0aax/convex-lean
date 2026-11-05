import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def pC {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : E) (C : Set E)
    (hC₁ : IsClosed C) (hC₂ : Convex ℝ C) (hC₃ : Set.Nonempty C) : E
    := Classical.choose (exists_norm_eq_iInf_of_complete_convex hC₃ hC₁.isComplete hC₂ x)

theorem CAMA_chap_3_3_1_3
  (C : Set E)
  (x₁ x₂ : E)
  (hC₀ : IsClosed C)
  (hC₁ : Convex ℝ C)
  (hC₂ : Set.Nonempty C) :
  ‖(pC x₁ C hC₀ hC₁ hC₂) - (pC x₂ C hC₀ hC₁ hC₂)‖ ^ 2
  ≤ inner ℝ ((pC x₁ C hC₀ hC₁ hC₂) - (pC x₂ C hC₀ hC₁ hC₂)) (x₁ - x₂) := by
  sorry
