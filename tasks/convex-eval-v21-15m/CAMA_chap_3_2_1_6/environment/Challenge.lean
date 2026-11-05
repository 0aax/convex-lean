import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_2_1_6
  (x₁ : E)
  (x₂ : E)
  (C : Set E)
  (hC_nonempty : Set.Nonempty C)
  (hC_convex : Convex ℝ C)
  (hx₁ : x₁ ∈ closure C)
  (hx₂ : x₂ ∈ (intrinsicInterior ℝ C)) :
  {v : E | ∃ (α : ℝ), (0 ≤ α) ∧ (α < 1) ∧
                                  (v = α • x₁ + (1-α) • x₂)} ⊆ intrinsicInterior ℝ C := by
  sorry
