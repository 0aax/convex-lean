import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_2_1_10
  (C₁ : Set E)
  (C₂ : Set E)
  (hC₁ : Convex ℝ C₁)
  (hC₂ : Convex ℝ C₂)
  (hC : Set.Nonempty (intrinsicInterior ℝ C₁ ∩ intrinsicInterior ℝ C₂)) :
  (intrinsicInterior ℝ (C₁ ∩ C₂) = intrinsicInterior ℝ C₁ ∩ intrinsicInterior ℝ C₂) ∧
  (closure (C₁ ∩ C₂) = closure C₁ ∩ closure C₂) := by
  sorry
