import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 800000 in
theorem FCA_chap_B_4_1_1
  (f : E → ℝ)
  (Ω : Set E)
  (C : Set E)
  (c : ℝ)
  (hΩ_open : IsOpen Ω)
  (hC_convex : Convex ℝ C)
  (hC_subset : C ⊆ Ω)
  (hf_differentiable : DifferentiableOn ℝ f Ω) :
  (ConvexOn ℝ C f ↔
  ∀ x₀ ∈ C, ∀ x ∈ C, f x ≥ f x₀ + @inner ℝ _ _ (gradient f x₀) (x - x₀)) ∧
  (StrictConvexOn ℝ C f ↔
  ∀ x₀ ∈ C, ∀ x ∈ C,
  (f x ≥ f x₀ + @inner ℝ _ _ (gradient f x₀) (x - x₀)) ∧
  ((x ≠ x₀) → f x > f x₀ + @inner ℝ _ _ (gradient f x₀) (x - x₀))) ∧
  (StrongConvexOn C c f ↔
  ∀ x₀ ∈ C, ∀ x ∈ C,
  f x ≥ f x₀ + @inner ℝ _ _ (gradient f x₀) (x - x₀) + 1/2 * c * ‖x - x₀‖^2) := by
  sorry
