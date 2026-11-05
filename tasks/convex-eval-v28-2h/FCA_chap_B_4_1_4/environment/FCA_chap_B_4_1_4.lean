import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def IsMonotone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (T : E → Set E) : Prop :=
  ∀ (x₀ x₁ v₀ v₁ : E), v₀ ∈ T x₀ → v₁ ∈ T x₁ →
  0 ≤ inner ℝ (v₁ - v₀) (x₁ - x₀)

def IsStrictMonotone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (T : E → Set E) : Prop :=
  ∀ (x₀ x₁ v₀ v₁ : E), x₀ ≠ x₁ → v₀ ∈ T x₀ → v₁ ∈ T x₁ →
  0 < inner ℝ (v₁ - v₀) (x₁ - x₀)

def IsStronglyMonotone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (T : E → Set E)
  (c : ℝ) : Prop :=
  ∀ (x₀ x₁ v₀ v₁ : E), v₀ ∈ T x₀ → v₁ ∈ T x₁ →
  c * ‖x₁ - x₀‖^2 ≤ inner ℝ (v₁ - v₀) (x₁ - x₀)

theorem FCA_chap_B_4_1_4
    (f : E → ℝ) (Ω C : Set E) (c : ℝ)
    (hΩ_open : IsOpen Ω) (hC_convex : Convex ℝ C) (hC_subset : C ⊆ Ω)
    (hf_differentiable : DifferentiableOn ℝ f Ω) (hc_pos : c > 0) :
    ((ConvexOn ℝ C f) ↔ IsMonotone (fun x => {v | x ∈ C ∧ v = gradient f x})) ∧
      ((StrictConvexOn ℝ C f) ↔ IsStrictMonotone (fun x => {v | x ∈ C ∧ v = gradient f x})) ∧
      ((StrongConvexOn C c f) ↔ IsStronglyMonotone (fun x => {v | x ∈ C ∧ v = gradient f x}) c) := by
  sorry
