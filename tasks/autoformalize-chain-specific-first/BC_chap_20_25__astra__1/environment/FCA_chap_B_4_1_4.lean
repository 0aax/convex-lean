import LeanWorkspace.Defs

open scoped InnerProductSpace

/-- Hiriart-Urruty and Lemaréchal, *Fundamentals of Convex Analysis*,
Theorem B.4.1.4 (PDF page 122), stated for a real Hilbert space.

On a convex subset of an open set where `f` is differentiable, convexity,
strict convexity, and strong convexity are equivalent to monotonicity,
strict monotonicity, and strong monotonicity of the gradient, respectively.
The gradient conditions are written as the inequalities of Definition B.4.1.3. -/
theorem FCA_chap_B_4_1_4
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Ω C : Set E} {f : E → ℝ}
    (hΩ : IsOpen Ω) (hf : DifferentiableOn ℝ f Ω)
    (hCΩ : C ⊆ Ω) (hC : Convex ℝ C) :
    (ConvexOn ℝ C f ↔
      ∀ x ∈ C, ∀ y ∈ C,
        0 ≤ ⟪gradient f x - gradient f y, x - y⟫_ℝ) ∧
    (StrictConvexOn ℝ C f ↔
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        0 < ⟪gradient f x - gradient f y, x - y⟫_ℝ) ∧
    (∀ c : ℝ, 0 < c →
      (StrongConvexOn C c f ↔
        ∀ x ∈ C, ∀ y ∈ C,
          c * ‖x - y‖ ^ 2 ≤ ⟪gradient f x - gradient f y, x - y⟫_ℝ)) := by
  sorry
