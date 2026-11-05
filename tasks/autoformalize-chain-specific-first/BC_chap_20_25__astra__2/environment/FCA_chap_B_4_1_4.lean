import LeanWorkspace.Defs

open scoped InnerProductSpace

/-- Hiriart-Urruty and Lemaréchal, *Fundamentals of Convex Analysis*,
Theorem B.4.1.4 (PDF page 122), stated for a real Hilbert space.

On a convex subset of an open set where `f` is differentiable, convexity,
strict convexity, and strong convexity are respectively equivalent to
monotonicity, strict monotonicity, and strong monotonicity of its gradient.
The inner-product inequalities express the monotonicity notions of
Definition B.4.1.3; the strong case uses the same positive modulus `c`. -/
theorem FCA_chap_B_4_1_4
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {Ω C : Set E}
    (hΩ : IsOpen Ω) (hC : Convex ℝ C) (hCΩ : C ⊆ Ω)
    (hf : DifferentiableOn ℝ f Ω) :
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
