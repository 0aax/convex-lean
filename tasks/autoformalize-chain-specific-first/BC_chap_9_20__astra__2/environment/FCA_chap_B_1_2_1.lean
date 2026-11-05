import LeanWorkspace.Defs

open ConvexAnalysis
open scoped InnerProductSpace

/-- Proposition B.1.2.1 of Hiriart-Urruty and Lemaréchal, *Fundamentals of Convex
Analysis* (PDF page 87), for a finite-dimensional real inner product space.

Every proper convex function has an affine minorant. At each point of the relative
interior of its effective domain, it has a supporting affine minorant whose slope
belongs to the direction space of the affine hull of the domain. -/
theorem FCA_chap_B_1_2_1
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → EReal) (hf : IsProperConvex f) :
    (∃ a : E →ᵃ[ℝ] ℝ, ∀ x : E, (a x : EReal) ≤ f x) ∧
      ∀ x₀ ∈ intrinsicInterior ℝ (effectiveDomain f),
        ∃ s ∈ (affineSpan ℝ (effectiveDomain f)).direction,
          ∀ x : E, f x₀ + (⟪s, x - x₀⟫_ℝ : EReal) ≤ f x := by
  sorry
