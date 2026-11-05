import LeanWorkspace.Defs

/-- Hiriart-Urruty and Lemaréchal, *Fundamentals of Convex Analysis*,
Proposition B.1.2.1 (PDF page 87).

A proper convex function on a finite-dimensional real inner product space has a
real-valued affine minorant. At every point of the relative interior of its
effective domain, it has a subgradient in the direction space of the domain's
affine hull. Here `intrinsicInterior` is relative interior, and convexity is
expressed by convexity of the epigraph, as in Proposition B.1.1.6 of the book. -/
theorem FCA_chap_B_1_2_1
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → EReal)
    (hf_proper : ConvexAnalysis.IsProper f)
    (hf_convex : Convex ℝ (ConvexAnalysis.epigraph f)) :
    (∃ a : E →ᵃ[ℝ] ℝ, ∀ x : E, (a x : EReal) ≤ f x) ∧
      (∀ x₀ ∈ intrinsicInterior ℝ (ConvexAnalysis.effectiveDomain f),
        ∃ s ∈ (affineSpan ℝ (ConvexAnalysis.effectiveDomain f)).direction,
          ∀ x : E, f x₀ + (inner ℝ s (x - x₀) : EReal) ≤ f x) := by
  sorry
