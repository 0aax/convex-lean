import LeanWorkspace.Defs

open scoped InnerProductSpace

/-- **Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*, Proposition B.1.2.1.**

Any `f ∈ Conv ℝⁿ` is minorized by some affine function.  More precisely, for any
`x₀ ∈ ri dom f` there is `s` in the subspace parallel to `aff dom f` such that
`f x ≥ f x₀ + ⟨s, x - x₀⟩` for all `x ∈ ℝⁿ`; in other words the affine minorant can be
forced to coincide with `f` at `x₀` (`s` is a subgradient of `f` at `x₀`).

Formalized over an arbitrary finite-dimensional real inner product space `E` (the book's
`ℝⁿ` is `EuclideanSpace ℝ (Fin n)`).  The relative interior `ri dom f` is
`intrinsicInterior ℝ (effectiveDomain f)` and the subspace parallel to `aff dom f` is
`vectorSpan ℝ (effectiveDomain f) = (affineSpan ℝ (effectiveDomain f)).direction`. -/
theorem FCA_chap_B_1_2_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → EReal} (hf : IsProperConvexFunction f) :
    (∃ g : E →ᵃ[ℝ] ℝ, ∀ x, (g x : EReal) ≤ f x) ∧
    ∀ x₀ ∈ intrinsicInterior ℝ (effectiveDomain f),
      ∃ s ∈ vectorSpan ℝ (effectiveDomain f),
        ∀ x, f x₀ + (⟪s, x - x₀⟫_ℝ : EReal) ≤ f x := by
  sorry
