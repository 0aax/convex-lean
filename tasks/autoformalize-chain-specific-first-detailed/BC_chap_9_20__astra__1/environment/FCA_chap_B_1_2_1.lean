/-
Hiriart-Urruty and Lemaréchal, *Fundamentals of Convex Analysis*, Chapter B,
Section 1.2, Proposition 1.2.1 (printed page 77; PDF page 87).

Source hypotheses and standing conventions:
* The ambient space is the finite-dimensional real Euclidean space ℝⁿ
  (Chapter A, Introduction, and Section 0.3).
* `f ∈ Conv ℝⁿ`: f takes values in ℝ ∪ {+∞}, is not identically +∞,
  and is convex (Definition B.1.1.3). Thus it is proper; convexity is
  equivalently convexity of its epigraph (Proposition B.1.1.6).
* `dom f = {x | f(x) < +∞}` (Definition B.1.1.4). Relative interior means
  interior in the affine hull (Definition A.2.1.1).

Source conclusion: f has an affine minorant. More precisely, for every
x₀ ∈ ri (dom f), there is s in the linear subspace parallel to aff (dom f)
such that f(x) ≥ f(x₀) + ⟪s, x - x₀⟫ for every x ∈ ℝⁿ. Hence the
minorant can be chosen to agree with f at x₀. The supporting inequality
in the proposition is unnumbered.

We use an abstract finite-dimensional real inner-product space for ℝⁿ,
Mathlib's `intrinsicInterior` for ri and `AffineSubspace.direction` for the
parallel subspace. The supporting inequality is expressed using the shared
extended-valued convex subdifferential.
-/

import LeanWorkspace.Defs

theorem FCA_chap_B_1_2_1
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → EReal)
    -- Function hypotheses: f belongs to the source's class Conv ℝⁿ.
    (hf_proper : IsProperEReal f) (hf_convex : ConvexEReal f) :
    (∃ a : E →ᵃ[ℝ] ℝ, ∀ x : E, (a x : EReal) ≤ f x) ∧
      (∀ x₀ ∈ intrinsicInterior ℝ (effDom f),
        ∃ s ∈ (affineSpan ℝ (effDom f)).direction,
          s ∈ convexSubdifferential f x₀) := by
  sorry
