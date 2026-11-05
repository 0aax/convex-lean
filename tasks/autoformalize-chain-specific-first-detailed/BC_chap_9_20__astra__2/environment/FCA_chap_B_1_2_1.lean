/-
Hiriart-Urruty and Lemaréchal, Fundamentals of Convex Analysis,
Chapter B, §1.2, Proposition 1.2.1, printed page 77 (PDF page 87).

Source hypotheses and standing assumptions:
* The ambient space is the finite-dimensional real Euclidean space ℝⁿ.
* f ∈ Conv ℝⁿ: f takes values in ℝ ∪ {+∞}, is not identically +∞,
  and is convex (Definition B.1.1.3). Equivalently, it is proper and
  has a convex epigraph (Proposition B.1.1.6).
* dom f = {x | f(x) < +∞} (Definition B.1.1.4).
* ri denotes the interior relative to the affine hull (Definition A.2.1.1).

Source conclusions:
* There exists an affine function minorizing f on all of ℝⁿ.
* For every x₀ ∈ ri dom f, there is s in the linear subspace parallel
  to aff dom f such that f(x) ≥ f(x₀) + ⟨s, x - x₀⟩ for every x ∈ ℝⁿ.
  This affine minorant coincides with f at x₀.

The statement uses an abstract finite-dimensional real inner-product space.
Mathlib's `intrinsicInterior` and `AffineSubspace.direction` express the
relative interior and the parallel subspace. Properness and membership in
ri dom f ensure that f(x₀) is finite in the supporting inequality.
-/

import LeanWorkspace.Defs

theorem FCA_chap_B_1_2_1
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → EReal)
    -- Function: membership in the source's class `Conv ℝⁿ`.
    (hf_proper : IsProper f)
    (hf_convex : ConvexEReal f) :
    (∃ a : E →ᵃ[ℝ] ℝ, ∀ x : E, (a x : EReal) ≤ f x) ∧
      (∀ x₀ ∈ intrinsicInterior ℝ (effDom f),
        ∃ s ∈ (affineSpan ℝ (effDom f)).direction,
          ∀ x : E, f x₀ + (inner ℝ s (x - x₀) : EReal) ≤ f x) := by
  sorry
