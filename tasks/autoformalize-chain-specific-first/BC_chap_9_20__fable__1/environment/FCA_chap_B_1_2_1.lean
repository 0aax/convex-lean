import LeanWorkspace.Defs

open scoped InnerProductSpace

/-!
# Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*, Proposition B.1.2.1

**Statement in the book.** Any `f ∈ Conv ℝⁿ` is minorized by some affine function.
More precisely: for any `x₀ ∈ ri dom f`, there is `s` in the subspace parallel to
`aff dom f` such that `f(x) ≥ f(x₀) + ⟨s, x - x₀⟩` for all `x ∈ ℝⁿ`.
In other words, the affine function can be forced to coincide with `f` at `x₀`.

**Formalization choices.**
* `Conv ℝⁿ` (Definition B.1.1.3) is the class of convex functions `ℝⁿ → ℝ ∪ {+∞}` that are
  not identically `+∞`.  As the book itself explains (Definitions B.1.1.1, B.1.1.3, B.1.1.4
  and (1.1.3)), such an `f` is the same thing as a real-valued function that is convex on its
  nonempty effective domain `D = dom f`, extended by `+∞` outside `D`.  We therefore represent
  `f ∈ Conv ℝⁿ` by `f : E → ℝ` together with `hD : D.Nonempty` and `hf : ConvexOn ℝ D f`
  (Mathlib's idiom), and the inequality `f x ≥ f x₀ + ⟨s, x - x₀⟩` is only required for
  `x ∈ D`, since for `x ∉ D` it reads `+∞ ≥ …` and is vacuous.
* `ℝⁿ` is generalized to an arbitrary finite-dimensional real inner product space `E`; the
  relative interior `ri` is Mathlib's `intrinsicInterior ℝ`, and "the subspace parallel to
  `aff dom f`" is `(affineSpan ℝ D).direction`.  Finite-dimensionality is essential: the
  statement (even the mere existence of a continuous affine minorant) fails in infinite
  dimensions for non-lower-semicontinuous `f`.
-/

/-- **Proposition B.1.2.1** (Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*).
Let `f ∈ Conv ℝⁿ`, represented by `f : E → ℝ` convex on its nonempty effective domain `D`.
Then
1. `f` is minorized by an affine function `x ↦ ⟪s, x⟫ - b`, and
2. more precisely, for every `x₀` in the relative interior of `D = dom f` there is a
   subgradient `s`, lying in the linear subspace parallel to `aff dom f`, with
   `f x ≥ f x₀ + ⟪s, x - x₀⟫` for all `x`, i.e. the affine minorant can be forced to
   coincide with `f` at `x₀`. -/
theorem FCA_chap_B_1_2_1
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {D : Set E} {f : E → ℝ} (hD : D.Nonempty) (hf : ConvexOn ℝ D f) :
    (∃ s : E, ∃ b : ℝ, ∀ x ∈ D, ⟪s, x⟫_ℝ - b ≤ f x) ∧
    ∀ x₀ ∈ intrinsicInterior ℝ D, ∃ s ∈ (affineSpan ℝ D).direction,
      ∀ x ∈ D, f x₀ + ⟪s, x - x₀⟫_ℝ ≤ f x := by
  sorry
