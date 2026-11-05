import LeanWorkspace.Defs

/-!
# Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*, Proposition B.1.2.1

Source (Chapter B, §1.2(a), p. 77): "Any `f ∈ Conv ℝⁿ` is minorized by some affine function.
More precisely: for any `x₀ ∈ ri dom f`, there is `s` in the subspace parallel to `aff dom f`
such that `f(x) ≥ f(x₀) + ⟨s, x - x₀⟩` for all `x ∈ ℝⁿ`. In other words, the affine function
can be forced to coincide with `f` at `x₀`."

Standing setting and definitions used:
* the space is `ℝⁿ` with the scalar product `⟨·, ·⟩`;
* Definition B.1.1.3: `Conv ℝⁿ` is the class of functions `f : ℝⁿ → ℝ ∪ {+∞}` (the value `-∞`
  is excluded from the start), not identically `+∞`, that are convex; by Proposition B.1.1.6
  convexity is equivalent to convexity of `epi f = {(x, r) ∈ ℝⁿ × ℝ : r ≥ f(x)}`;
* Definition B.1.1.4: `dom f := {x ∈ ℝⁿ : f(x) < +∞}`;
* `aff S` is the affine hull (§A.1.3) and `ri C` the relative interior, the interior of `C`
  for the topology relative to `aff C` (Definition A.2.1.1).

Hypotheses:
* `f ∈ Conv ℝⁿ`: `f` never takes the value `-∞`, is not identically `+∞`, and is convex.

Conclusion:
1. some affine function `a` satisfies `a(x) ≤ f(x)` for all `x`;
2. for every `x₀ ∈ ri dom f` there is `s ∈ V`, where `V` is the subspace parallel to
   `aff dom f`, such that `f(x) ≥ f(x₀) + ⟨s, x - x₀⟩` for all `x`.

Formalization: `ℝⁿ` becomes a finite-dimensional real inner-product space `E`; `f : E → EReal`;
`f ∈ Conv ℝⁿ` is `ProperEReal f` (never `⊥`, `effDom f` nonempty) together with
`ConvexEReal f` (convex epigraph); an affine function is a Mathlib affine map `E →ᵃ[ℝ] ℝ`;
`ri` is Mathlib's `intrinsicInterior ℝ`; the subspace parallel to `aff dom f` is
`(affineSpan ℝ (effDom f)).direction`.
-/

theorem FCA_chap_B_1_2_1
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal)
    -- the function: `f ∈ Conv ℝⁿ` (values in `ℝ ∪ {+∞}`, not identically `+∞`, convex)
    (hf_proper : ProperEReal f) (hf_convex : ConvexEReal f) :
    -- `f` is minorized by some affine function
    (∃ a : E →ᵃ[ℝ] ℝ, ∀ x, ((a x : ℝ) : EReal) ≤ f x) ∧
    -- at each `x₀ ∈ ri dom f`, an affine minorant equal to `f` at `x₀`, with slope `s`
    -- in the subspace parallel to `aff dom f`
    (∀ x₀ ∈ intrinsicInterior ℝ (effDom f),
      ∃ s ∈ (affineSpan ℝ (effDom f)).direction,
        ∀ x, f x₀ + ((inner ℝ s (x - x₀) : ℝ) : EReal) ≤ f x) := by
  sorry
