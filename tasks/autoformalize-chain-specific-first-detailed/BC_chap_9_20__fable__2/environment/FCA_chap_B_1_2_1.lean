import LeanWorkspace.Defs

/-!
# Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*, Proposition B.1.2.1

Source: Chapter B, §1.2, Proposition 1.2.1 (PDF page 87).

## Standing assumptions of Chapter B
* The ambient space is `ℝⁿ` equipped with a scalar product `⟨·,·⟩`; here an abstract
  finite-dimensional real inner-product space `E` (no coordinates are used).
* Functions take values in `ℝ ∪ {+∞}`: the value `−∞` is excluded throughout the book.

## Hypotheses stated by the source
* `f ∈ Conv ℝⁿ` (Definition B.1.1.3): `f : ℝⁿ → ℝ ∪ {+∞}`, not identically `+∞`, and
  `f(αx + (1 − α)x') ≤ αf(x) + (1 − α)f(x')` in `ℝ ∪ {+∞}` for all `x, x'` and
  `α ∈ ]0,1[`; equivalently (Proposition B.1.1.6) the epigraph `epi f` is convex.  The book
  remarks that this is the "proper convexity" of other authors, so it is encoded as
  `IsProperEReal f` (never `−∞`, `dom f ≠ ∅`) together with `ConvexEReal f`.
* `dom f := {x : f(x) < +∞}` (Definition B.1.1.4) is `effDom f`.
* `aff dom f` is the affine hull of `dom f` (§A.1.3), and "the subspace parallel to
  `aff dom f`" is the linear subspace `V` with `aff dom f = x₀ + V` (§A.1.3 (iv')):
  `(affineSpan ℝ (effDom f)).direction`.
* `ri dom f` is the interior of `dom f` for the topology relative to `aff dom f`
  (Definition A.2.1.1): `intrinsicInterior ℝ (effDom f)`.

## Conclusion stated by the source
1. `f` is minorized by some affine function `ℝⁿ → ℝ`.
2. More precisely: for any `x₀ ∈ ri dom f`, there is `s` in the subspace parallel to
   `aff dom f` such that `f(x) ≥ f(x₀) + ⟨s, x − x₀⟩` for all `x ∈ ℝⁿ`
   (the affine function can be forced to coincide with `f` at `x₀`).
-/

theorem FCA_chap_B_1_2_1
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal)
    -- function: `f ∈ Conv ℝⁿ`, i.e. proper (values in `ℝ ∪ {+∞}`, not identically `+∞`)
    -- and convex
    (hf_proper : IsProperEReal f)
    (hf_convex : ConvexEReal f) :
    -- (1) `f` is minorized by an affine function
    (∃ a : E →ᵃ[ℝ] ℝ, ∀ x, (a x : EReal) ≤ f x) ∧
    -- (2) at every `x₀ ∈ ri dom f` the affine minorant can be chosen to coincide with `f`
    -- at `x₀`, with slope in the subspace parallel to `aff dom f`
    ∀ x₀ ∈ intrinsicInterior ℝ (effDom f),
      ∃ s ∈ (affineSpan ℝ (effDom f)).direction,
        ∀ x, f x₀ + ((inner ℝ s (x - x₀) : ℝ) : EReal) ≤ f x := by
  sorry
