import LeanWorkspace.Defs

/-!
# Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*, Proposition B.1.2.1

Source (Chapter B, §1.2(a), Proposition 1.2.1; p. 77 of the book, p. 87 of the PDF):

> Any `f ∈ Conv ℝⁿ` is minorized by some affine function. More precisely: for any
> `x₀ ∈ ri dom f`, there is `s` in the subspace parallel to `aff dom f` such that
>   `f(x) ≥ f(x₀) + ⟨s, x - x₀⟩` for all `x ∈ ℝⁿ`.
> In other words, the affine function can be forced to coincide with `f` at `x₀`.

Hypotheses, including the standing ones:
* The space is `ℝⁿ` with its scalar product `⟨·,·⟩`; no coordinates are used, so `E` is an
  abstract finite-dimensional real inner-product space.
* `f ∈ Conv ℝⁿ` (Definition B.1.1.3): `f : ℝⁿ → ℝ ∪ {+∞}` (the value `-∞` is excluded from the
  start of the book), not identically `+∞`, and convex; by Proposition B.1.1.6 convexity is
  convexity of `epi f = {(x, r) ∈ ℝⁿ × ℝ : r ≥ f(x)}` (Definition B.1.1.5).
  Encoded as `f : E → EReal` with `ProperEReal f` (never `⊥`, `effDom f` nonempty) and
  `ConvexEReal f`.
* `dom f := {x : f(x) < +∞}` (Definition B.1.1.4) is `effDom f`.
* `ri` (Definition A.2.1.1: the interior relative to the affine hull) is Mathlib's
  `intrinsicInterior ℝ`; `aff` is `affineSpan ℝ`, and the subspace parallel to `aff dom f` is
  `(affineSpan ℝ (effDom f)).direction`.

Conclusion:
1. some affine function `a : ℝⁿ → ℝ` minorizes `f`: `a(x) ≤ f(x)` for all `x`;
2. for every `x₀ ∈ ri dom f` there is `s` in the subspace parallel to `aff dom f` with
   `f(x₀) + ⟨s, x - x₀⟩ ≤ f(x)` for all `x`.
-/

theorem FCA_chap_B_1_2_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → EReal)
    -- the function: `f ∈ Conv ℝⁿ`, i.e. proper (values in `ℝ ∪ {+∞}`, not identically `+∞`)
    -- and convex
    (hf_proper : ProperEReal f) (hf_convex : ConvexEReal f) :
    -- `f` is minorized by some affine function
    (∃ a : E →ᵃ[ℝ] ℝ, ∀ x, (a x : EReal) ≤ f x) ∧
    -- at each `x₀ ∈ ri dom f`, an affine minorant coinciding with `f` at `x₀`, whose slope lies
    -- in the subspace parallel to `aff dom f`
    (∀ x₀ ∈ intrinsicInterior ℝ (effDom f),
      ∃ s ∈ (affineSpan ℝ (effDom f)).direction,
        ∀ x, f x₀ + ((inner ℝ s (x - x₀) : ℝ) : EReal) ≤ f x) := by
  sorry
