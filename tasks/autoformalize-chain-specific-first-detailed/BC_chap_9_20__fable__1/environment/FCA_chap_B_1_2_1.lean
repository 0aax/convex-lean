import LeanWorkspace.Defs

/-!
# Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*, Proposition B.1.2.1

Source: Chapter B, §1.2 (a), Proposition 1.2.1 (book p. 77, PDF p. 87).

## Statement in the source
"Any `f ∈ Conv ℝⁿ` is minorized by some affine function. More precisely: for any
`x₀ ∈ ri dom f`, there is `s` in the subspace parallel to `aff dom f` such that
    `f(x) ≥ f(x₀) + ⟨s, x − x₀⟩` for all `x ∈ ℝⁿ`.
In other words, the affine function can be forced to coincide with `f` at `x₀`."

## Hypotheses, including the standing ones
* Ambient space: `ℝⁿ` with its Euclidean scalar product `⟨·,·⟩` (standing setting of
  Chapters A and B).  Formalized as an abstract finite-dimensional real inner-product space `E`.
* `f ∈ Conv ℝⁿ` (Definition B.1.1.3): `f : ℝⁿ → ℝ ∪ {+∞}` (the value `−∞` is "excluded from
  the very beginning in the present book"), `f` not identically `+∞`, and `f` convex, which by
  Proposition B.1.1.6 means that the epigraph `epi f = {(x, r) : r ≥ f(x)}`
  (Definition B.1.1.5) is a convex set.  The book notes that `Conv ℝⁿ` coincides with the
  "proper convex" functions of other authors: `ProperEReal f ∧ ConvexEReal f`.
* `dom f = {x : f(x) < +∞}` (Definition B.1.1.4) is `effDom f`.
* `aff C` is the affine hull (§A.1.3), `affineSpan ℝ C`; "the subspace parallel to `aff C`"
  (Definition A.2.1.1) is its direction `(affineSpan ℝ C).direction`.
* `ri C` is the interior of `C` for the topology relative to `aff C` (Definition A.2.1.1),
  which is Mathlib's `intrinsicInterior ℝ C`.
* `x₀ ∈ ri dom f` (quantified inside the conclusion, as in the source).

## Conclusion
1. `f` is minorized by an affine function: there are `(s, b) ∈ ℝⁿ × ℝ` with
   `f(x) ≥ ⟨s, x⟩ − b` for all `x` (the book's form of an affine minorant, cf. Example B.2.1.3
   and Proposition B.2.3.3).
2. For every `x₀ ∈ ri dom f` there is `s` in the linear subspace parallel to `aff dom f` with
   `f(x) ≥ f(x₀) + ⟨s, x − x₀⟩` for all `x ∈ ℝⁿ`, i.e. `s ∈ ∂f(x₀)` (`subdifferential f x₀`).

No further hypotheses are needed to rule out junk values: by properness and `x₀ ∈ dom f`,
`f x₀` is a real number, so the `EReal` sum `f x₀ + ⟨s, x − x₀⟩` is the source's.
-/

theorem FCA_chap_B_1_2_1
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal)
    -- function: `f ∈ Conv ℝⁿ`, i.e. `f : ℝⁿ → ℝ ∪ {+∞}` not identically `+∞` (proper)
    -- with convex epigraph
    (hf_proper : ProperEReal f)
    (hf_convex : ConvexEReal f) :
    -- (1) `f` is minorized by some affine function `x ↦ ⟨s, x⟩ − b`
    (∃ (s : E) (b : ℝ), ∀ x, ((inner ℝ s x - b : ℝ) : EReal) ≤ f x) ∧
    -- (2) for any `x₀ ∈ ri dom f` there is a subgradient `s ∈ ∂f(x₀)`, i.e.
    --     `f(x) ≥ f(x₀) + ⟨s, x − x₀⟩` for all `x`, lying in the subspace parallel to `aff dom f`
    (∀ x₀ ∈ intrinsicInterior ℝ (effDom f),
      ∃ s ∈ (affineSpan ℝ (effDom f)).direction, s ∈ subdifferential f x₀) := by
  sorry
