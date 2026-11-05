import LeanWorkspace.Defs

open scoped RealInnerProductSpace

/-- **Proposition B.1.2.1** (Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*).
Any `f ∈ Conv ℝⁿ` is minorized by some affine function. More precisely: for any
`x₀ ∈ ri dom f`, there is `s` in the subspace parallel to `aff dom f` such that
`f x ≥ f x₀ + ⟪s, x - x₀⟫` for all `x ∈ ℝⁿ`
(i.e. the affine minorant can be forced to coincide with `f` at `x₀`).

Formalization conventions:
* `ℝⁿ` (equipped with a scalar product `⟪·, ·⟫`) is generalized to a finite-dimensional real
  inner product space `E`;
* a function `f : ℝⁿ → ℝ ∪ {+∞}` is an `f : E → EReal` that never takes the value `⊥`;
* `f ∈ Conv ℝⁿ` (Definition B.1.1.3): `f` is not identically `+∞` and
  `f (α • x + (1 - α) • x') ≤ α f x + (1 - α) f x'` in `ℝ ∪ {+∞}` for all `x, x'` and
  `α ∈ ]0, 1[`;
* `dom f = {x | f x < ⊤}` (Definition B.1.1.4), `ri` is `intrinsicInterior ℝ`, and the
  subspace parallel to `aff dom f` is `(affineSpan ℝ (dom f)).direction`. -/
theorem FCA_chap_B_1_2_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → EReal)
    (hf_ne_bot : ∀ x, f x ≠ ⊥)
    (hf_ne_top : ∃ x, f x ≠ ⊤)
    (hf_conv : ∀ x x' : E, ∀ α : ℝ, 0 < α → α < 1 →
      f (α • x + (1 - α) • x') ≤ (α : EReal) * f x + ((1 - α : ℝ) : EReal) * f x') :
    (∃ a : E →ᵃ[ℝ] ℝ, ∀ x, (a x : EReal) ≤ f x) ∧
    ∀ x₀ ∈ intrinsicInterior ℝ {x | f x < ⊤},
      ∃ s ∈ (affineSpan ℝ {x | f x < ⊤}).direction,
        ∀ x, f x₀ + ((⟪s, x - x₀⟫ : ℝ) : EReal) ≤ f x := by
  sorry
