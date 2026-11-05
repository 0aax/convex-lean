import LeanWorkspace.Defs

open scoped InnerProductSpace

/-- **Proposition B.1.2.1** (Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*).
Any `f ∈ Conv ℝⁿ` is minorized by some affine function. More precisely: for any
`x₀ ∈ ri dom f`, there is `s` in the subspace parallel to `aff dom f` such that
`f x ≥ f x₀ + ⟪s, x - x₀⟫` for all `x`, i.e. the affine minorant can be forced to coincide
with `f` at `x₀`.

The Euclidean space `ℝⁿ` is generalized to a finite-dimensional real inner product space `E`.
A function `f ∈ Conv E` (Definition B.1.1.3) is encoded as `f : E → EReal` taking values in
`ℝ ∪ {+∞}` (`hf_ne_bot`), not identically `+∞` (`hf_proper`), and satisfying the convexity
inequality in `ℝ ∪ {+∞}` (`hf_conv`). Its domain is `dom f = {x | f x < ⊤}`, the relative
interior is `intrinsicInterior ℝ`, and the subspace parallel to `aff dom f` is the `direction`
of `affineSpan ℝ (dom f)`. -/
theorem FCA_chap_B_1_2_1
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal)
    (hf_ne_bot : ∀ x, f x ≠ ⊥)
    (hf_proper : ∃ x, f x ≠ ⊤)
    (hf_conv : ∀ x x' : E, ∀ α : ℝ, 0 < α → α < 1 →
      f (α • x + (1 - α) • x') ≤ (α : EReal) * f x + ((1 - α : ℝ) : EReal) * f x') :
    (∃ a : E →ᵃ[ℝ] ℝ, ∀ x, (a x : EReal) ≤ f x) ∧
    ∀ x₀ ∈ intrinsicInterior ℝ {x | f x < ⊤},
      ∃ s ∈ (affineSpan ℝ {x | f x < ⊤}).direction,
        ∀ x, f x₀ + ((⟪s, x - x₀⟫_ℝ : ℝ) : EReal) ≤ f x := by
  sorry
