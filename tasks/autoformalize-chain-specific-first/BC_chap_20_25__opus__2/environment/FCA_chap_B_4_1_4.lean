import LeanWorkspace.Defs

open scoped InnerProductSpace Gradient

/-- **Theorem B.4.1.4** (Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*).

Let `f` be differentiable on an open set `Ω` (the book works in `ℝⁿ`; here `E` is any real
Hilbert space) and let `C ⊆ Ω` be convex. Then `f` is convex [resp. strictly convex, resp. strongly
convex with modulus `c > 0`] on `C` if and only if its gradient `∇f` is monotone [resp. strictly
monotone, resp. strongly monotone with modulus `c`] on `C`.

Monotonicity of a mapping `F` on `C` is Definition B.4.1.3: for all `x, x' ∈ C`,
`⟪F x - F x', x - x'⟫ ≥ 0` [resp. `> 0` whenever `x ≠ x'`, resp. `≥ c * ‖x - x'‖ ^ 2`].

Strong convexity with modulus `c` (B.(1.1.2)) is Mathlib's `StrongConvexOn C c f`, i.e.
`f (a • x + b • y) ≤ a • f x + b • f y - a * b * (c / 2 * ‖x - y‖ ^ 2)` for `a, b ≥ 0`,
`a + b = 1`. -/
theorem FCA_chap_B_4_1_4
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {Ω C : Set E} (hΩ : IsOpen Ω) (hf : DifferentiableOn ℝ f Ω)
    (hC : Convex ℝ C) (hCΩ : C ⊆ Ω) :
    (ConvexOn ℝ C f ↔
      ∀ x ∈ C, ∀ x' ∈ C, 0 ≤ ⟪∇ f x - ∇ f x', x - x'⟫_ℝ) ∧
    (StrictConvexOn ℝ C f ↔
      ∀ x ∈ C, ∀ x' ∈ C, x ≠ x' → 0 < ⟪∇ f x - ∇ f x', x - x'⟫_ℝ) ∧
    (∀ c : ℝ, 0 < c → (StrongConvexOn C c f ↔
      ∀ x ∈ C, ∀ x' ∈ C, c * ‖x - x'‖ ^ 2 ≤ ⟪∇ f x - ∇ f x', x - x'⟫_ℝ)) := by
  sorry
