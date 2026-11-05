import LeanWorkspace.Defs

open scoped Gradient InnerProductSpace

/-- **Theorem B.4.1.4** (Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*).

Let `f` be differentiable on an open set `Ω` and let `C ⊆ Ω` be convex. Then `f` is convex
[resp. strictly convex, resp. strongly convex with modulus `c > 0`] on `C` if and only if its
gradient `∇f` is monotone [resp. strictly monotone, resp. strongly monotone with modulus `c`]
on `C`.

The book works in `ℝⁿ` equipped with an arbitrary scalar product `⟪·, ·⟫`; here the ambient
space is any real Hilbert space `E` (completeness is what makes the gradient `∇f` available).

* Convexity, strict convexity and strong convexity with modulus `c` on `C` (Definition B.1.1.1
  and (B.1.1.2): `f (α x + (1 - α) x') ≤ α f x + (1 - α) f x' - ½ c α (1 - α) ‖x - x'‖²`)
  are Mathlib's `ConvexOn ℝ C f`, `StrictConvexOn ℝ C f` and `StrongConvexOn C c f`.
* Monotonicity of a mapping `F` on `C` (Definition B.4.1.3) is spelled out for `F = ∇f`:
  for all `x, x' ∈ C`, `⟪F x - F x', x - x'⟫ ≥ 0` [resp. `> 0` whenever `x ≠ x'`,
  resp. `≥ c ‖x - x'‖²`]. -/
theorem FCA_chap_B_4_1_4 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {Ω C : Set E} (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℝ f Ω) (hC : Convex ℝ C) (hCΩ : C ⊆ Ω) :
    (ConvexOn ℝ C f ↔
      ∀ x ∈ C, ∀ x' ∈ C, 0 ≤ ⟪∇ f x - ∇ f x', x - x'⟫_ℝ) ∧
    (StrictConvexOn ℝ C f ↔
      ∀ x ∈ C, ∀ x' ∈ C, x ≠ x' → 0 < ⟪∇ f x - ∇ f x', x - x'⟫_ℝ) ∧
    (∀ c : ℝ, 0 < c → (StrongConvexOn C c f ↔
      ∀ x ∈ C, ∀ x' ∈ C, c * ‖x - x'‖ ^ 2 ≤ ⟪∇ f x - ∇ f x', x - x'⟫_ℝ)) := by
  sorry
