import LeanWorkspace.Defs

/-!
# Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*, Theorem B.4.1.4

**Theorem 4.1.4** (Chapter B, §4.1). Let `f` be a function differentiable on an open set
`Ω ⊂ ℝⁿ`, and let `C` be a convex subset of `Ω`. Then `f` is convex [resp. strictly convex,
resp. strongly convex with modulus `c`] on `C` if and only if its gradient `∇ f` is monotone
[resp. strictly monotone, resp. strongly monotone with modulus `c`] on `C`.

## Formalization notes

* The statement is given for a real-valued function on an arbitrary real Hilbert space `E`
  (the setting in which Mathlib's gradient `∇ f = gradient f` is available); `ℝⁿ` is the special
  case `E = EuclideanSpace ℝ (Fin n)`.
* Differentiability is Fréchet differentiability: `DifferentiableOn ℝ f Ω` with `Ω` open, so that
  `∇ f x` is the gradient of `f` at every `x ∈ Ω ⊇ C`.
* Convexity notions are Mathlib's `ConvexOn`, `StrictConvexOn` and `StrongConvexOn`; the latter
  follows the book's convention (B.1.1.2),
  `f (α x + (1 - α) x') ≤ α f x + (1 - α) f x' - ½ c α (1 - α) ‖x - x'‖²`.
* Monotonicity notions are `MonotoneMapOn`, `StrictMonotoneMapOn` and `StrongMonotoneMapOn` from
  `LeanWorkspace.Defs` (Definition B.4.1.3), e.g. strong monotonicity with modulus `c` means
  `⟪∇ f x - ∇ f x', x - x'⟫ ≥ c ‖x - x'‖²` on `C`.
* The book takes the modulus `c > 0`. The equivalence holds for every real `c`
  (`c = 0` being the "convex ⇔ monotone" case), so no positivity assumption is imposed.
-/

open scoped Gradient

theorem FCA_chap_B_4_1_4 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {Ω C : Set E} (hΩ : IsOpen Ω) (hC : Convex ℝ C) (hCΩ : C ⊆ Ω)
    {f : E → ℝ} (hf : DifferentiableOn ℝ f Ω) :
    (ConvexOn ℝ C f ↔ MonotoneMapOn C (∇ f)) ∧
    (StrictConvexOn ℝ C f ↔ StrictMonotoneMapOn C (∇ f)) ∧
    (∀ c : ℝ, StrongConvexOn C c f ↔ StrongMonotoneMapOn C c (∇ f)) := by
  sorry
