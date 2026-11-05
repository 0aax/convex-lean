import LeanWorkspace.Defs

/-!
# Theorem B.4.1.4 (Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*)

**Theorem 4.1.4** (Chapter B, §4.1). Let `f` be a function differentiable on an open set
`Ω ⊂ ℝⁿ`, and let `C` be a convex subset of `Ω`. Then `f` is convex [resp. strictly convex,
resp. strongly convex with modulus `c`] on `C` if and only if its gradient `∇f` is monotone
[resp. strictly monotone, resp. strongly monotone with modulus `c`] on `C`.

We formalize it over an arbitrary real Hilbert space `E` (the book's `ℝⁿ` being a special
case), which is what Mathlib's `gradient` (Riesz representative of the Fréchet derivative)
requires. The notions involved are:

* `ConvexOn ℝ C f`, `StrictConvexOn ℝ C f` : Mathlib's convexity notions (Def. B.1.1.1);
* `StrongConvexOn C c f` : Mathlib's strong convexity with modulus `c`, i.e.
  `f (a • x + b • y) ≤ a * f x + b * f y - a * b * (c / 2 * ‖x - y‖ ^ 2)`, which is exactly
  the book's definition (B.1.1.2);
* `IsMonotoneOn F C`, `IsStrictlyMonotoneOn F C`, `IsStronglyMonotoneOn F C c` (from
  `LeanWorkspace.Defs`, Def. B.4.1.3): `⟪F x - F y, x - y⟫ ≥ 0` for `x, y ∈ C`
  [resp. `> 0` for `x ≠ y`, resp. `≥ c * ‖x - y‖ ^ 2`].

The modulus `c` is positive, as in the book's definitions of strong convexity and strong
monotonicity.
-/

theorem FCA_chap_B_4_1_4
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (Ω C : Set E)
    (hΩ : IsOpen Ω) (hf : DifferentiableOn ℝ f Ω) (hC : Convex ℝ C) (hCΩ : C ⊆ Ω) :
    (ConvexOn ℝ C f ↔ IsMonotoneOn (gradient f) C) ∧
    (StrictConvexOn ℝ C f ↔ IsStrictlyMonotoneOn (gradient f) C) ∧
    (∀ c : ℝ, 0 < c → (StrongConvexOn C c f ↔ IsStronglyMonotoneOn (gradient f) C c)) := by
  sorry
