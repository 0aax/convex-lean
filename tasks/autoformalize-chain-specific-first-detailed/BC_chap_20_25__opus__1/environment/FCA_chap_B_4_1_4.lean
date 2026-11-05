import LeanWorkspace.Defs

/-!
# Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*, Theorem B.4.1.4 (p. 112)

Source statement: Let `f` be a function differentiable on an open set `Ω ⊂ ℝⁿ`, and let `C` be a
convex subset of `Ω`. Then `f` is convex [resp. strictly convex, resp. strongly convex with
modulus `c`] on `C` if and only if its gradient `∇f` is monotone [resp. strictly monotone,
resp. strongly monotone with modulus `c`] on `C`.

Hypotheses, including the standing ones:
* `Ω ⊂ ℝⁿ` is open and `f` is (finite-valued and) differentiable on `Ω` (§4.1);
* `C` is convex and `C ⊂ Ω`; `C` is nonempty (standing assumption of §4, and Def. 1.1.1);
* `c > 0`, the modulus of strong convexity in (1.1.2) and of strong monotonicity in Def. 4.1.3.

Definitions used by the source:
* convex on `C` (Def. 1.1.1): `f(αx + (1-α)x') ≤ αf(x) + (1-α)f(x')` for `x, x' ∈ C`,
  `α ∈ ]0,1[` — Mathlib's `ConvexOn ℝ C f`;
* strictly convex on `C`: the same inequality, strict when `x ≠ x'` — `StrictConvexOn ℝ C f`;
* strongly convex on `C` with modulus `c` (1.1.2):
  `f(αx + (1-α)x') ≤ αf(x) + (1-α)f(x') - ½ c α(1-α)‖x - x'‖²` — `StrongConvexOn C c f`;
* `F : C → ℝⁿ` monotone [strictly, strongly with modulus `c`] on `C` (Def. 4.1.3): for all
  `x, x' ∈ C`, `⟨F(x) - F(x'), x - x'⟩ ≥ 0` [`> 0` when `x ≠ x'`, `≥ c‖x - x'‖²`] — the shared
  multifunction notions `IsMonotoneOperator`, `IsStrictlyMonotoneOperator` and
  `IsStronglyMonotoneOperator`, applied to `∇f` restricted to `C`, i.e. the multifunction
  `x ↦ {∇f(x)}` for `x ∈ C` and `x ↦ ∅` otherwise.

Conclusion: the three equivalences convex ↔ monotone, strictly convex ↔ strictly monotone,
strongly convex with modulus `c` ↔ strongly monotone with modulus `c`.

`ℝⁿ` is an abstract finite-dimensional real inner-product space `E`, and `∇f` is Mathlib's
`gradient f`; it is the true gradient at every point of `C`, because `f` is differentiable on the
open set `Ω ⊇ C`.
-/

open scoped InnerProductSpace

theorem FCA_chap_B_4_1_4
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℝ) (Ω C : Set E) (c : ℝ)
    -- the open set `Ω` on which `f` is differentiable
    (hΩ_open : IsOpen Ω) (hf_diff : DifferentiableOn ℝ f Ω)
    -- the set `C`: nonempty, convex, contained in `Ω`
    (hC_nonempty : C.Nonempty) (hC_convex : Convex ℝ C) (hC_sub : C ⊆ Ω)
    -- the modulus of strong convexity / strong monotonicity
    (hc : 0 < c) :
    (ConvexOn ℝ C f ↔
      IsMonotoneOperator (fun x => {v | x ∈ C ∧ v = gradient f x})) ∧
    (StrictConvexOn ℝ C f ↔
      IsStrictlyMonotoneOperator (fun x => {v | x ∈ C ∧ v = gradient f x})) ∧
    (StrongConvexOn C c f ↔
      IsStronglyMonotoneOperator (fun x => {v | x ∈ C ∧ v = gradient f x}) c) := by
  sorry
