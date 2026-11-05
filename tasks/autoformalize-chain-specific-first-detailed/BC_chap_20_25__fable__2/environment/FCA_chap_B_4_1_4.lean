import LeanWorkspace.Defs

/-!
# Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*, Theorem B.4.1.4

Source (Chapter B, §4.1, p. 112; PDF p. 122):

> **Theorem 4.1.4** Let `f` be a function differentiable on an open set `Ω ⊂ ℝⁿ`, and let
> `C` be a convex subset of `Ω`. Then, `f` is convex [resp. strictly convex, resp. strongly
> convex with modulus `c`] on `C` if and only if its gradient `∇f` is monotone [resp.
> strictly monotone, resp. strongly monotone with modulus `c`] on `C`.

## Hypotheses (stated and standing)
* Standing assumption of Chapter B §4: `C ⊂ ℝⁿ` is nonempty and convex, and `f` is
  defined (finite) on `C`; §4.1 assumes `C` is contained in an open set `Ω` on which `f`
  is differentiable.
* Stated: `Ω` open, `f` differentiable on `Ω`, `C ⊆ Ω` convex.
* The modulus `c` of strong convexity (Def. 1.1.1, (1.1.2)) and of strong monotonicity
  (Def. 4.1.3) is `c > 0`.

## Definitions used by the source
* Convex / strictly convex on `C` (Def. 1.1.1, (1.1.1)): Mathlib's `ConvexOn ℝ C f`,
  `StrictConvexOn ℝ C f`.
* Strongly convex on `C` with modulus `c` ((1.1.2)):
  `f(αx + (1-α)x') ≤ αf(x) + (1-α)f(x') - ½ c α(1-α) ‖x - x'‖²`; Mathlib's
  `StrongConvexOn C c f` uses the same `c/2` convention.
* Monotone / strictly monotone / strongly monotone with modulus `c > 0` on `C`
  (Def. 4.1.3), for `F : C → ℝⁿ`: for all `x, x' ∈ C`, `⟨F(x) - F(x'), x - x'⟩ ≥ 0`
  [resp. `> 0` whenever `x ≠ x'`, resp. `≥ c ‖x - x'‖²`]. These are the set-valued notions
  `IsMonotoneMultifun`, `IsStrictlyMonotoneMultifun`, `IsStronglyMonotoneMultifun` of
  `Defs.lean` (shared with Rockafellar–Wets Def. 12.1 / 12.53 and Bauschke–Combettes
  Def. 20.1 / 22.1) applied to `(gradient f).toMultifunOn C`, the gradient map restricted
  to `C` (values `∅` outside `C`).
* `∇f`: Mathlib's `gradient f` (finite dimension gives the completeness it needs);
  on the open set `Ω` where `f` is differentiable it is the true gradient.

## Conclusion
The three equivalences, with the source's constant `c` (coefficient `½c` on the convexity
side, `c` on the monotonicity side).

Ambient space: an abstract finite-dimensional real inner-product space (no coordinates
are used).
-/

theorem FCA_chap_B_4_1_4
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    -- data: the function, the open set and the convex set
    (f : E → ℝ) (Ω C : Set E)
    -- the modulus of strong convexity / strong monotonicity
    (c : ℝ)
    -- the set `C`: nonempty, convex, contained in `Ω`
    (hC_nonempty : C.Nonempty) (hC_convex : Convex ℝ C) (hC_sub : C ⊆ Ω)
    -- the function: differentiable on the open set `Ω`
    (hΩ_open : IsOpen Ω) (hf_diff : DifferentiableOn ℝ f Ω)
    -- the modulus is positive
    (hc_pos : 0 < c) :
    (ConvexOn ℝ C f ↔ IsMonotoneMultifun ((gradient f).toMultifunOn C)) ∧
    (StrictConvexOn ℝ C f ↔ IsStrictlyMonotoneMultifun ((gradient f).toMultifunOn C)) ∧
    (StrongConvexOn C c f ↔ IsStronglyMonotoneMultifun ((gradient f).toMultifunOn C) c) := by
  sorry
