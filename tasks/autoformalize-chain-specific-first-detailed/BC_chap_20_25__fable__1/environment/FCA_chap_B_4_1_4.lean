import LeanWorkspace.Defs

/-!
# Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*, Theorem B.4.1.4

Chapter B (Convex Functions), §4 (First- and Second-Order Differentiation), §4.1
(Differentiable Convex Functions), Theorem 4.1.4; PDF page 122, book page 112.

## Source statement
"Let `f` be a function differentiable on an open set `Ω ⊂ ℝⁿ`, and let `C` be a convex subset
of `Ω`.  Then, `f` is convex [resp. strictly convex, resp. strongly convex with modulus `c`]
on `C` if and only if its gradient `∇f` is monotone [resp. strictly monotone, resp. strongly
monotone with modulus `c`] on `C`."

## Hypotheses, including the standing assumptions
* Ambient space: `ℝⁿ` with its scalar product `⟨·,·⟩` and the associated norm `‖·‖`
  (Chapter A, §0); here an abstract finite-dimensional real inner-product space `E`.
* Standing assumptions of §4: `C ⊂ ℝⁿ` is nonempty and convex, and `f` is finite on `C`
  (`f(x) < +∞` for all `x ∈ C`).  §4.1 adds that `C` is contained in an open set `Ω` on which
  `f` is differentiable; being differentiable on `Ω ⊇ C`, `f` is real-valued where the
  statement looks at it, so `f : E → ℝ`.
* Theorem 4.1.4: `Ω` open, `f` differentiable on `Ω`, `C` convex, `C ⊆ Ω`.
* The modulus `c` of strong convexity (Definition 1.1.1, (1.1.2)) and of strong monotonicity
  (Definition 4.1.3) is a positive number: `c > 0`.

## Definitions of the source
* Convex, strictly convex, strongly convex with modulus `c` on `C` (Definition B.1.1.1):
  `f(αx + (1-α)x') ≤ αf(x) + (1-α)f(x')` for `x, x' ∈ C`, `α ∈ ]0,1[` [resp. strict
  inequality when `x ≠ x'`, resp. with `- (c/2) α(1-α) ‖x - x'‖²` on the right-hand side].
  These are Mathlib's `ConvexOn ℝ C f`, `StrictConvexOn ℝ C f` and `StrongConvexOn C c f`
  (the last one is `UniformConvexOn` with modulus `r ↦ c/2 · r²`, i.e. exactly (1.1.2)).
* Monotone, strictly monotone, strongly monotone with modulus `c > 0` mapping `F : C → ℝⁿ`
  on `C` (Definition B.4.1.3): for all `x, x' ∈ C`, `⟨F(x) - F(x'), x - x'⟩ ≥ 0`
  [resp. `> 0` whenever `x ≠ x'`, resp. `≥ c ‖x - x'‖²`].  The project states monotonicity
  for multifunctions `T : E → Set E` on their graph (`IsMonotoneOperator`,
  `IsStrictlyMonotoneOperator`, `IsStronglyMonotoneOperator`); the single-valued mapping
  `∇f` on `C` is the multifunction `toMultifunOn (gradient f) C`, whose value is `{∇f x}` on
  `C` and `∅` outside `C`, so the graph conditions are exactly those of Definition 4.1.3.

## Conclusion
Three equivalences, with the same `C` and the same modulus `c` on both sides:
`f` convex on `C` ↔ `∇f` monotone on `C`; `f` strictly convex on `C` ↔ `∇f` strictly
monotone on `C`; `f` strongly convex with modulus `c` on `C` ↔ `∇f` strongly monotone with
modulus `c` on `C`.

`gradient f x` is only evaluated at points of `C ⊆ Ω`, where `f` is differentiable.
-/

open scoped InnerProductSpace

theorem FCA_chap_B_4_1_4
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℝ) (Ω C : Set E) (c : ℝ)
    -- the function: differentiable on the open set Ω
    (hΩ_open : IsOpen Ω) (hf_diff : DifferentiableOn ℝ f Ω)
    -- the set: C is a nonempty convex subset of Ω
    (hC_nonempty : C.Nonempty) (hC_convex : Convex ℝ C) (hC_sub : C ⊆ Ω)
    -- the modulus of strong convexity / strong monotonicity
    (hc_pos : 0 < c) :
    (ConvexOn ℝ C f ↔ IsMonotoneOperator (toMultifunOn (gradient f) C)) ∧
    (StrictConvexOn ℝ C f ↔ IsStrictlyMonotoneOperator (toMultifunOn (gradient f) C)) ∧
    (StrongConvexOn C c f ↔ IsStronglyMonotoneOperator (toMultifunOn (gradient f) C) c) := by
  sorry
