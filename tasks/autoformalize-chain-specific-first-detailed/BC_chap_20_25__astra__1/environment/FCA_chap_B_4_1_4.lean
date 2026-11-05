/-
Hiriart-Urruty & Lemaréchal, Fundamentals of Convex Analysis,
Chapter B, Section 4.1, Theorem 4.1.4 (PDF page 122, printed page 112).

Source hypotheses, including the standing assumptions of Section B.4:
* The ambient space is a finite-dimensional real Euclidean space.
* C is nonempty and convex, Ω is open, and C ⊆ Ω.
* f is real-valued and differentiable on Ω.
* The strong convexity and strong monotonicity modulus is c > 0
  (Definitions B.1.1.1 and B.4.1.3).

The conclusion consists of three equivalences on C:
* f is convex iff ⟨∇f(x) - ∇f(x'), x - x'⟩ ≥ 0 for every x, x' ∈ C.
* f is strictly convex iff this inequality is strict whenever x ≠ x'.
* f is strongly convex with modulus c iff
    ⟨∇f(x) - ∇f(x'), x - x'⟩ ≥ c ‖x - x'‖² for every x, x' ∈ C.
  Strong convexity uses the subtraction (c/2) α (1-α) ‖x-x'‖² in (1.1.2),
  exactly the modulus convention of Mathlib's StrongConvexOn.

The gradient restricted to C is viewed as a set-valued operator, with singleton
values on C and empty values elsewhere, so the shared monotonicity definitions
quantify only over points of C.
-/

import LeanWorkspace.Defs

theorem FCA_chap_B_4_1_4
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (Ω C : Set E) (c : ℝ)
    -- Constraint set and open neighborhood.
    (hC_nonempty : C.Nonempty) (hC_convex : Convex ℝ C)
    (hΩ_open : IsOpen Ω) (hC_subset : C ⊆ Ω)
    -- Function.
    (hf_differentiable : DifferentiableOn ℝ f Ω)
    -- Modulus.
    (hc_pos : 0 < c) :
    let gradientOnC : E → Set E := fun x => {v | x ∈ C ∧ v = gradient f x}
    (ConvexOn ℝ C f ↔ IsMonotoneOperator gradientOnC) ∧
      (StrictConvexOn ℝ C f ↔ IsStrictlyMonotoneOperator gradientOnC) ∧
      (StrongConvexOn C c f ↔ IsStronglyMonotoneOperator gradientOnC c) := by
  sorry
