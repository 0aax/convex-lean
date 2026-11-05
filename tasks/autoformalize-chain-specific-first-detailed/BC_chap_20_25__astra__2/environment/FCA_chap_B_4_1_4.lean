/-
Hiriart-Urruty and Lemaréchal, Fundamentals of Convex Analysis,
Chapter B, Theorem 4.1.4, printed page 112 (PDF page 122).

Source hypotheses, including the standing assumptions of B.4 (page 110):
* The ambient space is a finite-dimensional real Euclidean space, with its
  inner product and associated norm (Section 0.3).
* C is nonempty and convex, and C ⊆ Ω, where Ω is open.
* f is real-valued and differentiable on Ω.
* The modulus c in the strong case is positive (Definitions B.1.1.1 and B.4.1.3).

The conclusion consists of the following three equivalences:
* f is convex on C iff, for every x, x' ∈ C,
    ⟪∇f(x) - ∇f(x'), x - x'⟫ ≥ 0.
* f is strictly convex on C iff, for every distinct x, x' ∈ C,
    ⟪∇f(x) - ∇f(x'), x - x'⟫ > 0.
* f is strongly convex with modulus c on C iff, for every x, x' ∈ C,
    ⟪∇f(x) - ∇f(x'), x - x'⟫ ≥ c ‖x - x'‖².
  The source's strong convexity convention (B.1.1.2) is
    f(α x + (1 - α) x') ≤ α f(x) + (1 - α) f(x')
                          - (c / 2) α (1 - α) ‖x - x'‖²
  for α ∈ (0, 1); this is Mathlib's `StrongConvexOn C c f`.

The real-valued function below is an arbitrary extension off Ω. The local
`gradOnC` represents the gradient as a set-valued operator with domain C, so
all three monotonicity properties concern C only. Openness of Ω and
differentiability on Ω ensure that `gradient f x` is defined by the actual
derivative at every x ∈ C.
-/

import LeanWorkspace.Defs

theorem FCA_chap_B_4_1_4
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (Ω C : Set E) (f : E → ℝ) (c : ℝ)
    -- Domain and constraint set.
    (hΩ_open : IsOpen Ω)
    (hC_nonempty : C.Nonempty)
    (hC_convex : Convex ℝ C)
    (hC_subset : C ⊆ Ω)
    -- Differentiability on the open neighborhood of C.
    (hf_differentiable : DifferentiableOn ℝ f Ω)
    -- Modulus for the strong equivalence.
    (hc_pos : 0 < c) :
    let gradOnC : E → Set E := fun x => {v | x ∈ C ∧ v = gradient f x}
    (ConvexOn ℝ C f ↔ IsMonotoneOperator gradOnC) ∧
      (StrictConvexOn ℝ C f ↔ IsStrictlyMonotoneOperator gradOnC) ∧
      (StrongConvexOn C c f ↔ IsStronglyMonotoneOperator gradOnC c) := by
  sorry
