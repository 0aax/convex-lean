import ConvexStarLib.Defs

/-!
# `FCA_chap_E_1_3_1_iv`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_1_3_1_iv` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_1_3_1_iv`, so the main result is `FCA_chap_E_1_3_1_iv.FCA_chap_E_1_3_1_iv`.
-/

namespace FCA_chap_E_1_3_1_iv

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_E_1_3_1_iv
  (f : E → EReal)
  (A : E ≃ₗ[ℝ] E)
  (hf_nondegenerate : IsNondegenerate f) :
  let g := fun x => f (A x)
  let A_adjoint_inverse : (E →ₗ[ℝ] E) :=
                          (A.symm : E →ₗ[ℝ] E).adjoint
  ∀ s, conjugate g s = conjugate f (A_adjoint_inverse s) := by
  intro g A_adjoint_inverse s
  unfold conjugate
  congr 1
  ext z
  simp only [Set.image_univ, Set.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨A x, ?_⟩
    simp only [A_adjoint_inverse, g]
    rw [LinearMap.adjoint_inner_left]
    simp
  · rintro ⟨y, rfl⟩
    refine ⟨A.symm y, ?_⟩
    simp only [A_adjoint_inverse, g]
    rw [LinearMap.adjoint_inner_left]
    simp

end FCA_chap_E_1_3_1_iv
