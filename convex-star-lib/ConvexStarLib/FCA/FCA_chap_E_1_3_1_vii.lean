import ConvexStarLib.Defs

/-!
# `FCA_chap_E_1_3_1_vii`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_1_3_1_vii` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_1_3_1_vii`, so the main result is `FCA_chap_E_1_3_1_vii.FCA_chap_E_1_3_1_vii`.
-/

namespace FCA_chap_E_1_3_1_vii

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_E_1_3_1_vii
  (f₁ : E → EReal) (f₂ : E → EReal)
  (hf_nondegenerate : IsNondegenerate f₁ ∧ IsNondegenerate f₂)
  (hf₁_minorizes : Minorizes f₁ f₂) :
  Minorizes (conjugate f₂) (conjugate f₁) := by
  intro v
  unfold conjugate
  apply sSup_le
  rintro _ ⟨x, -, rfl⟩
  refine le_sSup_of_le (Set.mem_image_of_mem _ (Set.mem_univ x)) ?_
  exact EReal.sub_le_sub le_rfl (hf₁_minorizes x)

end FCA_chap_E_1_3_1_vii
