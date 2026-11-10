import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_2_3_7`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_2_3_7` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_2_3_7`, so the main result is `CAMA_chap_3_2_3_7.CAMA_chap_3_2_3_7`.
-/

namespace CAMA_chap_3_2_3_7

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

set_option linter.unusedVariables false in
theorem CAMA_chap_3_2_3_7
  (C : Set E)
  (F : Set E)
  (hF : IsFaceOf F C)
  (hC₀ : Set.Nonempty C)
  (hC₁ : Convex ℝ C) :
  ∀ (x : E), x ∈ (Set.extremePoints ℝ F) →
  x ∈ (Set.extremePoints ℝ C) := by
  intro x hx
  exact hF.2.2.extremePoints_subset_extremePoints hx

end CAMA_chap_3_2_3_7
