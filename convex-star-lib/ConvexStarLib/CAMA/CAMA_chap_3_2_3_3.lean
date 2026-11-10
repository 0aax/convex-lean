import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_2_3_3`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_2_3_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_2_3_3`, so the main result is `CAMA_chap_3_2_3_3.CAMA_chap_3_2_3_3`.
-/

namespace CAMA_chap_3_2_3_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem CAMA_chap_3_2_3_3
  (C : Set E)
  (hC₀ : Set.Nonempty C)
  (hC₁ : Convex ℝ C)
  (hC₂ : IsCompact C) :
  Set.Nonempty (Set.extremePoints ℝ C) := by
  exact hC₂.extremePoints_nonempty hC₀

end CAMA_chap_3_2_3_3
