import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_1_2_7`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_1_2_7` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_1_2_7`, so the main result is `CAMA_chap_3_1_2_7.CAMA_chap_3_1_2_7`.
-/

namespace CAMA_chap_3_1_2_7

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_1_2_7
  (C : Set E)
  (hC : Convex ℝ C) :
  Convex ℝ (interior C) ∧ Convex ℝ (closure C) := by
  exact ⟨hC.interior, hC.closure⟩

end CAMA_chap_3_1_2_7
