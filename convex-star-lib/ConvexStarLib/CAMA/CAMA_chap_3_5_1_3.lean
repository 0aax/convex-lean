import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_5_1_3`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_5_1_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_5_1_3`, so the main result is `CAMA_chap_3_5_1_3.CAMA_chap_3_5_1_3`.
-/

namespace CAMA_chap_3_5_1_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_5_1_3
  (S : Set E)
  (x : E) :
  IsClosed (posTangentConeAt S x) := by
  rw [posTangentConeAt, tangentConeAt_def]
  exact isClosed_setOf_clusterPt

end CAMA_chap_3_5_1_3
