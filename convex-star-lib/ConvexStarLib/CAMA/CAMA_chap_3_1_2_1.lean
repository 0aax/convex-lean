import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_1_2_1`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_1_2_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_1_2_1`, so the main result is `CAMA_chap_3_1_2_1.CAMA_chap_3_1_2_1`.
-/

namespace CAMA_chap_3_1_2_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_1_2_1 {ι : Type*}
  (J : Set ι)
  (C : ι → Set E)
  (hC : ∀ i, Convex ℝ (C i)) :
  Convex ℝ (⋂ (j : ι) (_ : j ∈ J), (C j)) := by
  exact convex_iInter₂ (fun i _ => hC i)

end CAMA_chap_3_1_2_1
