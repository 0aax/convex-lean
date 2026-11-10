import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_1_2_4`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_1_2_4` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_1_2_4`, so the main result is `CAMA_chap_3_1_2_4.CAMA_chap_3_1_2_4`.
-/

namespace CAMA_chap_3_1_2_4

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem CAMA_chap_3_1_2_4
  (A : AffineMap ℝ E F)
  (C : Set E)
  (D : Set F)
  (hC : Convex ℝ C)
  (hD : Convex ℝ D) :
  Convex ℝ (Set.image A C) ∧
  (Convex ℝ (Set.preimage A D)) := by
  exact ⟨hC.affine_image A, hD.affine_preimage A⟩

end CAMA_chap_3_1_2_4
