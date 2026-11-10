import ConvexStarLib.Defs

/-!
# `FCA_chap_C_3_1_4`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_3_1_4` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_3_1_4`, so the main result is `FCA_chap_C_3_1_4.FCA_chap_C_3_1_4`.
-/

namespace FCA_chap_C_3_1_4

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_C_3_1_4
  (C : Set E)
  (x d : E)
  (hC_nonempty : C.Nonempty)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C)
  (hx : x ∈ C)
  (hd : d ≠ 0) :
  x ∈ exposedFace C d ↔ d ∈ convexNormalCone x C := by
  simp only [exposedFace, argmax, convexNormalCone, Set.mem_setOf_eq, inner_sub_right, sub_nonpos]
  exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩

end FCA_chap_C_3_1_4
