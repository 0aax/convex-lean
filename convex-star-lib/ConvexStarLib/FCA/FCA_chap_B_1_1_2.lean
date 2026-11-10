import ConvexStarLib.Defs

/-!
# `FCA_chap_B_1_1_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_1_1_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_1_1_2`, so the main result is `FCA_chap_B_1_1_2.FCA_chap_B_1_1_2`.
-/

namespace FCA_chap_B_1_1_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_B_1_1_2
  (c : ℝ)
  (C : Set E)
  (f : E → ℝ)
  (hC_nonempty : Set.Nonempty C)
  (hC_convex : Convex ℝ C) :
  StrongConvexOn C c f ↔ ConvexOn ℝ C (fun x => f x - (c/2) * ‖x‖^2) := by
  exact strongConvexOn_iff_convex

end FCA_chap_B_1_1_2
