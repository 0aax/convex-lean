import ConvexStarLib.Defs

/-!
# `FCA_chap_A_ex_11`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_A_ex_11` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_A_ex_11`, so the main result is `FCA_chap_A_ex_11.FCA_chap_A_ex_11`.
-/

namespace FCA_chap_A_ex_11

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_A_ex_11
  (S : Set E) :
  ∀ x ∈ Set.extremePoints ℝ (convexHull ℝ S), x ∈ S := by
  intro x hx
  exact extremePoints_convexHull_subset hx

end FCA_chap_A_ex_11
