import ConvexStarLib.Defs

/-!
# `FCA_chap_A_ex_20`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_A_ex_20` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_A_ex_20`, so the main result is `FCA_chap_A_ex_20.FCA_chap_A_ex_20`.
-/

namespace FCA_chap_A_ex_20

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_A_ex_20
  (S : Set E)
  (hS_bounded : Bornology.IsBounded S) :
  sSup {v | ∃ x y, (x ∈ S) ∧ (y ∈ S) ∧ (v = ‖y - x‖)} =
  sSup {v | ∃ x y, (x ∈ convexHull ℝ S) ∧ (y ∈ convexHull ℝ S) ∧ (v = ‖y - x‖)} := by
  -- For a bounded set, the supremum of pairwise distances is its diameter.
  have key : ∀ T : Set E, Bornology.IsBounded T →
      sSup {v | ∃ x y, (x ∈ T) ∧ (y ∈ T) ∧ (v = ‖y - x‖)} = Metric.diam T := by
    intro T hT
    have hbdd : BddAbove {v | ∃ x y, (x ∈ T) ∧ (y ∈ T) ∧ (v = ‖y - x‖)} := by
      refine ⟨Metric.diam T, ?_⟩
      rintro v ⟨x, y, hx, hy, rfl⟩
      rw [← dist_eq_norm]
      exact Metric.dist_le_diam_of_mem hT hy hx
    apply le_antisymm
    · apply Real.sSup_le _ Metric.diam_nonneg
      rintro v ⟨x, y, hx, hy, rfl⟩
      rw [← dist_eq_norm]
      exact Metric.dist_le_diam_of_mem hT hy hx
    · apply Metric.diam_le_of_forall_dist_le
      · apply Real.sSup_nonneg
        rintro v ⟨x, y, hx, hy, rfl⟩
        exact norm_nonneg _
      · intro x hx y hy
        rw [dist_eq_norm]
        exact le_csSup hbdd ⟨y, x, hy, hx, rfl⟩
  -- The convex hull is bounded and has the same diameter.
  rw [key S hS_bounded, key (convexHull ℝ S) (isBounded_convexHull.mpr hS_bounded),
    convexHull_diam]

end FCA_chap_A_ex_20
