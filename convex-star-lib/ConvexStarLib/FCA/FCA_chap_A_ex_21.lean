import ConvexStarLib.Defs

/-!
# `FCA_chap_A_ex_21`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_A_ex_21` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_A_ex_21`, so the main result is `FCA_chap_A_ex_21.FCA_chap_A_ex_21`.
-/

namespace FCA_chap_A_ex_21

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_A_ex_21
  (S₁ S₂ : Set E) :
  convexHull ℝ (S₁ ∩ S₂) ⊆ convexHull ℝ S₁ ∩ convexHull ℝ S₂ ∧
  convexHull ℝ (setAdd S₁ S₂) = setAdd (convexHull ℝ S₁) (convexHull ℝ S₂) ∧
  convexHull ℝ (S₁ ∪ S₂) = convexHull ℝ (convexHull ℝ S₁ ∪ convexHull ℝ S₂) := by
  have hadd : ∀ C K : Set E, setAdd C K = C + K := by
    intro C K
    ext v
    simp only [setAdd, Set.mem_setOf_eq, Set.mem_add]
    constructor
    · rintro ⟨c, hc, k, hk, rfl⟩
      exact ⟨c, hc, k, hk, rfl⟩
    · rintro ⟨c, hc, k, hk, rfl⟩
      exact ⟨c, hc, k, hk, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · exact Set.subset_inter (convexHull_mono Set.inter_subset_left)
      (convexHull_mono Set.inter_subset_right)
  · rw [hadd, hadd, convexHull_add]
  · rw [convexHull_convexHull_union_left, convexHull_convexHull_union_right]

end FCA_chap_A_ex_21
