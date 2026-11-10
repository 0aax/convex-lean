import ConvexStarLib.Defs

/-!
# `BC_chap_7_12`

Source: Bauschke & Combettes, Convex Analysis and Monotone Operator Theory in Hilbert Spaces.

Statement from the `convex-eval-v28-2h/BC_chap_7_12` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace BC_chap_7_12`, so the main result is `BC_chap_7_12.BC_chap_7_12`.
-/

namespace BC_chap_7_12

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem BC_chap_7_12
  (C : Set E)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C) :
  C = ⋂ (u : E) (η : ℝ) (_ : C ⊆ hyperplaneHalfspace u η), hyperplaneHalfspace u η := by
  apply Set.Subset.antisymm
  · intro x hx
    simp only [Set.mem_iInter]
    intro u η h
    exact h hx
  · intro x hx
    by_contra hxC
    obtain ⟨f, η, hf, hfx⟩ := geometric_hahn_banach_closed_point hC_convex hC_closed hxC
    have hsub : C ⊆ hyperplaneHalfspace ((InnerProductSpace.toDual ℝ E).symm f) η := by
      intro a ha
      show inner ℝ ((InnerProductSpace.toDual ℝ E).symm f) a ≤ η
      rw [InnerProductSpace.toDual_symm_apply]
      exact (hf a ha).le
    have hmem := Set.mem_iInter.mp (Set.mem_iInter.mp
      (Set.mem_iInter.mp hx ((InnerProductSpace.toDual ℝ E).symm f)) η) hsub
    have h2 : inner ℝ ((InnerProductSpace.toDual ℝ E).symm f) x ≤ η := hmem
    rw [InnerProductSpace.toDual_symm_apply] at h2
    linarith

end BC_chap_7_12
