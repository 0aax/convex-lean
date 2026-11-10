import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_1_3_4`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_1_3_4` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_1_3_4`, so the main result is `CAMA_chap_3_1_3_4.CAMA_chap_3_1_3_4`.
-/

namespace CAMA_chap_3_1_3_4

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


set_option maxHeartbeats 1000000 in
theorem CAMA_chap_3_1_3_4 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n))) :
  (convexHull ℝ C) = (conv C) := by
  ext v
  rw [mem_convexHull_iff_exists_fintype]
  simp only [conv, Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ι, _, w, z, hw0, hw1, hz, rfl⟩
    have hne : Nonempty ι := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp at hw1
    let e := Fintype.equivFin ι
    refine ⟨Fintype.card ι, Fintype.card_pos, fun j => z (e.symm j), fun j => hz _,
      WithLp.toLp 2 (fun j => w (e.symm j)), ⟨fun j => hw0 _, ?_⟩, ?_⟩
    · rw [Equiv.sum_comp e.symm w]
      exact hw1
    · exact (Equiv.sum_comp e.symm (fun i => w i • z i)).symm
  · rintro ⟨k, hk, x, hx, a, ⟨ha0, ha1⟩, rfl⟩
    exact ⟨Fin k, inferInstance, fun i => a i, x, ha0, ha1, hx, rfl⟩

end CAMA_chap_3_1_3_4
