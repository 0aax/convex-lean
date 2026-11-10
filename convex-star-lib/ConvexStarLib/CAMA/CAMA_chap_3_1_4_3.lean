import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_1_4_3`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_1_4_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_1_4_3`, so the main result is `CAMA_chap_3_1_4_3.CAMA_chap_3_1_4_3`.
-/

namespace CAMA_chap_3_1_4_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_1_4_3
  (S : Set E) :
  (Bornology.IsBounded S → Bornology.IsBounded (convexHull ℝ S)) ∧
  (IsCompact S → IsCompact (convexHull ℝ S)) := by
  refine ⟨fun h => isBounded_convexHull.mpr h, fun hS => ?_⟩
  set n := Module.finrank ℝ E
  have key : convexHull ℝ S = ⋃ k ∈ Finset.range (n + 2),
      (fun p : (Fin k → ℝ) × (Fin k → E) => ∑ i, p.1 i • p.2 i) ''
        (stdSimplex ℝ (Fin k) ×ˢ Set.univ.pi (fun _ => S)) := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨ι, hι, z, w, hzS, hz, hw0, hw1, hy⟩ := eq_pos_convex_span_of_mem_convexHull hy
      have hcard : Fintype.card ι ≤ n + 1 :=
        hz.card_le_finrank_succ.trans (Nat.succ_le_succ (Submodule.finrank_le _))
      set e := Fintype.equivFin ι
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_image]
      refine ⟨Fintype.card ι, by omega, (w ∘ e.symm, z ∘ e.symm), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · intro i
        exact (hw0 _).le
      · simp only [Function.comp_apply]
        rw [e.symm.sum_comp w]
        exact hw1
      · intro i _
        exact hzS (Set.mem_range_self _)
      · simp only [Function.comp_apply]
        rw [e.symm.sum_comp (fun i => w i • z i)]
        exact hy
    · simp only [Set.iUnion_subset_iff]
      rintro k - _ ⟨⟨w, x⟩, ⟨hw, hx⟩, rfl⟩
      exact (convex_convexHull ℝ S).sum_mem (fun i _ => hw.1 i) hw.2
        (fun i _ => subset_convexHull ℝ S (hx i (Set.mem_univ _)))
  rw [key]
  refine (Finset.range (n + 2)).isCompact_biUnion fun k _ => ?_
  exact ((isCompact_stdSimplex _).prod (isCompact_univ_pi fun _ => hS)).image (by fun_prop)

end CAMA_chap_3_1_4_3
