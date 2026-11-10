import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_1_3_3`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_1_3_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_1_3_3`, so the main result is `CAMA_chap_3_1_3_3.CAMA_chap_3_1_3_3`.
-/

namespace CAMA_chap_3_1_3_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


theorem CAMA_chap_3_1_3_3 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n))) :
  (Convex ℝ C) ↔ (∀ z ∈ (conv C), z ∈ C) := by
  constructor
  · intro hC z hz
    simp only [conv, Set.mem_iUnion, Set.mem_setOf_eq] at hz
    obtain ⟨k, hk, x, hx, a, ⟨ha0, ha1⟩, rfl⟩ := hz
    exact hC.sum_mem (fun i _ => ha0 i) ha1 (fun i _ => hx i)
  · intro h x hx y hy a b ha hb hab
    apply h
    simp only [conv, Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨2, by norm_num, ![x, y], ?_, WithLp.toLp 2 ![a, b], ⟨?_, ?_⟩, ?_⟩
    · intro i; fin_cases i <;> simp [hx, hy]
    · intro i; fin_cases i <;> simp [ha, hb]
    · simp [Fin.sum_univ_two, hab]
    · simp [Fin.sum_univ_two]

end CAMA_chap_3_1_3_3
