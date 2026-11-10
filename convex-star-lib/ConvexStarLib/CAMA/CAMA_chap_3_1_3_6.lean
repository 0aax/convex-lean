import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_1_3_6`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_1_3_6` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_1_3_6`, so the main result is `CAMA_chap_3_1_3_6.CAMA_chap_3_1_3_6`.
-/

namespace CAMA_chap_3_1_3_6

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


set_option maxHeartbeats 1000000 in
theorem CAMA_chap_3_1_3_6 {n : ℕ}
  (S : Set (EuclideanSpace ℝ (Fin n))) :
  ∀ x ∈ (convexHull ℝ S),
  ∃ (v : Fin (n + 1) → EuclideanSpace ℝ (Fin n)) (a : EuclideanSpace ℝ (Fin (n + 1))),
  (∀ i, v i ∈ S) ∧ (a.ofLp ∈ probSimplex (n + 1)) ∧ (x = ∑ i, a i • v i) := by
  classical
  intro x hx
  obtain ⟨s₀, hs₀⟩ : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, convexHull_empty] at hx
    exact hx
  obtain ⟨ι, _, z, w, hzS, hai, hwpos, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hx
  have hcard : Fintype.card ι ≤ n + 1 := by
    have h1 := hai.card_le_finrank_succ
    have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤ n := by
      have := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
      simpa [finrank_euclideanSpace] using this
    omega
  let f : ι ↪ Fin (n + 1) := (Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb hcard)
  let v : Fin (n + 1) → EuclideanSpace ℝ (Fin n) := Function.extend f z (fun _ => s₀)
  let a' : Fin (n + 1) → ℝ := Function.extend f w 0
  refine ⟨v, WithLp.toLp 2 a', ?_, ?_, ?_⟩
  · intro j
    by_cases h : ∃ i, f i = j
    · obtain ⟨i, rfl⟩ := h
      simp only [v, f.injective.extend_apply]
      exact hzS ⟨i, rfl⟩
    · simp only [v, Function.extend_apply' _ _ _ h]
      exact hs₀
  · refine ⟨fun j => ?_, ?_⟩
    · by_cases h : ∃ i, f i = j
      · obtain ⟨i, rfl⟩ := h
        simp only [a', f.injective.extend_apply]
        exact (hwpos i).le
      · simp [a', Function.extend_apply' _ _ _ h]
    · rw [← hw1]
      symm
      apply Fintype.sum_of_injective f f.injective
      · intro j hj
        simp [a', Function.extend_apply' _ _ _ hj]
      · intro i
        simp [a', f.injective.extend_apply]
  · rw [← hwz]
    apply Fintype.sum_of_injective f f.injective
    · intro j hj
      simp [a', Function.extend_apply' _ _ _ hj]
    · intro i
      simp [a', v, f.injective.extend_apply]

end CAMA_chap_3_1_3_6
