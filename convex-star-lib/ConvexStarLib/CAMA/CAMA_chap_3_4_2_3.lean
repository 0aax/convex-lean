import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_4_2_3`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_4_2_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_4_2_3`, so the main result is `CAMA_chap_3_4_2_3.CAMA_chap_3_4_2_3`.
-/

namespace CAMA_chap_3_4_2_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


theorem CAMA_chap_3_4_2_3 {n : ℕ}
    (S C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : C = convexHull ℝ S) :
    ∀ x ∈ C ∩ frontier C,
      ∃ (v : Fin n → EuclideanSpace ℝ (Fin n)) (a : EuclideanSpace ℝ (Fin n)),
        (∀ i, v i ∈ S) ∧ (a.ofLp ∈ probSimplex n) ∧ x = ∑ i, a i • v i := by
  intro x ⟨hxC, hxF⟩
  have hxI : x ∉ interior C := hxF.2
  rw [hC] at hxC hxI
  obtain ⟨ι, _, z, w, hzS, hzind, hwpos, hwsum, hx⟩ := eq_pos_convex_span_of_mem_convexHull hxC
  have hcard : Fintype.card ι ≤ n := by
    have h1 := hzind.card_le_finrank_succ
    have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤ n := by
      calc _ ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := Submodule.finrank_le _
        _ = n := finrank_euclideanSpace_fin
    by_contra hlt
    push_neg at hlt
    have hc : Fintype.card ι = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) + 1 := by
      rw [finrank_euclideanSpace_fin]; omega
    have htot := hzind.affineSpan_eq_top_iff_card_eq_finrank_add_one.2 hc
    let b : AffineBasis ι ℝ (EuclideanSpace ℝ (Fin n)) := ⟨z, hzind, htot⟩
    apply hxI
    have hsub : interior (convexHull ℝ (Set.range b)) ⊆ interior (convexHull ℝ S) :=
      interior_mono (convexHull_mono hzS)
    apply hsub
    rw [b.interior_convexHull]
    intro i
    have : x = Finset.univ.affineCombination ℝ b w := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hwsum]
      exact hx.symm
    rw [this, b.coord_apply_combination_of_mem (Finset.mem_univ i) hwsum]
    exact hwpos i
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hwsum
  obtain ⟨i0⟩ := hne
  obtain ⟨emb⟩ : Nonempty (ι ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hcard)
  classical
  have hw0 : ∀ j ∉ Set.range emb, Function.extend emb w 0 j = 0 := by
    intro j hj
    rw [Function.extend_apply' _ _ _ hj]
    rfl
  refine ⟨Function.extend emb z (fun _ => z i0), WithLp.toLp 2 (Function.extend emb w 0),
    ?_, ?_, ?_⟩
  · intro j
    by_cases hj : ∃ i, emb i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [emb.injective.extend_apply]
      exact hzS ⟨i, rfl⟩
    · rw [Function.extend_apply' _ _ _ hj]
      exact hzS ⟨i0, rfl⟩
  · constructor
    · intro j
      show 0 ≤ Function.extend emb w 0 j
      by_cases hj : ∃ i, emb i = j
      · obtain ⟨i, rfl⟩ := hj
        rw [emb.injective.extend_apply]
        exact (hwpos i).le
      · rw [hw0 j hj]
    · show ∑ j, Function.extend emb w 0 j = 1
      rw [← hwsum]
      symm
      apply Fintype.sum_of_injective emb emb.injective
      · exact hw0
      · intro i
        rw [emb.injective.extend_apply]
  · rw [← hx]
    apply Fintype.sum_of_injective emb emb.injective
    · intro j hj
      show Function.extend emb w 0 j • _ = 0
      rw [hw0 j hj, zero_smul]
    · intro i
      show _ = Function.extend emb w 0 (emb i) • Function.extend emb z (fun _ => z i0) (emb i)
      rw [emb.injective.extend_apply, emb.injective.extend_apply]

end CAMA_chap_3_4_2_3
