import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_4_3_3`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_4_3_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_4_3_3`, so the main result is `CAMA_chap_3_4_3_3.CAMA_chap_3_4_3_3`.
-/

namespace CAMA_chap_3_4_3_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_4_3_3 {m n : ℕ}
  (s : Fin m → EuclideanSpace ℝ (Fin n)) :
  IsClosed (cone s) := by
  classical
  -- conversion between sums over `Fin m` and over a finset `J` (as a type)
  have conv : ∀ (J : Finset (Fin m)) (α : Fin m → ℝ), (∀ i ∉ J, α i = 0) →
      ∑ i, α i • s i = ∑ i : J, α i • s i := by
    intro J α hα
    rw [Finset.sum_coe_sort J (fun i => α i • s i)]
    exact (Finset.sum_subset (Finset.subset_univ J) (fun i _ hi => by simp [hα i hi])).symm
  let C : Finset (Fin m) → Set (EuclideanSpace ℝ (Fin n)) := fun J =>
    {v | ∃ α : Fin m → ℝ, (∀ i, 0 ≤ α i) ∧ (∀ i ∉ J, α i = 0) ∧ v = ∑ i, α i • s i}
  have hC : ∀ J, IsClosed (C J) := by
    intro J
    induction J using Finset.strongInduction with
    | H J ih =>
      by_cases hli : LinearIndependent ℝ (fun i : J => s i)
      · -- linearly independent case: image of the orthant under a closed embedding
        let f : (J → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
          Fintype.linearCombination ℝ (fun i : J => s i)
        have hf : Function.Injective f := hli.fintypeLinearCombination_injective
        have hP : IsClosed {γ : J → ℝ | ∀ i, 0 ≤ γ i} := by
          simp only [Set.setOf_forall]
          exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
        have hCJ : C J = f '' {γ : J → ℝ | ∀ i, 0 ≤ γ i} := by
          ext v
          constructor
          · rintro ⟨α, hα0, hαJ, rfl⟩
            refine ⟨fun i => α i, fun i => hα0 i, ?_⟩
            rw [conv J α hαJ]
            simp [f, Fintype.linearCombination_apply]
          · rintro ⟨γ, hγ, rfl⟩
            refine ⟨fun i => if h : i ∈ J then γ ⟨i, h⟩ else 0, ?_, ?_, ?_⟩
            · intro i
              by_cases h : i ∈ J
              · simp only [h, dif_pos]; exact hγ _
              · simp [h]
            · intro i hi
              simp [hi]
            · rw [conv J _ (fun i hi => by simp [hi])]
              simp [f, Fintype.linearCombination_apply]
        rw [hCJ]
        exact (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hf)).isClosedMap _ hP
      · -- dependent case: reduce to smaller index sets
        rw [Fintype.not_linearIndependent_iff] at hli
        obtain ⟨g, hg, i₀, hi₀⟩ := hli
        have hc : ∃ c : Fin m → ℝ, (∀ i ∉ J, c i = 0) ∧ ∑ i, c i • s i = 0 ∧ ∃ j, 0 < c j := by
          let c₀ : Fin m → ℝ := fun i => if h : i ∈ J then g ⟨i, h⟩ else 0
          have hc₀J : ∀ i ∉ J, c₀ i = 0 := fun i hi => dif_neg hi
          have hc₀s : ∑ i, c₀ i • s i = 0 := by
            rw [conv J c₀ hc₀J, ← hg]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            simp [c₀, i.2]
          have hc₀i : c₀ i₀ ≠ 0 := by simp [c₀, i₀.2, hi₀]
          rcases lt_or_gt_of_ne hc₀i with h | h
          · refine ⟨-c₀, fun i hi => by simp [hc₀J i hi], ?_, i₀, by simp; linarith⟩
            simp [neg_smul, Finset.sum_neg_distrib, hc₀s]
          · exact ⟨c₀, hc₀J, hc₀s, i₀, h⟩
        obtain ⟨c, hcJ, hcs, j₀, hj₀⟩ := hc
        have key : C J = ⋃ j ∈ J, C (J.erase j) := by
          apply Set.Subset.antisymm
          · rintro v ⟨α, hα0, hαJ, rfl⟩
            have hj₀J : j₀ ∈ J := by
              by_contra h
              rw [hcJ j₀ h] at hj₀
              exact lt_irrefl _ hj₀
            have hne : (J.filter (fun j => 0 < c j)).Nonempty :=
              ⟨j₀, Finset.mem_filter.mpr ⟨hj₀J, hj₀⟩⟩
            obtain ⟨j, hj, hmin⟩ :=
              Finset.exists_min_image (J.filter (fun j => 0 < c j)) (fun j => α j / c j) hne
            rw [Finset.mem_filter] at hj
            have ht : 0 ≤ α j / c j := div_nonneg (hα0 j) hj.2.le
            refine Set.mem_biUnion hj.1 ⟨fun i => α i - (α j / c j) * c i, ?_, ?_, ?_⟩
            · intro i
              by_cases hci : 0 < c i
              · have hiJ : i ∈ J := by
                  by_contra h
                  rw [hcJ i h] at hci
                  exact lt_irrefl _ hci
                have := hmin i (Finset.mem_filter.mpr ⟨hiJ, hci⟩)
                rw [le_div_iff₀ hci] at this
                simp only
                linarith
              · push_neg at hci
                simp only
                nlinarith [hα0 i]
            · intro i hi
              rw [Finset.mem_erase, not_and_or, not_not] at hi
              rcases hi with hij | hiJ
              · subst hij
                simp only
                rw [div_mul_cancel₀ (α i) hj.2.ne', sub_self]
              · simp [hαJ i hiJ, hcJ i hiJ]
            · simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hcs,
                smul_zero, sub_zero]
          · apply Set.iUnion₂_subset
            intro j hj
            rintro v ⟨α, hα0, hαJ, rfl⟩
            exact ⟨α, hα0, fun i hi => hαJ i (fun h => hi (Finset.mem_of_mem_erase h)), rfl⟩
        rw [key]
        exact isClosed_biUnion_finset (fun j hj => ih _ (Finset.erase_ssubset hj))
  have hcone : cone s = C Finset.univ := by
    ext v
    simp [C, cone]
  rw [hcone]
  exact hC _

end CAMA_chap_3_4_3_3
