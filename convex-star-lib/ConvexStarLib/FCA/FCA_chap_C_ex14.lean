import ConvexStarLib.Defs

/-!
# `FCA_chap_C_ex14`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_ex14` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_ex14`, so the main result is `FCA_chap_C_ex14.FCA_chap_C_ex14`.
-/

namespace FCA_chap_C_ex14

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_C_ex14
  (S : ℕ → Set E)
  (hS_nested : ∀ k, S (k + 1) ⊆ S k)
  (hS_compact : ∀ k, IsCompact (S k)) :
  convexHull ℝ (⋂ k, S k) = ⋂ k, convexHull ℝ (S k) := by
  apply Set.Subset.antisymm
  · exact Set.subset_iInter fun k => convexHull_mono (Set.iInter_subset S k)
  · intro x hx
    rw [Set.mem_iInter] at hx
    have hanti : Antitone S := antitone_nat_of_succ_le hS_nested
    -- Carathéodory: for each `k`, `x` is a convex combination of `finrank + 1` points of `S k`
    -- (padding with zero weights if fewer points are needed).
    have hrep : ∀ k, ∃ p : (Fin (Module.finrank ℝ E + 1) → ℝ) × (Fin (Module.finrank ℝ E + 1) → E),
        (∀ i, 0 ≤ p.1 i) ∧ ∑ i, p.1 i = 1 ∧ (∀ i, p.2 i ∈ S k) ∧ ∑ i, p.1 i • p.2 i = x := by
      intro k
      classical
      obtain ⟨ι, _, z, w, hzs, hai, hw0, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull (hx k)
      have hcard : Fintype.card ι ≤ Module.finrank ℝ E + 1 :=
        hai.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
      have hne : Nonempty ι := by
        by_contra h
        rw [not_nonempty_iff] at h
        simp at hw1
      obtain ⟨i0⟩ := hne
      let e : ι ⊕ Fin (Module.finrank ℝ E + 1 - Fintype.card ι) ≃ Fin (Module.finrank ℝ E + 1) :=
        Fintype.equivFinOfCardEq (by simp [Fintype.card_sum, Nat.add_sub_cancel' hcard])
      let W : ι ⊕ Fin (Module.finrank ℝ E + 1 - Fintype.card ι) → ℝ := Sum.elim w 0
      let Z : ι ⊕ Fin (Module.finrank ℝ E + 1 - Fintype.card ι) → E := Sum.elim z (fun _ => z i0)
      have hW0 : ∀ j, 0 ≤ W j := by
        rintro (j | j)
        · exact (hw0 j).le
        · exact le_rfl
      have hZ : ∀ j, Z j ∈ S k := by
        rintro (j | j)
        · exact hzs ⟨j, rfl⟩
        · exact hzs ⟨i0, rfl⟩
      refine ⟨(W ∘ e.symm, Z ∘ e.symm), fun i => hW0 _, ?_, fun i => hZ _, ?_⟩
      · simp only [Function.comp_apply]
        rw [Equiv.sum_comp e.symm W]
        simp [W, Fintype.sum_sum_type, hw1]
      · simp only [Function.comp_apply]
        rw [Equiv.sum_comp e.symm (fun j => W j • Z j)]
        simp [W, Z, Fintype.sum_sum_type, hwz]
    choose p hp using hrep
    -- All representations live in a fixed compact set; extract a convergent subsequence.
    let K : Set ((Fin (Module.finrank ℝ E + 1) → ℝ) × (Fin (Module.finrank ℝ E + 1) → E)) :=
      stdSimplex ℝ (Fin (Module.finrank ℝ E + 1)) ×ˢ Set.univ.pi (fun _ => S 0)
    have hK : IsCompact K :=
      (isCompact_stdSimplex _).prod (isCompact_univ_pi fun _ => hS_compact 0)
    have hpK : ∀ k, p k ∈ K := by
      intro k
      refine ⟨⟨(hp k).1, (hp k).2.1⟩, ?_⟩
      intro i _
      exact hanti (Nat.zero_le k) ((hp k).2.2.1 i)
    obtain ⟨q, hqK, ψ, hψ, hlim⟩ := hK.tendsto_subseq hpK
    have hlim1 : Filter.Tendsto (fun j => (p (ψ j)).1) Filter.atTop (𝓝 q.1) :=
      (continuous_fst.tendsto q).comp hlim
    have hlim2 : Filter.Tendsto (fun j => (p (ψ j)).2) Filter.atTop (𝓝 q.2) :=
      (continuous_snd.tendsto q).comp hlim
    apply mem_convexHull_of_exists_fintype q.1 q.2 hqK.1.1 hqK.1.2
    · -- each limit point lies in every (closed) `S m`
      intro i
      rw [Set.mem_iInter]
      intro m
      apply (hS_compact m).isClosed.mem_of_tendsto (f := fun j => (p (ψ j)).2 i)
        (b := Filter.atTop)
      · exact ((continuous_apply i).tendsto q.2).comp hlim2
      · filter_upwards [Filter.eventually_ge_atTop m] with j hj
        exact hanti (hj.trans (hψ.id_le j)) ((hp (ψ j)).2.2.1 i)
    · -- the convex combination passes to the limit
      have hsum : Filter.Tendsto (fun j => ∑ i, (p (ψ j)).1 i • (p (ψ j)).2 i) Filter.atTop
          (𝓝 (∑ i, q.1 i • q.2 i)) := by
        apply tendsto_finset_sum
        intro i _
        exact (((continuous_apply i).tendsto q.1).comp hlim1).smul
          (((continuous_apply i).tendsto q.2).comp hlim2)
      have hconst : (fun j => ∑ i, (p (ψ j)).1 i • (p (ψ j)).2 i) = fun _ => x := by
        funext j
        exact (hp (ψ j)).2.2.2
      rw [hconst] at hsum
      exact tendsto_nhds_unique hsum tendsto_const_nhds

end FCA_chap_C_ex14
