import ConvexStarLib.Defs

/-!
# `FCA_chap_A_ex_26`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_A_ex_26` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_A_ex_26`, so the main result is `FCA_chap_A_ex_26.FCA_chap_A_ex_26`.
-/

namespace FCA_chap_A_ex_26

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


theorem FCA_chap_A_ex_26 :
  (∀ {n m : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)),
    let P := {x : EuclideanSpace ℝ (Fin n) | A x = b ∧ ∀ i, x i ≥ 0}
    ∀ x ∈ P, x ≠ 0 →
      (x ∈ Set.extremePoints ℝ P ↔
        LinearIndependent ℝ (fun i : {i : Fin n // x i > 0} =>
          A (EuclideanSpace.single i.val 1)))) ∧
  (∀ {n : ℕ},
    IsCompact (birkhoffPolytope n) ∧ Convex ℝ (birkhoffPolytope n) ∧
    Set.extremePoints ℝ (birkhoffPolytope n) =
      {A | ∃ σ : Equiv.Perm (Fin n),
        ∀ j, A (EuclideanSpace.single j 1) = EuclideanSpace.single (σ j) 1}) := by
  refine ⟨?_, ?_⟩
  · intro n m A b P x hxP _hx0
    classical
    have hdecomp : ∀ v : EuclideanSpace ℝ (Fin n),
        A v = ∑ i, v i • A (EuclideanSpace.single i 1) := by
      intro v
      have hv : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
        ext j
        simp [Pi.single_apply, mul_ite, Finset.sum_ite_eq]
      calc A v = A (∑ i, v i • EuclideanSpace.single i (1 : ℝ)) := congrArg A hv
        _ = _ := by simp [map_sum, map_smul]
    have hsupp : ∀ v : EuclideanSpace ℝ (Fin n), (∀ j, ¬ x j > 0 → v j = 0) →
        A v = ∑ i : {i : Fin n // x i > 0}, v i • A (EuclideanSpace.single i.val 1) := by
      intro v hv
      rw [hdecomp v, ← Fintype.sum_subtype_add_sum_subtype (fun j => x j > 0)]
      have h2 : ∑ i : {j : Fin n // ¬ x j > 0}, v i • A (EuclideanSpace.single i.val 1) = 0 :=
        Finset.sum_eq_zero fun j _ => by simp [hv j j.2]
      rw [h2, add_zero]
    have hxnn : ∀ j, ¬ x j > 0 → x j = 0 := fun j hj => le_antisymm (not_lt.mp hj) (hxP.2 j)
    constructor
    · intro hext
      rw [Fintype.linearIndependent_iff]
      intro g hg i₀
      by_contra hne
      set d : EuclideanSpace ℝ (Fin n) :=
        WithLp.toLp 2 (fun j => if h : x j > 0 then g ⟨j, h⟩ else 0) with hd
      have hd_apply : ∀ j, d j = if h : x j > 0 then g ⟨j, h⟩ else 0 := fun j => rfl
      have hAd : A d = 0 := by
        rw [hsupp d (fun j hj => by simp [hd_apply, hj])]
        rw [← hg]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hd_apply, dif_pos i.2]
      have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε ∈ Set.Ioi 0 ∧
          ∀ i : {i : Fin n // x i > 0}, ε * |g i| < x i := by
        refine Filter.Eventually.and self_mem_nhdsWithin ?_
        apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
        rw [Filter.eventually_all]
        intro i
        have ht : Filter.Tendsto (fun ε : ℝ => ε * |g i|) (𝓝 0) (𝓝 (0 * |g i|)) :=
          (continuous_id.mul continuous_const).tendsto 0
        rw [zero_mul] at ht
        exact ht.eventually_lt_const i.2
      obtain ⟨ε, hεpos, hε⟩ := hev.exists
      have hεpos' : (0:ℝ) < ε := hεpos
      have hy : x + ε • d ∈ P := by
        refine ⟨by simp [map_add, map_smul, hAd, hxP.1], fun j => ?_⟩
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hd_apply]
        by_cases hj : x j > 0
        · rw [dif_pos hj]
          have h1 := hε ⟨j, hj⟩
          have h2 : ε * (-|g ⟨j, hj⟩|) ≤ ε * g ⟨j, hj⟩ :=
            mul_le_mul_of_nonneg_left (neg_abs_le _) hεpos'.le
          simp only at h1
          linarith
        · rw [dif_neg hj]
          simpa using hxP.2 j
      have hz : x - ε • d ∈ P := by
        refine ⟨by simp [map_sub, map_smul, hAd, hxP.1], fun j => ?_⟩
        simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hd_apply]
        by_cases hj : x j > 0
        · rw [dif_pos hj]
          have h1 := hε ⟨j, hj⟩
          have h2 : ε * g ⟨j, hj⟩ ≤ ε * |g ⟨j, hj⟩| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hεpos'.le
          simp only at h1
          linarith
        · rw [dif_neg hj]
          simpa using hxP.2 j
      have hseg : x ∈ openSegment ℝ (x + ε • d) (x - ε • d) := by
        refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
        module
      have heq := hext.2 hy hz hseg
      have hεd : ε • d = 0 := by
        have := congrArg (fun v => v - x) heq
        simpa using this
      rcases smul_eq_zero.mp hεd with h | h
      · exact (ne_of_gt hεpos') h
      · apply hne
        have := congrArg (fun v => v i₀.val) h
        simpa [hd_apply, i₀.2] using this
    · intro hli
      rw [Fintype.linearIndependent_iff] at hli
      refine ⟨hxP, ?_⟩
      rintro y hy z hz ⟨a, c, ha, hc, hac, hxyz⟩
      have hzero : ∀ j, ¬ x j > 0 → y j = 0 := by
        intro j hj
        have hxj : x j = 0 := hxnn j hj
        have h1 : a * y j + c * z j = 0 := by
          have := congrArg (fun v => v j) hxyz
          simpa [hxj] using this
        have h2 := hy.2 j
        have h3 := hz.2 j
        have h4 : 0 ≤ c * z j := mul_nonneg hc.le h3
        have h5 : a * y j = 0 := by nlinarith [mul_nonneg ha.le h2]
        rcases mul_eq_zero.mp h5 with h | h
        · exact absurd h (ne_of_gt ha)
        · exact h
      have hAw : A (y - x) = 0 := by rw [map_sub, hy.1, hxP.1, sub_self]
      rw [hsupp (y - x) (fun j hj => by simp [hzero j hj, hxnn j hj])] at hAw
      have hc0 := hli (fun i => (y - x) i) hAw
      ext j
      by_cases hj : x j > 0
      · have := hc0 ⟨j, hj⟩
        simp only [PiLp.sub_apply] at this
        linarith
      · rw [hzero j hj, hxnn j hj]
  · intro n
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : Matrix (Fin n) (Fin n) ℝ ≃ₗ[ℝ]
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
        ∀ M i j, (Φ M (EuclideanSpace.single j 1)) i = M i j :=
      ⟨Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap, fun M i j => by simp⟩
    have entry_eq : ∀ (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (i j : Fin n), (A (EuclideanSpace.single j 1)) i = Φ.symm A i j := by
      intro A i j
      conv_lhs => rw [← Φ.apply_symm_apply A]
      exact hΦ _ i j
    have onesVec_apply : ∀ i : Fin n, onesVec n i = 1 := by
      intro i
      simp [onesVec]
    have apply_onesVec : ∀ (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (i : Fin n), (A (onesVec n)) i = ∑ j, (A (EuclideanSpace.single j 1)) i := by
      intro A i
      simp [onesVec, map_sum]
    have mem_iff : ∀ A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
        A ∈ birkhoffPolytope n ↔ Φ.symm A ∈ doublyStochastic ℝ (Fin n) := by
      intro A
      rw [mem_doublyStochastic_iff_sum]
      simp only [birkhoffPolytope, doublyStochasticSet, Set.mem_setOf_eq, entry_eq]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨fun i j => h3 i j, fun i => ?_, h2⟩
        have := congrArg (fun v => v i) h1
        simpa [apply_onesVec, onesVec_apply, entry_eq] using this
      · rintro ⟨h3, h1, h2⟩
        refine ⟨⟨?_, h2⟩, fun i j => h3 i j⟩
        ext i
        simp [apply_onesVec, onesVec_apply, h1, entry_eq]
    have himage : birkhoffPolytope n = Φ '' (doublyStochastic ℝ (Fin n) : Set _) := by
      ext A
      rw [mem_iff]
      constructor
      · intro h
        exact ⟨_, h, Φ.apply_symm_apply A⟩
      · rintro ⟨M, hM, rfl⟩
        simpa using hM
    rw [himage]
    refine ⟨?_, ?_, ?_⟩
    · apply IsCompact.image
      · rw [doublyStochastic_eq_convexHull_permMatrix]
        apply Set.Finite.isCompact_convexHull
        exact Set.finite_range _
      · exact LinearMap.continuous_of_finiteDimensional Φ.toLinearMap
    · exact (convex_doublyStochastic).linear_image Φ.toLinearMap
    · rw [← image_extremePoints, extremePoints_doublyStochastic]
      ext A
      constructor
      · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
        refine ⟨σ⁻¹, fun j => ?_⟩
        ext i
        rw [hΦ]
        simp [Equiv.Perm.permMatrix, Equiv.toPEquiv_apply, PEquiv.toMatrix_apply,
          Equiv.eq_symm_apply]
      · rintro ⟨σ, hσ⟩
        refine ⟨_, ⟨σ⁻¹, rfl⟩, ?_⟩
        apply Φ.symm.injective
        ext i j
        rw [LinearEquiv.symm_apply_apply, ← entry_eq, hσ]
        simp [Equiv.Perm.permMatrix, Equiv.toPEquiv_apply, PEquiv.toMatrix_apply,
          Equiv.symm_apply_eq]

end FCA_chap_A_ex_26
