import ConvexStarLib.Defs

/-!
# `FCA_chap_A_ex_15`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_A_ex_15` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_A_ex_15`, so the main result is `FCA_chap_A_ex_15.FCA_chap_A_ex_15`.
-/

namespace FCA_chap_A_ex_15

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


open InnerProductSpace in
theorem FCA_aux_hsInner_rankOne {n : ℕ} (v : EuclideanSpace ℝ (Fin n))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    hsInner (rankOne ℝ v v) A = inner ℝ v (A v) := by
  unfold hsInner
  set e := EuclideanSpace.basisFun (Fin n) ℝ with he
  have h := e.sum_repr' v
  have he' : ∀ i, e i = EuclideanSpace.single i 1 := fun i => by simp [he]
  calc ∑ j : Fin n, inner ℝ (rankOne ℝ v v (EuclideanSpace.single j 1))
          (A (EuclideanSpace.single j 1))
      = ∑ j, inner ℝ (e j) v * inner ℝ v (A (e j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [rankOne_apply, real_inner_smul_left, he', real_inner_comm]
    _ = inner ℝ v (A (∑ j, inner ℝ (e j) v • e j)) := by
        simp [map_sum, inner_sum, real_inner_smul_right]
    _ = inner ℝ v (A v) := by rw [h]

theorem FCA_aux_hsInner_sum_smul_left {n : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (B : ι → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    hsInner (∑ i ∈ s, c i • B i) A = ∑ i ∈ s, c i * hsInner (B i) A := by
  unfold hsInner
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, sum_inner,
    real_inner_smul_left, Finset.mul_sum]
  rw [Finset.sum_comm]

open InnerProductSpace in
theorem FCA_aux_inner_sum_rankOne {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (c : Fin n → ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ ((∑ i, c i • rankOne ℝ (b i) (b i)) x) y =
      ∑ i, c i * (inner ℝ (b i) x * inner ℝ (b i) y) := by
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, rankOne_apply,
    sum_inner, real_inner_smul_left]

open InnerProductSpace in
theorem FCA_aux_sum_rankOne_apply_basis {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (c : Fin n → ℝ) (k : Fin n) :
    (∑ i, c i • rankOne ℝ (b i) (b i)) (b k) = c k • b k := by
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, rankOne_apply]
  rw [Finset.sum_eq_single k]
  · rw [real_inner_self_eq_norm_sq, b.orthonormal.1 k]
    simp
  · intro i _ hik
    rw [orthonormal_iff_ite.mp b.orthonormal i k, if_neg hik]
    simp
  · simp

open InnerProductSpace in
theorem FCA_aux_isSelfAdjoint_sum_rankOne {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (c : Fin n → ℝ) : IsSelfAdjoint (∑ i, c i • rankOne ℝ (b i) (b i)) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe]
  rw [FCA_aux_inner_sum_rankOne, real_inner_comm, FCA_aux_inner_sum_rankOne]
  exact Finset.sum_congr rfl fun i _ => by ring

open InnerProductSpace in
theorem FCA_aux_spectral {n : ℕ} (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hM : IsSelfAdjoint M) :
    ∃ (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (μ : Fin n → ℝ),
      M = ∑ i, μ i • rankOne ℝ (b i) (b i) := by
  have hT : (M : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hM
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  refine ⟨hT.eigenvectorBasis hn, hT.eigenvalues hn, ?_⟩
  refine ContinuousLinearMap.ext fun x => ?_
  have hb : ∀ i, M (hT.eigenvectorBasis hn i) =
      hT.eigenvalues hn i • hT.eigenvectorBasis hn i := fun i => by
    have := hT.apply_eigenvectorBasis hn i
    exact this
  conv_lhs => rw [← (hT.eigenvectorBasis hn).sum_repr' x]
  simp only [map_sum, map_smul, hb, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, rankOne_apply]
  exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem FCA_chap_A_ex_15 {n : ℕ} :
  (conePolarSA (psdCone n) = negPsdCone n) ∧
  (∀ M : selfAdjoint (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
    ∃ Mp Mn : selfAdjoint _,
      Mp ∈ psdCone n ∧ Mn ∈ negPsdCone n ∧
      M = Mp + Mn ∧ hsInnerSA Mp Mn = 0) := by
  constructor
  · ext P
    constructor
    · intro hP x
      have hR : IsSelfAdjoint (InnerProductSpace.rankOne ℝ x x) :=
        ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
          (InnerProductSpace.isSymmetric_rankOne_self x)
      have hmem : (⟨InnerProductSpace.rankOne ℝ x x, hR⟩ : selfAdjoint _) ∈ psdCone n := by
        intro y
        simp only [InnerProductSpace.rankOne_apply, real_inner_smul_left]
        exact mul_self_nonneg _
      have := hP _ hmem
      simp only [hsInnerSA] at this
      rw [FCA_aux_hsInner_rankOne] at this
      rw [real_inner_comm]
      exact this
    · intro hP M hM
      obtain ⟨b, μ, hb⟩ := FCA_aux_spectral M.1 M.2
      have hμ : ∀ i, 0 ≤ μ i := by
        intro i
        have := hM (b i)
        rw [hb, FCA_aux_sum_rankOne_apply_basis, real_inner_smul_left,
          real_inner_self_eq_norm_sq, b.orthonormal.1 i] at this
        simpa using this
      simp only [hsInnerSA]
      rw [hb, FCA_aux_hsInner_sum_smul_left]
      simp only [FCA_aux_hsInner_rankOne]
      apply Finset.sum_nonpos
      intro i _
      apply mul_nonpos_of_nonneg_of_nonpos (hμ i)
      rw [real_inner_comm]
      exact hP (b i)
  · intro M
    obtain ⟨b, μ, hb⟩ := FCA_aux_spectral M.1 M.2
    refine ⟨⟨∑ i, max (μ i) 0 • InnerProductSpace.rankOne ℝ (b i) (b i),
        FCA_aux_isSelfAdjoint_sum_rankOne b _⟩,
      ⟨∑ i, min (μ i) 0 • InnerProductSpace.rankOne ℝ (b i) (b i),
        FCA_aux_isSelfAdjoint_sum_rankOne b _⟩,
      ?_, ?_, ?_, ?_⟩
    · intro x
      rw [FCA_aux_inner_sum_rankOne]
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (le_max_right _ _) (mul_self_nonneg _)
    · intro x
      rw [FCA_aux_inner_sum_rankOne]
      apply Finset.sum_nonpos
      intro i _
      exact mul_nonpos_of_nonpos_of_nonneg (min_le_right _ _) (mul_self_nonneg _)
    · apply Subtype.ext
      simp only [AddSubgroup.coe_add]
      rw [hb, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h : max (μ i) 0 + min (μ i) 0 = μ i := by
        rcases le_total (μ i) 0 with h | h <;> simp [h]
      conv_lhs => rw [← h]
      rw [add_smul]
    · simp only [hsInnerSA]
      rw [FCA_aux_hsInner_sum_smul_left]
      simp only [FCA_aux_hsInner_rankOne, FCA_aux_sum_rankOne_apply_basis, real_inner_smul_right]
      apply Finset.sum_eq_zero
      intro i _
      rcases le_total (μ i) 0 with h | h <;> simp [h]

end FCA_chap_A_ex_15
