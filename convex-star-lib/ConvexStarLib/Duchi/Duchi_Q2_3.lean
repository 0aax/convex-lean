import ConvexStarLib.Defs

/-!
# `Duchi_Q2_3`

Source: Duchi, EE364m Convex Optimization (exercise sets).

Statement from the `convex-eval-v28-2h/Duchi_Q2_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Duchi_Q2_3`, so the main result is `Duchi_Q2_3.Duchi_Q2_3`.
-/

namespace Duchi_Q2_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


open BigOperators
open scoped InnerProductSpace

section aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma ds_ineq {n : ℕ} (a b : Fin n → ℝ) (ha : Antitone a) (hb : Antitone b)
    (P : Fin n → Fin n → ℝ) (hP0 : ∀ i j, 0 ≤ P i j) (hProw : ∀ i, ∑ j, P i j = 1)
    (hPcol : ∀ j, ∑ i, P i j = 1) :
    ∑ i, ∑ j, a i * b j * P i j ≤ ∑ i, a i * b i := by
  have hM : (Matrix.of P) ∈ doublyStochastic ℝ (Fin n) := by
    rw [mem_doublyStochastic_iff_sum]
    exact ⟨hP0, hProw, hPcol⟩
  obtain ⟨w, hw0, hw1, hwM⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
  have hP : ∀ i j, P i j = ∑ σ : Equiv.Perm (Fin n), w σ * (if σ i = j then 1 else 0) := by
    intro i j
    have := congrFun (congrFun hwM i) j
    simp only [Matrix.of_apply] at this
    rw [← this, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  have key : ∀ σ : Equiv.Perm (Fin n), ∑ i, ∑ j, a i * b j * (if σ i = j then 1 else 0)
      = ∑ i, a i * b (σ i) := by
    intro σ
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  calc ∑ i, ∑ j, a i * b j * P i j
      = ∑ σ : Equiv.Perm (Fin n), w σ * ∑ i, a i * b (σ i) := by
        simp_rw [← key, hP, Finset.mul_sum]
        conv_rhs => rw [Finset.sum_comm]; arg 2; ext i; rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun σ _ => ?_
        ring
    _ ≤ ∑ σ : Equiv.Perm (Fin n), w σ * ∑ i, a i * b i := by
        refine Finset.sum_le_sum fun σ _ => ?_
        exact mul_le_mul_of_nonneg_left ((ha.monovary hb).sum_mul_comp_perm_le_sum_mul) (hw0 σ)
    _ = ∑ i, a i * b i := by rw [← Finset.sum_mul, hw1, one_mul]


lemma inner_sv {n : ℕ} (w : OrthonormalBasis (Fin n) ℝ E) (Q : Fin n → E) (τ : Fin n → ℝ)
    (T : E →ₗ[ℝ] E) (hT : ∀ l, T (w l) = τ l • Q l) (x y : E) :
    ⟪x, T y⟫_ℝ = ∑ l, τ l * (⟪w l, y⟫_ℝ * ⟪x, Q l⟫_ℝ) := by
  conv_lhs => rw [← w.sum_repr' y]
  rw [map_sum, inner_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, hT, smul_smul, real_inner_smul_right]
  ring

lemma inner_eig {n : ℕ} (v : OrthonormalBasis (Fin n) ℝ E) (b : Fin n → ℝ)
    (T : E →ₗ[ℝ] E) (hT : ∀ j, T (v j) = b j • v j) (x y : E) :
    ⟪x, T y⟫_ℝ = ∑ j, b j * (⟪v j, x⟫_ℝ * ⟪v j, y⟫_ℝ) := by
  rw [inner_sv v v b T hT x y]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_comm x (v j)]
  ring

lemma ds_onb {n : ℕ} (u v : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ)
    (ha : Antitone a) (hb : Antitone b) :
    ∑ i, ∑ j, a i * b j * ⟪u i, v j⟫_ℝ ^ 2 ≤ ∑ i, a i * b i :=
  ds_ineq a b ha hb (fun i j => ⟪u i, v j⟫_ℝ ^ 2) (fun i j => sq_nonneg _)
    (fun i => by simp [v.sum_sq_inner_left, u.orthonormal.1 i])
    (fun j => by simp [u.sum_sq_inner_right, v.orthonormal.1 j])

lemma trace_formula {n : ℕ} (X Y : E →ₗ[ℝ] E) (hX : X.IsSymmetric)
    (u v : OrthonormalBasis (Fin n) ℝ E) (a b : Fin n → ℝ)
    (hu : ∀ i, X (u i) = a i • u i) (hv : ∀ j, Y (v j) = b j • v j) :
    LinearMap.trace ℝ E (X ∘ₗ Y) = ∑ i, ∑ j, a i * b j * ⟪u i, v j⟫_ℝ ^ 2 := by
  rw [LinearMap.trace_eq_sum_inner _ u]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply, ← hX, hu, real_inner_smul_left, inner_eig v b Y hv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_comm (v j) (u i)]
  ring

end aux

section aux2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma eq_case {n : ℕ} (X Y : E →ₗ[ℝ] E) (hX : X.IsSymmetric) (hY : Y.IsSymmetric)
    (u v w : OrthonormalBasis (Fin n) ℝ E) (a b c : Fin n → ℝ)
    (ha : Antitone a) (hb : Antitone b) (hc : Antitone c)
    (hu : ∀ i, X (u i) = a i • u i) (hv : ∀ j, Y (v j) = b j • v j)
    (hw : ∀ i, (X + Y) (w i) = c i • w i)
    (heq : LinearMap.trace ℝ E (X ∘ₗ Y) = ∑ i, a i * b i) :
    ∀ i, X (w i) = a i • w i ∧ Y (w i) = b i • w i := by
  set d : Fin n → ℝ := fun i => ⟪w i, X (w i)⟫_ℝ with hd
  set e : Fin n → ℝ := fun i => ⟪w i, Y (w i)⟫_ℝ with he
  have hd' : ∀ i, d i = ∑ j, a j * ⟪w i, u j⟫_ℝ ^ 2 := by
    intro i
    simp only [hd]
    rw [inner_eig u a X hu]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm (w i) (u j)]
    ring
  have he' : ∀ i, e i = ∑ j, b j * ⟪w i, v j⟫_ℝ ^ 2 := by
    intro i
    simp only [he]
    rw [inner_eig v b Y hv]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm (w i) (v j)]
    ring
  have hcde : ∀ i, c i = d i + e i := by
    intro i
    have : ⟪w i, (X + Y) (w i)⟫_ℝ = c i := by
      rw [hw, real_inner_smul_right, real_inner_self_eq_norm_sq, w.orthonormal.1 i]; ring
    rw [← this, LinearMap.add_apply, inner_add_right]
  have gen : ∀ (p q : Fin n → ℝ) (hp : Antitone p) (hq : Antitone q)
      (z : OrthonormalBasis (Fin n) ℝ E),
      ∑ i, p i * ∑ j, q j * ⟪w i, z j⟫_ℝ ^ 2 ≤ ∑ i, p i * q i := by
    intro p q hp hq z
    refine le_of_eq_of_le ?_ (ds_onb w z p q hp hq)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have h1 : ∑ i, c i * d i ≤ ∑ i, c i * a i := by
    simp_rw [hd']; exact gen c a hc ha u
  have h2 : ∑ i, c i * e i ≤ ∑ i, c i * b i := by
    simp_rw [he']; exact gen c b hc hb v
  have h4 : ∑ i, a i * e i ≤ ∑ i, a i * b i := by
    simp_rw [he']; exact gen a b ha hb v
  have h5 : ∑ i, b i * d i ≤ ∑ i, b i * a i := by
    simp_rw [hd']; exact gen b a hb ha u
  have hN1 : ∑ i, ‖X (w i)‖ ^ 2 = ∑ i, a i ^ 2 := by
    have : ∀ i, ‖X (w i)‖ ^ 2 = ∑ j, a j ^ 2 * ⟪u j, w i⟫_ℝ ^ 2 := by
      intro i
      rw [← u.sum_sq_inner_right]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hX, hu, real_inner_smul_left]
      ring
    simp_rw [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, w.sum_sq_inner_left, u.orthonormal.1 j]
    ring
  have hN2 : ∑ i, ‖Y (w i)‖ ^ 2 = ∑ i, b i ^ 2 := by
    have : ∀ i, ‖Y (w i)‖ ^ 2 = ∑ j, b j ^ 2 * ⟪v j, w i⟫_ℝ ^ 2 := by
      intro i
      rw [← v.sum_sq_inner_right]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hY, hv, real_inner_smul_left]
      ring
    simp_rw [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, w.sum_sq_inner_left, v.orthonormal.1 j]
    ring
  have hN3 : ∑ i, ⟪X (w i), Y (w i)⟫_ℝ = ∑ i, a i * b i := by
    rw [← heq, LinearMap.trace_eq_sum_inner _ w]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.comp_apply, hX]
  have hN4 : ∑ i, c i ^ 2 = ∑ i, a i ^ 2 + 2 * ∑ i, a i * b i + ∑ i, b i ^ 2 := by
    have : ∀ i, c i ^ 2 = ‖X (w i)‖ ^ 2 + 2 * ⟪X (w i), Y (w i)⟫_ℝ + ‖Y (w i)‖ ^ 2 := by
      intro i
      have h := congrArg (fun z => ‖z‖ ^ 2) (hw i)
      simp only [LinearMap.add_apply] at h
      rw [norm_add_sq_real] at h
      rw [h, norm_smul, w.orthonormal.1 i, mul_one, Real.norm_eq_abs, sq_abs]
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, hN1, hN2, hN3]
  have hR : ∀ i, ‖X (w i) - a i • w i‖ ^ 2 + ‖Y (w i) - b i • w i‖ ^ 2
      = (‖X (w i)‖ ^ 2 - 2 * (a i * d i) + a i ^ 2)
        + (‖Y (w i)‖ ^ 2 - 2 * (b i * e i) + b i ^ 2) := by
    intro i
    rw [norm_sub_sq_real, norm_sub_sq_real, real_inner_smul_right, real_inner_smul_right,
      norm_smul, norm_smul, w.orthonormal.1 i, Real.norm_eq_abs, Real.norm_eq_abs, mul_one,
      mul_one, sq_abs, sq_abs, real_inner_comm (w i) (X (w i)), real_inner_comm (w i) (Y (w i))]
  have F1 : ∑ i, c i * a i = ∑ i, a i * d i + ∑ i, a i * e i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcde]; ring
  have F2 : ∑ i, c i * b i = ∑ i, b i * d i + ∑ i, b i * e i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcde]; ring
  have F3 : ∑ i, c i ^ 2 = ∑ i, c i * d i + ∑ i, c i * e i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcde]; ring
  have F4 : ∑ i, b i * a i = ∑ i, a i * b i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hRsum : ∑ i, (‖X (w i) - a i • w i‖ ^ 2 + ‖Y (w i) - b i • w i‖ ^ 2)
      = 2 * ∑ i, a i ^ 2 + 2 * ∑ i, b i ^ 2 - 2 * ∑ i, a i * d i - 2 * ∑ i, b i * e i := by
    simp_rw [hR]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hN1, hN2]
    ring
  have hle : ∑ i, (‖X (w i) - a i • w i‖ ^ 2 + ‖Y (w i) - b i • w i‖ ^ 2) ≤ 0 := by
    rw [hRsum]
    linarith
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ ‖X (w i) - a i • w i‖ ^ 2 + ‖Y (w i) - b i • w i‖ ^ 2 :=
    fun i _ => by positivity
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp (le_antisymm hle (Finset.sum_nonneg hnn))
  intro i
  have hi := hzero i (Finset.mem_univ i)
  have hx : ‖X (w i) - a i • w i‖ ^ 2 = 0 := by
    linarith [sq_nonneg ‖X (w i) - a i • w i‖, sq_nonneg ‖Y (w i) - b i • w i‖]
  have hy : ‖Y (w i) - b i • w i‖ ^ 2 = 0 := by
    linarith [sq_nonneg ‖X (w i) - a i • w i‖, sq_nonneg ‖Y (w i) - b i • w i‖]
  constructor
  · rw [← sub_eq_zero, ← norm_eq_zero]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx
  · rw [← sub_eq_zero, ← norm_eq_zero]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy

end aux2

section aux3

lemma svd_exists {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hT : ((ContinuousLinearMap.adjoint A).comp A).toLinearMap.IsSymmetric) :
    (∀ k, 0 ≤ hT.eigenvalues finrank_euclideanSpace_fin k) ∧
      ∃ P : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      ∀ k, A (hT.eigenvectorBasis finrank_euclideanSpace_fin k) =
        Real.sqrt (hT.eigenvalues finrank_euclideanSpace_fin k) • P k := by
  set lam := hT.eigenvalues finrank_euclideanSpace_fin with hlam
  set v := hT.eigenvectorBasis finrank_euclideanSpace_fin with hv
  have hTv : ∀ k, ((ContinuousLinearMap.adjoint A).comp A) (v k) = lam k • v k := by
    intro k
    exact hT.apply_eigenvectorBasis finrank_euclideanSpace_fin k
  have hAv : ∀ k l, ⟪A (v k), A (v l)⟫_ℝ = if k = l then lam l else 0 := by
    intro k l
    rw [← ContinuousLinearMap.adjoint_inner_right]
    have : (ContinuousLinearMap.adjoint A) (A (v l)) = lam l • v l := by
      rw [← hTv l]; rfl
    rw [this, real_inner_smul_right, orthonormal_iff_ite.mp v.orthonormal k l]
    split_ifs <;> simp
  have hlam0 : ∀ k, 0 ≤ lam k := by
    intro k
    have := hAv k k
    simp only [if_true] at this
    rw [← this]
    exact real_inner_self_nonneg
  refine ⟨hlam0, ?_⟩
  set σ : Fin n → ℝ := fun k => Real.sqrt (lam k) with hσ
  have hσ2 : ∀ k, σ k ^ 2 = lam k := fun k => Real.sq_sqrt (hlam0 k)
  set p : Fin n → EuclideanSpace ℝ (Fin n) := fun k => (σ k)⁻¹ • A (v k) with hp
  set s : Set (Fin n) := {k | σ k ≠ 0} with hs
  have hon : Orthonormal ℝ (s.restrict p) := by
    rw [orthonormal_iff_ite]
    rintro ⟨k, hk⟩ ⟨l, hl⟩
    simp only [Set.restrict_apply, hp, real_inner_smul_left, real_inner_smul_right, hAv,
      Subtype.mk.injEq]
    split_ifs with hkl
    · subst hkl
      have hk' : σ k ≠ 0 := hk
      rw [← hσ2 k]
      field_simp
    · simp
  obtain ⟨P, hP⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨P, fun k => ?_⟩
  by_cases hk : σ k = 0
  · have h0 : lam k = 0 := by rw [← hσ2 k, hk]; ring
    have : ‖A (v k)‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, hAv k k, if_pos rfl, h0]
    have hz : A (v k) = 0 := by
      rw [← norm_eq_zero]; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    change A (v k) = σ k • P k
    rw [hz, hk, zero_smul]
  · change A (v k) = σ k • P k
    rw [hP k hk, hp]
    simp only
    rw [smul_smul, mul_inv_cancel₀ hk, one_smul]

end aux3

lemma vn_general {n : ℕ} (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    |LinearMap.trace ℝ _ ((ContinuousLinearMap.adjoint A).toLinearMap.comp B.toLinearMap)| ≤
      ∑ i, singularValues A i * singularValues B i := by
  have hTA : ((ContinuousLinearMap.adjoint A).comp A).toLinearMap.IsSymmetric :=
    (ContinuousLinearMap.isPositive_adjoint_comp_self A).toLinearMap.isSymmetric
  have hTB : ((ContinuousLinearMap.adjoint B).comp B).toLinearMap.IsSymmetric :=
    (ContinuousLinearMap.isPositive_adjoint_comp_self B).toLinearMap.isSymmetric
  have hsA : ∀ i, singularValues A i =
      Real.sqrt (hTA.eigenvalues finrank_euclideanSpace_fin i) := fun i => rfl
  have hsB : ∀ i, singularValues B i =
      Real.sqrt (hTB.eigenvalues finrank_euclideanSpace_fin i) := fun i => rfl
  obtain ⟨-, P, hP⟩ := svd_exists A hTA
  obtain ⟨-, Q, hQ⟩ := svd_exists B hTB
  set v := hTA.eigenvectorBasis finrank_euclideanSpace_fin with hv
  set w := hTB.eigenvectorBasis finrank_euclideanSpace_fin with hw
  have hP' : ∀ k, A (v k) = singularValues A k • P k := fun k => by rw [hP k, hsA k]
  have hQ' : ∀ l, B (w l) = singularValues B l • Q l := fun l => by rw [hQ l, hsB l]
  set σ := singularValues A with hσ
  set τ := singularValues B with hτ
  have hσa : Antitone σ := fun i j hij => by
    rw [hsA, hsA]; exact Real.sqrt_le_sqrt (hTA.eigenvalues_antitone _ hij)
  have hτa : Antitone τ := fun i j hij => by
    rw [hsB, hsB]; exact Real.sqrt_le_sqrt (hTB.eigenvalues_antitone _ hij)
  have hσ0 : ∀ k, 0 ≤ σ k := fun k => by rw [hsA]; exact Real.sqrt_nonneg _
  have hτ0 : ∀ k, 0 ≤ τ k := fun k => by rw [hsB]; exact Real.sqrt_nonneg _
  have hBQ : ∀ l, B.toLinearMap (w l) = τ l • Q l := fun l => by
    rw [ContinuousLinearMap.coe_coe, hQ' l]
  have htr : LinearMap.trace ℝ _ ((ContinuousLinearMap.adjoint A).toLinearMap.comp B.toLinearMap)
      = ∑ k, ∑ l, σ k * τ l * (⟪v k, w l⟫_ℝ * ⟪P k, Q l⟫_ℝ) := by
    rw [LinearMap.trace_eq_sum_inner _ v]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.adjoint_inner_right, hP', real_inner_smul_left,
      inner_sv w Q τ B.toLinearMap hBQ (P k) (v k),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [real_inner_comm (w l) (v k)]
    ring
  rw [htr]
  have hds1 := ds_onb v w σ τ hσa hτa
  have hds2 := ds_onb P Q σ τ hσa hτa
  calc |∑ k, ∑ l, σ k * τ l * (⟪v k, w l⟫_ℝ * ⟪P k, Q l⟫_ℝ)|
      ≤ ∑ k, |∑ l, σ k * τ l * (⟪v k, w l⟫_ℝ * ⟪P k, Q l⟫_ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, ∑ l, |σ k * τ l * (⟪v k, w l⟫_ℝ * ⟪P k, Q l⟫_ℝ)| :=
        Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, ∑ l, (σ k * τ l * ⟪v k, w l⟫_ℝ ^ 2 / 2 + σ k * τ l * ⟪P k, Q l⟫_ℝ ^ 2 / 2) := by
        refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
        have hst : 0 ≤ σ k * τ l := mul_nonneg (hσ0 k) (hτ0 l)
        set x := ⟪v k, w l⟫_ℝ
        set y := ⟪P k, Q l⟫_ℝ
        rw [abs_le]
        constructor
        · nlinarith [mul_nonneg hst (sq_nonneg (x + y))]
        · nlinarith [mul_nonneg hst (sq_nonneg (x - y))]
    _ = (∑ k, ∑ l, σ k * τ l * ⟪v k, w l⟫_ℝ ^ 2) / 2
          + (∑ k, ∑ l, σ k * τ l * ⟪P k, Q l⟫_ℝ ^ 2) / 2 := by
        rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    _ ≤ ∑ i, σ i * τ i := by linarith

theorem Duchi_Q2_3 {n : ℕ}
  (X Y : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
  (hX : X.toLinearMap.IsSymmetric) (hY : Y.toLinearMap.IsSymmetric) :
  let lamX : Fin n → ℝ := hX.eigenvalues finrank_euclideanSpace_fin
  let lamY : Fin n → ℝ := hY.eigenvalues finrank_euclideanSpace_fin
  (LinearMap.trace ℝ _ (X.toLinearMap.comp Y.toLinearMap) ≤ ∑ (i : Fin n), lamX i * lamY i) ∧
  (LinearMap.trace ℝ _ (X.toLinearMap.comp Y.toLinearMap) = ∑ (i : Fin n), lamX i * lamY i ↔
    ∃ U : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      ∀ i, X (U i) = lamX i • U i ∧ Y (U i) = lamY i • U i) ∧
  (∀ (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
    abs (LinearMap.trace ℝ _ ((ContinuousLinearMap.adjoint A).toLinearMap.comp B.toLinearMap)) ≤
      ∑ (i : Fin n), singularValues A i * singularValues B i) := by
  intro lamX lamY
  set u := hX.eigenvectorBasis finrank_euclideanSpace_fin with hu_def
  set v := hY.eigenvectorBasis finrank_euclideanSpace_fin with hv_def
  have hu : ∀ i, X.toLinearMap (u i) = lamX i • u i := fun i => hX.apply_eigenvectorBasis _ i
  have hv : ∀ j, Y.toLinearMap (v j) = lamY j • v j := fun j => hY.apply_eigenvectorBasis _ j
  have ha : Antitone lamX := hX.eigenvalues_antitone _
  have hb : Antitone lamY := hY.eigenvalues_antitone _
  have part1 : LinearMap.trace ℝ _ (X.toLinearMap.comp Y.toLinearMap) ≤
      ∑ i, lamX i * lamY i := by
    rw [trace_formula _ _ hX u v lamX lamY hu hv]
    exact ds_onb u v lamX lamY ha hb
  refine ⟨part1, ?_, fun A B => vn_general A B⟩
  constructor
  · intro heq
    have hZ : (X.toLinearMap + Y.toLinearMap).IsSymmetric := hX.add hY
    refine ⟨hZ.eigenvectorBasis finrank_euclideanSpace_fin, ?_⟩
    have := eq_case X.toLinearMap Y.toLinearMap hX hY u v
      (hZ.eigenvectorBasis finrank_euclideanSpace_fin) lamX lamY
      (hZ.eigenvalues finrank_euclideanSpace_fin) ha hb (hZ.eigenvalues_antitone _) hu hv
      (fun i => hZ.apply_eigenvectorBasis _ i) heq
    intro i
    exact this i
  · rintro ⟨U, hU⟩
    rw [LinearMap.trace_eq_sum_inner _ U]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe,
      (hU i).2, map_smul, (hU i).1, smul_smul, real_inner_smul_right,
      real_inner_self_eq_norm_sq, U.orthonormal.1 i]
    ring

end Duchi_Q2_3
