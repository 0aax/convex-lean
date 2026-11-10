import ConvexStarLib.Defs

/-!
# `FCA_chap_D_ex6`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_ex6` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_ex6`, so the main result is `FCA_chap_D_ex6.FCA_chap_D_ex6`.
-/

namespace FCA_chap_D_ex6

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma jorgens_alg (a b c k00 k10 k01 k11 : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hdet : a * c - b * b = 1)
    (E1 : k00 + (k00 * a + k10 * b) = 1) (E2 : k10 + (k00 * b + k10 * c) = 0)
    (E3 : k01 + (k01 * a + k11 * b) = 0) (E4 : k11 + (k01 * b + k11 * c) = 1) :
    k01 = k10 ∧ k11 = 1 - k00 := by
  have hD : 0 < (1 + a) * (1 + c) - b * b := by nlinarith
  constructor
  · have h : ((1 + a) * (1 + c) - b * b) * (k01 - k10) = 0 := by
      linear_combination (1 + c) * E3 - b * E4 - (1 + a) * E2 + b * E1
    rcases mul_eq_zero.1 h with h | h
    · linarith
    · linarith
  · have h : ((1 + a) * (1 + c) - b * b) * (k11 + k00 - 1) = 0 := by
      linear_combination (1 + a) * E4 - b * E3 + (1 + c) * E1 - b * E2 - hdet
    rcases mul_eq_zero.1 h with h | h
    · linarith
    · linarith

set_option maxHeartbeats 1000000 in
theorem FCA_chap_D_ex6
  (f : EuclideanSpace ℝ (Fin 2) → ℝ)
  (hf_convex : InConvRn (liftRealtoEReal f))
  (hf_smooth : ContDiff ℝ 2 f)
  (hf_det : ∀ x, LinearMap.det (hessianOperator f x).toLinearMap = 1) :
  ∃ (A : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
  (b : EuclideanSpace ℝ (Fin 2)) (c : ℝ),
  (∀ x, hessianOperator f x = A) ∧
  (∀ x, f x = (1 / 2) * inner ℝ (A x) x + inner ℝ b x + c) := by
  classical
  set u0 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1 with hu0
  set u1 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1 with hu1
  have hdecomp : ∀ v : EuclideanSpace ℝ (Fin 2), v = v 0 • u0 + v 1 • u1 := by
    intro v; ext i; fin_cases i <;> simp [hu0, hu1]
  -- calculus setup
  let T : StrongDual ℝ (EuclideanSpace ℝ (Fin 2)) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hTinner : ∀ (l : StrongDual ℝ (EuclideanSpace ℝ (Fin 2))) (w : EuclideanSpace ℝ (Fin 2)),
      ⟪T l, w⟫ = l w := fun l w => InnerProductSpace.toDual_symm_apply
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf_smooth.fderiv_right (m := 1) (by norm_num)
  have hfd : Differentiable ℝ f := hf_smooth.differentiable (by norm_num)
  have hDf : ∀ x, HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x := fun x =>
    ((hf1.differentiable one_ne_zero) x).hasFDerivAt
  have hHeq : ∀ x, hessianOperator f x = T.comp (fderiv ℝ (fderiv ℝ f) x) := fun x =>
    (T.hasFDerivAt.comp x (hDf x)).fderiv
  have hH : ∀ x, HasFDerivAt (gradient f) (hessianOperator f x) x := by
    intro x
    rw [hHeq x]; exact T.hasFDerivAt.comp x (hDf x)
  have hHinner : ∀ x v w, ⟪hessianOperator f x v, w⟫ = fderiv ℝ (fderiv ℝ f) x v w := by
    intro x v w
    rw [hHeq x]; exact hTinner _ _
  have hsymm : ∀ x v w, ⟪hessianOperator f x v, w⟫ = ⟪v, hessianOperator f x w⟫ := by
    intro x v w
    have hs := (hf_smooth.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
    rw [hHinner, real_inner_comm, hHinner, hs v w]
  have hginner : ∀ x v, ⟪gradient f x, v⟫ = fderiv ℝ f x v := fun x v => hTinner _ _
  -- convexity
  have hconv : ∀ (x y : EuclideanSpace ℝ (Fin 2)) (t : ℝ), 0 ≤ t → t ≤ 1 →
      f ((1 - t) • x + t • y) ≤ (1 - t) * f x + t * f y := by
    intro x y t ht0 ht1
    have hc := hf_convex.2.2
    have hx : (x, f x) ∈ epigraph (liftRealtoEReal f) := by simp [epigraph, liftRealtoEReal]
    have hy : (y, f y) ∈ epigraph (liftRealtoEReal f) := by simp [epigraph, liftRealtoEReal]
    have := hc hx hy (sub_nonneg.2 ht1) ht0 (by ring)
    simpa [epigraph, liftRealtoEReal] using this
  have hfo : ∀ x y, f x + ⟪gradient f x, y - x⟫ ≤ f y := by
    intro x y
    have h1 : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const (y - x)).const_add x
    have hφ : HasDerivAt (fun t : ℝ => f (x + t • (y - x))) (fderiv ℝ f x (y - x)) 0 := by
      have h2 := (hfd (x + (0:ℝ) • (y - x))).hasFDerivAt.comp_hasDerivAt (0:ℝ) h1
      simpa using h2
    have hlim := hφ.tendsto_slope_zero_right
    have key : fderiv ℝ f x (y - x) ≤ f y - f x := by
      apply le_of_tendsto hlim
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
      have h3 := hconv x y t ht.1.le ht.2.le
      have e1 : (1 - t) • x + t • y = x + t • (y - x) := by
        rw [smul_sub, sub_smul, one_smul]; abel
      rw [e1] at h3
      simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
      rw [inv_mul_le_iff₀ ht.1]
      nlinarith
    rw [hginner]; linarith
  have hmono : ∀ x y, 0 ≤ ⟪gradient f x - gradient f y, x - y⟫ := by
    intro x y
    have h1 := hfo x y
    have h2 := hfo y x
    have : ⟪gradient f x - gradient f y, x - y⟫ =
        -(⟪gradient f x, y - x⟫ + ⟪gradient f y, x - y⟫) := by
      simp only [inner_sub_left, inner_sub_right]; ring
    rw [this]; linarith
  have hpsd : ∀ x v, 0 ≤ ⟪hessianOperator f x v, v⟫ := by
    intro x v
    have h1 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
    have h2 : HasDerivAt (fun t : ℝ => gradient f (x + t • v)) (hessianOperator f x v) 0 := by
      have := (hH (x + (0:ℝ) • v)).comp_hasDerivAt (0:ℝ) h1
      simpa using this
    have h3 : HasDerivAt (fun t : ℝ => ⟪v, gradient f (x + t • v)⟫) ⟪v, hessianOperator f x v⟫ 0 := by
      have := ((innerSL ℝ v).hasFDerivAt).comp_hasDerivAt (0:ℝ) h2
      simpa using this
    have hlim := h3.tendsto_slope_zero_right
    rw [real_inner_comm]
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
    have h4 : 0 ≤ t * ⟪gradient f (x + t • v) - gradient f x, v⟫ := by
      have := hmono (x + t • v) x
      rwa [add_sub_cancel_left, real_inner_smul_right] at this
    have h5 : 0 ≤ ⟪gradient f (x + t • v) - gradient f x, v⟫ := (mul_nonneg_iff_of_pos_left ht).1 h4
    have h6 : ⟪v, gradient f (x + t • v)⟫ - ⟪v, gradient f x⟫ =
        ⟪gradient f (x + t • v) - gradient f x, v⟫ := by
      rw [inner_sub_left, real_inner_comm v (gradient f (x + t • v)), real_inner_comm v (gradient f x)]
    rw [h6]; exact mul_nonneg (inv_nonneg.2 ht.le) h5
  -- the map Φ
  set Φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun x => x + gradient f x with hΦ_def
  have hΦexp : ∀ x y, ‖x - y‖ ≤ ‖Φ x - Φ y‖ := by
    intro x y
    have h := hmono x y
    have e1 : Φ x - Φ y = (x - y) + (gradient f x - gradient f y) := by simp only [hΦ_def]; abel
    have h2 : ‖x - y‖ ^ 2 ≤ ‖Φ x - Φ y‖ ^ 2 := by
      rw [e1, norm_add_sq_real]
      nlinarith [real_inner_comm (x - y) (gradient f x - gradient f y), norm_nonneg (gradient f x - gradient f y)]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
  have hΦinj : Function.Injective Φ := by
    intro x y hxy
    have := hΦexp x y
    rw [hxy, sub_self, norm_zero] at this
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  have hΦsurj : Function.Surjective Φ := by
    intro ξ
    let ψ : EuclideanSpace ℝ (Fin 2) → ℝ := fun x => ‖x‖ ^ 2 + 2 * f x - 2 * ⟪ξ, x⟫
    have hψcont : Continuous ψ := by
      have := hfd.continuous
      fun_prop
    have hψcoer : Filter.Tendsto ψ (Filter.cocompact _) Filter.atTop := by
      have hlow : ∀ x, ‖x‖ + (2 * f 0 - (‖gradient f 0 - ξ‖ + 1) ^ 2) ≤ ψ x := by
        intro x
        have h1 := hfo 0 x
        have h2 : -(‖gradient f 0 - ξ‖ * ‖x‖) ≤ ⟪gradient f 0 - ξ, x⟫ := by
          have := abs_real_inner_le_norm (gradient f 0 - ξ) x
          linarith [neg_abs_le ⟪gradient f 0 - ξ, x⟫]
        simp only [sub_zero, inner_sub_left] at h1 h2
        show ‖x‖ + (2 * f 0 - (‖gradient f 0 - ξ‖ + 1) ^ 2) ≤ ‖x‖ ^ 2 + 2 * f x - 2 * ⟪ξ, x⟫
        nlinarith [norm_nonneg x, norm_nonneg (gradient f 0 - ξ), sq_nonneg (‖x‖ - ‖gradient f 0 - ξ‖ - 1)]
      refine Filter.tendsto_atTop_mono hlow ?_
      exact Filter.tendsto_atTop_add_const_right _ _ tendsto_norm_cocompact_atTop
    obtain ⟨x, hx⟩ := hψcont.exists_forall_le hψcoer
    have hmin : IsLocalMin ψ x := Filter.Eventually.of_forall hx
    have hψd : HasFDerivAt ψ ((2:ℕ) • innerSL ℝ x + (2:ℝ) • fderiv ℝ f x - (2:ℝ) • innerSL ℝ ξ) x := by
      have h1 := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
      have h2 := ((hfd x).hasFDerivAt).const_smul (2:ℝ)
      have h3 := ((innerSL ℝ ξ).hasFDerivAt (x := x)).const_smul (2:ℝ)
      convert (h1.add h2).sub h3 using 1
    have h0 := hmin.hasFDerivAt_eq_zero hψd
    refine ⟨x, ?_⟩
    have hv : ∀ v, ⟪Φ x - ξ, v⟫ = 0 := by
      intro v
      have := congrArg (fun L => L v) h0
      simp only [hΦ_def, inner_add_left, inner_sub_left, hginner] at this ⊢
      simp at this
      linarith
    have := hv (Φ x - ξ)
    rw [inner_self_eq_zero] at this
    exact sub_eq_zero.1 this
  -- the derivative of Φ is invertible
  have hLinj : ∀ x, Function.Injective (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) + hessianOperator f x) := by
    intro x
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h0 : v + hessianOperator f x v = 0 := by simpa using hv
    have h1 : ⟪v + hessianOperator f x v, v⟫ = 0 := by rw [h0, inner_zero_left]
    rw [inner_add_left, real_inner_self_eq_norm_sq] at h1
    have := hpsd x v
    have h2 : ‖v‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖v‖]
    simpa using h2
  let L : EuclideanSpace ℝ (Fin 2) → (EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2)) := fun x =>
    ContinuousLinearEquiv.ofBijective (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) + hessianOperator f x)
      (LinearMap.ker_eq_bot.2 (hLinj x))
      (LinearMap.range_eq_top.2 (LinearMap.injective_iff_surjective.1 (hLinj x)))
  have hLcoe : ∀ x, (L x : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) + hessianOperator f x := fun x =>
    ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hΦd : ∀ x, HasFDerivAt Φ (L x : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) x := by
    intro x; rw [hLcoe]; exact (hasFDerivAt_id x).add (hH x)
  -- the inverse Ψ
  obtain ⟨Ψ, hΦΨ, hΨΦ⟩ : ∃ Ψ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      (∀ ξ, Φ (Ψ ξ) = ξ) ∧ (∀ x, Ψ (Φ x) = x) :=
    ⟨Function.surjInv hΦsurj, Function.surjInv_eq hΦsurj,
      fun x => hΦinj (Function.surjInv_eq hΦsurj _)⟩
  have hΨlip : ∀ ξ ζ, ‖Ψ ξ - Ψ ζ‖ ≤ ‖ξ - ζ‖ := by
    intro ξ ζ
    have := hΦexp (Ψ ξ) (Ψ ζ)
    rwa [hΦΨ, hΦΨ] at this
  have hΨL : LipschitzWith 1 Ψ := LipschitzWith.of_dist_le_mul fun ξ ζ => by
    simp only [dist_eq_norm, NNReal.coe_one, one_mul]; exact hΨlip ξ ζ
  set K : EuclideanSpace ℝ (Fin 2) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :=
    fun x => ((L x).symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) with hK_def
  have hΨd : ∀ x, HasFDerivAt Ψ (K x) (Φ x) := by
    intro x
    apply HasFDerivAt.of_local_left_inverse hΨL.continuous.continuousAt
    · rw [hΨΦ]; exact hΦd x
    · exact Filter.Eventually.of_forall hΦΨ
  have hKinv : ∀ x v, K x v + hessianOperator f x (K x v) = v := by
    intro x v
    have h := (L x).apply_symm_apply v
    have h2 : (L x : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) (K x v) = v := h
    rw [hLcoe] at h2
    simpa using h2
  -- coordinates
  have hHdec : ∀ x v, hessianOperator f x v = v 0 • hessianOperator f x u0 + v 1 • hessianOperator f x u1 := by
    intro x v
    conv_lhs => rw [hdecomp v]
    rw [map_add, map_smul, map_smul]
  have hkey : ∀ x, (K x u1) 0 = (K x u0) 1 ∧ (K x u1) 1 = 1 - (K x u0) 0 := by
    intro x
    have ha : 0 ≤ (hessianOperator f x u0) 0 := by
      have := hpsd x u0
      simpa [hu0, EuclideanSpace.inner_single_right] using this
    have hc : 0 ≤ (hessianOperator f x u1) 1 := by
      have := hpsd x u1
      simpa [hu1, EuclideanSpace.inner_single_right] using this
    have hb : (hessianOperator f x u1) 0 = (hessianOperator f x u0) 1 := by
      have := hsymm x u0 u1
      simp [hu0, hu1, EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_left] at this
      linarith
    have hdet : (hessianOperator f x u0) 0 * (hessianOperator f x u1) 1 -
        (hessianOperator f x u0) 1 * (hessianOperator f x u0) 1 = 1 := by
      have := hf_det x
      rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis, Matrix.det_fin_two] at this
      simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
        EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr, ContinuousLinearMap.coe_coe] at this
      rw [← hu0, ← hu1, hb] at this
      exact this
    have E1 := congrArg (fun w => w 0) (hKinv x u0)
    have E2 := congrArg (fun w => w 1) (hKinv x u0)
    have E3 := congrArg (fun w => w 0) (hKinv x u1)
    have E4 := congrArg (fun w => w 1) (hKinv x u1)
    simp only at E1 E2 E3 E4
    rw [hHdec x (K x u0)] at E1 E2
    rw [hHdec x (K x u1)] at E3 E4
    have hu00 : u0 0 = 1 := by simp [hu0]
    have hu01 : u0 1 = 0 := by simp [hu0]
    have hu10 : u1 0 = 0 := by simp [hu1]
    have hu11 : u1 1 = 1 := by simp [hu1]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hu00, hu01, hu10, hu11] at E1 E2 E3 E4
    rw [hb] at E1 E3
    exact jorgens_alg _ _ _ _ _ _ _ ha hc hdet E1 E2 E3 E4
  -- the complex function
  let e : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv
  have he0 : ∀ z, (e z) 0 = z.re := fun z => by simp [e]
  have he1 : ∀ z, (e z) 1 = z.im := fun z => by simp [e]
  have hes0 : ∀ v, (e.symm v).re = v 0 := fun v => by simp [e]
  have hes1 : ∀ v, (e.symm v).im = v 1 := fun v => by simp [e]
  have hne : ∀ z, ‖e z‖ = ‖z‖ := fun z => Complex.orthonormalBasisOneI.repr.norm_map z
  have hnes : ∀ v, ‖e.symm v‖ = ‖v‖ := fun v => Complex.orthonormalBasisOneI.repr.symm.norm_map v
  have hKe : ∀ x w, K x (e w) = w.re • K x u0 + w.im • K x u1 := by
    intro x w
    rw [hdecomp (e w), map_add, map_smul, map_smul, he0, he1]
  let F : ℂ → ℂ := fun z => Complex.conjCLE (e.symm ((2:ℝ) • Ψ (e z) - e z))
  let κ : EuclideanSpace ℝ (Fin 2) → ℂ := fun x => ⟨2 * (K x u0) 0 - 1, -(2 * (K x u0) 1)⟩
  have hFc : ∀ x, HasDerivAt F (κ x) (e.symm (Φ x)) := by
    intro x
    have h1 : HasFDerivAt (fun ξ => (2:ℝ) • Ψ ξ - ξ)
        ((2:ℝ) • K x - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) (e (e.symm (Φ x))) := by
      rw [e.apply_symm_apply]
      exact ((hΨd x).const_smul (2:ℝ)).sub (hasFDerivAt_id _)
    have h2 := (Complex.conjCLE.hasFDerivAt).comp _ ((e.symm.hasFDerivAt).comp _ (h1.comp _ e.hasFDerivAt))
    rw [hasDerivAt_iff_hasFDerivAt]
    refine hasFDerivAt_of_restrictScalars ℝ h2 ?_
    refine ContinuousLinearMap.ext fun w => ?_
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    rw [hKe x w]
    obtain ⟨h01, h11⟩ := hkey x
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.conj_re, hes0, PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply,
        smul_eq_mul, he0, h01, κ]
      ring
    · simp only [Complex.mul_im, Complex.conj_im, hes1, PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply,
        smul_eq_mul, he1, h11, κ]
      ring
  have hFdiff : Differentiable ℂ F := by
    intro z
    have := hFc (Ψ (e z))
    rw [hΦΨ, e.symm_apply_apply] at this
    exact this.differentiableAt
  have hFlip : LipschitzWith 3 F := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [dist_eq_norm, dist_eq_norm]
    simp only [F]
    rw [← map_sub, ← map_sub, Complex.conjCLE_apply, Complex.norm_conj, hnes]
    have h := hΨlip (e z) (e w)
    have e1 : (2:ℝ) • Ψ (e z) - e z - ((2:ℝ) • Ψ (e w) - e w) =
        (2:ℝ) • (Ψ (e z) - Ψ (e w)) - (e z - e w) := by
      rw [smul_sub]; abel
    rw [e1]
    have e2 : e z - e w = e (z - w) := (map_sub e z w).symm
    calc ‖(2:ℝ) • (Ψ (e z) - Ψ (e w)) - (e z - e w)‖
        ≤ ‖(2:ℝ) • (Ψ (e z) - Ψ (e w))‖ + ‖e z - e w‖ := norm_sub_le _ _
      _ = 2 * ‖Ψ (e z) - Ψ (e w)‖ + ‖e z - e w‖ := by rw [norm_smul]; norm_num
      _ ≤ 2 * ‖e z - e w‖ + ‖e z - e w‖ := by linarith
      _ = ((3 : NNReal) : ℝ) * ‖z - w‖ := by rw [e2, hne]; push_cast; ring
  -- Liouville
  have hFd' : Differentiable ℂ (deriv F) := fun z => ((hFdiff.analyticAt z).deriv).differentiableAt
  have hbdd : Bornology.IsBounded (Set.range (deriv F)) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨3, ?_⟩
    rintro _ ⟨z, rfl⟩
    have := norm_deriv_le_of_lipschitz (x₀ := z) hFlip
    simpa using this
  have hconst := hFd'.apply_eq_apply_of_bounded hbdd
  have hκconst : ∀ x, κ x = κ 0 := by
    intro x
    rw [← (hFc x).deriv, ← (hFc 0).deriv]
    exact hconst _ _
  -- the Hessian is constant
  have hKconst : ∀ x, K x = K 0 := by
    intro x
    have hk := hκconst x
    simp only [κ, Complex.mk.injEq] at hk
    obtain ⟨hk1, hk2⟩ := hk
    obtain ⟨h01x, h11x⟩ := hkey x
    obtain ⟨h01y, h11y⟩ := hkey 0
    have hA : K x u0 = K 0 u0 := by
      ext i; fin_cases i
      · show (K x u0) 0 = (K 0 u0) 0
        linarith
      · show (K x u0) 1 = (K 0 u0) 1
        linarith
    have hB : K x u1 = K 0 u1 := by
      ext i; fin_cases i
      · show (K x u1) 0 = (K 0 u1) 0
        linarith
      · show (K x u1) 1 = (K 0 u1) 1
        linarith
    refine ContinuousLinearMap.ext fun v => ?_
    rw [hdecomp v, map_add, map_smul, map_smul, map_add, map_smul, map_smul, hA, hB]
  have hHconst : ∀ x, hessianOperator f x = hessianOperator f 0 := by
    intro x
    refine ContinuousLinearMap.ext fun v => ?_
    have h1 : (L 0) ((L 0).symm ((L x) v)) = (L x) v := (L 0).apply_symm_apply _
    have h2 : (L x).symm ((L x) v) = v := (L x).symm_apply_apply v
    have h3 : (L 0).symm ((L x) v) = (L x).symm ((L x) v) := by
      have := congrArg (fun M => M ((L x) v)) (hKconst x)
      exact this.symm
    rw [h3, h2] at h1
    have h4 : (L 0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) v =
        (L x : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) v := h1
    rw [hLcoe, hLcoe] at h4
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply] at h4
    exact (add_left_cancel h4).symm
  -- conclusion
  set A := hessianOperator f 0 with hA_def
  have hgaff : ∀ x, gradient f x = A x + gradient f 0 := by
    have hd : ∀ x, HasFDerivAt (fun y => gradient f y - A y) (0 : _ →L[ℝ] _) x := by
      intro x
      have := (hH x).sub A.hasFDerivAt
      rwa [hHconst x, sub_self] at this
    intro x
    have := is_const_of_fderiv_eq_zero (𝕜 := ℝ) (fun y => (hd y).differentiableAt)
      (fun y => (hd y).fderiv) x 0
    simp only [map_zero, sub_zero] at this
    rw [← this]; abel
  have hAsymm : ∀ v w, ⟪A v, w⟫ = ⟪v, A w⟫ := hsymm 0
  have hfquad : ∀ x, f x = 1 / 2 * ⟪A x, x⟫ + ⟪gradient f 0, x⟫ + f 0 := by
    have hd : ∀ x, HasFDerivAt (fun y => f y - 1 / 2 * ⟪A y, y⟫ - ⟪gradient f 0, y⟫)
        (0 : _ →L[ℝ] ℝ) x := by
      intro x
      have h1 := (hfd x).hasFDerivAt
      have h2 := ((A.hasFDerivAt (x := x)).inner ℝ (hasFDerivAt_id x)).const_mul (1 / 2 : ℝ)
      have h3 := (innerSL ℝ (gradient f 0)).hasFDerivAt (x := x)
      have h4 := (h1.sub h2).sub h3
      convert h4 using 1
      refine ContinuousLinearMap.ext fun v => ?_
      have hg := hginner x v
      rw [hgaff x, inner_add_left] at hg
      simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        fderivInnerCLM_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul, id_eq]
      rw [← hg, hAsymm v x, real_inner_comm v (A x)]
      ring
    intro x
    have := is_const_of_fderiv_eq_zero (𝕜 := ℝ) (fun y => (hd y).differentiableAt)
      (fun y => (hd y).fderiv) x 0
    simp only [map_zero, inner_zero_right, mul_zero, sub_zero] at this
    linarith
  refine ⟨(A : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)), gradient f 0, f 0, ?_, ?_⟩
  · intro x
    rw [hHconst x]
  · intro x
    rw [ContinuousLinearMap.coe_coe]
    exact hfquad x

end FCA_chap_D_ex6
