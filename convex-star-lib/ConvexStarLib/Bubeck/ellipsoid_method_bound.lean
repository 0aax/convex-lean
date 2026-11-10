import ConvexStarLib.Defs

/-!
# `ellipsoid_method_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/ellipsoid_method_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace ellipsoid_method_bound`, so the main result is `ellipsoid_method_bound.ellipsoid_method_bound`.
-/

namespace ellipsoid_method_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


lemma ell_numeric (n : ℕ) (hn : 2 ≤ n) :
    ((n:ℝ)^2 / ((n:ℝ)^2 - 1)) ^ n * (((n:ℝ) - 1) / ((n:ℝ) + 1)) ≤ Real.exp (-1 / (n:ℝ)) := by
  have hn' : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have hn0 : (n:ℝ) ≠ 0 := ne_of_gt hnpos
  set x : ℝ := 1 / (n:ℝ) with hx
  have hxpos : 0 < x := by positivity
  have hnx : (n:ℝ) * x = 1 := by rw [hx]; field_simp
  have hxle : x ≤ 1/2 := by
    rw [hx, div_le_div_iff₀ hnpos (by norm_num)]; linarith
  have hx2 : |x^2| < 1 := by
    rw [abs_of_pos (by positivity)]; nlinarith
  have hx1 : |x| < 1 := by
    rw [abs_of_pos hxpos]; linarith
  have h1 := (Real.hasSum_pow_div_log_of_abs_lt_one hx2).mul_left (n:ℝ)
  have h2 := Real.hasSum_log_sub_log_of_abs_lt_one hx1
  have h3 := h1.sub h2
  have h4 : HasSum (fun k : ℕ => if k = 0 then -x else 0) (-x) := hasSum_ite_eq 0 (-x)
  have key : (n:ℝ) * -Real.log (1 - x^2) - (Real.log (1 + x) - Real.log (1 - x)) ≤ -x := by
    refine hasSum_le ?_ h3 h4
    intro k
    have hpow : (n:ℝ) * (x^2)^(k+1) = x^(2*k+1) := by
      rw [← pow_mul, show 2 * (k+1) = (2*k+1) + 1 by ring, pow_succ]
      rw [mul_comm, mul_assoc, mul_comm x, hnx, mul_one]
    have e : (n:ℝ) * ((x^2)^(k+1) / ((k:ℝ)+1)) - 2 * (1 / (2 * (k:ℝ) + 1)) * x^(2*k+1)
        = - (x^(2*k+1) / (((k:ℝ)+1) * (2*(k:ℝ)+1))) := by
      rw [← mul_div_assoc, hpow]
      field_simp
      ring
    rw [e]
    split_ifs with hk
    · subst hk; simp
    · have : 0 ≤ x^(2*k+1) / (((k:ℝ)+1) * (2*(k:ℝ)+1)) := by positivity
      linarith
  have h1mx2 : 0 < 1 - x^2 := by nlinarith
  have h1px : 0 < 1 + x := by linarith
  have h1mx : 0 < 1 - x := by linarith
  have e1 : (n:ℝ)^2/((n:ℝ)^2-1) = (1-x^2)⁻¹ := by
    have : (n:ℝ)^2 - 1 ≠ 0 := by nlinarith
    rw [hx]; field_simp
  have e2 : ((n:ℝ)-1)/((n:ℝ)+1) = (1-x)/(1+x) := by
    have : (n:ℝ) + 1 ≠ 0 := by linarith
    have : (n:ℝ) - 1 ≠ 0 := by linarith
    rw [hx]; field_simp
  have e3 : -1/(n:ℝ) = -x := by rw [hx]; ring
  rw [e1, e2, e3]
  calc ((1-x^2)⁻¹)^n * ((1-x)/(1+x))
      = Real.exp ((n:ℝ) * -Real.log (1 - x^2) - (Real.log (1 + x) - Real.log (1 - x))) := by
        rw [Real.exp_sub, Real.exp_sub, Real.exp_nat_mul, Real.exp_neg, Real.exp_log h1mx2,
          Real.exp_log h1px, Real.exp_log h1mx]
        field_simp
    _ ≤ Real.exp (-x) := Real.exp_le_exp.mpr key

lemma det_id_sub_proj {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) (k : ℝ) :
    LinearMap.det (LinearMap.id - k • LinearMap.smulRight (innerRightLM u) u) = 1 - k * ‖u‖ ^ 2 := by
  set b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  rw [← LinearMap.det_toMatrix b, map_sub, LinearMap.toMatrix_id, map_smul,
    LinearMap.toMatrix_smulRight, Matrix.vecMulVec_eq Unit]
  have key : (1 : Matrix (Fin n) (Fin n) ℝ) - k • (Matrix.replicateCol Unit (b.repr u) *
      Matrix.replicateRow Unit (⇑(innerRightLM u) ∘ ⇑b)) =
      1 + Matrix.replicateCol Unit (-k • ⇑(b.repr u)) * Matrix.replicateRow Unit (⇑(innerRightLM u) ∘ ⇑b) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.replicateCol, Matrix.replicateRow, sub_eq_add_neg, mul_assoc]
  rw [key, Matrix.det_one_add_replicateCol_mul_replicateRow]
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  simp only [dotProduct, b, innerRightLM, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
    OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_right, Pi.smul_apply, smul_eq_mul]
  rw [sub_eq_add_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp
  ring

lemma vol_ball_le_det {n : ℕ} (hn : 0 < n)
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (c z : EuclideanSpace ℝ (Fin n)) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : Metric.ball z δ ⊆ {y | ∃ v, ‖v‖ ≤ 1 ∧ y = c + A v}) :
    δ ^ n ≤ |LinearMap.det A| := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    infer_instance
  have hsub : Metric.ball (z - c) δ ⊆ A '' Metric.closedBall 0 1 := by
    intro y hy
    have : y + c ∈ Metric.ball z δ := by
      rw [Metric.mem_ball] at hy ⊢
      rwa [dist_eq_norm, show y + c - z = y - (z - c) by abel, ← dist_eq_norm]
    obtain ⟨v, hv, hveq⟩ := h this
    refine ⟨v, by simpa using hv, ?_⟩
    rw [← add_left_cancel_iff (a := c), ← hveq, add_comm]
  have hmono := MeasureTheory.measure_mono (μ := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) hsub
  rw [MeasureTheory.Measure.addHaar_ball _ _ hδ, MeasureTheory.Measure.addHaar_image_linearMap,
    MeasureTheory.Measure.addHaar_closedBall _ _ zero_le_one, finrank_euclideanSpace_fin] at hmono
  simp only [one_pow, ENNReal.ofReal_one, one_mul] at hmono
  have hpos : MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0 :=
    (Metric.measure_ball_pos _ _ zero_lt_one).ne'
  have hfin : MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have := (ENNReal.mul_le_mul_iff_left hpos hfin).mp hmono
  rwa [ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)] at this

lemma step_contain_core {n : ℕ} (hn : 1 < n) (σ τ : ℝ) (hσpos : 0 < σ)
    (hσ : σ ^ 2 = (n:ℝ)^2 / ((n:ℝ)^2 - 1))
    (hτpos : 0 < τ) (hτ : τ ^ 2 = ((n:ℝ) - 1) / ((n:ℝ) + 1))
    (u z : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (hz : ‖z‖ ≤ 1) (huz : inner ℝ u z ≤ 0) :
    ∃ z' : EuclideanSpace ℝ (Fin n), ‖z'‖ ≤ 1 ∧
      σ • (z' - ((1 - τ) * inner ℝ u z') • u) = z + (1 / ((n:ℝ) + 1)) • u := by
  have hN : (1:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hN1 : (0:ℝ) < (n:ℝ) - 1 := by linarith
  have hN2 : (0:ℝ) < (n:ℝ) + 1 := by linarith
  have hN3 : (0:ℝ) < (n:ℝ)^2 - 1 := by nlinarith
  have hσ2 : σ ^ 2 * ((n:ℝ)^2 - 1) = (n:ℝ)^2 := by
    rw [hσ]; field_simp
  have hτ2 : τ ^ 2 * ((n:ℝ) + 1) = (n:ℝ) - 1 := by
    rw [hτ]; field_simp
  set t : ℝ := inner ℝ u z with ht_def
  set q : ℝ := 1 / ((n:ℝ) + 1) with hq_def
  have hq : q * ((n:ℝ) + 1) = 1 := by rw [hq_def]; field_simp
  set s : ℝ := τ⁻¹ with hs_def
  have hsτ : s * τ = 1 := inv_mul_cancel₀ hτpos.ne'
  have hs2 : s ^ 2 * ((n:ℝ) - 1) = (n:ℝ) + 1 := by
    have h1 : s ^ 2 * ((n:ℝ) - 1) = s^2 * (τ ^ 2 * ((n:ℝ) + 1)) := by rw [hτ2]
    rw [h1]
    have h2 : s^2 * τ^2 = 1 := by rw [← mul_pow, hsτ, one_pow]
    linear_combination ((n:ℝ) + 1) * h2
  have ht_abs : |t| ≤ 1 := by
    have := abs_real_inner_le_norm u z
    rw [hu, one_mul] at this
    linarith
  have ht1 : -1 ≤ t := by linarith [neg_abs_le t]
  set b : ℝ := s * (t + q) - t with hb_def
  have hb : b - (1 - τ) * (t + b) = q := by
    rw [hb_def]
    linear_combination (t + q) * hsτ
  set w : EuclideanSpace ℝ (Fin n) := z + b • u with hw_def
  have huu : inner ℝ u u = (1:ℝ) := by
    rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have huw : inner ℝ u w = t + b := by
    rw [hw_def, inner_add_right, inner_smul_right, huu, mul_one]
  have hww : ‖w‖ ^ 2 = ‖z‖ ^ 2 + 2 * b * t + b ^ 2 := by
    rw [hw_def, norm_add_sq_real, norm_smul, inner_smul_right, real_inner_comm u z, mul_pow, hu,
      ← ht_def, Real.norm_eq_abs, sq_abs]
    ring
  refine ⟨σ⁻¹ • w, ?_, ?_⟩
  · -- norm
    have hkey : ‖w‖ ^ 2 ≤ σ ^ 2 := by
      rw [hww]
      have e1 : ‖z‖ ^ 2 + 2 * b * t + b ^ 2 = ‖z‖^2 - t^2 + s^2 * (t + q)^2 := by
        rw [hb_def]; ring
      rw [e1]
      have e2 : s ^ 2 * (t + q) ^ 2 * ((n:ℝ)^2 - 1) = (((n:ℝ) + 1) * t + 1) ^ 2 := by
        linear_combination (((n:ℝ) + 1) * (t + q) ^ 2) * hs2 + (2 * ((n:ℝ) + 1) * t + ((n:ℝ) + 1) * q + 1) * hq
      have hz2 : ‖z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg z) hz
      have hfin : (‖z‖ ^ 2 - t ^ 2 + s ^ 2 * (t + q) ^ 2) * ((n:ℝ)^2 - 1) ≤ σ ^ 2 * ((n:ℝ)^2 - 1) := by
        rw [hσ2]
        have h1 : 0 ≤ (1 - ‖z‖^2) * ((n:ℝ)^2 - 1) := mul_nonneg (by linarith) hN3.le
        have h2 : 0 ≤ (-t) * (t + 1) * ((n:ℝ) + 1) := mul_nonneg (mul_nonneg (by linarith) (by linarith)) hN2.le
        linear_combination e2 + h1 + 2 * h2
      exact le_of_mul_le_mul_right hfin hN3
    have hnorm : ‖σ⁻¹ • w‖ = σ⁻¹ * ‖w‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hσpos)]
    rw [hnorm]
    have hwσ : ‖w‖ ≤ σ := (sq_le_sq₀ (norm_nonneg w) hσpos.le).mp hkey
    rw [inv_mul_le_iff₀ hσpos]
    linarith
  · -- equation
    rw [inner_smul_right, huw, smul_sub, smul_inv_smul₀ hσpos.ne', smul_smul]
    have hsc : σ * ((1 - τ) * (σ⁻¹ * (t + b))) = (1 - τ) * (t + b) := by
      field_simp
    rw [hsc, hw_def, add_sub_assoc, ← sub_smul, hb]

noncomputable def Mmap {n : ℕ} (σ τ : ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  σ • (LinearMap.id - (1 - τ) • LinearMap.smulRight (innerRightLM u) u)

lemma Mmap_apply {n : ℕ} (σ τ : ℝ) (u v : EuclideanSpace ℝ (Fin n)) :
    Mmap σ τ u v = σ • (v - ((1 - τ) * inner ℝ u v) • u) := by
  simp [Mmap, innerRightLM, mul_smul]

lemma Mmap_adjoint {n : ℕ} (σ τ : ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    LinearMap.adjoint (Mmap σ τ u) = Mmap σ τ u := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  simp only [Mmap_apply, real_inner_smul_right, inner_sub_right, real_inner_comm]
  ring

lemma Mmap_Mmap {n : ℕ} (σ τ : ℝ) (u v : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) :
    Mmap σ τ u (Mmap σ τ u v) = (σ ^ 2) • (v - ((1 - τ ^ 2) * inner ℝ u v) • u) := by
  have huu : inner ℝ u u = (1:ℝ) := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  rw [Mmap_apply, Mmap_apply]
  simp only [real_inner_smul_right, inner_sub_right, huu]
  module

noncomputable def Aseq {n : ℕ} (R σ τ : ℝ) (w : ℕ → EuclideanSpace ℝ (Fin n)) :
    ℕ → (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  | 0 => R • LinearMap.id
  | s + 1 =>
    Aseq R σ τ w s ∘ₗ Mmap σ τ (‖LinearMap.adjoint (Aseq R σ τ w s) (w s)‖⁻¹ •
      LinearMap.adjoint (Aseq R σ τ w s) (w s))

lemma c_step {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (w c : EuclideanSpace ℝ (Fin n)) :
    (ellipsoidMethodStep w c (A ∘ₗ LinearMap.adjoint A)).1 =
      c - (1 / ((n:ℝ) + 1) * (1 / ‖LinearMap.adjoint A w‖)) • A (LinearMap.adjoint A w) := by
  have h1 : inner ℝ w (A (LinearMap.adjoint A w)) = ‖LinearMap.adjoint A w‖ ^ 2 := by
    rw [← LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
  simp only [ellipsoidMethodStep, LinearMap.comp_apply]
  rw [h1, Real.sqrt_sq (norm_nonneg _)]

lemma H_step {n : ℕ} (hn : 1 < n) (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin n)) (hg : LinearMap.adjoint A w ≠ 0)
    (σ τ : ℝ) (hσ : σ ^ 2 = (n:ℝ)^2 / ((n:ℝ)^2 - 1)) (hτ : τ ^ 2 = ((n:ℝ) - 1) / ((n:ℝ) + 1)) :
    ellipsoidAxesLinMap w (A ∘ₗ LinearMap.adjoint A) =
      (A ∘ₗ Mmap σ τ (‖LinearMap.adjoint A w‖⁻¹ • LinearMap.adjoint A w)) ∘ₗ
        LinearMap.adjoint (A ∘ₗ Mmap σ τ (‖LinearMap.adjoint A w‖⁻¹ • LinearMap.adjoint A w)) := by
  have hn' : (1:ℝ) < n := by exact_mod_cast hn
  have h1 : inner ℝ w (A (LinearMap.adjoint A w)) = ‖LinearMap.adjoint A w‖ ^ 2 := by
    rw [← LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
  rw [LinearMap.adjoint_comp, Mmap_adjoint]
  have hN : 0 < ‖LinearMap.adjoint A w‖ := norm_pos_iff.mpr hg
  have hu : ‖‖LinearMap.adjoint A w‖⁻¹ • LinearMap.adjoint A w‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hN.ne']
  apply LinearMap.ext
  intro v
  have h2 : inner ℝ w (A (LinearMap.adjoint A v)) =
      inner ℝ (LinearMap.adjoint A w) (LinearMap.adjoint A v) := by
    rw [← LinearMap.adjoint_inner_left]
  simp only [LinearMap.comp_apply, Mmap_Mmap σ τ _ _ hu]
  simp only [ellipsoidAxesLinMap, updateHRank1, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.smulRight_apply, innerRightLM, LinearMap.coe_mk,
    AddHom.coe_mk, h2, h1, map_smul, map_sub, real_inner_smul_left, hσ, hτ]
  have hn1 : (n:ℝ) + 1 ≠ 0 := by positivity
  have e : (1 - ((n:ℝ) - 1) / ((n:ℝ) + 1)) = 2 / ((n:ℝ) + 1) := by field_simp; ring
  rw [e]
  module

lemma inv_step {n : ℕ} (hn : 1 < n) (σ τ : ℝ) (hσpos : 0 < σ)
    (hσ2 : σ ^ 2 = (n:ℝ)^2 / ((n:ℝ)^2 - 1))
    (hτpos : 0 < τ) (hτ2 : τ ^ 2 = ((n:ℝ) - 1) / ((n:ℝ) + 1))
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (w c y : EuclideanSpace ℝ (Fin n)) (hg : LinearMap.adjoint A w ≠ 0)
    (hy : ∃ v, ‖v‖ ≤ 1 ∧ y = c + A v) (hcut : inner ℝ (y - c) w ≤ 0) :
    ∃ v, ‖v‖ ≤ 1 ∧ y = (c - (1 / ((n:ℝ) + 1) * (1 / ‖LinearMap.adjoint A w‖)) •
        A (LinearMap.adjoint A w)) +
      (A ∘ₗ Mmap σ τ (‖LinearMap.adjoint A w‖⁻¹ • LinearMap.adjoint A w)) v := by
  obtain ⟨z, hz, hyz⟩ := hy
  have hAz : inner ℝ z (LinearMap.adjoint A w) = inner ℝ (y - c) w := by
    rw [LinearMap.adjoint_inner_right, hyz, add_sub_cancel_left]
  generalize LinearMap.adjoint A w = g at *
  have hN : 0 < ‖g‖ := norm_pos_iff.mpr hg
  have hu : ‖‖g‖⁻¹ • g‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hN.ne']
  have huz : inner ℝ (‖g‖⁻¹ • g) z ≤ 0 := by
    rw [real_inner_smul_left, real_inner_comm, hAz]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hN.le) hcut
  obtain ⟨z', hz', hMz⟩ := step_contain_core hn σ τ hσpos hσ2 hτpos hτ2 _ z hu hz huz
  refine ⟨z', hz', ?_⟩
  rw [hyz, LinearMap.comp_apply, Mmap_apply, hMz]
  simp only [map_add, map_smul]
  module

set_option linter.unusedVariables false in
theorem ellipsoid_method_bound {n t : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (c : ℕ → EuclideanSpace ℝ (Fin n))
  (H : ℕ → (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
  (w : ℕ → EuclideanSpace ℝ (Fin n)) (x : ℕ → EuclideanSpace ℝ (Fin n))
  (B R r : ℝ)
  (x_star : EuclideanSpace ℝ (Fin n))
  (ht : (t : ℝ) ≥ 2 * (n : ℝ) ^ 2 * Real.log (R / r))
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (h𝓧_nonempty : Set.Nonempty (interior 𝓧))
  (h𝓧_contained : 𝓧 ⊆ Metric.closedBall 0 R ∧ Metric.ball 0 r ⊆ 𝓧)
  (hf_continuous : Continuous f)
  (hf_convex : ConvexOn ℝ 𝓧 f)
  (hf_bounded : ∀ x ∈ 𝓧, f x ≤ B ∧ f x ≥ -B)
  (h_cog_sequence : IsEllipsoidMethodSequence 𝓧 f c H w x R)
  (hx_star_mem : x_star ∈ 𝓧)
  (hx_star : IsMinOn f 𝓧 x_star)
  (hn : n > 1)
  (hR : R > 0)
  (hr : r > 0)
  (hB : B > 0) :
  (∃ s ≤ t, c s ∈ 𝓧) ∧
  f (x t) - f x_star ≤ ellipsoidGapBound B R r n t := by
  obtain ⟨hc0, hH0, hw0, hcs, hHs, hcase, hmin⟩ := h_cog_sequence
  refine ⟨?_, ?_⟩
  · obtain ⟨hxt, ⟨i, hi, hci⟩, -⟩ := hmin t
    exact ⟨i, hi, hci ▸ hxt⟩
  have hn' : (1:ℝ) < n := by exact_mod_cast hn
  have hn2 : (0:ℝ) < (n:ℝ)^2 - 1 := by nlinarith
  have hσ2 : Real.sqrt ((n:ℝ)^2 / ((n:ℝ)^2 - 1)) ^ 2 = (n:ℝ)^2 / ((n:ℝ)^2 - 1) :=
    Real.sq_sqrt (by positivity)
  have hτ2 : Real.sqrt (((n:ℝ) - 1) / ((n:ℝ) + 1)) ^ 2 = ((n:ℝ) - 1) / ((n:ℝ) + 1) :=
    Real.sq_sqrt (div_nonneg (by linarith) (by linarith))
  have hσpos : 0 < Real.sqrt ((n:ℝ)^2 / ((n:ℝ)^2 - 1)) := Real.sqrt_pos.mpr (by positivity)
  have hτpos : 0 < Real.sqrt (((n:ℝ) - 1) / ((n:ℝ) + 1)) :=
    Real.sqrt_pos.mpr (div_pos (by linarith) (by linarith))
  set σ := Real.sqrt ((n:ℝ)^2 / ((n:ℝ)^2 - 1)) with hσdef
  set τ := Real.sqrt (((n:ℝ) - 1) / ((n:ℝ) + 1)) with hτdef
  set A := Aseq (n := n) R σ τ w with hAdef
  have hA0 : A 0 = R • LinearMap.id := rfl
  have hAs : ∀ s, A (s + 1) = A s ∘ₗ Mmap σ τ (‖LinearMap.adjoint (A s) (w s)‖⁻¹ •
      LinearMap.adjoint (A s) (w s)) := fun s => rfl
  -- nondegeneracy
  have hg_of_det : ∀ s, LinearMap.det (A s) ≠ 0 → LinearMap.adjoint (A s) (w s) ≠ 0 := by
    intro s hdet hzero
    have hunit : IsUnit (A s) :=
      (LinearMap.isUnit_iff_isUnit_det (A s)).mpr (isUnit_iff_ne_zero.mpr hdet)
    obtain ⟨y, hy⟩ := ((Module.End.isUnit_iff (A s)).mp hunit).2 (w s)
    have h0 : inner ℝ (A s y) (w s) = (0:ℝ) := by
      rw [← LinearMap.adjoint_inner_right, hzero, inner_zero_right]
    rw [hy] at h0
    exact hw0 s (inner_self_eq_zero.mp h0)
  have key : ∀ s, H s = A s ∘ₗ LinearMap.adjoint (A s) ∧
      LinearMap.det (A s) = R ^ n * (σ ^ n * τ) ^ s := by
    intro s
    induction s with
    | zero =>
      refine ⟨?_, ?_⟩
      · have hadj : LinearMap.adjoint (R • (LinearMap.id : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] _)) =
            R • LinearMap.id := by
          symm
          rw [LinearMap.eq_adjoint_iff]
          intro a b
          simp [real_inner_smul_left, real_inner_smul_right]
        rw [hH0, hA0, hadj]
        apply LinearMap.ext
        intro v
        simp [smul_smul, sq]
      · rw [hA0, LinearMap.det_smul, LinearMap.det_id, finrank_euclideanSpace_fin]
        ring
    | succ s ih =>
      have hdet : LinearMap.det (A s) ≠ 0 := by rw [ih.2]; positivity
      have hg := hg_of_det s hdet
      have hN : 0 < ‖LinearMap.adjoint (A s) (w s)‖ := norm_pos_iff.mpr hg
      have hu : ‖‖LinearMap.adjoint (A s) (w s)‖⁻¹ • LinearMap.adjoint (A s) (w s)‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hN.ne']
      refine ⟨?_, ?_⟩
      · rw [hHs]
        simp only [ellipsoidMethodStep]
        rw [ih.1, hAs]
        exact H_step hn (A s) (w s) hg σ τ hσ2 hτ2
      · rw [hAs, LinearMap.det_comp, ih.2, Mmap, LinearMap.det_smul, det_id_sub_proj,
          finrank_euclideanSpace_fin, hu]
        ring
  have hc : ∀ s, c (s + 1) = c s - (1 / ((n:ℝ) + 1) * (1 / ‖LinearMap.adjoint (A s) (w s)‖)) •
      A s (LinearMap.adjoint (A s) (w s)) := by
    intro s
    rw [hcs, (key s).1, c_step]
  have inv : ∀ s, ∀ y ∈ 𝓧, (∀ i < s, c i ∈ 𝓧 → f y ≤ f (c i)) →
      ∃ v, ‖v‖ ≤ 1 ∧ y = c s + A s v := by
    intro s
    induction s with
    | zero =>
      intro y hy _
      refine ⟨R⁻¹ • y, ?_, ?_⟩
      · have := h𝓧_contained.1 hy
        rw [mem_closedBall_zero_iff] at this
        rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR, inv_mul_le_iff₀ hR]
        linarith
      · rw [hc0, hA0]
        simp [smul_smul, inv_mul_cancel₀ hR.ne']
    | succ s ih =>
      intro y hy hle
      have hcut : inner ℝ (y - c s) (w s) ≤ 0 := by
        rcases hcase s with ⟨hcs_mem, hsub⟩ | ⟨_, hsep⟩
        · have h1 := hsub y hy
          have h2 := hle s (Nat.lt_succ_self s) hcs_mem
          linarith
        · exact hsep hy
      have hdet : LinearMap.det (A s) ≠ 0 := by rw [(key s).2]; positivity
      rw [hc s, hAs]
      exact inv_step hn σ τ hσpos hσ2 hτpos hτ2 (A s) (w s) (c s) y (hg_of_det s hdet)
        (ih y hy (fun i hi => hle i (Nat.lt_succ_of_lt hi))) hcut
  -- final
  obtain ⟨hxt, -, hxmin⟩ := hmin t
  have hfx := hf_bounded _ hxt
  have hfs := hf_bounded _ hx_star_mem
  have hD0 : 0 ≤ f (x t) - f x_star := by
    have := isMinOn_iff.mp hx_star _ hxt
    linarith
  have hρ : σ ^ n * τ ≤ Real.exp (-1 / (2 * n)) := by
    have h1 := ell_numeric n (by omega)
    have h2 : (σ ^ n * τ) ^ 2 =
        ((n:ℝ)^2 / ((n:ℝ)^2 - 1)) ^ n * (((n:ℝ) - 1) / ((n:ℝ) + 1)) := by
      rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul, hσ2, hτ2]
    have h3 : Real.exp (-1 / (2 * n)) ^ 2 = Real.exp (-1 / n) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      field_simp
    rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero, h2, h3]
    exact h1
  set D := f (x t) - f x_star with hD
  set ε := D / (2 * B) with hε
  have hε0 : 0 ≤ ε := div_nonneg hD0 (by positivity)
  have hDε : D = 2 * B * ε := by rw [hε]; field_simp
  have hball : Metric.ball ((1 - ε) • x_star) (ε * r) ⊆ {y | ∃ v, ‖v‖ ≤ 1 ∧ y = c t + A t v} := by
    intro y hy
    have hεpos : 0 < ε := by
      rcases hε0.lt_or_eq with h | h
      · exact h
      · rw [← h, zero_mul] at hy
        simp at hy
    have hε1 : ε ≤ 1 := by
      rw [hε, div_le_one (by positivity)]
      linarith [hfx.1, hfs.2]
    set x' := ε⁻¹ • (y - (1 - ε) • x_star) with hx'
    have hx'mem : x' ∈ 𝓧 := by
      apply h𝓧_contained.2
      rw [Metric.mem_ball, dist_eq_norm] at hy
      rw [mem_ball_zero_iff, hx', norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_pos hεpos, inv_mul_lt_iff₀ hεpos]
      linarith
    have hyeq : y = (1 - ε) • x_star + ε • x' := by
      rw [hx', smul_smul, mul_inv_cancel₀ hεpos.ne', one_smul]
      abel
    have hymem : y ∈ 𝓧 := by
      rw [hyeq]
      exact h𝓧_convex hx_star_mem hx'mem (by linarith) hε0 (by ring)
    have hfy : f y ≤ f (x t) := by
      have hconv := hf_convex.2 hx_star_mem hx'mem (by linarith : 0 ≤ 1 - ε) hε0 (by ring)
      rw [← hyeq] at hconv
      simp only [smul_eq_mul] at hconv
      have hfx' := hf_bounded _ hx'mem
      have : f (x t) = f x_star + 2 * B * ε := by rw [← hDε, hD]; ring
      nlinarith
    exact inv t y hymem (fun i hi hci => le_trans hfy (hxmin i hi.le hci))
  have hvol := vol_ball_le_det (by omega) (A t) (c t) _ (ε * r) (by positivity) hball
  rw [(key t).2] at hvol
  have hfinal : ε * r ≤ R * Real.exp (-(t:ℝ) / (2 * (n:ℝ)^2)) := by
    have h1 : (ε * r) ^ n ≤ (R * Real.exp (-(t:ℝ) / (2 * (n:ℝ)^2))) ^ n := by
      calc (ε * r) ^ n ≤ |R ^ n * (σ ^ n * τ) ^ t| := hvol
        _ = R ^ n * (σ ^ n * τ) ^ t := abs_of_nonneg (by positivity)
        _ ≤ R ^ n * Real.exp (-1 / (2 * n)) ^ t := by gcongr
        _ = (R * Real.exp (-(t:ℝ) / (2 * (n:ℝ)^2))) ^ n := by
          rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
          congr 2
          field_simp
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega)).mp h1
  unfold ellipsoidGapBound ellipsoidDecay
  rw [le_div_iff₀ hr]
  calc D * r = 2 * B * (ε * r) := by rw [hDε]; ring
    _ ≤ 2 * B * (R * Real.exp (-(t:ℝ) / (2 * (n:ℝ)^2))) := by gcongr
    _ = 2 * B * R * Real.exp (-(t:ℝ) / (2 * (n:ℝ)^2)) := by ring

end ellipsoid_method_bound
