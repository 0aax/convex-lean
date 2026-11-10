import ConvexStarLib.Defs

/-!
# `newtons_method_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/newtons_method_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace newtons_method_bound`, so the main result is `newtons_method_bound.newtons_method_bound`.
-/

namespace newtons_method_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The gradient of a `C²` function has the Hessian operator as its derivative. -/
lemma nmb_hasFDerivAt_gradient {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f) (y : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (gradient f) (hessianOperator f y) y := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have h2 : ContDiff ℝ 1 (gradient f) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.contDiff.comp h1
  exact (h2.differentiable (by norm_num) y).hasFDerivAt

/-- Taylor-type estimate for the gradient, using the Lipschitz continuity of the Hessian. -/
lemma nmb_taylor {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (M : ℝ)
    (x_star y : EuclideanSpace ℝ (Fin n)) (hf : ContDiff ℝ 2 f) (hLip : IsLipschitzHess f M) :
    ‖gradient f y - gradient f x_star - hessianOperator f y (y - x_star)‖ ≤
      M / 2 * ‖y - x_star‖ ^ 2 := by
  set d := y - x_star with hd
  set A := hessianOperator f y with hA
  let g : ℝ → EuclideanSpace ℝ (Fin n) := fun t =>
    gradient f (x_star + t • d) - t • A d
  let g' : ℝ → EuclideanSpace ℝ (Fin n) := fun t =>
    hessianOperator f (x_star + t • d) d - A d
  have hg : ∀ t, HasDerivAt g (g' t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x_star + t • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x_star
    have h2 := (nmb_hasFDerivAt_gradient f hf (x_star + t • d)).comp_hasDerivAt t h1
    have h3 : HasDerivAt (fun t : ℝ => t • A d) (A d) t := by
      simpa using (hasDerivAt_id t).smul_const (A d)
    exact h2.sub h3
  let ψ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => g t - g 0
  let B : ℝ → ℝ := fun t => M * ‖d‖ ^ 2 * (t - t ^ 2 / 2)
  let B' : ℝ → ℝ := fun t => M * ‖d‖ ^ 2 * (1 - t)
  have hψ : ∀ t, HasDerivAt ψ (g' t) t := fun t => by
    simpa [ψ] using (hg t).sub_const (g 0)
  have hB : ∀ t, HasDerivAt B (B' t) t := by
    intro t
    have := ((hasDerivAt_id t).sub ((hasDerivAt_pow 2 t).div_const 2)).const_mul (M * ‖d‖ ^ 2)
    convert this using 1
    simp [B']
  have hbound : ∀ t ∈ Set.Ico (0:ℝ) 1, ‖g' t‖ ≤ B' t := by
    intro t ht
    have e : g' t = (hessianOperator f (x_star + t • d) - A) d := by
      simp [g']
    rw [e]
    calc ‖(hessianOperator f (x_star + t • d) - A) d‖
        ≤ ‖hessianOperator f (x_star + t • d) - A‖ * ‖d‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (M * ‖(x_star + t • d) - y‖) * ‖d‖ := by
        gcongr; exact hLip _ _
      _ = B' t := by
        have : (x_star + t • d) - y = (t - 1) • d := by
          simp only [hd, sub_smul, one_smul, smul_sub]
          abel
        rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith [ht.2])]
        simp only [B']
        ring
  have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := 1) (f := ψ)
    (f' := g')
    (fun t _ => (hψ t).continuousAt.continuousWithinAt)
    (fun t _ => (hψ t).hasDerivWithinAt) (by simp [ψ, B]) hB hbound
    (show (1:ℝ) ∈ Set.Icc (0:ℝ) 1 by simp)
  have e1 : ψ 1 = gradient f y - gradient f x_star - A d := by
    simp only [ψ, g, hd, one_smul, zero_smul, add_zero]
    abel_nf
  have e2 : B 1 = M / 2 * ‖d‖ ^ 2 := by
    simp only [B]; ring
  rw [e1, e2] at this
  exact this

/-- Lower bound on the quadratic form of the Hessian near `x_star`. -/
lemma nmb_coercive {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (M μ : ℝ)
    (x_star y v : EuclideanSpace ℝ (Fin n)) (hLip : IsLipschitzHess f M)
    (hpos : ∀ v, inner ℝ v (hessianOperator f x_star v) ≥ μ * ‖v‖^2) :
    (μ - M * ‖y - x_star‖) * ‖v‖ ^ 2 ≤ inner ℝ v (hessianOperator f y v) := by
  have h1 := hpos v
  have h2 : |inner ℝ v ((hessianOperator f y - hessianOperator f x_star) v)| ≤
      M * ‖y - x_star‖ * ‖v‖ ^ 2 := by
    calc |inner ℝ v ((hessianOperator f y - hessianOperator f x_star) v)|
        ≤ ‖v‖ * ‖(hessianOperator f y - hessianOperator f x_star) v‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ ‖v‖ * (‖hessianOperator f y - hessianOperator f x_star‖ * ‖v‖) := by
        gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖v‖ * (M * ‖y - x_star‖ * ‖v‖) := by
        gcongr; exact hLip _ _
      _ = M * ‖y - x_star‖ * ‖v‖ ^ 2 := by ring
  have h3 : inner ℝ v (hessianOperator f y v) = inner ℝ v (hessianOperator f x_star v) +
      inner ℝ v ((hessianOperator f y - hessianOperator f x_star) v) := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_right]; ring
  rw [h3]
  have := neg_abs_le (inner ℝ v ((hessianOperator f y - hessianOperator f x_star) v))
  nlinarith

/-- One Newton step contracts quadratically near `x_star`. -/
lemma nmb_step {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (M μ : ℝ)
    (x_star y : EuclideanSpace ℝ (Fin n)) (hM : M > 0) (hμ : μ > 0)
    (hf : ContDiff ℝ 2 f) (hLip : IsLipschitzHess f M)
    (hpos : ∀ v, inner ℝ v (hessianOperator f x_star v) ≥ μ * ‖v‖^2)
    (hgrad : gradient f x_star = 0)
    (hy : ‖y - x_star‖ ≤ μ / (2 * M)) :
    ‖newtonStep f y - x_star‖ ≤ (M / μ) * ‖y - x_star‖ ^ 2 := by
  have hMr : M * ‖y - x_star‖ ≤ μ / 2 := by
    rw [le_div_iff₀ (by positivity)] at hy
    linarith
  have hc : 0 < μ - M * ‖y - x_star‖ := by linarith
  have hlow : ∀ v, (μ - M * ‖y - x_star‖) * ‖v‖ ≤ ‖hessianOperator f y v‖ := by
    intro v
    have h1 := nmb_coercive f M μ x_star y v hLip hpos
    have h2 : inner ℝ v (hessianOperator f y v) ≤ ‖v‖ * ‖hessianOperator f y v‖ :=
      real_inner_le_norm _ _
    rcases eq_or_lt_of_le (norm_nonneg v) with h | h
    · rw [← h]; simp
    · nlinarith
  have hinj : Function.Injective (hessianOperator f y) := by
    intro u w huw
    have := hlow (u - w)
    rw [map_sub, huw, sub_self, norm_zero] at this
    have : ‖u - w‖ = 0 := by
      have := norm_nonneg (u - w)
      nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  have hinv : (hessianOperator f y).IsInvertible :=
    ⟨(LinearEquiv.ofInjectiveEndo ((hessianOperator f y) : _ →ₗ[ℝ] _) hinj).toContinuousLinearEquiv,
      by ext v; rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = (hessianOperator f y).inverse (gradient f y) := ⟨_, rfl⟩
  have hAu : hessianOperator f y u = gradient f y :=
    ((hinv.inverse_apply_eq (x := u) (y := gradient f y)).mp hu.symm).symm
  have hstep : newtonStep f y - x_star = (y - x_star) - u := by
    rw [newtonStep, ← hu, sub_right_comm]
  have hAw : hessianOperator f y ((y - x_star) - u) =
      hessianOperator f y (y - x_star) - gradient f y := by
    rw [map_sub, hAu]
  have hk := nmb_taylor f M x_star y hf hLip
  rw [hgrad, sub_zero] at hk
  have h1 : ‖hessianOperator f y ((y - x_star) - u)‖ ≤ M / 2 * ‖y - x_star‖ ^ 2 := by
    rw [hAw, norm_sub_rev]; exact hk
  have h2 := hlow ((y - x_star) - u)
  rw [hstep]
  have h3 : (μ / 2) * ‖(y - x_star) - u‖ ≤ M / 2 * ‖y - x_star‖ ^ 2 := by
    have := norm_nonneg ((y - x_star) - u)
    nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
  nlinarith


set_option linter.unusedVariables false in
theorem newtons_method_bound {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
  (M μ : ℝ) (x_star : EuclideanSpace ℝ (Fin n))
  (hM : M > 0) (hμ : μ > 0)
  (hx_init : ‖x 0 - x_star‖ ≤ μ / (2 * M))
  (hf_in_c2 : ContDiff ℝ 2 f)
  (hf_convex : ConvexOn ℝ Set.univ f)
  (hf_lipschitz_hessian : IsLipschitzHess f M)
  (hf_pos_hessian : ∀ v, inner ℝ v (hessianOperator f x_star v) ≥ μ * ‖v‖^2)
  (h_ps_seq : IsNewtonsMethodSequence f x)
  (hx_star : IsMinOn f Set.univ x_star) :
  (∀ k, ∀ v, v ≠ 0 → 0 < inner ℝ v (hessianOperator f (x k) v)) ∧
  (∀ k, ‖x (k + 1) - x_star‖ ≤ (M / μ) * ‖x k - x_star‖ ^ 2) ∧
  Filter.Tendsto x Filter.atTop (𝓝 x_star) := by
  -- the gradient vanishes at the minimizer
  have hgrad_star : gradient f x_star = 0 := by
    have hmin : IsLocalMin f x_star := hx_star.isLocalMin Filter.univ_mem
    have h0 := hmin.fderiv_eq_zero
    simp only [gradient, h0, map_zero]
  have step := fun y => nmb_step f M μ x_star y hM hμ hf_in_c2 hf_lipschitz_hessian
    hf_pos_hessian hgrad_star
  -- induction
  have bound : ∀ k, ‖x k - x_star‖ ≤ μ / (2 * M) * (1 / 2) ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, mul_one]; exact hx_init
    | succ k ih =>
      have hk : ‖x k - x_star‖ ≤ μ / (2 * M) := by
        calc ‖x k - x_star‖ ≤ μ / (2 * M) * (1 / 2) ^ k := ih
          _ ≤ μ / (2 * M) * 1 := by
            gcongr
            exact pow_le_one₀ (by norm_num) (by norm_num)
          _ = μ / (2 * M) := mul_one _
      rw [h_ps_seq k]
      have := step (x k) hk
      calc ‖newtonStep f (x k) - x_star‖ ≤ (M / μ) * ‖x k - x_star‖ ^ 2 := this
        _ = ((M / μ) * ‖x k - x_star‖) * ‖x k - x_star‖ := by ring
        _ ≤ ((M / μ) * (μ / (2 * M))) * (μ / (2 * M) * (1 / 2) ^ k) := by
          gcongr
        _ = μ / (2 * M) * (1 / 2) ^ (k + 1) := by
          field_simp
          ring
  have hsmall : ∀ k, ‖x k - x_star‖ ≤ μ / (2 * M) := by
    intro k
    calc ‖x k - x_star‖ ≤ μ / (2 * M) * (1 / 2) ^ k := bound k
      _ ≤ μ / (2 * M) * 1 := by
        gcongr
        exact pow_le_one₀ (by norm_num) (by norm_num)
      _ = μ / (2 * M) := mul_one _
  refine ⟨?_, ?_, ?_⟩
  · intro k v hv
    have h1 := nmb_coercive f M μ x_star (x k) v hf_lipschitz_hessian hf_pos_hessian
    have h2 := hsmall k
    have hMr : M * ‖x k - x_star‖ ≤ μ / 2 := by
      rw [le_div_iff₀ (by positivity)] at h2
      linarith
    have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have : 0 < (μ - M * ‖x k - x_star‖) * ‖v‖ ^ 2 := by
      apply _root_.mul_pos
      · linarith
      · positivity
    linarith
  · intro k
    rw [h_ps_seq k]
    exact step (x k) (hsmall k)
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Filter.Tendsto (fun k : ℕ => μ / (2 * M) * (1 / 2 : ℝ) ^ k) Filter.atTop
        (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2 : ℝ)) (by norm_num)
        (by norm_num)).const_mul (μ / (2 * M))
      simpa using this
    exact squeeze_zero (fun k => norm_nonneg _) bound hlim

end newtons_method_bound
