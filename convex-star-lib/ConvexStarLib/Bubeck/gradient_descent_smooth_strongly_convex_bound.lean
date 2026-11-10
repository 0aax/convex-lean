import ConvexStarLib.Defs

/-!
# `gradient_descent_smooth_strongly_convex_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/gradient_descent_smooth_strongly_convex_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace gradient_descent_smooth_strongly_convex_bound`, so the main result is `gradient_descent_smooth_strongly_convex_bound.gradient_descent_smooth_strongly_convex_bound`.
-/

namespace gradient_descent_smooth_strongly_convex_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open scoped Gradient RealInnerProductSpace


theorem gradient_descent_smooth_strongly_convex_bound {n t : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (α β : ℝ)
  (x_star : EuclideanSpace ℝ (Fin n))
  (hβ_pos : β > 0)
  (hα_pos : α > 0)
  (hf_differentiable : Differentiable ℝ f)
  (hf_beta_smooth : LipschitzWith (Real.toNNReal β) (gradient f))
  (hf_strongly_convex : StrongConvexOn Set.univ α f)
  (h_gd_seq : IsGradientDescentSequence f x (2 / (α + β)))
  (hx_star : IsMinOn f Set.univ x_star) :
  let κ := β / α
  f (x t) - f x_star ≤ (β / 2) * Real.exp (- (4 * t)/ (κ + 1)) * ‖x 0 - x_star‖ ^ 2 := by
  intro κ
  have hκ : κ = β / α := rfl
  -- derivative of `f` along a line
  have hline : ∀ (p v : EuclideanSpace ℝ (Fin n)) (s : ℝ),
      HasDerivAt (fun r : ℝ => f (p + r • v)) ⟪∇ f (p + s • v), v⟫ s := by
    intro p v s
    have h1 : HasFDerivAt f (InnerProductSpace.toDual ℝ _ (∇ f (p + s • v))) (p + s • v) :=
      (hf_differentiable (p + s • v)).hasGradientAt.hasFDerivAt
    have h2 : HasDerivAt (fun r : ℝ => p + r • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add p
    have := h1.comp_hasDerivAt s h2
    simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using this
  -- the gradient vanishes at the minimizer
  have hgrad0 : ∇ f x_star = 0 := by
    have hmin : IsLocalMin f x_star := hx_star.isLocalMin Filter.univ_mem
    have := hmin.fderiv_eq_zero
    simp [gradient, this]
  -- first-order lower bound from strong convexity
  have hlow : ∀ p v : EuclideanSpace ℝ (Fin n), f p + ⟪∇ f p, v⟫ + α / 2 * ‖v‖ ^ 2 ≤ f (p + v) := by
    intro p v
    have hd := hline p v 0
    have ht := hd.tendsto_slope_zero_right
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul] at ht
    have hc : Filter.Tendsto (fun s : ℝ => f (p + v) - f p - (1 - s) * (α / 2) * ‖v‖ ^ 2)
        (𝓝[>] 0) (𝓝 (f (p + v) - f p - (1 - 0) * (α / 2) * ‖v‖ ^ 2)) := by
      apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
      apply Continuous.tendsto
      fun_prop
    have hle : ∀ᶠ s in 𝓝[>] (0:ℝ), s⁻¹ * (f (p + s • v) - f p) ≤
        f (p + v) - f p - (1 - s) * (α / 2) * ‖v‖ ^ 2 := by
      filter_upwards [Ioo_mem_nhdsGT one_pos] with s hs
      obtain ⟨hs0, hs1⟩ := hs
      have := hf_strongly_convex.2 (Set.mem_univ p) (Set.mem_univ (p + v))
        (sub_nonneg.2 hs1.le) hs0.le (by ring)
      have e1 : (1 - s) • p + s • (p + v) = p + s • v := by module
      have e2 : ‖p - (p + v)‖ = ‖v‖ := by rw [sub_add_cancel_left, norm_neg]
      rw [e1, e2, smul_eq_mul, smul_eq_mul] at this
      rw [inv_mul_le_iff₀ hs0]
      nlinarith
    have := le_of_tendsto_of_tendsto ht hc hle
    linarith
  -- quadratic upper bound (descent lemma) from smoothness
  have hup : ∀ p v : EuclideanSpace ℝ (Fin n), f (p + v) ≤ f p + ⟪∇ f p, v⟫ + β / 2 * ‖v‖ ^ 2 := by
    intro p v
    let g : ℝ → ℝ := fun s => f (p + s • v) - s * ⟪∇ f p, v⟫ - β / 2 * s ^ 2 * ‖v‖ ^ 2
    have hg : ∀ s, HasDerivAt g (⟪∇ f (p + s • v), v⟫ - ⟪∇ f p, v⟫ - β * s * ‖v‖ ^ 2) s := by
      intro s
      have h1 := hline p v s
      have h2 : HasDerivAt (fun s : ℝ => s * ⟪∇ f p, v⟫) ⟪∇ f p, v⟫ s := by
        simpa using (hasDerivAt_id s).mul_const ⟪∇ f p, v⟫
      have h3 : HasDerivAt (fun s : ℝ => β / 2 * s ^ 2 * ‖v‖ ^ 2) (β * s * ‖v‖ ^ 2) s := by
        have := ((hasDerivAt_pow 2 s).const_mul (β / 2)).mul_const (‖v‖ ^ 2)
        convert this using 1
        push_cast
        ring
      exact (h1.sub h2).sub h3
    have hcont : ContinuousOn g (Set.Icc 0 1) :=
      (continuous_iff_continuousAt.2 fun s => (hg s).continuousAt).continuousOn
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g _ zero_lt_one hcont (fun s _ => hg s)
    have hc0 : 0 < c := hc.1
    have hlip : ‖∇ f (p + c • v) - ∇ f p‖ ≤ β * ‖c • v‖ := by
      have := hf_beta_smooth.dist_le_mul (p + c • v) p
      rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, Real.coe_toNNReal _ hβ_pos.le] at this
      exact this
    have hinner : ⟪∇ f (p + c • v), v⟫ - ⟪∇ f p, v⟫ ≤ β * c * ‖v‖ ^ 2 := by
      rw [← inner_sub_left]
      have := real_inner_le_norm (∇ f (p + c • v) - ∇ f p) v
      rw [norm_smul, Real.norm_of_nonneg hc0.le] at hlip
      nlinarith [norm_nonneg v]
    have : g 1 - g 0 ≤ 0 := by
      rw [sub_zero, div_one] at hcd
      rw [← hcd]; linarith
    simp only [g] at this
    simp at this
    linarith
  -- co-coercivity type inequality relative to the minimizer
  have hcoco : ∀ z : EuclideanSpace ℝ (Fin n),
      α * β * ‖z - x_star‖ ^ 2 + ‖∇ f z‖ ^ 2 ≤ (α + β) * ⟪∇ f z, z - x_star⟫ := by
    intro z
    set d := z - x_star with hd
    set g := ∇ f z with hg
    set u := g - α • d with hu
    have hz : z = x_star + d := by rw [hd]; abel
    have hgu : g = u + α • d := by rw [hu]; abel
    have hfam : ∀ s : ℝ, (2 * s - (β - α) * s ^ 2) * ‖u‖ ^ 2 ≤ ⟪u, d⟫ := by
      intro s
      have A1 := hlow z (s • u - d)
      have A2 := hup x_star (s • u)
      have B1 := hlow x_star (d - s • u)
      have B2 := hup z (-(s • u))
      have e1 : z + (s • u - d) = x_star + s • u := by rw [hz]; abel
      have e2 : x_star + (d - s • u) = z + -(s • u) := by rw [hz]; abel
      rw [e1] at A1
      rw [e2] at B1
      rw [hgrad0, inner_zero_left] at A2 B1
      rw [← hg, hgu] at A1 B2
      simp only [norm_sub_sq_real, norm_neg, norm_smul, inner_sub_right, inner_add_left,
        inner_smul_left, inner_smul_right, inner_neg_right, real_inner_self_eq_norm_sq,
        Real.norm_eq_abs, mul_pow, sq_abs, RCLike.conj_to_real] at A1 A2 B1 B2
      have hc := real_inner_comm d u
      rw [hc] at A1 ⊢
      linarith
    have key : ‖u‖ ^ 2 ≤ (β - α) * ⟪u, d⟫ := by
      rcases lt_or_ge 0 (β - α) with hL | hL
      · have h := hfam (1 / (β - α))
        have h' : (2 * (1 / (β - α)) - (β - α) * (1 / (β - α)) ^ 2) = 1 / (β - α) := by
          field_simp; ring
        rw [h', div_mul_eq_mul_div, one_mul, div_le_iff₀ hL] at h
        linarith
      · have hu0 : ‖u‖ ^ 2 = 0 := by
          by_contra hne
          have hpos : 0 < ‖u‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
          have h0 := hfam 0
          set b := ⟪u, d⟫
          set c := ‖u‖ ^ 2
          have h1 := hfam (b / c + 1)
          have hs : (b / c + 1) * c = b + c := by field_simp
          have hs1 : 1 ≤ b / c + 1 := by
            have : 0 ≤ b / c := div_nonneg (by linarith) hpos.le
            linarith
          nlinarith [mul_nonneg (neg_nonneg.2 hL) (mul_nonneg (by linarith : (0:ℝ) ≤ b / c + 1)
            (by linarith : (0:ℝ) ≤ b + c))]
        have : u = 0 := by
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hu0
          exact norm_eq_zero.1 this
        rw [this, inner_zero_left, norm_zero]
        simp
    rw [hu] at key
    simp only [norm_sub_sq_real, norm_smul, inner_sub_left, inner_smul_left, inner_smul_right,
      real_inner_self_eq_norm_sq, Real.norm_eq_abs, mul_pow, sq_abs, RCLike.conj_to_real] at key
    nlinarith
  -- one step of gradient descent contracts the distance to the minimizer
  have hstep : ∀ k, x (k + 1) = gradientDescentStep f (x k) (2 / (α + β)) := h_gd_seq
  have hcontr : ∀ z : EuclideanSpace ℝ (Fin n),
      ‖gradientDescentStep f z (2 / (α + β)) - x_star‖ ^ 2 ≤
        ((β - α) / (β + α)) ^ 2 * ‖z - x_star‖ ^ 2 := by
    intro z
    have h := hcoco z
    have e : gradientDescentStep f z (2 / (α + β)) - x_star
        = (z - x_star) - (2 / (α + β)) • ∇ f z := by
      unfold gradientDescentStep; abel
    have hη : (0:ℝ) ≤ 2 / (α + β) := by positivity
    rw [e, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_of_nonneg hη, mul_pow,
      real_inner_comm]
    have hid : ((β - α) / (β + α)) ^ 2 * ‖z - x_star‖ ^ 2 - (‖z - x_star‖ ^ 2
        - 2 * (2 / (α + β) * ⟪∇ f z, z - x_star⟫) + (2 / (α + β)) ^ 2 * ‖∇ f z‖ ^ 2)
        = 4 / (α + β) ^ 2 * ((α + β) * ⟪∇ f z, z - x_star⟫ - α * β * ‖z - x_star‖ ^ 2
          - ‖∇ f z‖ ^ 2) := by
      have : α + β ≠ 0 := by positivity
      have : β + α ≠ 0 := by positivity
      field_simp
      ring
    have hpos : 0 ≤ 4 / (α + β) ^ 2 * ((α + β) * ⟪∇ f z, z - x_star⟫
        - α * β * ‖z - x_star‖ ^ 2 - ‖∇ f z‖ ^ 2) := by
      apply mul_nonneg
      · positivity
      · linarith
    linarith
  have hiter : ∀ k : ℕ,
      ‖x k - x_star‖ ^ 2 ≤ (((β - α) / (β + α)) ^ 2) ^ k * ‖x 0 - x_star‖ ^ 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [hstep k, pow_succ]
      calc ‖gradientDescentStep f (x k) (2 / (α + β)) - x_star‖ ^ 2
          ≤ ((β - α) / (β + α)) ^ 2 * ‖x k - x_star‖ ^ 2 := hcontr (x k)
        _ ≤ ((β - α) / (β + α)) ^ 2 * ((((β - α) / (β + α)) ^ 2) ^ k * ‖x 0 - x_star‖ ^ 2) := by
          gcongr
        _ = (((β - α) / (β + α)) ^ 2) ^ k * ((β - α) / (β + α)) ^ 2 * ‖x 0 - x_star‖ ^ 2 := by
          ring
  -- function value gap is controlled by the squared distance
  have hfinal : f (x t) - f x_star ≤ β / 2 * ‖x t - x_star‖ ^ 2 := by
    have := hup x_star (x t - x_star)
    rw [hgrad0, inner_zero_left, add_sub_cancel] at this
    linarith
  rcases le_or_gt α β with hab | hab
  · have hq0 : 0 ≤ (β - α) / (β + α) := div_nonneg (by linarith) (by linarith)
    have hq1 : (β - α) / (β + α) ≤ Real.exp (-(2 * α / (α + β))) := by
      have h1 := Real.add_one_le_exp (-(2 * α / (α + β)))
      have h2 : (β - α) / (β + α) = -(2 * α / (α + β)) + 1 := by
        have : α + β ≠ 0 := by positivity
        have : β + α ≠ 0 := by positivity
        field_simp
        ring
      linarith
    have hq2 : ((β - α) / (β + α)) ^ 2 ≤ Real.exp (-(4 * α / (α + β))) := by
      calc ((β - α) / (β + α)) ^ 2 ≤ Real.exp (-(2 * α / (α + β))) ^ 2 := by gcongr
        _ = Real.exp (-(4 * α / (α + β))) := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
    have hqt : (((β - α) / (β + α)) ^ 2) ^ t ≤ Real.exp (-(4 * t) / (κ + 1)) := by
      calc (((β - α) / (β + α)) ^ 2) ^ t ≤ Real.exp (-(4 * α / (α + β))) ^ t := by gcongr
        _ = Real.exp (t * (-(4 * α / (α + β)))) := by rw [← Real.exp_nat_mul]
        _ = Real.exp (-(4 * t) / (κ + 1)) := by
          congr 1
          rw [hκ]
          have : α + β ≠ 0 := by positivity
          have : α ≠ 0 := by positivity
          have : β / α + 1 ≠ 0 := by positivity
          field_simp
          ring
    calc f (x t) - f x_star ≤ β / 2 * ‖x t - x_star‖ ^ 2 := hfinal
      _ ≤ β / 2 * ((((β - α) / (β + α)) ^ 2) ^ t * ‖x 0 - x_star‖ ^ 2) := by
        gcongr
        exact hiter t
      _ ≤ β / 2 * (Real.exp (-(4 * t) / (κ + 1)) * ‖x 0 - x_star‖ ^ 2) := by
        gcongr
      _ = (β / 2) * Real.exp (- (4 * t)/ (κ + 1)) * ‖x 0 - x_star‖ ^ 2 := by ring
  · -- if `α > β` the space collapses to the single point `x_star`
    have hzero : ‖x t - x_star‖ ^ 2 ≤ 0 := by
      have h1 := hlow x_star (x t - x_star)
      have h2 := hup x_star (x t - x_star)
      nlinarith [sq_nonneg ‖x t - x_star‖]
    have : 0 ≤ β / 2 * Real.exp (-(4 * t) / (κ + 1)) * ‖x 0 - x_star‖ ^ 2 := by positivity
    nlinarith

end gradient_descent_smooth_strongly_convex_bound
