import ConvexStarLib.Defs

/-!
# `nesterov_smooth_strongly_convex_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/nesterov_smooth_strongly_convex_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace nesterov_smooth_strongly_convex_bound`, so the main result is `nesterov_smooth_strongly_convex_bound.nesterov_smooth_strongly_convex_bound`.
-/

namespace nesterov_smooth_strongly_convex_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open RealInnerProductSpace


section NesterovAux

open Filter InnerProductSpace

lemma nesterov_aux_sc_first_order {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {α : ℝ} (hf : StrongConvexOn Set.univ α f) (x y : E)
    (hfx : DifferentiableAt ℝ f x) :
    f x + ⟪gradient f x, y - x⟫ + α / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  set d := y - x with hd
  have hφ : HasDerivAt (fun t : ℝ => f (x + t • d)) ⟪gradient f x, d⟫ 0 := by
    have h1 : HasFDerivAt f (toDual ℝ E (gradient f x)) (x + (0:ℝ) • d) := by
      simpa using hfx.hasGradientAt.hasFDerivAt
    have h2 : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const d).const_add x
    have := h1.comp_hasDerivAt (0:ℝ) h2
    simpa [toDual_apply_apply] using this
  have hlim := hφ.tendsto_slope_zero_right
  have hbound : ∀ᶠ t in 𝓝[>] (0:ℝ),
      t⁻¹ • ((fun t : ℝ => f (x + t • d)) (0 + t) - (fun t : ℝ => f (x + t • d)) 0)
        ≤ f y - f x - (1 - t) * (α / 2) * ‖d‖ ^ 2 := by
    have : Set.Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT one_pos
    filter_upwards [this] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hconv := hf.2 (Set.mem_univ x) (Set.mem_univ y) (show (0:ℝ) ≤ 1 - t by linarith)
      ht0.le (show (1 - t) + t = 1 by ring)
    have heq : (1 - t) • x + t • y = x + t • d := by
      rw [hd]; module
    rw [heq, norm_sub_rev, ← hd] at hconv
    simp only [smul_eq_mul] at hconv
    simp only [smul_eq_mul, zero_add, zero_smul, add_zero]
    rw [inv_mul_le_iff₀ ht0]
    nlinarith [hconv]
  have hlim2 : Tendsto (fun t : ℝ => f y - f x - (1 - t) * (α / 2) * ‖d‖ ^ 2) (𝓝[>] 0)
      (𝓝 (f y - f x - (1 - 0) * (α / 2) * ‖d‖ ^ 2)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply Continuous.tendsto
    fun_prop
  have := le_of_tendsto_of_tendsto hlim hlim2 hbound
  linarith

lemma nesterov_aux_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {L : ℝ} (hf : Differentiable ℝ f)
    (hlip : ∀ u v, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖) (x y : E) :
    f y ≤ f x + ⟪gradient f x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set d := y - x with hd
  let h : ℝ → ℝ := fun t => f (x + t • d) - t * ⟪gradient f x, d⟫ - L / 2 * t ^ 2 * ‖d‖ ^ 2
  let h' : ℝ → ℝ := fun t => ⟪gradient f (x + t • d), d⟫ - ⟪gradient f x, d⟫ - L * t * ‖d‖ ^ 2
  have hderiv : ∀ t, HasDerivAt h (h' t) t := by
    intro t
    have h1 : HasFDerivAt f (toDual ℝ E (gradient f (x + t • d))) (x + t • d) :=
      (hf _).hasGradientAt.hasFDerivAt
    have h2 : HasDerivAt (fun s : ℝ => x + s • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have h3 := h1.comp_hasDerivAt t h2
    have h4 : HasDerivAt (fun s : ℝ => s * ⟪gradient f x, d⟫) ⟪gradient f x, d⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient f x, d⟫
    have h5 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖d‖ ^ 2) (L * t * ‖d‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖d‖ ^ 2)
      convert this using 1
      push_cast
      ring
    have := (h3.sub h4).sub h5
    convert this using 1
  have hcont : ContinuousOn h (Set.Icc 0 1) :=
    fun t _ => (hderiv t).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hceq⟩ :=
    exists_hasDerivAt_eq_slope h h' (zero_lt_one) hcont (fun t _ => hderiv t)
  have hc_nonpos : h' c ≤ 0 := by
    simp only [h']
    have hl := hlip (x + c • d) x
    rw [show x + c • d - x = c • d by abel, norm_smul, Real.norm_eq_abs,
      abs_of_pos hc.1] at hl
    have hinner : ⟪gradient f (x + c • d), d⟫ - ⟪gradient f x, d⟫
        = ⟪gradient f (x + c • d) - gradient f x, d⟫ := by
      rw [inner_sub_left]
    have hcs := real_inner_le_norm (gradient f (x + c • d) - gradient f x) d
    rw [hinner]
    have hd0 := norm_nonneg d
    calc ⟪gradient f (x + c • d) - gradient f x, d⟫ - L * c * ‖d‖ ^ 2
        ≤ ‖gradient f (x + c • d) - gradient f x‖ * ‖d‖ - L * c * ‖d‖ ^ 2 := by linarith
      _ ≤ L * (c * ‖d‖) * ‖d‖ - L * c * ‖d‖ ^ 2 := by
          gcongr
      _ = 0 := by ring
  have : h 1 ≤ h 0 := by
    rw [sub_zero, div_one] at hceq
    linarith
  simp only [h] at this
  simp at this
  rw [show x + d = y by rw [hd]; abel] at this
  linarith

lemma nesterov_aux_norm_sq_three {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b g : E) (p q w : ℝ) :
    ‖p • a + q • b + w • g‖ ^ 2 = p ^ 2 * ‖a‖ ^ 2 + q ^ 2 * ‖b‖ ^ 2 + w ^ 2 * ‖g‖ ^ 2
      + 2 * p * q * ⟪a, b⟫ + 2 * p * w * ⟪a, g⟫ + 2 * q * w * ⟪b, g⟫ := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [real_inner_comm a b, real_inner_comm a g, real_inner_comm b g]
  ring

lemma nesterov_aux_norm_sq_two {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (p q : ℝ) :
    ‖p • a + q • b‖ ^ 2 = p ^ 2 * ‖a‖ ^ 2 + q ^ 2 * ‖b‖ ^ 2 + 2 * p * q * ⟪a, b⟫ := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [real_inner_comm a b]
  ring

lemma nesterov_aux_key_ineq (α r Fx Fy Fy' A B G AB AG BG : ℝ) (hα : 0 < α) (hr : 1 ≤ r)
    (ha : Fy' ≤ Fx - G / (2 * (α * r ^ 2)))
    (hb : Fx + (BG - AG) ≤ Fy)
    (hc : Fx - AG + α / 2 * A ≤ 0)
    (hd : 0 ≤ A + B - 2 * AB) :
    Fy' + α / 2 * (r ^ 2 * A + (-(r - 1)) ^ 2 * B + (-(r / (α * r ^ 2))) ^ 2 * G
      + 2 * r * (-(r - 1)) * AB + 2 * r * (-(r / (α * r ^ 2))) * AG
      + 2 * (-(r - 1)) * (-(r / (α * r ^ 2))) * BG)
    ≤ (1 - 1 / r) * (Fy + α / 2 * ((1 + r) ^ 2 * A + (-r) ^ 2 * B + 2 * (1 + r) * (-r) * AB)) := by
  have hr0 : 0 < r := by linarith
  have h1 : 0 ≤ 1 - 1 / r := by
    rw [sub_nonneg, div_le_one hr0]; exact hr
  have key : (1 - 1 / r) * (Fy + α / 2 * ((1 + r) ^ 2 * A + (-r) ^ 2 * B + 2 * (1 + r) * (-r) * AB))
      - (Fy' + α / 2 * (r ^ 2 * A + (-(r - 1)) ^ 2 * B + (-(r / (α * r ^ 2))) ^ 2 * G
        + 2 * r * (-(r - 1)) * AB + 2 * r * (-(r / (α * r ^ 2))) * AG
        + 2 * (-(r - 1)) * (-(r / (α * r ^ 2))) * BG))
      = (Fx - G / (2 * (α * r ^ 2)) - Fy') + (1 - 1 / r) * (Fy - (Fx + (BG - AG)))
        + (1 / r) * (-(Fx - AG + α / 2 * A)) + α / 2 * (r - 1) * (A + B - 2 * AB) := by
    field_simp
    ring
  have t1 : 0 ≤ Fx - G / (2 * (α * r ^ 2)) - Fy' := by linarith
  have t2 : 0 ≤ (1 - 1 / r) * (Fy - (Fx + (BG - AG))) := mul_nonneg h1 (by linarith)
  have t3 : 0 ≤ (1 / r) * (-(Fx - AG + α / 2 * A)) := mul_nonneg (by positivity) (by linarith)
  have t4 : 0 ≤ α / 2 * (r - 1) * (A + B - 2 * AB) :=
    mul_nonneg (mul_nonneg (by positivity) (by linarith)) hd
  have : 0 ≤ (1 - 1 / r) * (Fy + α / 2 * ((1 + r) ^ 2 * A + (-r) ^ 2 * B + 2 * (1 + r) * (-r) * AB))
      - (Fy' + α / 2 * (r ^ 2 * A + (-(r - 1)) ^ 2 * B + (-(r / (α * r ^ 2))) ^ 2 * G
        + 2 * r * (-(r - 1)) * AB + 2 * r * (-(r / (α * r ^ 2))) * AG
        + 2 * (-(r - 1)) * (-(r / (α * r ^ 2))) * BG)) := by
    rw [key]; linarith
  linarith

end NesterovAux

theorem nesterov_smooth_strongly_convex_bound {n t : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (y : ℕ → EuclideanSpace ℝ (Fin n))
    (α β : ℝ)
    (x_star : EuclideanSpace ℝ (Fin n))
    (hβ_pos : β > 0)
    (hα_pos : α > 0)
    (hxy_init : x 0 = (y 0))
    (hf_strongly_convex : StrongConvexOn Set.univ α f)
    (hf_differentiable : Differentiable ℝ f)
    (hf_beta_smooth : LipschitzWith (Real.toNNReal β) (gradient f))
    (h_nesterov_seq : IsNesterovSequence f x y α β)
    (hx_star : IsMinOn f Set.univ x_star) :
    let κ := β / α
    f (y t) - f x_star
    ≤ ((α + β) / 2) * ‖x 0 - x_star‖ ^ 2 * Real.exp (-1 * t / (Real.sqrt κ)) := by
  intro κ
  have hβ' : (Real.toNNReal β : ℝ) = β := Real.coe_toNNReal β hβ_pos.le
  have hlip : ∀ u v : EuclideanSpace ℝ (Fin n),
      ‖gradient f u - gradient f v‖ ≤ β * ‖u - v‖ := by
    intro u v
    have := hf_beta_smooth.dist_le_mul u v
    rwa [dist_eq_norm, dist_eq_norm, hβ'] at this
  have hdesc : ∀ u v : EuclideanSpace ℝ (Fin n),
      f v ≤ f u + ⟪gradient f u, v - u⟫ + β / 2 * ‖v - u‖ ^ 2 :=
    fun u v => nesterov_aux_descent hf_differentiable hlip u v
  have hsc : ∀ u v : EuclideanSpace ℝ (Fin n),
      f u + ⟪gradient f u, v - u⟫ + α / 2 * ‖v - u‖ ^ 2 ≤ f v :=
    fun u v => nesterov_aux_sc_first_order hf_strongly_convex u v (hf_differentiable u)
  have hgrad_star : gradient f x_star = 0 := by
    have hmin : IsLocalMin f x_star := hx_star.isLocalMin Filter.univ_mem
    simp [gradient, hmin.fderiv_eq_zero]
  by_cases hαβ : α ≤ β
  · have hκ1 : 1 ≤ κ := by
      show 1 ≤ β / α
      rw [le_div_iff₀ hα_pos]; linarith
    set r := Real.sqrt κ with hr_def
    have hr1 : 1 ≤ r := by rw [hr_def]; exact Real.one_le_sqrt.mpr hκ1
    have hr0 : 0 < r := by linarith
    have hr2 : r ^ 2 = κ := Real.sq_sqrt (by linarith)
    have hβeq : β = α * r ^ 2 := by
      rw [hr2]; show β = α * (β / α); field_simp
    have hq : 0 ≤ 1 - 1 / r := by
      rw [sub_nonneg, div_le_one hr0]; exact hr1
    set v : ℕ → EuclideanSpace ℝ (Fin n) := fun s => x s + r • (x s - y s) with hv_def
    set E : ℕ → ℝ := fun s => f (y s) - f x_star + α / 2 * ‖v s - x_star‖ ^ 2 with hE_def
    have hstep : ∀ s, E (s + 1) ≤ (1 - 1 / r) * E s := by
      intro s
      have hy1 : y (s + 1) = x s - (1 / β) • gradient f (x s) := by
        rw [h_nesterov_seq.1 s]; rfl
      have hx1 : x (s + 1) = (1 + (r - 1) / (r + 1)) • y (s + 1) - ((r - 1) / (r + 1)) • y s := by
        rw [h_nesterov_seq.2 s, hy1]; rfl
      set g := gradient f (x s) with hg
      set a := x s - x_star with ha_def
      set b := y s - x_star with hb_def
      have hr1' : r + 1 ≠ 0 := (by linarith : (0:ℝ) < r + 1).ne'
      have hβ0 : β ≠ 0 := hβ_pos.ne'
      have hv1 : v (s + 1) - x_star
          = r • a + (-(r - 1)) • b + (-(r / (α * r ^ 2))) • g := by
        simp only [hv_def]
        rw [hx1, hy1, ha_def, hb_def, ← hβeq]
        match_scalars <;> field_simp <;> ring
      have hvs : v s - x_star = (1 + r) • a + (-r) • b := by
        simp only [hv_def]
        rw [ha_def, hb_def]
        module
      have hN1 : ‖v (s + 1) - x_star‖ ^ 2 = r ^ 2 * ‖a‖ ^ 2 + (-(r - 1)) ^ 2 * ‖b‖ ^ 2
          + (-(r / (α * r ^ 2))) ^ 2 * ‖g‖ ^ 2 + 2 * r * (-(r - 1)) * ⟪a, b⟫
          + 2 * r * (-(r / (α * r ^ 2))) * ⟪a, g⟫
          + 2 * (-(r - 1)) * (-(r / (α * r ^ 2))) * ⟪b, g⟫ := by
        rw [hv1]; exact nesterov_aux_norm_sq_three a b g _ _ _
      have hN0 : ‖v s - x_star‖ ^ 2
          = (1 + r) ^ 2 * ‖a‖ ^ 2 + (-r) ^ 2 * ‖b‖ ^ 2 + 2 * (1 + r) * (-r) * ⟪a, b⟫ := by
        rw [hvs]; exact nesterov_aux_norm_sq_two a b _ _
      have ha : f (y (s + 1)) - f x_star
          ≤ (f (x s) - f x_star) - ‖g‖ ^ 2 / (2 * (α * r ^ 2)) := by
        have h := hdesc (x s) (y (s + 1))
        have e1 : y (s + 1) - x s = (-(1 / β)) • g := by rw [hy1]; module
        rw [e1, real_inner_smul_right, norm_smul, real_inner_self_eq_norm_sq, Real.norm_eq_abs,
          mul_pow, sq_abs] at h
        rw [← hβeq]
        have e2 : -(1 / β) * ‖g‖ ^ 2 + β / 2 * ((-(1 / β)) ^ 2 * ‖g‖ ^ 2)
            = -(‖g‖ ^ 2 / (2 * β)) := by
          field_simp; ring
        linarith
      have hb : (f (x s) - f x_star) + (⟪b, g⟫ - ⟪a, g⟫) ≤ f (y s) - f x_star := by
        have h := hsc (x s) (y s)
        rw [← hg] at h
        have e1 : y s - x s = b - a := by rw [ha_def, hb_def]; abel
        rw [e1, inner_sub_right, real_inner_comm b g, real_inner_comm a g] at h
        have : 0 ≤ α / 2 * ‖b - a‖ ^ 2 := by positivity
        linarith
      have hc : (f (x s) - f x_star) - ⟪a, g⟫ + α / 2 * ‖a‖ ^ 2 ≤ 0 := by
        have h := hsc (x s) x_star
        rw [← hg] at h
        have e1 : x_star - x s = -a := by rw [ha_def]; abel
        rw [e1, inner_neg_right, norm_neg, real_inner_comm a g] at h
        linarith
      have hd : 0 ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * ⟪a, b⟫ := by
        have := norm_sub_sq_real a b
        nlinarith [sq_nonneg ‖a - b‖]
      have hk := nesterov_aux_key_ineq α r (f (x s) - f x_star) (f (y s) - f x_star)
        (f (y (s + 1)) - f x_star) (‖a‖ ^ 2) (‖b‖ ^ 2) (‖g‖ ^ 2) ⟪a, b⟫ ⟪a, g⟫ ⟪b, g⟫
        hα_pos hr1 ha hb hc hd
      simp only [hE_def]
      rw [hN1, hN0]
      linarith
    have hiter : ∀ s, E s ≤ (1 - 1 / r) ^ s * E 0 := by
      intro s
      induction s with
      | zero => simp
      | succ k ih =>
        calc E (k + 1) ≤ (1 - 1 / r) * E k := hstep k
          _ ≤ (1 - 1 / r) * ((1 - 1 / r) ^ k * E 0) := mul_le_mul_of_nonneg_left ih hq
          _ = (1 - 1 / r) ^ (k + 1) * E 0 := by ring
    have hE0 : E 0 ≤ (α + β) / 2 * ‖x 0 - x_star‖ ^ 2 := by
      have hv0 : v 0 = x 0 := by simp [hv_def, hxy_init]
      have h1 := hdesc x_star (x 0)
      rw [hgrad_star, inner_zero_left] at h1
      simp only [hE_def, hv0, ← hxy_init]
      linarith
    have hfinal : f (y t) - f x_star ≤ E t := by
      simp only [hE_def]
      have : 0 ≤ α / 2 * ‖v t - x_star‖ ^ 2 := by positivity
      linarith
    have hexp : (1 - 1 / r) ^ t ≤ Real.exp (-1 * t / r) := by
      have h1 : 1 - 1 / r ≤ Real.exp (-1 / r) := by
        have := Real.add_one_le_exp (-1 / r)
        have e : -1 / r + 1 = 1 - 1 / r := by ring
        linarith
      calc (1 - 1 / r) ^ t ≤ Real.exp (-1 / r) ^ t := pow_le_pow_left₀ hq h1 t
        _ = Real.exp (-1 * t / r) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
    calc f (y t) - f x_star ≤ E t := hfinal
      _ ≤ (1 - 1 / r) ^ t * E 0 := hiter t
      _ ≤ (1 - 1 / r) ^ t * ((α + β) / 2 * ‖x 0 - x_star‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hE0 (pow_nonneg hq t)
      _ ≤ Real.exp (-1 * t / r) * ((α + β) / 2 * ‖x 0 - x_star‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = ((α + β) / 2) * ‖x 0 - x_star‖ ^ 2 * Real.exp (-1 * t / r) := by ring
  · push_neg at hαβ
    have hall : ∀ d : EuclideanSpace ℝ (Fin n), d = 0 := by
      intro d
      have h1 := hsc 0 d
      have h2 := hdesc 0 d
      have h3 : α / 2 * ‖d - 0‖ ^ 2 ≤ β / 2 * ‖d - 0‖ ^ 2 := by linarith
      rw [sub_zero] at h3
      have h4 : ‖d‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖d‖]
      have h5 : ‖d‖ = 0 := by
        have := sq_nonneg ‖d‖
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h4 this)
      exact norm_eq_zero.mp h5
    have : y t = x_star := by rw [hall (y t), hall x_star]
    rw [this, sub_self]
    positivity

end nesterov_smooth_strongly_convex_bound
