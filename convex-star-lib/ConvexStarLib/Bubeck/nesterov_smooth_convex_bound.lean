import ConvexStarLib.Defs

/-!
# `nesterov_smooth_convex_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/nesterov_smooth_convex_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace nesterov_smooth_convex_bound`, so the main result is `nesterov_smooth_convex_bound.nesterov_smooth_convex_bound`.
-/

namespace nesterov_smooth_convex_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {n : ℕ}

theorem nesterov_smooth_convex_bound {n t : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n)) (y : ℕ → EuclideanSpace ℝ (Fin n))
  (β : ℝ) (lambda : ℕ → ℝ) (x_star : EuclideanSpace ℝ (Fin n))
  (hβ_pos : β > 0) (ht_one : t ≥ 1)
  (hxy_init : x 0 = (y 0))
  (hf_convex : ConvexOn ℝ Set.univ f)
  (hf_differentiable : Differentiable ℝ f)
  (hf_beta_smooth : LipschitzWith (Real.toNNReal β) (gradient f))
  (h_nesterov_seq : IsNesterovSequenceAlphaZero f x y β lambda)
  (hx_star : IsMinOn f Set.univ x_star) :
  f (y t) - f x_star
  ≤ (2 * β) * ‖x 0 - x_star‖^2 / t^2 := by
  obtain ⟨hy, hx, hl0, hl⟩ := h_nesterov_seq
  have hβne : β ≠ 0 := ne_of_gt hβ_pos
  -- Derivative of `f` along a line.
  have hderiv : ∀ a d : EuclideanSpace ℝ (Fin n), ∀ s : ℝ,
      HasDerivAt (fun r : ℝ => f (a + r • d)) (inner ℝ (gradient f (a + s • d)) d) s := by
    intro a d s
    have h1 : HasFDerivAt f (fderiv ℝ f (a + s • d)) (a + s • d) :=
      (hf_differentiable _).hasFDerivAt
    have h2 : HasDerivAt (fun r : ℝ => a + r • d) d s := by
      simpa using ((hasDerivAt_id s).smul_const d).const_add a
    rw [inner_gradient_left (hf_differentiable _)]
    exact h1.comp_hasDerivAt s h2
  -- First-order condition for convexity.
  have hconv : ∀ a b : EuclideanSpace ℝ (Fin n),
      f a + inner ℝ (gradient f a) (b - a) ≤ f b := by
    intro a b
    have hc : ConvexOn ℝ Set.univ (fun r : ℝ => f (a + r • (b - a))) := by
      have := hf_convex.comp_affineMap (AffineMap.lineMap a b)
      rw [Set.preimage_univ] at this
      convert this using 1
      ext r
      simp [AffineMap.lineMap_apply, add_comm]
    have h := hc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one
      (by simpa using hderiv a (b - a) 0)
    simp [slope] at h
    linarith
  -- Descent lemma.
  have hβ' : ((Real.toNNReal β : NNReal) : ℝ) = β := Real.coe_toNNReal β hβ_pos.le
  have hdesc : ∀ a d : EuclideanSpace ℝ (Fin n),
      f (a + d) ≤ f a + inner ℝ (gradient f a) d + β / 2 * ‖d‖ ^ 2 := by
    intro a d
    have hφ : ∀ r : ℝ, HasDerivAt
        (fun r : ℝ => f (a + r • d) - r * inner ℝ (gradient f a) d - β / 2 * r ^ 2 * ‖d‖ ^ 2)
        (inner ℝ (gradient f (a + r • d)) d - inner ℝ (gradient f a) d - β * r * ‖d‖ ^ 2) r := by
      intro r
      have := ((hderiv a d r).sub ((hasDerivAt_id' r).mul_const (inner ℝ (gradient f a) d))).sub
        (((hasDerivAt_pow 2 r).const_mul (β / 2)).mul_const (‖d‖ ^ 2))
      convert this using 1
      push_cast
      ring
    obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope
      (fun r : ℝ => f (a + r • d) - r * inner ℝ (gradient f a) d - β / 2 * r ^ 2 * ‖d‖ ^ 2)
      (fun r => inner ℝ (gradient f (a + r • d)) d - inner ℝ (gradient f a) d - β * r * ‖d‖ ^ 2)
      zero_lt_one (fun r _ => (hφ r).continuousAt.continuousWithinAt) (fun r _ => hφ r)
    have h1 : inner ℝ (gradient f (a + c • d)) d - inner ℝ (gradient f a) d
        = inner ℝ (gradient f (a + c • d) - gradient f a) d := by rw [inner_sub_left]
    have h2 := real_inner_le_norm (gradient f (a + c • d) - gradient f a) d
    have h3 := hf_beta_smooth.norm_sub_le (a + c • d) a
    rw [hβ'] at h3
    have h4 : ‖a + c • d - a‖ = c * ‖d‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]
    rw [h4] at h3
    have h5 : ‖gradient f (a + c • d) - gradient f a‖ * ‖d‖ ≤ β * (c * ‖d‖) * ‖d‖ :=
      mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    simp only [sub_zero, div_one, one_smul, zero_smul, add_zero, zero_mul, one_mul,
      one_pow, mul_one] at hc'
    nlinarith
  -- Combined inequality (Bubeck, Lemma 3.6), in a division-free form.
  have hA : ∀ a b : EuclideanSpace ℝ (Fin n),
      f (a - (1 / β) • gradient f a) - f b
        ≤ β * inner ℝ ((1 / β) • gradient f a) (a - b)
          - β / 2 * ‖(1 / β) • gradient f a‖ ^ 2 := by
    intro a b
    set v := (1 / β) • gradient f a with hv
    have hgv : gradient f a = β • v := by
      rw [hv, smul_smul, mul_one_div_cancel hβne, one_smul]
    have h1 := hdesc a (-v)
    have h2 := hconv a b
    rw [← sub_eq_add_neg, norm_neg, hgv, inner_neg_right, real_inner_smul_left,
      real_inner_self_eq_norm_sq] at h1
    rw [hgv, real_inner_smul_left] at h2
    have h3 : inner ℝ v (b - a) = - inner ℝ v (a - b) := by
      rw [← inner_neg_right, neg_sub]
    rw [h3] at h2
    linarith
  -- Unfolding the recursion.
  have hy' : ∀ s, y (s + 1) = x s - (1 / β) • gradient f (x s) := by
    intro s; rw [hy s]; rfl
  have hx' : ∀ s, x (s + 1) = (1 - (1 - lambda s) / lambda (s + 1)) • y (s + 1)
      + ((1 - lambda s) / lambda (s + 1)) • y s := by
    intro s; rw [hx s, hl s, hy' s]; rfl
  -- Facts about the sequence `lambda`.
  have hS : ∀ s, Real.sqrt (1 + 4 * lambda s ^ 2) ^ 2 = 1 + 4 * lambda s ^ 2 := fun s =>
    Real.sq_sqrt (by positivity)
  have hl_ge1 : ∀ s, 1 ≤ lambda (s + 1) := by
    intro s
    have : 1 ≤ Real.sqrt (1 + 4 * lambda s ^ 2) := by
      rw [Real.one_le_sqrt]; nlinarith [sq_nonneg (lambda s)]
    rw [hl s]; linarith
  have hl_sq : ∀ s, lambda (s + 1) ^ 2 - lambda (s + 1) = lambda s ^ 2 := by
    intro s; rw [hl s]; linear_combination (1 / 4) * hS s
  have hl1 : lambda 1 = 1 := by rw [hl 0, hl0]; norm_num
  have hl_nonneg : ∀ s, 0 ≤ lambda s := by
    intro s
    cases s with
    | zero => rw [hl0]
    | succ k => linarith [hl_ge1 k]
  have hl_grow : ∀ s, lambda s + 1 / 2 ≤ lambda (s + 1) := by
    intro s
    rw [hl s]
    have h1 := hS s
    have h2 := Real.sqrt_nonneg (1 + 4 * lambda s ^ 2)
    have h3 := hl_nonneg s
    nlinarith
  have hl_lb : ∀ s : ℕ, ((s : ℝ) + 2) / 2 ≤ lambda (s + 1) := by
    intro s
    induction s with
    | zero => rw [hl1]; norm_num
    | succ k ih =>
      have := hl_grow (k + 1)
      push_cast
      linarith
  -- Lyapunov function.
  set u : ℕ → EuclideanSpace ℝ (Fin n) :=
    fun s => lambda s • x s - (lambda s - 1) • y s - x_star with hu_def
  have hx1 : x 1 = x 0 := by
    rw [hx' 0, hl0, hl1, hxy_init]; simp
  have hstep : ∀ s, 1 ≤ s →
      (lambda (s + 1) ^ 2 - lambda (s + 1)) * (f (y (s + 1)) - f x_star)
          + β / 2 * ‖u (s + 1)‖ ^ 2
        ≤ (lambda s ^ 2 - lambda s) * (f (y s) - f x_star) + β / 2 * ‖u s‖ ^ 2 := by
    intro s hs
    have hL1 : 1 ≤ lambda s := by
      obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
      exact hl_ge1 k
    have hL'pos : 0 < lambda (s + 1) := by linarith [hl_ge1 s]
    have h13 := hA (x s) (y s)
    have h14 := hA (x s) x_star
    rw [← hy' s] at h13 h14
    set v := (1 / β) • gradient f (x s) with hv
    set L := lambda s with hL
    set L' := lambda (s + 1) with hL'
    have hγ : L' * ((1 - L) / L') = 1 - L := by field_simp
    have hu : u (s + 1) = u s - L • v := by
      simp only [hu_def]
      rw [hx' s, hy' s]
      linear_combination (norm := module) hγ • (y s - (x s - v))
    have hus : u s = (L - 1) • (x s - y s) + (x s - x_star) := by
      simp only [hu_def]; module
    have hinner : inner ℝ (u s) v = (L - 1) * inner ℝ v (x s - y s) + inner ℝ v (x s - x_star) := by
      rw [hus, inner_add_left, real_inner_smul_left, real_inner_comm, real_inner_comm v]
    have hnorm : ‖u (s + 1)‖ ^ 2 = ‖u s‖ ^ 2 - 2 * L * inner ℝ (u s) v + L ^ 2 * ‖v‖ ^ 2 := by
      rw [hu, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ L)]
      ring
    rw [hl_sq s, hnorm, hinner]
    have hLL : 0 ≤ L * (L - 1) := by nlinarith
    have e1 := mul_le_mul_of_nonneg_left h13 hLL
    have e2 := mul_le_mul_of_nonneg_left h14 (by linarith : (0:ℝ) ≤ L)
    nlinarith
  have hE : ∀ k : ℕ,
      (lambda (k + 1) ^ 2 - lambda (k + 1)) * (f (y (k + 1)) - f x_star)
          + β / 2 * ‖u (k + 1)‖ ^ 2 ≤ β / 2 * ‖x 0 - x_star‖ ^ 2 := by
    intro k
    induction k with
    | zero =>
      have hu1 : u 1 = x 0 - x_star := by
        simp only [hu_def]; rw [hl1, hx1]; simp
      rw [hu1, hl1]; simp
    | succ k ih =>
      exact (hstep (k + 1) (by omega)).trans ih
  have hδ : ∀ s, 0 ≤ f (y s) - f x_star := by
    intro s
    have := isMinOn_iff.mp hx_star (y s) (Set.mem_univ _)
    linarith
  have hnorm_nonneg : ∀ s, 0 ≤ β / 2 * ‖u s‖ ^ 2 := fun s => by positivity
  -- Conclusion.
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rcases Nat.eq_zero_or_pos s with hs | hs
  · -- t = 1
    subst hs
    have hy21 : y 2 = y 1 := by
      rw [hy' 1, hx1, hy' 0]
    have h2 := hE 1
    rw [hl_sq 1, hl1, hy21] at h2
    have h3 := hnorm_nonneg (1 + 1)
    have h4 : 0 ≤ β * ‖x 0 - x_star‖ ^ 2 := by positivity
    have h5 : ((0 + 1 : ℕ) : ℝ) ^ 2 = 1 := by norm_num
    rw [h5, div_one]
    linarith
  · -- t ≥ 2
    have h1 := hE s
    rw [hl_sq s] at h1
    obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
    have hlb := hl_lb k
    have hpos : (0 : ℝ) < ((k + 1 + 1 : ℕ) : ℝ) ^ 2 := by positivity
    rw [le_div_iff₀ hpos]
    have h3 := hnorm_nonneg (k + 1 + 1)
    have hD := hδ (k + 1 + 1)
    have hlb' : ((k + 1 + 1 : ℕ) : ℝ) / 2 ≤ lambda (k + 1) := by push_cast; linarith
    have hsq : (((k + 1 + 1 : ℕ) : ℝ) / 2) ^ 2 ≤ lambda (k + 1) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlb' 2
    have h4 := mul_le_mul_of_nonneg_left hsq hD
    linarith

end nesterov_smooth_convex_bound
