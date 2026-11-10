import ConvexStarLib.Defs

/-!
# `gradient_descent_smooth_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/gradient_descent_smooth_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace gradient_descent_smooth_bound`, so the main result is `gradient_descent_smooth_bound.gradient_descent_smooth_bound`.
-/

namespace gradient_descent_smooth_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


set_option linter.unusedVariables false in
set_option maxHeartbeats 1000000 in
theorem gradient_descent_smooth_bound {n t : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
  (β : ℝ) (x_star : EuclideanSpace ℝ (Fin n))
  (hβ_pos : β > 0) (ht_one : t ≥ 1)
  (hf_convex : ConvexOn ℝ Set.univ f)
  (hf_differentiable : Differentiable ℝ f)
  (hf_beta_smooth : LipschitzWith (Real.toNNReal β) (gradient f))
  (h_gd_seq : IsGradientDescentSequence f x (1 / β))
  (hx_star : IsMinOn f Set.univ x_star) :
  f (x t) - f x_star ≤ (2 * β) * ‖x 0 - x_star‖ ^ 2 / t := by
  -- the gradient is β-Lipschitz, in norm form
  have hL : ∀ a b, ‖gradient f a - gradient f b‖ ≤ β * ‖a - b‖ := by
    intro a b
    have := hf_beta_smooth.dist_le_mul a b
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hβ_pos.le] at this
    exact this
  -- descent lemma: f q ≤ f p + ⟪∇f p, q - p⟫ + β/2 ‖q - p‖²
  have hdesc : ∀ p q : EuclideanSpace ℝ (Fin n),
      f q ≤ f p + inner ℝ (gradient f p) (q - p) + β / 2 * ‖q - p‖ ^ 2 := by
    intro p q
    set v := q - p with hv
    set c := inner ℝ (gradient f p) v with hc
    let g : ℝ → ℝ := fun s => f (p + s • v) - s * c - β / 2 * ‖v‖ ^ 2 * s ^ 2
    have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => p + s • v) v s := by
      intro s
      simpa using ((hasDerivAt_id s).smul_const v).const_add p
    have hφ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => f (p + s • v))
        (inner ℝ (gradient f (p + s • v)) v) s := by
      intro s
      have h1 : HasFDerivAt f (fderiv ℝ f (p + s • v)) (p + s • v) :=
        (hf_differentiable _).hasFDerivAt
      have h2 := h1.comp_hasDerivAt s (hline s)
      convert h2 using 1
      simp [gradient]
    have hg' : ∀ s : ℝ, HasDerivAt g
        (inner ℝ (gradient f (p + s • v)) v - c - β / 2 * ‖v‖ ^ 2 * (2 * s)) s := by
      intro s
      have := ((hφ s).sub ((hasDerivAt_id s).mul_const c)).sub
        (((hasDerivAt_id s).pow 2).const_mul (β / 2 * ‖v‖ ^ 2))
      convert this using 1
      simp
    have hanti : AntitoneOn g (Set.Ici 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      · exact fun s _ => (hg' s).continuousAt.continuousWithinAt
      · exact fun s _ => (hg' s).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Ici] at hs
        rw [(hg' s).deriv]
        have hs' : 0 < s := hs
        have key : inner ℝ (gradient f (p + s • v)) v - c ≤ β * ‖v‖ ^ 2 * s := by
          have e : inner ℝ (gradient f (p + s • v)) v - c
              = inner ℝ (gradient f (p + s • v) - gradient f p) v := by
            simp [c, inner_sub_left]
          rw [e]
          calc inner ℝ (gradient f (p + s • v) - gradient f p) v
              ≤ ‖gradient f (p + s • v) - gradient f p‖ * ‖v‖ := real_inner_le_norm _ _
            _ ≤ (β * ‖(p + s • v) - p‖) * ‖v‖ := by gcongr; exact hL _ _
            _ = β * ‖v‖ ^ 2 * s := by
              rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs'.le]; ring
        linarith
    have h01 := hanti Set.self_mem_Ici (show (1:ℝ) ∈ Set.Ici 0 by simp) zero_le_one
    simp only [g] at h01
    simp at h01
    have : p + v = q := by simp [v]
    rw [this] at h01
    linarith
  -- first-order characterization of convexity: f p + ⟪∇f p, q - p⟫ ≤ f q
  have hconv : ∀ p q : EuclideanSpace ℝ (Fin n),
      f p + inner ℝ (gradient f p) (q - p) ≤ f q := by
    intro p q
    let ℓ : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin n) := AffineMap.lineMap p q
    have hℓ0 : ℓ 0 = p := AffineMap.lineMap_apply_zero p q
    have hℓ1 : ℓ 1 = q := AffineMap.lineMap_apply_one p q
    have hφconv : ConvexOn ℝ Set.univ (f ∘ ℓ) := by
      simpa using hf_convex.comp_affineMap ℓ
    have hφ0 : HasDerivAt (f ∘ ℓ) (inner ℝ (gradient f p) (q - p)) 0 := by
      have h1 : HasFDerivAt f (fderiv ℝ f (ℓ 0)) (ℓ 0) := (hf_differentiable _).hasFDerivAt
      have h2 := h1.comp_hasDerivAt (0:ℝ)
        (AffineMap.hasDerivAt_lineMap (a := p) (b := q) (x := (0:ℝ)))
      rw [hℓ0] at h2
      convert h2 using 1
      simp [gradient]
    have := hφconv.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hφ0
    rw [slope_def_field] at this
    simp only [Function.comp, hℓ0, hℓ1] at this
    norm_num at this
    linarith
  have hstep : ∀ k, x (k+1) = x k - (1/β) • gradient f (x k) := fun k => h_gd_seq k
  -- sufficient decrease: f (x (k+1)) ≤ f (x k) - 1/(2β) ‖∇f (x k)‖²
  have hmono : ∀ k, f (x (k+1)) ≤ f (x k) - 1 / (2 * β) * ‖gradient f (x k)‖ ^ 2 := by
    intro k
    have h := hdesc (x k) (x (k+1))
    rw [hstep k] at h ⊢
    have e1 : x k - (1/β) • gradient f (x k) - x k = -((1/β) • gradient f (x k)) := by abel
    rw [e1, inner_neg_right, inner_smul_right, norm_neg, norm_smul,
      real_inner_self_eq_norm_sq, Real.norm_of_nonneg (by positivity)] at h
    have e2 : β / 2 * (1 / β * ‖gradient f (x k)‖) ^ 2
        = 1 / (2 * β) * ‖gradient f (x k)‖ ^ 2 := by
      field_simp
    have e3 : 1 / β * ‖gradient f (x k)‖ ^ 2 = 2 * (1 / (2 * β) * ‖gradient f (x k)‖ ^ 2) := by
      field_simp
    rw [e2, e3] at h
    linarith
  -- one-step bound: f (x (k+1)) - f x* ≤ β/2 (‖x k - x*‖² - ‖x (k+1) - x*‖²)
  have hkey : ∀ k, f (x (k+1)) - f x_star
      ≤ β / 2 * (‖x k - x_star‖ ^ 2 - ‖x (k+1) - x_star‖ ^ 2) := by
    intro k
    have h1 := hmono k
    have h2 := hconv (x k) x_star
    have h3 : ‖x (k+1) - x_star‖ ^ 2 = ‖x k - x_star‖ ^ 2
        - 2 / β * inner ℝ (gradient f (x k)) (x k - x_star)
        + 1 / β ^ 2 * ‖gradient f (x k)‖ ^ 2 := by
      rw [hstep k]
      have : x k - (1/β) • gradient f (x k) - x_star
          = (x k - x_star) - (1/β) • gradient f (x k) := by abel
      rw [this, norm_sub_sq_real, inner_smul_right, norm_smul, real_inner_comm,
        Real.norm_of_nonneg (by positivity)]
      ring
    have h4 : inner ℝ (gradient f (x k)) (x_star - x k)
        = - inner ℝ (gradient f (x k)) (x k - x_star) := by
      rw [← inner_neg_right, neg_sub]
    rw [h3]
    rw [h4] at h2
    have e : β / 2 * (‖x k - x_star‖ ^ 2 - (‖x k - x_star‖ ^ 2
        - 2 / β * inner ℝ (gradient f (x k)) (x k - x_star)
        + 1 / β ^ 2 * ‖gradient f (x k)‖ ^ 2))
        = inner ℝ (gradient f (x k)) (x k - x_star)
          - 1 / (2 * β) * ‖gradient f (x k)‖ ^ 2 := by
      field_simp
      ring
    rw [e]
    linarith
  -- telescoping, using that f (x k) is non-increasing
  have hind : ∀ m : ℕ, (m : ℝ) * (f (x m) - f x_star)
      ≤ β / 2 * (‖x 0 - x_star‖ ^ 2 - ‖x m - x_star‖ ^ 2) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 := hkey m
      have h2 := hmono m
      have hg : 0 ≤ 1 / (2 * β) * ‖gradient f (x m)‖ ^ 2 := by positivity
      have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
      have h5 : (m:ℝ) * (f (x (m+1)) - f x_star) ≤ (m:ℝ) * (f (x m) - f x_star) := by
        apply mul_le_mul_of_nonneg_left _ hm
        linarith
      push_cast
      nlinarith
  have ht : (0:ℝ) < t := by exact_mod_cast ht_one
  have h := hind t
  rw [le_div_iff₀ ht]
  have : 0 ≤ ‖x t - x_star‖ ^ 2 := by positivity
  have : 0 ≤ ‖x 0 - x_star‖ ^ 2 := by positivity
  nlinarith

end gradient_descent_smooth_bound
