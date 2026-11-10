import ConvexStarLib.Defs

/-!
# `ISTA_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/ISTA_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace ISTA_bound`, so the main result is `ISTA_bound.ISTA_bound`.
-/

namespace ISTA_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Auxiliary lemmas for `ISTA_bound` -/
lemma ista_first_order {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_differentiable : Differentiable ℝ f) (hf_convex : ConvexOn ℝ Set.univ f)
    (a b : EuclideanSpace ℝ (Fin n)) :
    f a + inner ℝ (gradient f a) (b - a) ≤ f b := by
  have hconv : ConvexOn ℝ Set.univ (fun s : ℝ => f (a + s • (b - a))) := by
    have := hf_convex.comp_affineMap (AffineMap.lineMap a b)
    convert this using 1
    funext s
    simp [AffineMap.lineMap_apply, add_comm]
  have h1 : HasDerivAt (fun s : ℝ => a + s • (b - a)) (b - a) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (b - a)).const_add a
  have h2 := (hf_differentiable (a + (0:ℝ) • (b - a))).hasFDerivAt.comp_hasDerivAt (0:ℝ) h1
  have hderiv : HasDerivAt (fun s : ℝ => f (a + s • (b - a))) (inner ℝ (gradient f a) (b - a)) 0 := by
    rw [inner_gradient_left (hf_differentiable a)]
    simpa using h2
  have := hconv.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hderiv
  simp [slope_def_field] at this
  linarith

lemma ista_descent {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (β : ℝ) (hβ_pos : β > 0)
    (hf_differentiable : Differentiable ℝ f)
    (hf_beta_smooth : LipschitzWith (Real.toNNReal β) (gradient f))
    (a b : EuclideanSpace ℝ (Fin n)) :
    f b ≤ f a + inner ℝ (gradient f a) (b - a) + β / 2 * ‖b - a‖ ^ 2 := by
  set d := b - a with hd
  set ψ : ℝ → ℝ := fun s => f (a + s • d) - s * inner ℝ (gradient f a) d - β / 2 * s ^ 2 * ‖d‖ ^ 2
    with hψ
  have hψ' : ∀ s, HasDerivAt ψ (inner ℝ (gradient f (a + s • d)) d - inner ℝ (gradient f a) d
      - β * s * ‖d‖ ^ 2) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => a + s • d) d s := by
      simpa using ((hasDerivAt_id s).smul_const d).const_add a
    have h2 := (hf_differentiable (a + s • d)).hasFDerivAt.comp_hasDerivAt s h1
    rw [← inner_gradient_left (hf_differentiable _)] at h2
    have h3 : HasDerivAt (fun s : ℝ => s * inner ℝ (gradient f a) d) (inner ℝ (gradient f a) d) s := by
      simpa using (hasDerivAt_id s).mul_const (inner ℝ (gradient f a) d)
    have h4 : HasDerivAt (fun s : ℝ => β / 2 * s ^ 2 * ‖d‖ ^ 2) (β * s * ‖d‖ ^ 2) s := by
      have := ((hasDerivAt_pow 2 s).const_mul (β / 2)).mul_const (‖d‖ ^ 2)
      convert this using 1
      push_cast
      ring
    exact (h2.sub h3).sub h4
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    · exact fun s _ => (hψ' s).continuousAt.continuousWithinAt
    · intro s _
      exact (hψ' s).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hL : ‖gradient f (a + s • d) - gradient f a‖ ≤ β * ‖s • d‖ := by
        have := hf_beta_smooth.dist_le_mul (a + s • d) a
        rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hβ_pos.le] at this
        simpa using this
      have hcs : inner ℝ (gradient f (a + s • d) - gradient f a) d
          ≤ ‖gradient f (a + s • d) - gradient f a‖ * ‖d‖ := real_inner_le_norm _ _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs.1] at hL
      rw [inner_sub_left] at hcs
      have := mul_le_mul_of_nonneg_right hL (norm_nonneg d)
      nlinarith
  have := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  simp [ψ] at this
  have hab : a + d = b := by rw [hd]; abel
  rw [hab] at this
  linarith


lemma ista_prox_real {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (β : ℝ) (hβ_pos : β > 0) (h_ista_seq : IsISTASequence f g x (1 / β)) (k : ℕ)
    (z : EuclideanSpace ℝ (Fin n)) :
    g (x (k+1)) + β / 2 * ‖x (k+1) - (x k - (1/β) • gradient f (x k))‖ ^ 2
      ≤ g z + β / 2 * ‖z - (x k - (1/β) • gradient f (x k))‖ ^ 2 := by
  have h := (h_ista_seq k).2 z
  have hc : (2 * (1 / β))⁻¹ = β / 2 := by field_simp
  simp only [hc] at h
  exact_mod_cast h

lemma ista_prox_subgrad {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (β : ℝ) (hβ_pos : β > 0)
    (hg_convex : ConvexOn ℝ Set.univ g) (y w : EuclideanSpace ℝ (Fin n))
    (hw : ∀ z, g w + β / 2 * ‖w - y‖ ^ 2 ≤ g z + β / 2 * ‖z - y‖ ^ 2)
    (z : EuclideanSpace ℝ (Fin n)) :
    g w + β * inner ℝ (y - w) (z - w) ≤ g z := by
  set d := z - w with hd
  set A := g z - g w - β * inner ℝ (y - w) d with hA
  set C := β / 2 * ‖d‖ ^ 2 with hC
  have hC0 : 0 ≤ C := by positivity
  have key : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ A + s * C := by
    intro s hs0 hs1
    have h1 := hw (w + s • d)
    have h2 : g (w + s • d) ≤ (1 - s) * g w + s * g z := by
      have := hg_convex.2 (Set.mem_univ w) (Set.mem_univ z) (by linarith : (0:ℝ) ≤ 1 - s) hs0.le
        (by ring)
      have e : (1 - s) • w + s • z = w + s • d := by
        rw [hd, smul_sub, sub_smul, one_smul]; abel
      rw [e] at this
      simpa [smul_eq_mul] using this
    have h3 : ‖w + s • d - y‖ ^ 2 = ‖w - y‖ ^ 2 + 2 * s * inner ℝ (w - y) d + s ^ 2 * ‖d‖ ^ 2 := by
      have : w + s • d - y = (w - y) + s • d := by abel
      rw [this, norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    have h4 : inner ℝ (w - y) d = - inner ℝ (y - w) d := by
      rw [← inner_neg_left, neg_sub]
    have h5 : 0 ≤ s * (A + s * C) := by
      rw [h3, h4] at h1
      rw [hA, hC]
      nlinarith
    exact (mul_nonneg_iff_of_pos_left hs0).mp h5
  by_contra hcon
  push_neg at hcon
  have hA0 : A < 0 := by rw [hA]; linarith
  have hCA : 0 < C - A := by linarith
  have hs0 : 0 < -A / (C - A) := div_pos (by linarith) hCA
  have hs1 : -A / (C - A) ≤ 1 := by rw [div_le_one hCA]; linarith
  have h1 := key _ hs0 hs1
  have h2 : 0 ≤ (A + -A / (C - A) * C) * (C - A) := mul_nonneg h1 hCA.le
  have e : (A + -A / (C - A) * C) * (C - A) = -A ^ 2 := by field_simp; ring
  rw [e] at h2
  nlinarith

lemma ista_strong_fo {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (β : ℝ) (hβ_pos : β > 0)
    (hf_differentiable : Differentiable ℝ f) (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_beta_smooth : LipschitzWith (Real.toNNReal β) (gradient f))
    (a b : EuclideanSpace ℝ (Fin n)) :
    f a + inner ℝ (gradient f a) (b - a) + 1 / (2 * β) * ‖gradient f b - gradient f a‖ ^ 2
      ≤ f b := by
  set e := gradient f b - gradient f a with he
  set c := b - (1 / β) • e with hc
  have h1 := ista_first_order f hf_differentiable hf_convex a c
  have h2 := ista_descent f β hβ_pos hf_differentiable hf_beta_smooth b c
  have e1 : c - a = (b - a) - (1 / β) • e := by rw [hc]; abel
  have e2 : c - b = -((1 / β) • e) := by rw [hc]; abel
  rw [e1, inner_sub_right, inner_smul_right] at h1
  rw [e2, inner_neg_right, inner_smul_right, norm_neg, norm_smul] at h2
  have e3 : inner ℝ (gradient f b) e - inner ℝ (gradient f a) e = ‖e‖ ^ 2 := by
    rw [← inner_sub_left, ← he, real_inner_self_eq_norm_sq]
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)] at h2
  have e4 : β / 2 * (1 / β * ‖e‖) ^ 2 = 1 / (2 * β) * ‖e‖ ^ 2 := by field_simp
  have e5 : 1 / β * inner ℝ (gradient f b) e - 1 / β * inner ℝ (gradient f a) e
      = 1 / β * ‖e‖ ^ 2 := by rw [← mul_sub, e3]
  have e6 : 1 / β * ‖e‖ ^ 2 = 2 * (1 / (2 * β) * ‖e‖ ^ 2) := by field_simp
  linarith

lemma ista_cocoercive {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (β : ℝ) (hβ_pos : β > 0)
    (hf_differentiable : Differentiable ℝ f) (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_beta_smooth : LipschitzWith (Real.toNNReal β) (gradient f))
    (a b : EuclideanSpace ℝ (Fin n)) :
    ‖gradient f a - gradient f b‖ ^ 2 ≤ β * inner ℝ (gradient f a - gradient f b) (a - b) := by
  have h1 := ista_strong_fo f β hβ_pos hf_differentiable hf_convex hf_beta_smooth a b
  have h2 := ista_strong_fo f β hβ_pos hf_differentiable hf_convex hf_beta_smooth b a
  rw [norm_sub_rev (gradient f b) (gradient f a)] at h1
  have e1 : inner ℝ (gradient f a) (b - a) + inner ℝ (gradient f b) (a - b)
      = - inner ℝ (gradient f a - gradient f b) (a - b) := by
    rw [inner_sub_left, ← neg_sub a b, inner_neg_right]; ring
  have h3 : 1 / β * ‖gradient f a - gradient f b‖ ^ 2
      ≤ inner ℝ (gradient f a - gradient f b) (a - b) := by
    have : 1 / β * ‖gradient f a - gradient f b‖ ^ 2
        = 2 * (1 / (2 * β) * ‖gradient f a - gradient f b‖ ^ 2) := by field_simp
    linarith
  have h4 := mul_le_mul_of_nonneg_left h3 hβ_pos.le
  rw [← mul_assoc, mul_one_div_cancel hβ_pos.ne', one_mul] at h4
  exact h4

set_option linter.unusedVariables false in
theorem ISTA_bound
  {n t : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (g : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (β : ℝ)
  (x_star : EuclideanSpace ℝ (Fin n))
  (hβ_pos : β > 0)
  (ht_one : t ≥ 1)
  (hg_convex : ConvexOn ℝ Set.univ g)
  (hf_differentiable : Differentiable ℝ f)
  (hf_convex : ConvexOn ℝ Set.univ f)
  (hf_beta_smooth : LipschitzWith (Real.toNNReal β) (gradient f))
  (h_ista_seq : IsISTASequence f g x (1 / β))
  (hx_star : IsMinOn (f + g) Set.univ x_star) :
  f (x t) + g (x t) - (f x_star + g x_star) ≤ β * ‖x 0 - x_star‖ ^ 2 / (2 * (t + 1)) := by
  -- subgradient inequality at each prox step
  have hsub : ∀ k z, g (x (k+1)) + β * inner ℝ ((x k - (1/β) • gradient f (x k)) - x (k+1))
      (z - x (k+1)) ≤ g z := fun k z =>
    ista_prox_subgrad g β hβ_pos hg_convex _ _
      (ista_prox_real f g x β hβ_pos h_ista_seq k) z
  have hfo := ista_first_order f hf_differentiable hf_convex
  have hdesc := ista_descent f β hβ_pos hf_differentiable hf_beta_smooth
  have hcc := ista_cocoercive f β hβ_pos hf_differentiable hf_convex hf_beta_smooth
  -- fundamental prox-grad inequality
  have hA : ∀ k z, f (x (k+1)) + g (x (k+1))
      ≤ f z + g z + β / 2 * ‖z - x k‖ ^ 2 - β / 2 * ‖z - x (k+1)‖ ^ 2 := by
    intro k z
    have h1 := hsub k z
    have h2 := hdesc (x k) (x (k+1))
    have h3 := hfo (x k) z
    have e1 : β * inner ℝ ((x k - (1/β) • gradient f (x k)) - x (k+1)) (z - x (k+1))
        = - (β * inner ℝ (z - x (k+1)) (x (k+1) - x k))
          - inner ℝ (gradient f (x k)) (z - x (k+1)) := by
      have : (x k - (1/β) • gradient f (x k)) - x (k+1)
          = -(x (k+1) - x k) - (1/β) • gradient f (x k) := by abel
      rw [this, inner_sub_left, inner_neg_left, real_inner_smul_left,
        real_inner_comm (z - x (k+1)) (x (k+1) - x k), mul_sub, ← mul_assoc,
        mul_one_div_cancel hβ_pos.ne', one_mul]
      ring
    have e2 : inner ℝ (gradient f (x k)) (x (k+1) - x k)
        + inner ℝ (gradient f (x k)) (z - x (k+1)) = inner ℝ (gradient f (x k)) (z - x k) := by
      rw [← inner_add_right]; congr 1; abel
    have e3 : β / 2 * ‖z - x k‖ ^ 2
        = β / 2 * ‖z - x (k+1)‖ ^ 2 + β * inner ℝ (z - x (k+1)) (x (k+1) - x k)
          + β / 2 * ‖x (k+1) - x k‖ ^ 2 := by
      have : z - x k = (z - x (k+1)) + (x (k+1) - x k) := by abel
      rw [this, norm_add_sq_real]; ring
    linarith
  -- subgradient bound on the gap at x (k+1)
  have hII : ∀ k z, f (x (k+1)) + g (x (k+1)) - (f z + g z)
      ≤ β * inner ℝ (x k - x (k+1)) (x (k+1) - z)
        - inner ℝ (gradient f (x k) - gradient f (x (k+1))) (x (k+1) - z) := by
    intro k z
    have h1 := hsub k z
    have h2 := hfo (x (k+1)) z
    have e1 : β * inner ℝ ((x k - (1/β) • gradient f (x k)) - x (k+1)) (z - x (k+1))
        = - (β * inner ℝ (x k - x (k+1)) (x (k+1) - z))
          + inner ℝ (gradient f (x k)) (x (k+1) - z) := by
      have h' : (x k - (1/β) • gradient f (x k)) - x (k+1)
          = (x k - x (k+1)) - (1/β) • gradient f (x k) := by abel
      have hzw : z - x (k+1) = -(x (k+1) - z) := by abel
      rw [h', hzw, inner_neg_right, inner_sub_left, real_inner_smul_left, mul_neg, mul_sub,
        ← mul_assoc, mul_one_div_cancel hβ_pos.ne', one_mul]
      ring
    have e2 : inner ℝ (gradient f (x (k+1))) (z - x (k+1))
        = - inner ℝ (gradient f (x (k+1))) (x (k+1) - z) := by
      rw [← inner_neg_right, neg_sub]
    have e3 : inner ℝ (gradient f (x k) - gradient f (x (k+1))) (x (k+1) - z)
        = inner ℝ (gradient f (x k)) (x (k+1) - z)
          - inner ℝ (gradient f (x (k+1))) (x (k+1) - z) := inner_sub_left _ _ _
    linarith
  -- one-step Lyapunov decrease
  have hstep : ∀ k : ℕ, ((k:ℝ) + 1) * (f (x (k+1)) + g (x (k+1)) - (f x_star + g x_star))
      + β / 2 * ‖x (k+1) - x_star‖ ^ 2 + (k:ℝ) * (β / 2 * ‖x k - x (k+1)‖ ^ 2)
      ≤ (k:ℝ) * (f (x k) + g (x k) - (f x_star + g x_star)) + β / 2 * ‖x k - x_star‖ ^ 2 := by
    intro k
    have h1 := hA k (x k)
    have h2 := hA k x_star
    simp only [sub_self, norm_zero] at h1
    rw [norm_sub_rev x_star (x k), norm_sub_rev x_star (x (k+1))] at h2
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have h3 : (k:ℝ) * (f (x (k+1)) + g (x (k+1)) + β / 2 * ‖x k - x (k+1)‖ ^ 2)
        ≤ (k:ℝ) * (f (x k) + g (x k)) := by
      apply mul_le_mul_of_nonneg_left _ hk
      linarith
    nlinarith
  -- Lyapunov bound
  have hΦ : ∀ k : ℕ, (k:ℝ) * (f (x k) + g (x k) - (f x_star + g x_star))
      + β / 2 * ‖x k - x_star‖ ^ 2 ≤ β / 2 * ‖x 0 - x_star‖ ^ 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 := hstep k
      have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
      have h2 : (0:ℝ) ≤ (k:ℝ) * (β / 2 * ‖x k - x (k+1)‖ ^ 2) := by positivity
      push_cast
      linarith
  -- final step
  have key : ∀ m : ℕ, (f (x (m+1)) + g (x (m+1)) - (f x_star + g x_star)) * (2 * ((m:ℝ) + 1 + 1))
      ≤ β * ‖x 0 - x_star‖ ^ 2 := by
    intro m
    have hII' := hII m x_star
    have hcc' := hcc (x m) (x (m+1))
    have hΦm := hΦ m
    have hstepm := hstep m
    set p := x m - x (m+1) with hp
    set q := x (m+1) - x_star with hq
    set d := gradient f (x m) - gradient f (x (m+1)) with hd
    set Fm := f (x (m+1)) + g (x (m+1)) - (f x_star + g x_star) with hFm
    rw [real_inner_comm p d] at hcc'
    rw [real_inner_comm q d] at hII'
    rcases Nat.eq_zero_or_pos m with hm | hm
    · -- t = 1
      subst hm
      have e0 : x 0 - x_star = p + q := by rw [hp, hq]; abel
      have hsq : 0 ≤ β ^ 2 * ‖q‖ ^ 2 - 2 * β ^ 2 * inner ℝ p q + β ^ 2 * ‖p‖ ^ 2
          + 4 * β * inner ℝ q d - 4 * β * inner ℝ p d + 4 * ‖d‖ ^ 2 := by
        have h0 : 0 ≤ ‖β • (q - p) + (2:ℝ) • d‖ ^ 2 := by positivity
        have expand : ‖β • (q - p) + (2:ℝ) • d‖ ^ 2 = β ^ 2 * ‖q‖ ^ 2 - 2 * β ^ 2 * inner ℝ p q
            + β ^ 2 * ‖p‖ ^ 2 + 4 * β * inner ℝ q d - 4 * β * inner ℝ p d + 4 * ‖d‖ ^ 2 := by
          rw [← real_inner_self_eq_norm_sq]
          simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
            real_inner_smul_left, real_inner_smul_right]
          simp only [real_inner_self_eq_norm_sq, real_inner_comm p q, real_inner_comm q d,
            real_inner_comm p d]
          ring
        linarith
      have h5 := mul_le_mul_of_nonneg_left hII' hβ_pos.le
      rw [e0, norm_add_sq_real]
      simp only [Nat.cast_zero]
      have h6 : β * (Fm * (2 * ((0:ℝ) + 1 + 1)))
          ≤ β * (β * (‖p‖ ^ 2 + 2 * inner ℝ p q + ‖q‖ ^ 2)) := by
        nlinarith [sq_nonneg ‖d‖]
      exact le_of_mul_le_mul_left h6 hβ_pos
    · -- t ≥ 2
      have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
      have hsq : 0 ≤ β ^ 2 * ‖p‖ ^ 2 + ‖d‖ ^ 2 + β ^ 2 * ‖q‖ ^ 2 - 2 * β * inner ℝ p d
          - 2 * β ^ 2 * inner ℝ p q + 2 * β * inner ℝ q d := by
        have h0 : 0 ≤ ‖β • p - d - β • q‖ ^ 2 := by positivity
        have expand : ‖β • p - d - β • q‖ ^ 2 = β ^ 2 * ‖p‖ ^ 2 + ‖d‖ ^ 2 + β ^ 2 * ‖q‖ ^ 2
            - 2 * β * inner ℝ p d - 2 * β ^ 2 * inner ℝ p q + 2 * β * inner ℝ q d := by
          rw [← real_inner_self_eq_norm_sq]
          simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
          simp only [real_inner_self_eq_norm_sq, real_inner_comm p q, real_inner_comm q d,
            real_inner_comm p d]
          ring
        linarith
      have h5 := mul_le_mul_of_nonneg_left hII' hβ_pos.le
      have h6 : β * Fm ≤ β * (β / 2 * ‖p‖ ^ 2 + β / 2 * ‖q‖ ^ 2) := by
        nlinarith [sq_nonneg ‖d‖]
      have h7 : Fm ≤ β / 2 * ‖p‖ ^ 2 + β / 2 * ‖q‖ ^ 2 := le_of_mul_le_mul_left h6 hβ_pos
      have h8 : 0 ≤ ((m:ℝ) - 1) * (β / 2 * ‖p‖ ^ 2) :=
        mul_nonneg (by linarith) (by positivity)
      linarith
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  rw [le_div_iff₀ (by positivity)]
  have := key m
  push_cast
  linarith

end ISTA_bound
