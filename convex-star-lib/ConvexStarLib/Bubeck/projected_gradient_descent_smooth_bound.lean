import ConvexStarLib.Defs

/-!
# `projected_gradient_descent_smooth_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/projected_gradient_descent_smooth_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace projected_gradient_descent_smooth_bound`, so the main result is `projected_gradient_descent_smooth_bound.projected_gradient_descent_smooth_bound`.
-/

namespace projected_gradient_descent_smooth_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem projected_gradient_descent_smooth_bound {n t : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (β : ℝ) (x_star : EuclideanSpace ℝ (Fin n))
  (hβ_pos : β > 0)
  (hx_init : x 0 ∈ 𝓧)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (hf_convex : ConvexOn ℝ 𝓧 f)
  (hf_differentiable : DifferentiableOn ℝ f 𝓧)
  (hf_beta_smooth : LipschitzOnWith (Real.toNNReal β) (gradient f) 𝓧)
  (h_gd_seq : IsProjectedGradientDescentSequence 𝓧 f g x (fun s => 1 / β)
              h𝓧_nonempty h𝓧_compact h𝓧_convex)
  (hx_star_mem : x_star ∈ 𝓧)
  (hx_star : IsMinOn f 𝓧 x_star) :
  f (x t) - f x_star ≤ ((3 * β) * ‖x 0 - x_star‖^2 + f (x 0) - f x_star) / (t + 1) := by
  obtain ⟨hgrad, hstep⟩ := h_gd_seq
  have hβ' : ((Real.toNNReal β : NNReal) : ℝ) = β := Real.coe_toNNReal β hβ_pos.le
  have hgf : ∀ z ∈ 𝓧, gradient f z = g z := fun z hz => (hgrad z hz).gradient
  -- projection property
  have hproj : ∀ y : EuclideanSpace ℝ (Fin n),
      pC y 𝓧 h𝓧_compact.isClosed h𝓧_convex h𝓧_nonempty ∈ 𝓧 ∧
      ∀ w ∈ 𝓧, inner ℝ (y - pC y 𝓧 h𝓧_compact.isClosed h𝓧_convex h𝓧_nonempty)
        (w - pC y 𝓧 h𝓧_compact.isClosed h𝓧_convex h𝓧_nonempty) ≤ 0 := by
    intro y
    have h := Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex h𝓧_nonempty
      h𝓧_compact.isClosed.isComplete h𝓧_convex y)
    exact ⟨h.1, (norm_eq_iInf_iff_real_inner_le_zero h𝓧_convex h.1).1 h.2⟩
  have hstep' : ∀ s, x (s + 1) =
      pC (x s - (1 / β) • g (x s)) 𝓧 h𝓧_compact.isClosed h𝓧_convex h𝓧_nonempty :=
    fun s => hstep s
  have hmem : ∀ s, x s ∈ 𝓧 := by
    intro s
    induction s with
    | zero => exact hx_init
    | succ s ih => rw [hstep' s]; exact (hproj _).1
  -- first-order condition for convexity
  have hfo : ∀ a ∈ 𝓧, ∀ b ∈ 𝓧, f a + inner ℝ (g a) (b - a) ≤ f b := by
    intro a ha b hb
    have hL : HasLineDerivAt ℝ f (inner ℝ (g a) (b - a)) a (b - a) := by
      have := (hgrad a ha).hasFDerivAt.hasLineDerivAt (b - a)
      simpa [InnerProductSpace.toDual_apply_apply] using this
    have ht := hL.tendsto_slope_zero_right
    have hle : ∀ᶠ t in 𝓝[>] (0:ℝ), t⁻¹ • (f (a + t • (b - a)) - f a) ≤ f b - f a := by
      have : Set.Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT one_pos
      filter_upwards [this] with t ht
      have hconv := hf_convex.2 ha hb (by linarith [ht.1, ht.2] : (0:ℝ) ≤ 1 - t) ht.1.le
        (by ring : (1 - t) + t = 1)
      have heq : (1 - t) • a + t • b = a + t • (b - a) := by
        rw [smul_sub, sub_smul, one_smul]; abel
      rw [heq] at hconv
      simp only [smul_eq_mul] at hconv ⊢
      rw [inv_mul_le_iff₀ ht.1]
      nlinarith
    have := le_of_tendsto ht hle
    linarith
  -- descent lemma
  have hsmooth : ∀ a ∈ 𝓧, ∀ b ∈ 𝓧,
      f b ≤ f a + inner ℝ (g a) (b - a) + β / 2 * ‖b - a‖ ^ 2 := by
    intro a ha b hb
    set d := b - a with hd
    have hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, a + t • d ∈ 𝓧 := by
      intro t ht
      have := h𝓧_convex ha hb (by linarith [ht.2] : (0:ℝ) ≤ 1 - t) ht.1 (by ring : (1 - t) + t = 1)
      convert this using 1
      rw [hd, smul_sub, sub_smul, one_smul]; abel
    let ph : ℝ → ℝ := fun t => f (a + t • d) - t * inner ℝ (g a) d - β / 2 * t ^ 2 * ‖d‖ ^ 2
    let phd : ℝ → ℝ := fun t => inner ℝ (g (a + t • d)) d - inner ℝ (g a) d - β * t * ‖d‖ ^ 2
    have hderiv : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt ph (phd t) t := by
      intro t ht
      have hline : HasDerivAt (fun s : ℝ => a + s • d) d t := by
        simpa using ((hasDerivAt_id t).smul_const d).const_add a
      have hf' := (hgrad _ (hseg t ht)).hasFDerivAt.comp_hasDerivAt t hline
      have h2 : HasDerivAt (fun s : ℝ => s * inner ℝ (g a) d) (inner ℝ (g a) d) t := by
        simpa using (hasDerivAt_id t).mul_const (inner ℝ (g a) d)
      have h3 : HasDerivAt (fun s : ℝ => β / 2 * s ^ 2 * ‖d‖ ^ 2) (β * t * ‖d‖ ^ 2) t := by
        have := ((hasDerivAt_pow 2 t).const_mul (β / 2)).mul_const (‖d‖ ^ 2)
        convert this using 1
        push_cast; ring
      have := (hf'.sub h2).sub h3
      convert this using 1
    obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope ph phd zero_lt_one
      (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
      (fun t ht => hderiv t (Set.Ioo_subset_Icc_self ht))
    have hphdc : phd c ≤ 0 := by
      have hz := hseg c (Set.Ioo_subset_Icc_self hc)
      have hlip := hf_beta_smooth.norm_sub_le hz ha
      rw [hgf _ hz, hgf _ ha, hβ'] at hlip
      have h1 : inner ℝ (g (a + c • d)) d - inner ℝ (g a) d = inner ℝ (g (a + c • d) - g a) d :=
        (inner_sub_left _ _ _).symm
      have h2 : inner ℝ (g (a + c • d) - g a) d ≤ ‖g (a + c • d) - g a‖ * ‖d‖ :=
        real_inner_le_norm _ _
      have h3 : ‖a + c • d - a‖ = c * ‖d‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hc.1.le]
      rw [h3] at hlip
      have h4 : ‖g (a + c • d) - g a‖ * ‖d‖ ≤ β * (c * ‖d‖) * ‖d‖ :=
        mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
      show inner ℝ (g (a + c • d)) d - inner ℝ (g a) d - β * c * ‖d‖ ^ 2 ≤ 0
      nlinarith
    have hph : ph 1 ≤ ph 0 := by
      have := hceq
      rw [sub_zero, div_one] at this
      linarith
    simp only [ph, one_smul, one_mul, zero_smul, add_zero, zero_mul, sub_zero, one_pow] at hph
    have had : a + d = b := by rw [hd]; abel
    rw [had] at hph
    norm_num at hph
    linarith
  -- one-step inequality
  have hone : ∀ s, ∀ z ∈ 𝓧, f (x (s + 1)) - f z ≤
      -(β * inner ℝ (x s - x (s + 1)) (z - x (s + 1))) + β / 2 * ‖x (s + 1) - x s‖ ^ 2 := by
    intro s z hz
    have hp := hmem s
    have hq := hmem (s + 1)
    have h1 := hsmooth (x s) hp (x (s + 1)) hq
    have h2 := hfo (x s) hp z hz
    have h3 : β * inner ℝ (x s - x (s + 1)) (z - x (s + 1)) ≤
        inner ℝ (g (x s)) (z - x (s + 1)) := by
      have h := (hproj (x s - (1 / β) • g (x s))).2 z hz
      rw [← hstep' s] at h
      rw [show x s - (1 / β) • g (x s) - x (s + 1) = (x s - x (s + 1)) - (1 / β) • g (x s) by abel,
        inner_sub_left, real_inner_smul_left] at h
      have := mul_le_mul_of_nonneg_left h hβ_pos.le
      rw [mul_sub, ← mul_assoc, mul_one_div_cancel hβ_pos.ne', one_mul, mul_zero] at this
      linarith
    have e1 : inner ℝ (g (x s)) (x (s + 1) - x s) =
        inner ℝ (g (x s)) (x (s + 1)) - inner ℝ (g (x s)) (x s) := inner_sub_right _ _ _
    have e2 : inner ℝ (g (x s)) (z - x s) =
        inner ℝ (g (x s)) z - inner ℝ (g (x s)) (x s) := inner_sub_right _ _ _
    have e3 : inner ℝ (g (x s)) (z - x (s + 1)) =
        inner ℝ (g (x s)) z - inner ℝ (g (x s)) (x (s + 1)) := inner_sub_right _ _ _
    linarith
  -- monotonicity of function values
  have hmono : ∀ s, f (x (s + 1)) ≤ f (x s) := by
    intro s
    have h := hone s (x s) (hmem s)
    have e : inner ℝ (x s - x (s + 1)) (x s - x (s + 1)) = ‖x (s + 1) - x s‖ ^ 2 := by
      rw [real_inner_self_eq_norm_sq, norm_sub_rev]
    rw [e] at h
    nlinarith [mul_nonneg hβ_pos.le (sq_nonneg ‖x (s + 1) - x s‖)]
  -- distance decrease
  have hdist : ∀ s, f (x (s + 1)) - f x_star ≤
      β / 2 * (‖x s - x_star‖ ^ 2 - ‖x (s + 1) - x_star‖ ^ 2) := by
    intro s
    have h := hone s x_star hx_star_mem
    have e : ‖x s - x_star‖ ^ 2 = ‖x s - x (s + 1)‖ ^ 2 -
        2 * inner ℝ (x s - x (s + 1)) (x_star - x (s + 1)) + ‖x_star - x (s + 1)‖ ^ 2 := by
      rw [← norm_sub_sq_real]; congr 2; abel
    rw [norm_sub_rev (x (s + 1)) (x s)] at h
    rw [e, norm_sub_rev (x (s + 1)) x_star]
    linarith
  -- main induction
  have key : ∀ s : ℕ, ((s:ℝ) + 1) * (f (x s) - f x_star) + β / 2 * ‖x s - x_star‖ ^ 2 ≤
      β / 2 * ‖x 0 - x_star‖ ^ 2 + (f (x 0) - f x_star) := by
    intro s
    induction s with
    | zero => simp only [Nat.cast_zero, zero_add, one_mul]; linarith
    | succ s ih =>
      have h1 := hmono s
      have h2 := hdist s
      have hs : (0:ℝ) ≤ (s:ℝ) + 1 := by positivity
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left (sub_le_sub_right h1 (f x_star)) hs]
  have hfin := key t
  have hD : 0 ≤ ‖x 0 - x_star‖ ^ 2 := sq_nonneg _
  have hDt : 0 ≤ ‖x t - x_star‖ ^ 2 := sq_nonneg _
  have ht : (0:ℝ) < (t:ℝ) + 1 := by positivity
  rw [le_div_iff₀ ht]
  nlinarith [mul_nonneg hβ_pos.le hD, mul_nonneg hβ_pos.le hDt]

end projected_gradient_descent_smooth_bound
