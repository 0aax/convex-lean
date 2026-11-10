import ConvexStarLib.Defs

/-!
# `sag_strongly_convex_linear_bound`

Source: Schmidt, Le Roux & Bach, 'Minimizing Finite Sums with the Stochastic Average Gradient' (2013), as stated in Tibshirani, Modern Stochastic Methods (10-725).

Statement from the `convex-eval-v28-2h/sag_strongly_convex_linear_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace sag_strongly_convex_linear_bound`, so the main result is `sag_strongly_convex_linear_bound.sag_strongly_convex_linear_bound`.
-/

namespace sag_strongly_convex_linear_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


lemma line_convex {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hc : ConvexOn ℝ Set.univ f)
    (x v : EuclideanSpace ℝ (Fin n)) :
    ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • v)) := by
  refine ⟨convex_univ, fun s _ t _ a b ha hb hab => ?_⟩
  have := hc.2 (Set.mem_univ (x + s • v)) (Set.mem_univ (x + t • v)) ha hb hab
  convert this using 2
  obtain rfl : b = 1 - a := by linarith
  simp only [smul_eq_mul]
  module

lemma line_deriv {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Differentiable ℝ f)
    (x v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    HasDerivAt (fun t : ℝ => f (x + t • v)) (inner ℝ (gradient f (x + t • v)) v) t := by
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have := (hf (x + t • v)).hasFDerivAt.comp_hasDerivAt t hl
  rw [inner_gradient_left (hf _)]
  exact this

lemma fo_convex_fderiv {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (f' : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (hfx : HasFDerivAt f f' x)
    (hc : ConvexOn ℝ Set.univ f) (y : EuclideanSpace ℝ (Fin n)) :
    f x + f' (y - x) ≤ f y := by
  have hφ := line_convex f hc x (y - x)
  have hl : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (y - x)).const_add x
  have hd : HasDerivAt (fun t : ℝ => f (x + t • (y - x))) (f' (y - x)) 0 := by
    have hfx' : HasFDerivAt f f' (x + (0:ℝ) • (y - x)) := by simpa using hfx
    exact hfx'.comp_hasDerivAt (0:ℝ) hl
  have := hφ.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd
  rw [slope_def_field] at this
  simp at this
  have hsub : f' (y - x) = f' y - f' x := map_sub f' y x
  linarith

/-- first-order condition for convex functions -/
theorem fo_convex {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Differentiable ℝ f)
    (hc : ConvexOn ℝ Set.univ f) (x y : EuclideanSpace ℝ (Fin n)) :
    f x + inner ℝ (gradient f x) (y - x) ≤ f y := by
  rw [inner_gradient_left (hf x)]
  exact fo_convex_fderiv f x _ (hf x).hasFDerivAt hc y

/-- descent lemma -/
theorem descent {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Differentiable ℝ f)
    (K : ℝ) (hK : 0 ≤ K)
    (hL : LipschitzWith (Real.toNNReal K) (gradient f)) (x y : EuclideanSpace ℝ (Fin n)) :
    f y ≤ f x + inner ℝ (gradient f x) (y - x) + K / 2 * ‖y - x‖ ^ 2 := by
  have hψ : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => f (x + t • (y - x)) - t * inner ℝ (gradient f x) (y - x)
        - K / 2 * t ^ 2 * ‖y - x‖ ^ 2)
      (inner ℝ (gradient f (x + t • (y - x))) (y - x) - inner ℝ (gradient f x) (y - x)
        - K * t * ‖y - x‖ ^ 2) t := by
    intro t
    have h1 := line_deriv f hf x (y - x) t
    have h2 : HasDerivAt (fun t : ℝ => t * inner ℝ (gradient f x) (y - x))
        (inner ℝ (gradient f x) (y - x)) t := by
      simpa using (hasDerivAt_id t).mul_const (inner ℝ (gradient f x) (y - x))
    have h3 : HasDerivAt (fun t : ℝ => K / 2 * t ^ 2 * ‖y - x‖ ^ 2) (K * t * ‖y - x‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (K / 2)).mul_const (‖y - x‖ ^ 2)
      convert this using 1
      push_cast; ring
    exact (h1.sub h2).sub h3
  have hnonpos : ∀ t : ℝ, 0 ≤ t → inner ℝ (gradient f (x + t • (y - x))) (y - x)
      - inner ℝ (gradient f x) (y - x) - K * t * ‖y - x‖ ^ 2 ≤ 0 := by
    intro t ht
    have hlip := hL.dist_le_mul (x + t • (y - x)) x
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht,
      Real.coe_toNNReal K hK] at hlip
    have hcs := real_inner_le_norm (gradient f (x + t • (y - x)) - gradient f x) (y - x)
    rw [inner_sub_left] at hcs
    have := mul_le_mul_of_nonneg_right hlip (norm_nonneg (y - x))
    nlinarith
  have hanti : AntitoneOn (fun t : ℝ => f (x + t • (y - x)) - t * inner ℝ (gradient f x) (y - x)
        - K / 2 * t ^ 2 * ‖y - x‖ ^ 2) (Set.Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    · exact fun t _ => (hψ t).continuousAt.continuousWithinAt
    · intro t _; exact (hψ t).hasDerivWithinAt
    · intro t ht; rw [interior_Ici] at ht; exact hnonpos t (le_of_lt ht)
  have := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr zero_le_one) zero_le_one
  simp at this
  linarith

/-- convex + smooth lower bound -/
theorem smooth_convex_lower {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Differentiable ℝ f)
    (hc : ConvexOn ℝ Set.univ f) (K : ℝ) (hK : 0 < K)
    (hL : LipschitzWith (Real.toNNReal K) (gradient f)) (x y : EuclideanSpace ℝ (Fin n)) :
    f x + inner ℝ (gradient f x) (y - x) + 1 / (2 * K) * ‖gradient f y - gradient f x‖ ^ 2 ≤ f y := by
  set g := gradient f y - gradient f x with hg
  have h1 := fo_convex f hf hc x (y - (1/K) • g)
  have h2 := descent f hf K hK.le hL y (y - (1/K) • g)
  have e1 : y - (1/K) • g - x = (y - x) - (1/K) • g := by abel
  have e2 : y - (1/K) • g - y = -((1/K) • g) := by abel
  rw [e1, inner_sub_right, inner_smul_right] at h1
  rw [e2, inner_neg_right, inner_smul_right, norm_neg, norm_smul] at h2
  have e4 : inner ℝ (gradient f y) g - inner ℝ (gradient f x) g = ‖g‖^2 := by
    rw [← inner_sub_left, ← hg, real_inner_self_eq_norm_sq]
  rw [Real.norm_of_nonneg (by positivity)] at h2
  have key : 1/(2*K) * ‖g‖^2 = 1/K * (inner ℝ (gradient f y) g - inner ℝ (gradient f x) g)
      - K/2 * (1/K * ‖g‖)^2 := by
    rw [e4]; field_simp; ring
  linarith

/-- strong convexity first-order condition -/
theorem fo_strong {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : Differentiable ℝ F) (a : ℝ)
    (hs : StrongConvexOn Set.univ a F) (x y : EuclideanSpace ℝ (Fin n)) :
    F x + inner ℝ (gradient F x) (y - x) + a / 2 * ‖y - x‖ ^ 2 ≤ F y := by
  have hG := (strongConvexOn_iff_convex).mp hs
  have hd : HasFDerivAt (fun x => F x - a / 2 * ‖x‖ ^ 2)
      (fderiv ℝ F x - (a / 2) • (2 • innerSL ℝ x)) x :=
    (hF x).hasFDerivAt.sub ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (a / 2))
  have h := fo_convex_fderiv _ x _ hd hG y
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, innerSL_apply_apply,
    smul_eq_mul, nsmul_eq_mul] at h
  rw [inner_gradient_left (hF x)]
  have e1 : ‖y - x‖ ^ 2 = ‖y‖ ^ 2 - 2 * inner ℝ y x + ‖x‖ ^ 2 := norm_sub_sq_real y x
  have e2 : inner ℝ x (y - x) = inner ℝ y x - ‖x‖ ^ 2 := by
    rw [inner_sub_right, real_inner_comm, real_inner_self_eq_norm_sq]
  rw [e2] at h
  rw [e1]
  push_cast at h
  nlinarith

/-- gradient of the finite-sum objective -/
theorem gradient_fso {m n : ℕ} (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i, Differentiable ℝ (f i)) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (finiteSumObjective f) x = (1 / (m : ℝ)) • ∑ i, gradient (f i) x := by
  have hs : HasFDerivAt (fun z => ∑ i, f i z) (∑ i, fderiv ℝ (f i) x) x :=
    HasFDerivAt.fun_sum (fun i _ => (hf i x).hasFDerivAt)
  have h2 := hs.const_mul (1 / (m : ℝ))
  have h3 : HasGradientAt (finiteSumObjective f) ((1 / (m : ℝ)) • ∑ i, gradient (f i) x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert h2 using 1
    simp [gradient, map_sum, map_smul]
  exact h3.gradient

theorem differentiable_fso {m n : ℕ} (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i, Differentiable ℝ (f i)) : Differentiable ℝ (finiteSumObjective f) := by
  unfold finiteSumObjective
  exact Differentiable.const_mul (Differentiable.fun_sum (fun i _ => hf i)) _

/-- gradient vanishes at a global minimizer -/
theorem gradient_min {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) (h : IsMinOn F Set.univ xs) :
    gradient F xs = 0 := by
  have hloc : IsLocalMin F xs := h.isLocalMin Filter.univ_mem
  rw [gradient, hloc.fderiv_eq_zero, map_zero]

/-- Per-step scalar expansion in a real inner product space. -/
lemma sag_step_aux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P p q r : E) (d a1 a2 b c X : ℝ) :
    a1 * ‖P + (q - p)‖ ^ 2 + a2 * X + 2 * b * inner ℝ (P + (q - p)) (r - d • (P + (q - p)))
      + c * ‖r - d • (P + (q - p))‖ ^ 2
    = (a1 - 2 * b * d + c * d ^ 2) *
        (‖P‖ ^ 2 + 2 * inner ℝ P q - 2 * inner ℝ P p
          + (‖q‖ ^ 2 - 2 * inner ℝ p q + ‖p‖ ^ 2))
      + a2 * X + 2 * (b - c * d) * (inner ℝ P r + inner ℝ q r - inner ℝ p r)
      + c * ‖r‖ ^ 2 := by
  have e1 : inner ℝ (P + (q - p)) (r - d • (P + (q - p)))
      = inner ℝ (P + (q - p)) r - d * ‖P + (q - p)‖ ^ 2 := by
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have e2 : ‖r - d • (P + (q - p))‖ ^ 2
      = ‖r‖ ^ 2 - 2 * d * inner ℝ (P + (q - p)) r + d ^ 2 * ‖P + (q - p)‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      real_inner_comm (P + (q - p)) r]
    ring
  have e3 : ‖P + (q - p)‖ ^ 2
      = ‖P‖ ^ 2 + 2 * inner ℝ P q - 2 * inner ℝ P p + (‖q‖ ^ 2 - 2 * inner ℝ p q + ‖p‖ ^ 2) := by
    rw [norm_add_sq_real, norm_sub_sq_real, inner_sub_right, real_inner_comm p q]
    ring
  have e4 : inner ℝ (P + (q - p)) r = inner ℝ P r + inner ℝ q r - inner ℝ p r := by
    rw [inner_add_left, inner_sub_left]
    ring
  rw [e1, e2, e4, e3]
  ring

/-- Expansion of the summed quadratic part of the SAG Lyapunov function after one step,
in terms of scalar "atoms". -/
theorem sag_expand {m n : ℕ} (x xs : EuclideanSpace ℝ (Fin n))
    (y z G : Fin m → EuclideanSpace ℝ (Fin n))
    (hz : ∑ i, z i = 0) (η a1 a2 b c : ℝ) :
    ∑ j : Fin m,
      (a1 * ‖∑ i, Function.update y j (G j) i‖ ^ 2
        + a2 * ∑ i, ‖Function.update y j (G j) i - z i‖ ^ 2
        + 2 * b * inner ℝ (∑ i, Function.update y j (G j) i)
            (x - η • ((1 / (m : ℝ)) • ∑ i, Function.update y j (G j) i) - xs)
        + c * ‖x - η • ((1 / (m : ℝ)) • ∑ i, Function.update y j (G j) i) - xs‖ ^ 2)
    = (a1 - 2 * b * (η / m) + c * (η / m) ^ 2) *
        ((m : ℝ) * ‖∑ i, y i‖ ^ 2
          + 2 * (inner ℝ (∑ i, y i) (∑ i, (G i - z i)) - ‖∑ i, y i‖ ^ 2)
          + (∑ i, ‖G i - z i‖ ^ 2 - 2 * ∑ i, inner ℝ (y i - z i) (G i - z i)
              + ∑ i, ‖y i - z i‖ ^ 2))
      + a2 * (((m : ℝ) - 1) * ∑ i, ‖y i - z i‖ ^ 2 + ∑ i, ‖G i - z i‖ ^ 2)
      + 2 * (b - c * (η / m)) *
          (((m : ℝ) - 1) * inner ℝ (∑ i, y i) (x - xs) + inner ℝ (∑ i, (G i - z i)) (x - xs))
      + (m : ℝ) * c * ‖x - xs‖ ^ 2 := by
  have hupd : ∀ j : Fin m,
      ∑ i, Function.update y j (G j) i = ∑ i, y i + ((G j - z j) - (y j - z j)) := by
    intro j
    rw [Finset.sum_update_of_mem (Finset.mem_univ j),
      Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ j) y]
    abel
  have hnorm : ∀ j : Fin m, ∑ i, ‖Function.update y j (G j) i - z i‖ ^ 2
      = ∑ i, ‖y i - z i‖ ^ 2 - ‖y j - z j‖ ^ 2 + ‖G j - z j‖ ^ 2 := by
    intro j
    have h1 : ∀ i, ‖Function.update y j (G j) i - z i‖ ^ 2
        = Function.update (fun k => ‖y k - z k‖ ^ 2) j (‖G j - z j‖ ^ 2) i := by
      intro i
      by_cases h : i = j
      · subst h; simp
      · simp [Function.update_of_ne h]
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_update_of_mem (Finset.mem_univ j),
      Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ j) (fun k => ‖y k - z k‖ ^ 2)]
    ring
  have hsmul : ∀ v : EuclideanSpace ℝ (Fin n),
      x - η • ((1 / (m : ℝ)) • v) - xs = (x - xs) - (η / m) • v := by
    intro v
    rw [smul_smul, mul_one_div]
    abel
  have hj : ∀ j : Fin m,
      (a1 * ‖∑ i, Function.update y j (G j) i‖ ^ 2
        + a2 * ∑ i, ‖Function.update y j (G j) i - z i‖ ^ 2
        + 2 * b * inner ℝ (∑ i, Function.update y j (G j) i)
            (x - η • ((1 / (m : ℝ)) • ∑ i, Function.update y j (G j) i) - xs)
        + c * ‖x - η • ((1 / (m : ℝ)) • ∑ i, Function.update y j (G j) i) - xs‖ ^ 2)
      = (a1 - 2 * b * (η / m) + c * (η / m) ^ 2) *
          (‖∑ i, y i‖ ^ 2 + 2 * inner ℝ (∑ i, y i) (G j - z j)
            - 2 * inner ℝ (∑ i, y i) (y j - z j)
            + (‖G j - z j‖ ^ 2 - 2 * inner ℝ (y j - z j) (G j - z j) + ‖y j - z j‖ ^ 2))
        + a2 * (∑ i, ‖y i - z i‖ ^ 2 - ‖y j - z j‖ ^ 2 + ‖G j - z j‖ ^ 2)
        + 2 * (b - c * (η / m)) *
            (inner ℝ (∑ i, y i) (x - xs) + inner ℝ (G j - z j) (x - xs)
              - inner ℝ (y j - z j) (x - xs))
        + c * ‖x - xs‖ ^ 2 := by
    intro j
    rw [hnorm j, hupd j, hsmul]
    exact sag_step_aux (∑ i, y i) (y j - z j) (G j - z j) (x - xs) (η / m) a1 a2 b c _
  rw [Finset.sum_congr rfl (fun j _ => hj j)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← inner_sum, ← sum_inner, hz, sub_zero,
    real_inner_self_eq_norm_sq]
  ring

open ProbabilityTheory in
theorem lyap_iter {m : ℕ} {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : ℕ → Ω → S) (I : ℕ → Ω → Fin m) (T : S → Fin m → S) (V : S → ℝ) (c : ℝ)
    (hs_meas : ∀ t, Measurable (s t)) (hI_meas : ∀ t, Measurable (I t))
    (hT_meas : ∀ j, Measurable fun p => T p j) (hV_meas : Measurable V)
    (hstep : ∀ t ω, s (t + 1) ω = T (s t ω) (I t ω))
    (hindep : ∀ t, IndepFun (I t) (s t) μ)
    (hunif : ∀ t j, μ (I t ⁻¹' {j}) = (m : ℝ≥0∞)⁻¹)
    (hc : 0 ≤ c)
    (hdec : ∀ p, (1 / (m : ℝ)) * ∑ j, V (T p j) ≤ c * V p)
    (hV_nonneg : ∀ p, 0 ≤ V p) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (V (s k ω)) ∂μ ≤
      ENNReal.ofReal (c ^ k) * ∫⁻ ω, ENNReal.ofReal (V (s 0 ω)) ∂μ := by
  have hOV : Measurable fun p => ENNReal.ofReal (V p) :=
    ENNReal.measurable_ofReal.comp hV_meas
  have hOVT : ∀ j, Measurable fun p => ENNReal.ofReal (V (T p j)) := fun j =>
    ENNReal.measurable_ofReal.comp (hV_meas.comp (hT_meas j))
  have hstep_ineq : ∀ t, ∫⁻ ω, ENNReal.ofReal (V (s (t+1) ω)) ∂μ ≤
      ENNReal.ofReal c * ∫⁻ ω, ENNReal.ofReal (V (s t ω)) ∂μ := by
    intro t
    have hm : 0 < m := by
      have hne : Nonempty Ω := by
        by_contra h
        rw [not_nonempty_iff] at h
        have h1 := measure_univ (μ := μ)
        rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at h1
        exact zero_ne_one h1
      obtain ⟨ω⟩ := hne
      exact Fin.pos (I 0 ω)
    have key : ∀ ω, ENNReal.ofReal (V (s (t+1) ω)) =
        ∑ j, (I t ⁻¹' {j}).indicator 1 ω * ENNReal.ofReal (V (T (s t ω) j)) := by
      intro ω
      rw [hstep, Finset.sum_eq_single (I t ω)]
      · simp [Set.indicator]
      · intro j _ hj
        simp [Set.indicator, Ne.symm hj]
      · simp
    have hfac : ∀ j, ∫⁻ ω, (I t ⁻¹' {j}).indicator 1 ω * ENNReal.ofReal (V (T (s t ω) j)) ∂μ
        = (m : ℝ≥0∞)⁻¹ * ∫⁻ ω, ENNReal.ofReal (V (T (s t ω) j)) ∂μ := by
      intro j
      have hind : IndepFun ((fun i => (({j} : Set (Fin m)).indicator (1 : Fin m → ℝ≥0∞) i)) ∘ I t)
          ((fun p => ENNReal.ofReal (V (T p j))) ∘ s t) μ :=
        (hindep t).comp (measurable_of_finite _) (hOVT j)
      have h1 := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
        ((measurable_of_finite _).comp (hI_meas t)) ((hOVT j).comp (hs_meas t)) hind
      have h2 : ∀ ω, (I t ⁻¹' {j}).indicator (1 : Ω → ℝ≥0∞) ω
          = ((fun i => (({j} : Set (Fin m)).indicator (1 : Fin m → ℝ≥0∞) i)) ∘ I t) ω := by
        intro ω
        simp [Set.indicator]
      simp_rw [h2]
      have h3 : ∫⁻ ω, ((fun i => (({j} : Set (Fin m)).indicator (1 : Fin m → ℝ≥0∞) i)) ∘ I t) ω
            * ENNReal.ofReal (V (T (s t ω) j)) ∂μ
          = (∫⁻ ω, ((fun i => (({j} : Set (Fin m)).indicator (1 : Fin m → ℝ≥0∞) i)) ∘ I t) ω ∂μ)
            * ∫⁻ ω, ENNReal.ofReal (V (T (s t ω) j)) ∂μ := h1
      rw [h3]
      congr 1
      rw [← hunif t j, ← lintegral_indicator_one (measurableSet_singleton j |>.preimage (hI_meas t))]
      exact lintegral_congr (fun ω => (h2 ω).symm)
    calc ∫⁻ ω, ENNReal.ofReal (V (s (t+1) ω)) ∂μ
        = ∫⁻ ω, ∑ j, (I t ⁻¹' {j}).indicator 1 ω * ENNReal.ofReal (V (T (s t ω) j)) ∂μ := by
          exact lintegral_congr (fun ω => key ω)
      _ = ∑ j, ∫⁻ ω, (I t ⁻¹' {j}).indicator 1 ω * ENNReal.ofReal (V (T (s t ω) j)) ∂μ := by
          rw [lintegral_finset_sum]
          intro j _
          exact ((measurable_one.indicator
            (measurableSet_singleton j |>.preimage (hI_meas t)))).mul ((hOVT j).comp (hs_meas t))
      _ = ∑ j, (m : ℝ≥0∞)⁻¹ * ∫⁻ ω, ENNReal.ofReal (V (T (s t ω) j)) ∂μ := by
          exact Finset.sum_congr rfl (fun j _ => hfac j)
      _ = ∫⁻ ω, (m : ℝ≥0∞)⁻¹ * ∑ j, ENNReal.ofReal (V (T (s t ω) j)) ∂μ := by
          rw [lintegral_const_mul, lintegral_finset_sum, Finset.mul_sum]
          · intro j _
            exact (hOVT j).comp (hs_meas t)
          · exact Finset.measurable_sum _ (fun j _ => (hOVT j).comp (hs_meas t))
      _ ≤ ∫⁻ ω, ENNReal.ofReal c * ENNReal.ofReal (V (s t ω)) ∂μ := by
          apply lintegral_mono
          intro ω
          dsimp only
          have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
          rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hV_nonneg _), ← ENNReal.ofReal_mul hc,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hmpos,
            ← ENNReal.ofReal_mul (inv_nonneg.mpr hmpos.le)]
          apply ENNReal.ofReal_le_ofReal
          have := hdec (s t ω)
          rw [one_div] at this
          exact this
      _ = ENNReal.ofReal c * ∫⁻ ω, ENNReal.ofReal (V (s t ω)) ∂μ :=
          lintegral_const_mul _ (hOV.comp (hs_meas t))
  induction k with
  | zero => simp
  | succ k ih =>
    calc ∫⁻ ω, ENNReal.ofReal (V (s (k+1) ω)) ∂μ
        ≤ ENNReal.ofReal c * ∫⁻ ω, ENNReal.ofReal (V (s k ω)) ∂μ := hstep_ineq k
      _ ≤ ENNReal.ofReal c * (ENNReal.ofReal (c ^ k) * ∫⁻ ω, ENNReal.ofReal (V (s 0 ω)) ∂μ) := by
          gcongr
      _ = ENNReal.ofReal (c ^ (k+1)) * ∫⁻ ω, ENNReal.ofReal (V (s 0 ω)) ∂μ := by
          rw [pow_succ, ENNReal.ofReal_mul (pow_nonneg hc k), ← mul_assoc, mul_comm (ENNReal.ofReal c)]

lemma side_P1 (x y : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 1/2) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ 64*x^6 - 48*x^5*y - 320*x^5 + 160*x^4*y + 896*x^4 + 4*x^3*y^3 + 8*x^3*y^2 - 256*x^3*y - 1520*x^3 - 4*x^2*y^3 - 44*x^2*y^2 + 160*x^2*y + 1344*x^2 + x*y^3 + 20*x*y^2 + 48*x*y - 240*x + 224 := by
  have ht : 0 ≤ 2 * x := by linarith
  have hu : 0 ≤ 1 - 2 * x := by linarith
  have hv : 0 ≤ 1 - y := by linarith
  linarith [mul_nonneg (mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 6)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 3)), mul_nonneg (mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 6)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 6)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 6)) (mul_nonneg (pow_nonneg hy 3) (pow_nonneg hv 0)), mul_nonneg (mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 5)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 3)), mul_nonneg (mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 5)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 5)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 5)) (mul_nonneg (pow_nonneg hy 3) (pow_nonneg hv 0)), mul_nonneg (mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 4)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 3)), mul_nonneg (mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 4)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 4)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 4)) (mul_nonneg (pow_nonneg hy 3) (pow_nonneg hv 0)), mul_nonneg (mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 3)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 3)), mul_nonneg (mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 3)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 3)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 3)) (mul_nonneg (pow_nonneg hy 3) (pow_nonneg hv 0)), mul_nonneg (mul_nonneg (pow_nonneg ht 4) (pow_nonneg hu 2)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 3)), mul_nonneg (mul_nonneg (pow_nonneg ht 4) (pow_nonneg hu 2)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 4) (pow_nonneg hu 2)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 4) (pow_nonneg hu 2)) (mul_nonneg (pow_nonneg hy 3) (pow_nonneg hv 0)), mul_nonneg (mul_nonneg (pow_nonneg ht 5) (pow_nonneg hu 1)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 3)), mul_nonneg (mul_nonneg (pow_nonneg ht 5) (pow_nonneg hu 1)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 5) (pow_nonneg hu 1)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 5) (pow_nonneg hu 1)) (mul_nonneg (pow_nonneg hy 3) (pow_nonneg hv 0)), mul_nonneg (mul_nonneg (pow_nonneg ht 6) (pow_nonneg hu 0)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 3)), mul_nonneg (mul_nonneg (pow_nonneg ht 6) (pow_nonneg hu 0)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 6) (pow_nonneg hu 0)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 6) (pow_nonneg hu 0)) (mul_nonneg (pow_nonneg hy 3) (pow_nonneg hv 0))]

lemma side_P2 (x y : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 1/2) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ 64*x^7*y - 48*x^6*y^2 - 320*x^6*y + 160*x^5*y^2 + 960*x^5*y + 4*x^4*y^4 + 8*x^4*y^3 - 272*x^4*y^2 - 1776*x^4*y - 4*x^3*y^4 - 52*x^3*y^3 + 192*x^3*y^2 + 1856*x^3*y + x^2*y^4 + 32*x^2*y^3 + 64*x^2*y^2 - 1207*x^2*y - 4*x*y^3 - 144*x*y^2 + 1081*x*y - 784*x + 56*y^2 - 406*y + 672 := by
  have ht : 0 ≤ 2 * x := by linarith
  have hu : 0 ≤ 1 - 2 * x := by linarith
  have hv : 0 ≤ 1 - y := by linarith
  linarith [mul_nonneg (mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 7)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 4)), mul_nonneg (mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 7)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 3)), mul_nonneg (mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 7)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 7)) (mul_nonneg (pow_nonneg hy 3) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 7)) (mul_nonneg (pow_nonneg hy 4) (pow_nonneg hv 0)), mul_nonneg (mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 6)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 4)), mul_nonneg (mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 6)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 3)), mul_nonneg (mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 6)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 6)) (mul_nonneg (pow_nonneg hy 3) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 6)) (mul_nonneg (pow_nonneg hy 4) (pow_nonneg hv 0)), mul_nonneg (mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 5)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 4)), mul_nonneg (mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 5)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 3)), mul_nonneg (mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 5)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 5)) (mul_nonneg (pow_nonneg hy 3) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 5)) (mul_nonneg (pow_nonneg hy 4) (pow_nonneg hv 0)), mul_nonneg (mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 4)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 4)), mul_nonneg (mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 4)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 3)), mul_nonneg (mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 4)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 4)) (mul_nonneg (pow_nonneg hy 3) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 4)) (mul_nonneg (pow_nonneg hy 4) (pow_nonneg hv 0)), mul_nonneg (mul_nonneg (pow_nonneg ht 4) (pow_nonneg hu 3)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 4)), mul_nonneg (mul_nonneg (pow_nonneg ht 4) (pow_nonneg hu 3)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 3)), mul_nonneg (mul_nonneg (pow_nonneg ht 4) (pow_nonneg hu 3)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 4) (pow_nonneg hu 3)) (mul_nonneg (pow_nonneg hy 3) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 4) (pow_nonneg hu 3)) (mul_nonneg (pow_nonneg hy 4) (pow_nonneg hv 0)), mul_nonneg (mul_nonneg (pow_nonneg ht 5) (pow_nonneg hu 2)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 4)), mul_nonneg (mul_nonneg (pow_nonneg ht 5) (pow_nonneg hu 2)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 3)), mul_nonneg (mul_nonneg (pow_nonneg ht 5) (pow_nonneg hu 2)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 5) (pow_nonneg hu 2)) (mul_nonneg (pow_nonneg hy 3) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 5) (pow_nonneg hu 2)) (mul_nonneg (pow_nonneg hy 4) (pow_nonneg hv 0)), mul_nonneg (mul_nonneg (pow_nonneg ht 6) (pow_nonneg hu 1)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 4)), mul_nonneg (mul_nonneg (pow_nonneg ht 6) (pow_nonneg hu 1)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 3)), mul_nonneg (mul_nonneg (pow_nonneg ht 6) (pow_nonneg hu 1)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 6) (pow_nonneg hu 1)) (mul_nonneg (pow_nonneg hy 3) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 6) (pow_nonneg hu 1)) (mul_nonneg (pow_nonneg hy 4) (pow_nonneg hv 0)), mul_nonneg (mul_nonneg (pow_nonneg ht 7) (pow_nonneg hu 0)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 4)), mul_nonneg (mul_nonneg (pow_nonneg ht 7) (pow_nonneg hu 0)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 3)), mul_nonneg (mul_nonneg (pow_nonneg ht 7) (pow_nonneg hu 0)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 7) (pow_nonneg hu 0)) (mul_nonneg (pow_nonneg hy 3) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 7) (pow_nonneg hu 0)) (mul_nonneg (pow_nonneg hy 4) (pow_nonneg hv 0))]

lemma side_P3 (x y : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 1/2) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ 64*x^7*y - 48*x^6*y^2 - 320*x^6*y + 160*x^5*y^2 + 1024*x^5*y + 4*x^4*y^4 + 8*x^4*y^3 - 288*x^4*y^2 - 2032*x^4*y - 4*x^3*y^4 - 60*x^3*y^3 + 224*x^3*y^2 + 2432*x^3*y + x^2*y^4 + 44*x^2*y^3 + 96*x^2*y^2 - 1918*x^2*y - 8*x*y^3 - 208*x*y^2 + 1458*x*y - 672*x + 72*y^2 - 428*y + 448 := by
  have ht : 0 ≤ 2 * x := by linarith
  have hu : 0 ≤ 1 - 2 * x := by linarith
  have hv : 0 ≤ 1 - y := by linarith
  linarith [mul_nonneg (mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 7)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 4)), mul_nonneg (mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 7)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 3)), mul_nonneg (mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 7)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 7)) (mul_nonneg (pow_nonneg hy 3) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 7)) (mul_nonneg (pow_nonneg hy 4) (pow_nonneg hv 0)), mul_nonneg (mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 6)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 4)), mul_nonneg (mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 6)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 3)), mul_nonneg (mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 6)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 6)) (mul_nonneg (pow_nonneg hy 3) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 6)) (mul_nonneg (pow_nonneg hy 4) (pow_nonneg hv 0)), mul_nonneg (mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 5)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 4)), mul_nonneg (mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 5)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 3)), mul_nonneg (mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 5)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 5)) (mul_nonneg (pow_nonneg hy 3) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 5)) (mul_nonneg (pow_nonneg hy 4) (pow_nonneg hv 0)), mul_nonneg (mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 4)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 4)), mul_nonneg (mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 4)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 3)), mul_nonneg (mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 4)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 4)) (mul_nonneg (pow_nonneg hy 3) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 4)) (mul_nonneg (pow_nonneg hy 4) (pow_nonneg hv 0)), mul_nonneg (mul_nonneg (pow_nonneg ht 4) (pow_nonneg hu 3)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 4)), mul_nonneg (mul_nonneg (pow_nonneg ht 4) (pow_nonneg hu 3)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 3)), mul_nonneg (mul_nonneg (pow_nonneg ht 4) (pow_nonneg hu 3)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 4) (pow_nonneg hu 3)) (mul_nonneg (pow_nonneg hy 3) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 4) (pow_nonneg hu 3)) (mul_nonneg (pow_nonneg hy 4) (pow_nonneg hv 0)), mul_nonneg (mul_nonneg (pow_nonneg ht 5) (pow_nonneg hu 2)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 4)), mul_nonneg (mul_nonneg (pow_nonneg ht 5) (pow_nonneg hu 2)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 3)), mul_nonneg (mul_nonneg (pow_nonneg ht 5) (pow_nonneg hu 2)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 5) (pow_nonneg hu 2)) (mul_nonneg (pow_nonneg hy 3) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 5) (pow_nonneg hu 2)) (mul_nonneg (pow_nonneg hy 4) (pow_nonneg hv 0)), mul_nonneg (mul_nonneg (pow_nonneg ht 6) (pow_nonneg hu 1)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 4)), mul_nonneg (mul_nonneg (pow_nonneg ht 6) (pow_nonneg hu 1)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 3)), mul_nonneg (mul_nonneg (pow_nonneg ht 6) (pow_nonneg hu 1)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 6) (pow_nonneg hu 1)) (mul_nonneg (pow_nonneg hy 3) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 6) (pow_nonneg hu 1)) (mul_nonneg (pow_nonneg hy 4) (pow_nonneg hv 0)), mul_nonneg (mul_nonneg (pow_nonneg ht 7) (pow_nonneg hu 0)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 4)), mul_nonneg (mul_nonneg (pow_nonneg ht 7) (pow_nonneg hu 0)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 3)), mul_nonneg (mul_nonneg (pow_nonneg ht 7) (pow_nonneg hu 0)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 7) (pow_nonneg hu 0)) (mul_nonneg (pow_nonneg hy 3) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 7) (pow_nonneg hu 0)) (mul_nonneg (pow_nonneg hy 4) (pow_nonneg hv 0))]

lemma side_P4 (x y : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 1/2) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ 2*x^3*y^2 + 32*x^3 - x^2*y^2 - 8*x^2*y - 160*x^2 - 4*x*y + 160*x - 8*y + 8 := by
  have ht : 0 ≤ 2 * x := by linarith
  have hu : 0 ≤ 1 - 2 * x := by linarith
  have hv : 0 ≤ 1 - y := by linarith
  linarith [mul_nonneg (mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 3)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 3)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 3)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 0)), mul_nonneg (mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 2)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 2)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 2)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 0)), mul_nonneg (mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 1)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 1)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 1)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 0)), mul_nonneg (mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 0)) (mul_nonneg (pow_nonneg hy 0) (pow_nonneg hv 2)), mul_nonneg (mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 0)) (mul_nonneg (pow_nonneg hy 1) (pow_nonneg hv 1)), mul_nonneg (mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 0)) (mul_nonneg (pow_nonneg hy 2) (pow_nonneg hv 0))]


set_option maxHeartbeats 2000000 in
theorem core_norm (x y : ℝ) (hx0 : 0 < x) (hx : x ≤ 1/2) (hy0 : 0 < y) (hy : y ≤ 1)
    (phx phu Ph2 PhQh Qh2 Phr Qhr rr pph qqh pqh : ℝ)
    (f_s1 : 0 ≤ phu - phx - PhQh / 16 - x * y / 256 * Ph2)
    (f_s2 : 0 ≤ Qhr - x * y * rr - phx)
    (f_s4 : 0 ≤ phx - x * y * rr)
    (f_cc : 0 ≤ Qhr - qqh)
    (CS : ∀ s t : ℝ, 0 ≤ (s ^ 2 * pph - 2 * s * t * pqh + t ^ 2 * qqh)
      - (s ^ 2 * Ph2 - 2 * s * t * PhQh + t ^ 2 * Qh2))
    (sqP : ∀ k1 k2 : ℝ, 0 ≤ Ph2 - 2 * k1 * PhQh - 2 * k2 * Phr + k1 ^ 2 * Qh2
      + 2 * k1 * k2 * Qhr + k2 ^ 2 * rr)
    (sqQ : ∀ k : ℝ, 0 ≤ Qh2 - 2 * k * Qhr + k ^ 2 * rr)
    (hPh2 : 0 ≤ Ph2) (hrr : 0 ≤ rr) :
    Ph2*x^2/32 - Ph2*x*y/512 - 3*Ph2*x/64 + Ph2*y/256 - Ph2/32 - PhQh*x^2/32 + PhQh*x/32 + PhQh/16 + Phr*x^2*y/16 - Phr*x*y/16 - Qhr*x/2 - phu*x^2*y/4 + phu*x*y/8 + 2*phu*x - phu - 2*phx*x + phx - pph*x^3/64 - pph*x^2*y/256 + 3*pph*x^2/64 + pph*x*y/128 - pph*x/32 + pqh*x^3/32 - pqh*x^2/32 - pqh*x/16 - qqh*x^3/64 - qqh*x^2/64 + 3*qqh*x/32 + rr*x^2*y/2 ≤ 0 := by
  have hs : 0 < 4 - 4 * x - y := by linarith
  have h1 := CS (-(4 - 4 * x - y)) (4 * (x + 1))
  have h2 := sqP (x * (4 * x ^ 2 - 2 * x * y - 8 * x + y + 12) / 7) (8 * x * y * (x - 1) / 7)
  have h3 := sqQ (2 * x * y)
  have q1 := side_P1 x y hx0.le hx hy0.le hy
  have q2 := side_P2 x y hx0.le hx hy0.le hy
  have q3 := side_P3 x y hx0.le hx hy0.le hy
  have q4 := side_P4 x y hx0.le hx hy0.le hy
  have m1 : 0 ≤ (4 - 4 * x - y) * (1 - 2 * x) * (1 - x * y / 8) := by
    apply mul_nonneg; apply mul_nonneg <;> linarith
    nlinarith
  have m2 : 0 ≤ (4 - 4 * x - y) * (x * y / 4) * (1 / 2 - x) := by
    apply mul_nonneg; apply mul_nonneg; linarith; positivity
    linarith
  have m3 : 0 ≤ x * (2 - x) / 256 := by apply div_nonneg; apply mul_nonneg <;> linarith; norm_num
  have m4 : 0 ≤ x * (2 - x) * (16 - 3 * y - x * y) / 64 := by
    apply div_nonneg; apply mul_nonneg; apply mul_nonneg <;> linarith
    nlinarith
    norm_num
  have m5 : 0 ≤ (4 - 4 * x - y) * 7 / 256 := by apply div_nonneg <;> linarith
  have m6 : 0 ≤ x * (64*x^6 - 48*x^5*y - 320*x^5 + 160*x^4*y + 896*x^4 + 4*x^3*y^3 + 8*x^3*y^2 - 256*x^3*y - 1520*x^3 - 4*x^2*y^3 - 44*x^2*y^2 + 160*x^2*y + 1344*x^2 + x*y^3 + 20*x*y^2 + 48*x*y - 240*x + 224) / 1792 := by apply div_nonneg; exact mul_nonneg hx0.le q1; norm_num
  have m7 : 0 ≤ x * (64*x^7*y - 48*x^6*y^2 - 320*x^6*y + 160*x^5*y^2 + 960*x^5*y + 4*x^4*y^4 + 8*x^4*y^3 - 272*x^4*y^2 - 1776*x^4*y - 4*x^3*y^4 - 52*x^3*y^3 + 192*x^3*y^2 + 1856*x^3*y + x^2*y^4 + 32*x^2*y^3 + 64*x^2*y^2 - 1207*x^2*y - 4*x*y^3 - 144*x*y^2 + 1081*x*y - 784*x + 56*y^2 - 406*y + 672) / 448 := by apply div_nonneg; exact mul_nonneg hx0.le q2; norm_num
  have m8 : 0 ≤ (4 - 4 * x - y) * (2*x^3*y^2 + 32*x^3 - x^2*y^2 - 8*x^2*y - 160*x^2 - 4*x*y + 160*x - 8*y + 8) / 2048 := by apply div_nonneg; exact mul_nonneg hs.le q4; norm_num
  have m9 : 0 ≤ x ^ 2 * y * (64*x^7*y - 48*x^6*y^2 - 320*x^6*y + 160*x^5*y^2 + 1024*x^5*y + 4*x^4*y^4 + 8*x^4*y^3 - 288*x^4*y^2 - 2032*x^4*y - 4*x^3*y^4 - 60*x^3*y^3 + 224*x^3*y^2 + 2432*x^3*y + x^2*y^4 + 44*x^2*y^3 + 96*x^2*y^2 - 1918*x^2*y - 8*x*y^3 - 208*x*y^2 + 1458*x*y - 672*x + 72*y^2 - 428*y + 448) / 448 := by
    apply div_nonneg; exact mul_nonneg (mul_nonneg (sq_nonneg x) hy0.le) q3; norm_num
  have f_sm : 0 ≤ (Qhr - x * y * rr - phx) + (phx - x * y * rr) := by linarith
  have key : (4 - 4 * x - y) * (Ph2*x^2/32 - Ph2*x*y/512 - 3*Ph2*x/64 + Ph2*y/256 - Ph2/32 - PhQh*x^2/32 + PhQh*x/32 + PhQh/16 + Phr*x^2*y/16 - Phr*x*y/16 - Qhr*x/2 - phu*x^2*y/4 + phu*x*y/8 + 2*phu*x - phu - 2*phx*x + phx - pph*x^3/64 - pph*x^2*y/256 + 3*pph*x^2/64 + pph*x*y/128 - pph*x/32 + pqh*x^3/32 - pqh*x^2/32 - pqh*x/16 - qqh*x^3/64 - qqh*x^2/64 + 3*qqh*x/32 + rr*x^2*y/2) ≤ 0 := by
    linarith only [mul_nonneg m1 f_s1, mul_nonneg m2 f_s2, mul_nonneg m3 h1, mul_nonneg m4 f_cc,
      mul_nonneg m5 h2, mul_nonneg m6 h3, mul_nonneg m7 f_sm, mul_nonneg m8 hPh2, mul_nonneg m9 hrr]
  by_contra hc
  push_neg at hc
  have := mul_pos hs hc
  linarith


theorem dom_norm (x y : ℝ) (hx0 : 0 < x) (hx : x ≤ 1/2) (hy0 : 0 ≤ y)
    (phx phu Ph2 PhQh Qh2 Phr Qhr rr pph : ℝ)
    (f_s1 : 0 ≤ phu - phx - PhQh / 16 - x * y / 256 * Ph2)
    (f_s6 : 0 ≤ rr / 2 - phx)
    (f_cs : 0 ≤ pph - Ph2)
    (f_coco : 0 ≤ Qhr - Qh2)
    (hQhr : 0 ≤ Qhr)
    (sqP : ∀ k1 k2 : ℝ, 0 ≤ Ph2 - 2 * k1 * PhQh - 2 * k2 * Phr + k1 ^ 2 * Qh2
      + 2 * k1 * k2 * Qhr + k2 ^ 2 * rr)
    (hPh2 : 0 ≤ Ph2) (hrr : 0 ≤ rr) :
    x * phx ≤ -Ph2*x/64 + Ph2/32 + Phr*x^2/2 - Phr*x/2 - 2*phu*x^2 + phu*x - pph*x^2/32
      + pph*x/16 + 4*rr*x^2 := by
  have h2 := sqP (-(5/2) * (1/2 - x) * x) (10 * x * (1 - x))
  have m1 : 0 ≤ 2 * (1/2 - x) * x := by apply mul_nonneg <;> linarith
  have m2 : 0 ≤ 2 * x ^ 2 := by positivity
  have m3 : 0 ≤ (x / 16) * (1 - x / 2) := by apply mul_nonneg <;> linarith
  have m4 : 0 ≤ (1:ℝ) / 40 := by norm_num
  have m5 : 0 ≤ (1:ℝ) / 40 * (-(5/2) * (1/2 - x) * x) ^ 2 := by positivity
  have m6 : 0 ≤ -(10*x^3*y - 5*x^2*y + 40*x^2 - 60*x - 8)/1280 := by
    have : 0 ≤ 5 * x ^ 2 * y * (1 - 2 * x) := by
      apply mul_nonneg; positivity; linarith
    nlinarith
  have m7 : 0 ≤ 5*x^2*(1 - 2*x)*(15 - 14*x)/128 := by
    apply div_nonneg; apply mul_nonneg; apply mul_nonneg; positivity; linarith; linarith; norm_num
  have m8 : 0 ≤ x^2*(1 + 10*x - 5*x^2)/2 := by
    apply div_nonneg; apply mul_nonneg; positivity; nlinarith; norm_num
  linarith only [mul_nonneg m1 f_s1, mul_nonneg m2 f_s6, mul_nonneg m3 f_cs, mul_nonneg m4 h2,
    mul_nonneg m5 f_coco, mul_nonneg m6 hPh2, mul_nonneg m7 hQhr, mul_nonneg m8 hrr]


noncomputable def lyH (M : ℝ) : ℝ := 1 / 2 - 1 / M
noncomputable def lyA1 (M L : ℝ) : ℝ := (1 / (32 * M * L)) * (1 - 1 / (2 * M))
noncomputable def lyA2 (M L : ℝ) : ℝ := (1 / (16 * M * L)) * (1 - 1 / (2 * M))
noncomputable def lyB (M : ℝ) : ℝ := -(1 / (4 * M)) * (1 - 1 / M)
noncomputable def lyC (M L : ℝ) : ℝ := 4 * L / M

noncomputable def DnFun (x y phx phu Ph2 PhQh Phr Qhr rr pph qqh pqh : ℝ) : ℝ :=
  Ph2*x^2/32 - Ph2*x*y/512 - 3*Ph2*x/64 + Ph2*y/256 - Ph2/32 - PhQh*x^2/32 + PhQh*x/32 + PhQh/16 + Phr*x^2*y/16 - Phr*x*y/16 - Qhr*x/2 - phu*x^2*y/4 + phu*x*y/8 + 2*phu*x - phu - 2*phx*x + phx - pph*x^3/64 - pph*x^2*y/256 + 3*pph*x^2/64 + pph*x*y/128 - pph*x/32 + pqh*x^3/32 - pqh*x^2/32 - pqh*x/16 - qqh*x^3/64 - qqh*x^2/64 + 3*qqh*x/32 + rr*x^2*y/2

noncomputable def DomFun (x phu Ph2 Phr rr pph : ℝ) : ℝ :=
  -Ph2*x/64 + Ph2/32 + Phr*x^2/2 - Phr*x/2 - 2*phu*x^2 + phu*x - pph*x^2/32 + pph*x/16 + 4*rr*x^2

theorem raw_bounds (M L a φx φu PP PQ QQ Pr Qr rr pp qq pq : ℝ)
    (hM : 2 ≤ M) (hL : 0 < L) (ha : 0 < a) (haM : a ≤ 2 * L / M)
    (s1 : φx + PQ / (16 * L * M ^ 2) + a / 2 * (PP / (16 * L * M) ^ 2) ≤ φu)
    (s2 : φx ≤ Qr / M - a / 2 * rr)
    (s4 : a / 2 * rr ≤ φx)
    (s6 : φx ≤ L / 2 * rr)
    (cc : qq ≤ L * Qr)
    (CS : ∀ s t : ℝ, s ^ 2 * PP - 2 * s * t * PQ + t ^ 2 * QQ
      ≤ M * (s ^ 2 * pp - 2 * s * t * pq + t ^ 2 * qq))
    (sqP : ∀ k1 k2 : ℝ, 0 ≤ PP - 2 * k1 * PQ - 2 * k2 * Pr + k1 ^ 2 * QQ
      + 2 * k1 * k2 * Qr + k2 ^ 2 * rr)
    (sqQ : ∀ k : ℝ, 0 ≤ QQ - 2 * k * Qr + k ^ 2 * rr)
    (hPP : 0 ≤ PP) (hrr : 0 ≤ rr) :
    (2 * lyH M * φx + (1 / M) * ((lyA1 M L - 2 * lyB M * ((1 / (16 * L)) / M)
        + lyC M L * ((1 / (16 * L)) / M) ^ 2) * (M * PP + 2 * (PQ - PP) + (qq - 2 * pq + pp))
        + lyA2 M L * ((M - 1) * pp + qq)
        + 2 * (lyB M - lyC M L * ((1 / (16 * L)) / M)) * ((M - 1) * Pr + Qr)
        + M * lyC M L * rr)
      ≤ (1 - a / (16 * L)) * (2 * lyH M * φu + lyA1 M L * PP + lyA2 M L * pp
        + 2 * lyB M * Pr + lyC M L * rr))
    ∧ φx ≤ 2 * lyH M * φu + lyA1 M L * PP + lyA2 M L * pp + 2 * lyB M * Pr + lyC M L * rr := by
  have hM0 : 0 < M := by linarith
  have hM' : M ≠ 0 := ne_of_gt hM0
  have hL' : L ≠ 0 := ne_of_gt hL
  have hx0 : 0 < 1 / M := by positivity
  have hx : 1 / M ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hM0 (by norm_num)]; linarith
  have hy0 : 0 < M * a / (2 * L) := by positivity
  have haM' : a * M ≤ 2 * L := by rwa [le_div_iff₀ hM0] at haM
  have hy : M * a / (2 * L) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  -- normalized facts
  have f_s1 : 0 ≤ φu / L - φx / L - (PQ / (M ^ 2 * L ^ 2)) / 16
      - (1 / M) * (M * a / (2 * L)) / 256 * (PP / (M ^ 2 * L ^ 2)) := by
    have e : φu / L - φx / L - (PQ / (M ^ 2 * L ^ 2)) / 16
        - (1 / M) * (M * a / (2 * L)) / 256 * (PP / (M ^ 2 * L ^ 2))
        = (φu - (φx + PQ / (16 * L * M ^ 2) + a / 2 * (PP / (16 * L * M) ^ 2))) / L := by
      field_simp
      ring
    rw [e]; apply div_nonneg _ hL.le; linarith
  have f_s2 : 0 ≤ Qr / (M * L) - (1 / M) * (M * a / (2 * L)) * rr - φx / L := by
    have e : Qr / (M * L) - (1 / M) * (M * a / (2 * L)) * rr - φx / L
        = (Qr / M - a / 2 * rr - φx) / L := by field_simp
    rw [e]; apply div_nonneg _ hL.le; linarith
  have f_s4 : 0 ≤ φx / L - (1 / M) * (M * a / (2 * L)) * rr := by
    have e : φx / L - (1 / M) * (M * a / (2 * L)) * rr = (φx - a / 2 * rr) / L := by
      field_simp
    rw [e]; apply div_nonneg _ hL.le; linarith
  have f_s6 : 0 ≤ rr / 2 - φx / L := by
    have e : rr / 2 - φx / L = (L / 2 * rr - φx) / L := by field_simp
    rw [e]; apply div_nonneg _ hL.le; linarith
  have f_cc : 0 ≤ Qr / (M * L) - qq / (M * L ^ 2) := by
    have e : Qr / (M * L) - qq / (M * L ^ 2) = (L * Qr - qq) / (M * L ^ 2) := by
      field_simp
    rw [e]; apply div_nonneg _ (by positivity); linarith
  have f_CS : ∀ s t : ℝ, 0 ≤ (s ^ 2 * (pp / (M * L ^ 2)) - 2 * s * t * (pq / (M * L ^ 2))
      + t ^ 2 * (qq / (M * L ^ 2))) - (s ^ 2 * (PP / (M ^ 2 * L ^ 2))
      - 2 * s * t * (PQ / (M ^ 2 * L ^ 2)) + t ^ 2 * (QQ / (M ^ 2 * L ^ 2))) := by
    intro s t
    have e : (s ^ 2 * (pp / (M * L ^ 2)) - 2 * s * t * (pq / (M * L ^ 2))
      + t ^ 2 * (qq / (M * L ^ 2))) - (s ^ 2 * (PP / (M ^ 2 * L ^ 2))
      - 2 * s * t * (PQ / (M ^ 2 * L ^ 2)) + t ^ 2 * (QQ / (M ^ 2 * L ^ 2)))
      = (M * (s ^ 2 * pp - 2 * s * t * pq + t ^ 2 * qq)
          - (s ^ 2 * PP - 2 * s * t * PQ + t ^ 2 * QQ)) / (M ^ 2 * L ^ 2) := by
      field_simp
    rw [e]; apply div_nonneg _ (by positivity); linarith [CS s t]
  have f_sqP : ∀ k1 k2 : ℝ, 0 ≤ PP / (M ^ 2 * L ^ 2) - 2 * k1 * (PQ / (M ^ 2 * L ^ 2))
      - 2 * k2 * (Pr / (M * L)) + k1 ^ 2 * (QQ / (M ^ 2 * L ^ 2))
      + 2 * k1 * k2 * (Qr / (M * L)) + k2 ^ 2 * rr := by
    intro k1 k2
    have e : PP / (M ^ 2 * L ^ 2) - 2 * k1 * (PQ / (M ^ 2 * L ^ 2))
      - 2 * k2 * (Pr / (M * L)) + k1 ^ 2 * (QQ / (M ^ 2 * L ^ 2))
      + 2 * k1 * k2 * (Qr / (M * L)) + k2 ^ 2 * rr
      = (PP - 2 * k1 * PQ - 2 * (k2 * M * L) * Pr + k1 ^ 2 * QQ
          + 2 * k1 * (k2 * M * L) * Qr + (k2 * M * L) ^ 2 * rr) / (M ^ 2 * L ^ 2) := by
      field_simp
    rw [e]; exact div_nonneg (sqP k1 (k2 * M * L)) (by positivity)
  have f_sqQ : ∀ k : ℝ, 0 ≤ QQ / (M ^ 2 * L ^ 2) - 2 * k * (Qr / (M * L)) + k ^ 2 * rr := by
    intro k
    have e : QQ / (M ^ 2 * L ^ 2) - 2 * k * (Qr / (M * L)) + k ^ 2 * rr
      = (QQ - 2 * (k * M * L) * Qr + (k * M * L) ^ 2 * rr) / (M ^ 2 * L ^ 2) := by
      field_simp
    rw [e]; exact div_nonneg (sqQ (k * M * L)) (by positivity)
  have hPh2 : 0 ≤ PP / (M ^ 2 * L ^ 2) := by positivity
  have hQhr : 0 ≤ Qr / (M * L) := by
    apply div_nonneg _ (by positivity)
    have : 0 ≤ Qr / M - a * rr := by linarith
    have h2 : 0 ≤ a * rr := mul_nonneg ha.le hrr
    have h3 : 0 ≤ Qr / M := by linarith
    have := mul_nonneg h3 hM0.le
    rwa [div_mul_cancel₀ _ hM'] at this
  have f_cs10 : 0 ≤ pp / (M * L ^ 2) - PP / (M ^ 2 * L ^ 2) := by
    have h := f_CS 1 0
    simp only [one_pow, zero_pow two_ne_zero, mul_zero, sub_zero, zero_mul, add_zero, mul_one] at h
    linarith
  have f_coco : 0 ≤ Qr / (M * L) - QQ / (M ^ 2 * L ^ 2) := by
    have h := f_CS 0 1
    simp only [one_pow, zero_pow two_ne_zero, mul_zero, sub_zero, zero_mul, zero_add, mul_one] at h
    linarith
  have hD := core_norm (1 / M) (M * a / (2 * L)) hx0 hx hy0 hy (φx / L) (φu / L)
    (PP / (M ^ 2 * L ^ 2)) (PQ / (M ^ 2 * L ^ 2)) (QQ / (M ^ 2 * L ^ 2)) (Pr / (M * L))
    (Qr / (M * L)) rr (pp / (M * L ^ 2)) (qq / (M * L ^ 2)) (pq / (M * L ^ 2))
    f_s1 f_s2 f_s4 f_cc f_CS f_sqP f_sqQ hPh2 hrr
  have hDom := dom_norm (1 / M) (M * a / (2 * L)) hx0 hx hy0.le (φx / L) (φu / L)
    (PP / (M ^ 2 * L ^ 2)) (PQ / (M ^ 2 * L ^ 2)) (QQ / (M ^ 2 * L ^ 2)) (Pr / (M * L))
    (Qr / (M * L)) rr (pp / (M * L ^ 2)) f_s1 f_s6 f_cs10 f_coco hQhr f_sqP hPh2 hrr
  have hD' : DnFun (1 / M) (M * a / (2 * L)) (φx / L) (φu / L)
    (PP / (M ^ 2 * L ^ 2)) (PQ / (M ^ 2 * L ^ 2)) (Pr / (M * L))
    (Qr / (M * L)) rr (pp / (M * L ^ 2)) (qq / (M * L ^ 2)) (pq / (M * L ^ 2)) ≤ 0 := by
    unfold DnFun; exact hD
  have hDom' : (1 / M) * (φx / L) ≤ DomFun (1 / M) (φu / L) (PP / (M ^ 2 * L ^ 2))
      (Pr / (M * L)) rr (pp / (M * L ^ 2)) := by
    unfold DomFun; exact hDom
  constructor
  · rw [← sub_nonpos]
    have e : (2 * lyH M * φx + (1 / M) * ((lyA1 M L - 2 * lyB M * ((1 / (16 * L)) / M)
        + lyC M L * ((1 / (16 * L)) / M) ^ 2) * (M * PP + 2 * (PQ - PP) + (qq - 2 * pq + pp))
        + lyA2 M L * ((M - 1) * pp + qq)
        + 2 * (lyB M - lyC M L * ((1 / (16 * L)) / M)) * ((M - 1) * Pr + Qr)
        + M * lyC M L * rr))
      - (1 - a / (16 * L)) * (2 * lyH M * φu + lyA1 M L * PP + lyA2 M L * pp
        + 2 * lyB M * Pr + lyC M L * rr)
      = L * DnFun (1 / M) (M * a / (2 * L)) (φx / L) (φu / L)
          (PP / (M ^ 2 * L ^ 2)) (PQ / (M ^ 2 * L ^ 2)) (Pr / (M * L))
          (Qr / (M * L)) rr (pp / (M * L ^ 2)) (qq / (M * L ^ 2)) (pq / (M * L ^ 2)) := by
      unfold DnFun lyH lyA1 lyA2 lyB lyC
      field_simp
      ring
    rw [e]
    exact mul_nonpos_of_nonneg_of_nonpos hL.le hD'
  · have e : (2 * lyH M * φu + lyA1 M L * PP + lyA2 M L * pp + 2 * lyB M * Pr + lyC M L * rr)
        - φx = L * M * (DomFun (1 / M) (φu / L) (PP / (M ^ 2 * L ^ 2))
          (Pr / (M * L)) rr (pp / (M * L ^ 2)) - (1 / M) * (φx / L)) := by
      unfold DomFun lyH lyA1 lyA2 lyB lyC
      field_simp
      ring
    have : 0 ≤ L * M * (DomFun (1 / M) (φu / L) (PP / (M ^ 2 * L ^ 2))
          (Pr / (M * L)) rr (pp / (M * L ^ 2)) - (1 / M) * (φx / L)) := by
      apply mul_nonneg (by positivity); linarith
    linarith


noncomputable def sagStep {m n : ℕ} (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (η : ℝ)
    (p : EuclideanSpace ℝ (Fin n) × (Fin m → EuclideanSpace ℝ (Fin n))) (j : Fin m) :
    EuclideanSpace ℝ (Fin n) × (Fin m → EuclideanSpace ℝ (Fin n)) :=
  (p.1 - η • ((1 / (m : ℝ)) • ∑ i, Function.update p.2 j (gradient (f j) p.1) i),
   Function.update p.2 j (gradient (f j) p.1))

noncomputable def sagV {m n : ℕ} (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (β : ℝ)
    (xs : EuclideanSpace ℝ (Fin n))
    (p : EuclideanSpace ℝ (Fin n) × (Fin m → EuclideanSpace ℝ (Fin n))) : ℝ :=
  2 * lyH (m : ℝ) * (finiteSumObjective f (p.1 + (1 / (16 * β)) • ((1 / (m : ℝ)) • ∑ i, p.2 i))
      - finiteSumObjective f xs)
  + (lyA1 (m : ℝ) β * ‖∑ i, p.2 i‖ ^ 2 + lyA2 (m : ℝ) β * ∑ i, ‖p.2 i - gradient (f i) xs‖ ^ 2
     + 2 * lyB (m : ℝ) * inner ℝ (∑ i, p.2 i) (p.1 - xs) + lyC (m : ℝ) β * ‖p.1 - xs‖ ^ 2)


theorem sqP_gen {n : ℕ} (P Q r : EuclideanSpace ℝ (Fin n)) (k1 k2 : ℝ) :
    0 ≤ ‖P‖ ^ 2 - 2 * k1 * inner ℝ P Q - 2 * k2 * inner ℝ P r + k1 ^ 2 * ‖Q‖ ^ 2
      + 2 * k1 * k2 * inner ℝ Q r + k2 ^ 2 * ‖r‖ ^ 2 := by
  have e : ‖P - k1 • Q - k2 • r‖ ^ 2 = ‖P‖ ^ 2 - 2 * k1 * inner ℝ P Q - 2 * k2 * inner ℝ P r
      + k1 ^ 2 * ‖Q‖ ^ 2 + 2 * k1 * k2 * inner ℝ Q r + k2 ^ 2 * ‖r‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_sub_sq_real, inner_sub_left, real_inner_smul_right,
      real_inner_smul_right, real_inner_smul_left, real_inner_smul_right, norm_smul, norm_smul,
      mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    ring
  rw [← e]
  positivity

theorem sqQ_gen {n : ℕ} (Q r : EuclideanSpace ℝ (Fin n)) (k : ℝ) :
    0 ≤ ‖Q‖ ^ 2 - 2 * k * inner ℝ Q r + k ^ 2 * ‖r‖ ^ 2 := by
  have e : ‖Q - k • r‖ ^ 2 = ‖Q‖ ^ 2 - 2 * k * inner ℝ Q r + k ^ 2 * ‖r‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  rw [← e]
  positivity

/-- Analytic facts at a state (x, y). -/
theorem state_facts {m n : ℕ} (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (β a : ℝ)
    (xs : EuclideanSpace ℝ (Fin n))
    (hm : 1 ≤ m) (hβ : 0 < β)
    (hf_differentiable : ∀ i, Differentiable ℝ (f i))
    (hf_convex : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hf_smooth : ∀ i, LipschitzWith (Real.toNNReal β) (gradient (f i)))
    (hF : StrongConvexOn Set.univ a (finiteSumObjective f))
    (hxs : IsMinOn (finiteSumObjective f) Set.univ xs)
    (x : EuclideanSpace ℝ (Fin n)) (y : Fin m → EuclideanSpace ℝ (Fin n)) :
    (∑ i, gradient (f i) xs = 0) ∧
    (finiteSumObjective f x - finiteSumObjective f xs
        + inner ℝ (∑ i, y i) (∑ i, (gradient (f i) x - gradient (f i) xs)) / (16 * β * (m : ℝ) ^ 2)
        + a / 2 * (‖∑ i, y i‖ ^ 2 / (16 * β * (m : ℝ)) ^ 2)
      ≤ finiteSumObjective f (x + (1 / (16 * β)) • ((1 / (m : ℝ)) • ∑ i, y i))
        - finiteSumObjective f xs) ∧
    (finiteSumObjective f x - finiteSumObjective f xs
      ≤ inner ℝ (∑ i, (gradient (f i) x - gradient (f i) xs)) (x - xs) / (m : ℝ)
        - a / 2 * ‖x - xs‖ ^ 2) ∧
    (a / 2 * ‖x - xs‖ ^ 2 ≤ finiteSumObjective f x - finiteSumObjective f xs) ∧
    (finiteSumObjective f x - finiteSumObjective f xs ≤ β / 2 * ‖x - xs‖ ^ 2) ∧
    (∑ i, ‖gradient (f i) x - gradient (f i) xs‖ ^ 2
      ≤ β * inner ℝ (∑ i, (gradient (f i) x - gradient (f i) xs)) (x - xs)) ∧
    (∀ s t : ℝ, s ^ 2 * ‖∑ i, y i‖ ^ 2
        - 2 * s * t * inner ℝ (∑ i, y i) (∑ i, (gradient (f i) x - gradient (f i) xs))
        + t ^ 2 * ‖∑ i, (gradient (f i) x - gradient (f i) xs)‖ ^ 2
      ≤ (m : ℝ) * (s ^ 2 * ∑ i, ‖y i - gradient (f i) xs‖ ^ 2
        - 2 * s * t * ∑ i, inner ℝ (y i - gradient (f i) xs) (gradient (f i) x - gradient (f i) xs)
        + t ^ 2 * ∑ i, ‖gradient (f i) x - gradient (f i) xs‖ ^ 2)) := by
  have hM : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hM0 : (m : ℝ) ≠ 0 := hM.ne'
  have hFd : Differentiable ℝ (finiteSumObjective f) := differentiable_fso f hf_differentiable
  have hgxs : gradient (finiteSumObjective f) xs = 0 := gradient_min _ xs hxs
  have hz : ∑ i, gradient (f i) xs = 0 := by
    have h1 := gradient_fso f hf_differentiable xs
    rw [hgxs] at h1
    have h2 := congrArg (fun v => (m : ℝ) • v) h1
    simp only [smul_zero, smul_smul] at h2
    rw [mul_one_div_cancel hM0, one_smul] at h2
    exact h2.symm
  have hQ : ∑ i, (gradient (f i) x - gradient (f i) xs) = ∑ i, gradient (f i) x := by
    rw [Finset.sum_sub_distrib, hz, sub_zero]
  have hgx : gradient (finiteSumObjective f) x
      = (1 / (m : ℝ)) • ∑ i, (gradient (f i) x - gradient (f i) xs) := by
    rw [hQ]; exact gradient_fso f hf_differentiable x
  have hFdef : ∀ z, finiteSumObjective f z = (1 / (m : ℝ)) * ∑ i, f i z := fun z => rfl
  refine ⟨hz, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- s1
    have h := fo_strong _ hFd a hF x (x + (1 / (16 * β)) • ((1 / (m : ℝ)) • ∑ i, y i))
    have hc : (0 : ℝ) ≤ 1 / (16 * β) := by positivity
    have hd : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
    rw [add_sub_cancel_left, hgx, real_inner_smul_left, real_inner_smul_right,
      real_inner_smul_right, norm_smul, norm_smul, Real.norm_of_nonneg hc,
      Real.norm_of_nonneg hd,
      real_inner_comm (∑ i, y i) (∑ i, (gradient (f i) x - gradient (f i) xs))] at h
    have e1 : 1 / (m : ℝ) * (1 / (16 * β) * (1 / (m : ℝ)
        * inner ℝ (∑ i, y i) (∑ i, (gradient (f i) x - gradient (f i) xs))))
        = inner ℝ (∑ i, y i) (∑ i, (gradient (f i) x - gradient (f i) xs))
          / (16 * β * (m : ℝ) ^ 2) := by
      ring
    have e2 : (1 / (16 * β) * (1 / (m : ℝ) * ‖∑ i, y i‖)) ^ 2
        = ‖∑ i, y i‖ ^ 2 / (16 * β * (m : ℝ)) ^ 2 := by
      ring
    rw [e1, e2] at h
    linarith
  · -- s2
    have h := fo_strong _ hFd a hF x xs
    rw [hgx, real_inner_smul_left, ← neg_sub x xs, inner_neg_right, norm_neg] at h
    have e1 : 1 / (m : ℝ) * -inner ℝ (∑ i, (gradient (f i) x - gradient (f i) xs)) (x - xs)
        = -(inner ℝ (∑ i, (gradient (f i) x - gradient (f i) xs)) (x - xs) / (m : ℝ)) := by
      ring
    rw [e1] at h
    linarith
  · -- s4
    have h := fo_strong _ hFd a hF xs x
    rw [hgxs, inner_zero_left] at h
    linarith
  · -- s6
    have h : ∀ i ∈ Finset.univ, f i x
        ≤ f i xs + inner ℝ (gradient (f i) xs) (x - xs) + β / 2 * ‖x - xs‖ ^ 2 :=
      fun i _ => descent (f i) (hf_differentiable i) β hβ.le (hf_smooth i) xs x
    have hs := Finset.sum_le_sum h
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← sum_inner, hz, inner_zero_left,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    rw [hFdef, hFdef]
    have e : 1 / (m : ℝ) * ∑ i, f i x - 1 / (m : ℝ) * ∑ i, f i xs
        = (1 / (m : ℝ)) * (∑ i, f i x - ∑ i, f i xs) := by ring
    rw [e]
    have h2 : ∑ i, f i x - ∑ i, f i xs ≤ (m : ℝ) * (β / 2 * ‖x - xs‖ ^ 2) := by linarith
    calc (1 / (m : ℝ)) * (∑ i, f i x - ∑ i, f i xs)
        ≤ (1 / (m : ℝ)) * ((m : ℝ) * (β / 2 * ‖x - xs‖ ^ 2)) := by
          apply mul_le_mul_of_nonneg_left h2; positivity
      _ = β / 2 * ‖x - xs‖ ^ 2 := by field_simp
  · -- cc
    have h : ∀ i ∈ Finset.univ, ‖gradient (f i) x - gradient (f i) xs‖ ^ 2
        ≤ β * inner ℝ (gradient (f i) x - gradient (f i) xs) (x - xs) := by
      intro i _
      have h1 := smooth_convex_lower (f i) (hf_differentiable i) (hf_convex i) β hβ
        (hf_smooth i) xs x
      have h2 := smooth_convex_lower (f i) (hf_differentiable i) (hf_convex i) β hβ
        (hf_smooth i) x xs
      rw [← neg_sub x xs, inner_neg_right, norm_sub_rev (gradient (f i) xs)] at h2
      rw [inner_sub_left]
      have h3 : 1 / β * ‖gradient (f i) x - gradient (f i) xs‖ ^ 2
          ≤ inner ℝ (gradient (f i) x) (x - xs) - inner ℝ (gradient (f i) xs) (x - xs) := by
        have e : 1 / β = 1 / (2 * β) + 1 / (2 * β) := by field_simp; ring
        rw [e]; linarith
      have h4 := mul_le_mul_of_nonneg_left h3 hβ.le
      rw [← mul_assoc, mul_one_div_cancel hβ.ne', one_mul] at h4
      exact h4
    have hs := Finset.sum_le_sum h
    rw [← Finset.mul_sum, ← sum_inner] at hs
    exact hs
  · -- CS
    intro s t
    obtain ⟨P, hP⟩ : ∃ P, P = ∑ i, y i := ⟨_, rfl⟩
    obtain ⟨Q, hQ'⟩ : ∃ Q, Q = ∑ i, (gradient (f i) x - gradient (f i) xs) := ⟨_, rfl⟩
    rw [← hP, ← hQ']
    have hw : ∑ i, (s • (y i - gradient (f i) xs) - t • (gradient (f i) x - gradient (f i) xs))
        = s • P - t • Q := by
      have e : ∑ i, (y i - gradient (f i) xs) = P := by
        rw [Finset.sum_sub_distrib, hz, sub_zero, hP]
      rw [Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.smul_sum, e, hQ']
    have hnorm : ‖∑ i, (s • (y i - gradient (f i) xs)
          - t • (gradient (f i) x - gradient (f i) xs))‖ ^ 2
        ≤ (m : ℝ) * ∑ i, ‖s • (y i - gradient (f i) xs)
          - t • (gradient (f i) x - gradient (f i) xs)‖ ^ 2 := by
      have h1 := norm_sum_le Finset.univ (fun i => s • (y i - gradient (f i) xs)
        - t • (gradient (f i) x - gradient (f i) xs))
      have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i =>
        ‖s • (y i - gradient (f i) xs) - t • (gradient (f i) x - gradient (f i) xs)‖)
      rw [Finset.card_univ, Fintype.card_fin] at h2
      calc _ ≤ (∑ i, ‖s • (y i - gradient (f i) xs)
              - t • (gradient (f i) x - gradient (f i) xs)‖) ^ 2 := by
            gcongr
        _ ≤ _ := h2
    rw [hw] at hnorm
    have e1 : ‖s • P - t • Q‖ ^ 2 = s ^ 2 * ‖P‖ ^ 2 - 2 * s * t * inner ℝ P Q
        + t ^ 2 * ‖Q‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right, norm_smul, norm_smul,
        mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
      ring
    have e2 : ∀ i, ‖s • (y i - gradient (f i) xs) - t • (gradient (f i) x - gradient (f i) xs)‖ ^ 2
        = s ^ 2 * ‖y i - gradient (f i) xs‖ ^ 2
          - 2 * s * t * inner ℝ (y i - gradient (f i) xs) (gradient (f i) x - gradient (f i) xs)
          + t ^ 2 * ‖gradient (f i) x - gradient (f i) xs‖ ^ 2 := by
      intro i
      rw [norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right, norm_smul, norm_smul,
        mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
      ring
    simp only [e2] at hnorm
    rw [e1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum] at hnorm
    exact hnorm

/-- Per-state Lyapunov decrease and domination (case m ≥ 2). -/
theorem sag_state_bounds {m n : ℕ} (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (β a : ℝ)
    (xs : EuclideanSpace ℝ (Fin n))
    (hm : 2 ≤ m) (hβ : 0 < β) (ha : 0 < a) (haM : a ≤ 2 * β / m)
    (hf_differentiable : ∀ i, Differentiable ℝ (f i))
    (hf_convex : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hf_smooth : ∀ i, LipschitzWith (Real.toNNReal β) (gradient (f i)))
    (hF : StrongConvexOn Set.univ a (finiteSumObjective f))
    (hxs : IsMinOn (finiteSumObjective f) Set.univ xs)
    (p : EuclideanSpace ℝ (Fin n) × (Fin m → EuclideanSpace ℝ (Fin n))) :
    (1 / (m : ℝ)) * ∑ j, sagV f β xs (sagStep f (1 / (16 * β)) p j)
        ≤ (1 - a / (16 * β)) * sagV f β xs p
      ∧ finiteSumObjective f p.1 - finiteSumObjective f xs ≤ sagV f β xs p := by
  obtain ⟨x, y⟩ := p
  have hM : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hM0 : (m:ℝ) ≠ 0 := ne_of_gt (by linarith)
  obtain ⟨hz, s1, s2, s4, s6, cc, CS⟩ :=
    state_facts f β a xs (by omega) hβ hf_differentiable hf_convex hf_smooth hF hxs x y
  have sqP := fun k1 k2 => sqP_gen (∑ i, y i)
    (∑ i, (gradient (f i) x - gradient (f i) xs)) (x - xs) k1 k2
  have sqQ := fun k => sqQ_gen (∑ i, (gradient (f i) x - gradient (f i) xs)) (x - xs) k
  obtain ⟨h1, h2⟩ := raw_bounds (m:ℝ) β a
    (finiteSumObjective f x - finiteSumObjective f xs)
    (finiteSumObjective f (x + (1 / (16 * β)) • ((1 / (m : ℝ)) • ∑ i, y i))
      - finiteSumObjective f xs)
    (‖∑ i, y i‖ ^ 2)
    (inner ℝ (∑ i, y i) (∑ i, (gradient (f i) x - gradient (f i) xs)))
    (‖∑ i, (gradient (f i) x - gradient (f i) xs)‖ ^ 2)
    (inner ℝ (∑ i, y i) (x - xs))
    (inner ℝ (∑ i, (gradient (f i) x - gradient (f i) xs)) (x - xs))
    (‖x - xs‖ ^ 2)
    (∑ i, ‖y i - gradient (f i) xs‖ ^ 2)
    (∑ i, ‖gradient (f i) x - gradient (f i) xs‖ ^ 2)
    (∑ i, inner ℝ (y i - gradient (f i) xs) (gradient (f i) x - gradient (f i) xs))
    hM hβ ha haM s1 s2 s4 s6 cc CS sqP sqQ (by positivity) (by positivity)
  have hexp := sag_expand x xs y (fun i => gradient (f i) xs) (fun j => gradient (f j) x) hz
    (1 / (16 * β)) (lyA1 (m:ℝ) β) (lyA2 (m:ℝ) β) (lyB (m:ℝ)) (lyC (m:ℝ) β)
  have hstep : ∀ j, sagV f β xs (sagStep f (1 / (16 * β)) (x, y) j)
      = 2 * lyH (m:ℝ) * (finiteSumObjective f x - finiteSumObjective f xs)
        + (lyA1 (m:ℝ) β * ‖∑ i, Function.update y j (gradient (f j) x) i‖ ^ 2
          + lyA2 (m:ℝ) β * ∑ i, ‖Function.update y j (gradient (f j) x) i - gradient (f i) xs‖ ^ 2
          + 2 * lyB (m:ℝ) * inner ℝ (∑ i, Function.update y j (gradient (f j) x) i)
              (x - (1 / (16 * β)) • ((1 / (m : ℝ)) • ∑ i, Function.update y j (gradient (f j) x) i)
                - xs)
          + lyC (m:ℝ) β * ‖x - (1 / (16 * β)) • ((1 / (m : ℝ)) •
              ∑ i, Function.update y j (gradient (f j) x) i) - xs‖ ^ 2) := by
    intro j
    simp only [sagV, sagStep, sub_add_cancel]
  have key : ∀ c R : ℝ, 1 / (m:ℝ) * ((m:ℝ) * c + R) = c + 1 / (m:ℝ) * R := by
    intro c R
    rw [mul_add, ← mul_assoc, one_div_mul_cancel hM0, one_mul]
  refine ⟨(le_of_eq ?_).trans (h1.trans (le_of_eq ?_)), h2.trans (le_of_eq ?_)⟩
  · rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_add_distrib, hexp, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact key _ _
  · simp only [sagV]
    ring
  · simp only [sagV]
    ring

lemma I_sum_sq_sub {m n : ℕ} (q : Fin m → EuclideanSpace ℝ (Fin n)) (w : EuclideanSpace ℝ (Fin n))
    (hq : ∑ i, q i = (m : ℝ) • w) :
    ∑ i, ‖q i - w‖ ^ 2 ≤ ∑ i, ‖q i‖ ^ 2 := by
  simp_rw [norm_sub_sq_real]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← sum_inner, hq,
    real_inner_smul_left, real_inner_self_eq_norm_sq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have := mul_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ m) (sq_nonneg ‖w‖)
  linarith

lemma I_S_bound {m n : ℕ} (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (xs x0 w : EuclideanSpace ℝ (Fin n))
    (hz : ∑ i, gradient (f i) xs = 0) (hw : ∑ i, gradient (f i) x0 = (m : ℝ) • w) :
    ∑ i, ‖(gradient (f i) x0 - w) - gradient (f i) xs‖ ^ 2
      ≤ ∑ i, ‖gradient (f i) x0 - gradient (f i) xs‖ ^ 2 := by
  calc ∑ i, ‖(gradient (f i) x0 - w) - gradient (f i) xs‖ ^ 2
      = ∑ i, ‖(gradient (f i) x0 - gradient (f i) xs) - w‖ ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [sub_right_comm]
    _ ≤ ∑ i, ‖gradient (f i) x0 - gradient (f i) xs‖ ^ 2 :=
        I_sum_sq_sub (fun i => gradient (f i) x0 - gradient (f i) xs) w
          (by rw [Finset.sum_sub_distrib, hz, sub_zero, hw])

lemma I_Q_bound {m n : ℕ} (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (β : ℝ)
    (xs x0 : EuclideanSpace ℝ (Fin n)) (hβ : 0 < β)
    (hf_differentiable : ∀ i, Differentiable ℝ (f i))
    (hf_convex : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hf_smooth : ∀ i, LipschitzWith (Real.toNNReal β) (gradient (f i)))
    (hz : ∑ i, gradient (f i) xs = 0) :
    ∑ i, ‖gradient (f i) x0 - gradient (f i) xs‖ ^ 2
      ≤ 2 * β * (∑ i, f i x0 - ∑ i, f i xs) := by
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      ‖gradient (f i) x0 - gradient (f i) xs‖ ^ 2
        ≤ 2 * β * (f i x0 - f i xs) - 2 * β * inner ℝ (gradient (f i) xs) (x0 - xs) := by
    intro i _
    have h := smooth_convex_lower (f i) (hf_differentiable i) (hf_convex i) β hβ (hf_smooth i) xs x0
    have h2 : 2 * β * (1 / (2 * β) * ‖gradient (f i) x0 - gradient (f i) xs‖ ^ 2)
        = ‖gradient (f i) x0 - gradient (f i) xs‖ ^ 2 := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ 2 * β)]
  have hs := Finset.sum_le_sum hi
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib,
    ← sum_inner, hz, inner_zero_left, mul_zero, sub_zero] at hs
  exact hs

/-- Initial value of the Lyapunov function (case m ≥ 2). -/
theorem sag_init_bound {m n : ℕ} (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (β : ℝ)
    (xs x0 : EuclideanSpace ℝ (Fin n))
    (hm : 2 ≤ m) (hβ : 0 < β)
    (hf_differentiable : ∀ i, Differentiable ℝ (f i))
    (hf_convex : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hf_smooth : ∀ i, LipschitzWith (Real.toNNReal β) (gradient (f i)))
    (hxs : IsMinOn (finiteSumObjective f) Set.univ xs) :
    sagV f β xs (x0, fun i => gradient (f i) x0 - gradient (finiteSumObjective f) x0)
      ≤ (3 / 2) * (finiteSumObjective f x0 - finiteSumObjective f xs)
        + ((4 * β) / (m : ℝ)) * ‖x0 - xs‖ ^ 2 := by
  have hM2 : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hMpos : (0:ℝ) < (m:ℝ) := by linarith
  have hz : ∑ i, gradient (f i) xs = 0 := by
    have h1 := gradient_min _ xs hxs
    rw [gradient_fso f hf_differentiable xs] at h1
    rcases smul_eq_zero.mp h1 with h | h
    · exact absurd h (by positivity)
    · exact h
  have hw := gradient_fso f hf_differentiable x0
  have hw' : ∑ i, gradient (f i) x0 = (m : ℝ) • gradient (finiteSumObjective f) x0 := by
    rw [hw, smul_smul, mul_one_div_cancel hMpos.ne', one_smul]
  have hy0 : ∑ i, (gradient (f i) x0 - gradient (finiteSumObjective f) x0) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, hw',
      ← Nat.cast_smul_eq_nsmul ℝ, sub_self]
  have hV : sagV f β xs (x0, fun i => gradient (f i) x0 - gradient (finiteSumObjective f) x0)
      = 2 * lyH (m:ℝ) * (finiteSumObjective f x0 - finiteSumObjective f xs)
        + lyA2 (m:ℝ) β * ∑ i, ‖(gradient (f i) x0 - gradient (finiteSumObjective f) x0)
            - gradient (f i) xs‖ ^ 2
        + lyC (m:ℝ) β * ‖x0 - xs‖ ^ 2 := by
    unfold sagV
    dsimp only
    rw [hy0]
    simp
    ring
  rw [hV]
  have hD : 0 ≤ finiteSumObjective f x0 - finiteSumObjective f xs :=
    sub_nonneg.mpr (hxs (Set.mem_univ x0))
  have hS := I_S_bound f xs x0 (gradient (finiteSumObjective f) x0) hz hw'
  have hQ := I_Q_bound f β xs x0 hβ hf_differentiable hf_convex hf_smooth hz
  have hAB : ∑ i, f i x0 - ∑ i, f i xs
      = (m:ℝ) * (finiteSumObjective f x0 - finiteSumObjective f xs) := by
    unfold finiteSumObjective; field_simp
  rw [hAB] at hQ
  have hA2 : 0 ≤ lyA2 (m:ℝ) β := by
    unfold lyA2
    apply mul_nonneg
    · positivity
    · rw [sub_nonneg, div_le_one (by positivity)]; linarith
  have h1 := mul_le_mul_of_nonneg_left (hS.trans hQ) hA2
  have e2 : lyA2 (m:ℝ) β * (2 * β * ((m:ℝ) * (finiteSumObjective f x0 - finiteSumObjective f xs)))
      = (1/8) * (1 - 1/(2*(m:ℝ))) * (finiteSumObjective f x0 - finiteSumObjective f xs) := by
    unfold lyA2; field_simp; ring
  have e1 : lyC (m:ℝ) β = 4 * β / (m:ℝ) := rfl
  have e3 : 2 * lyH (m:ℝ) * (finiteSumObjective f x0 - finiteSumObjective f xs)
      + (1/8) * (1 - 1/(2*(m:ℝ))) * (finiteSumObjective f x0 - finiteSumObjective f xs)
      = 3/2 * (finiteSumObjective f x0 - finiteSumObjective f xs)
        - (3/8 + 33/(16*(m:ℝ))) * (finiteSumObjective f x0 - finiteSumObjective f xs) := by
    unfold lyH; ring
  have h4 : 0 ≤ (3/8 + 33/(16*(m:ℝ))) * (finiteSumObjective f x0 - finiteSumObjective f xs) :=
    mul_nonneg (by positivity) hD
  rw [e1]
  linarith

/-- Gradient-descent decrease (case m = 1). -/
theorem gd_step_bound {n : ℕ} (f : Fin 1 → EuclideanSpace ℝ (Fin n) → ℝ) (β a : ℝ)
    (xs : EuclideanSpace ℝ (Fin n))
    (hβ : 0 < β) (ha : 0 < a)
    (hf_differentiable : ∀ i, Differentiable ℝ (f i))
    (hf_smooth : ∀ i, LipschitzWith (Real.toNNReal β) (gradient (f i)))
    (hF : StrongConvexOn Set.univ a (finiteSumObjective f))
    (hxs : IsMinOn (finiteSumObjective f) Set.univ xs)
    (p : EuclideanSpace ℝ (Fin n) × (Fin 1 → EuclideanSpace ℝ (Fin n))) :
    (1 / ((1 : ℕ) : ℝ)) * ∑ j, (finiteSumObjective f (sagStep f (1 / (16 * β)) p j).1
        - finiteSumObjective f xs)
      ≤ (1 - a / (16 * β)) * (finiteSumObjective f p.1 - finiteSumObjective f xs) := by
  have hFeq : finiteSumObjective f = f 0 := by
    funext z; simp [finiteSumObjective]
  have hstep : (sagStep f (1 / (16 * β)) p 0).1
      = p.1 - (1 / (16 * β)) • gradient (f 0) p.1 := by
    simp [sagStep]
  rw [Fin.sum_univ_one, hstep, hFeq]
  rw [hFeq] at hF hxs
  have hd := descent (f 0) (hf_differentiable 0) β hβ.le (hf_smooth 0) p.1
    (p.1 - (1 / (16 * β)) • gradient (f 0) p.1)
  have hs := fo_strong (f 0) (hf_differentiable 0) a hF p.1 xs
  have hmin : f 0 xs ≤ f 0 p.1 := hxs (Set.mem_univ _)
  have e1 : p.1 - (1 / (16 * β)) • gradient (f 0) p.1 - p.1
      = -((1 / (16 * β)) • gradient (f 0) p.1) := by abel
  rw [e1, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq, norm_neg, norm_smul,
    Real.norm_of_nonneg (by positivity)] at hd
  have hsq : 0 ≤ ‖gradient (f 0) p.1 + a • (xs - p.1)‖ ^ 2 := sq_nonneg _
  rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_of_nonneg ha.le] at hsq
  set G := ‖gradient (f 0) p.1‖ ^ 2 with hG
  set D := f 0 p.1 - f 0 xs with hDdef
  have hDnn : 0 ≤ D := sub_nonneg.mpr hmin
  have hGD : 2 * a * D ≤ G := by
    nlinarith [mul_le_mul_of_nonneg_left hs ha.le]
  have hd' : f 0 (p.1 - (1 / (16 * β)) • gradient (f 0) p.1) ≤ f 0 p.1 - 31 * G / (512 * β) := by
    have : f 0 p.1 + -(1 / (16 * β) * G) + β / 2 * (1 / (16 * β) * ‖gradient (f 0) p.1‖) ^ 2
        = f 0 p.1 - 31 * G / (512 * β) := by
      rw [hG]; field_simp; ring
    linarith
  have hkey : a * D / (16 * β) ≤ 31 * G / (512 * β) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg ha.le hDnn]
  have e2 : (1 - a / (16 * β)) * D = D - a * D / (16 * β) := by ring
  simp only [Nat.cast_one, div_one, one_mul]
  rw [e2]
  linarith


theorem M_main_bound {k m n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (g : ℕ → Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (I : ℕ → Ω → Fin m)
    (β : ℝ)
    (x0 x_star : EuclideanSpace ℝ (Fin n))
    (hx0 : ∀ ω, x 0 ω = x0)
    (h_sag_seq : IsSAGSequence μ f x g I (1 / (16 * β)))
    (hf_smooth : ∀ i, LipschitzWith (Real.toNNReal β) (gradient (f i)))
    (hx_star : IsMinOn (finiteSumObjective f) Set.univ x_star)
    (hf_sum_x_int : ∀ t, Integrable (fun ω => finiteSumObjective f (x t ω)) μ)
    (V : EuclideanSpace ℝ (Fin n) × (Fin m → EuclideanSpace ℝ (Fin n)) → ℝ) (c : ℝ)
    (hVc : Continuous V) (hc : 0 ≤ c)
    (hdec : ∀ p, (1 / (m : ℝ)) * ∑ j, V (sagStep f (1 / (16 * β)) p j) ≤ c * V p)
    (hVnn : ∀ p, 0 ≤ V p)
    (hdom : ∀ p, finiteSumObjective f p.1 - finiteSumObjective f x_star ≤ V p) :
    ∫ ω, finiteSumObjective f (x k ω) ∂μ - finiteSumObjective f x_star ≤
      c ^ k * V (x0, fun i => gradient (f i) x0 - gradient (finiteSumObjective f) x0) := by
  obtain ⟨hxm, hgm, hIm, ⟨hg0, hgI, hgO, hxU⟩, hiid, hind, hunif⟩ := h_sag_seq
  have hgupd : ∀ t ω, (fun i => g (t + 1) i ω) =
      Function.update (fun i => g t i ω) (I t ω) (gradient (f (I t ω)) (x t ω)) := by
    intro t ω
    funext i
    by_cases hi : i = I t ω
    · subst hi
      rw [Function.update_self]
      exact hgI t ω
    · rw [Function.update_of_ne hi]
      exact hgO t i ω hi
  have hstep : ∀ t ω, (fun t ω => (x t ω, fun i => g t i ω)) (t + 1) ω =
      sagStep f (1 / (16 * β)) ((fun t ω => (x t ω, fun i => g t i ω)) t ω) (I t ω) := by
    intro t ω
    have h1 := hgupd t ω
    simp only [sagStep]
    rw [← h1, hxU t ω]
  have hs_meas : ∀ t, Measurable ((fun t ω => (x t ω, fun i => g t i ω)) t) := by
    intro t
    exact (hxm t).prodMk (measurable_pi_lambda _ (fun i => hgm t i))
  have hT_meas : ∀ j, Measurable fun p => sagStep f (1 / (16 * β)) p j := by
    intro j
    have hgc : Continuous fun p : EuclideanSpace ℝ (Fin n) × (Fin m → EuclideanSpace ℝ (Fin n)) =>
        gradient (f j) p.1 := (hf_smooth j).continuous.comp continuous_fst
    have hu : Continuous fun p : EuclideanSpace ℝ (Fin n) × (Fin m → EuclideanSpace ℝ (Fin n)) =>
        Function.update p.2 j (gradient (f j) p.1) := continuous_snd.update j hgc
    have hcont : Continuous fun p => sagStep f (1 / (16 * β)) p j := by
      unfold sagStep
      refine Continuous.prodMk ?_ hu
      refine continuous_fst.sub (Continuous.const_smul (Continuous.const_smul ?_ _) _)
      exact continuous_finset_sum _ (fun i _ => (continuous_apply i).comp hu)
    exact hcont.measurable
  have key := lyap_iter μ (fun t ω => (x t ω, fun i => g t i ω)) I (sagStep f (1 / (16 * β))) V c
    hs_meas hIm hT_meas hVc.measurable hstep hind hunif hc hdec hVnn k
  have hs0 : ∀ ω, (x 0 ω, fun i => g 0 i ω) =
      (x0, fun i => gradient (f i) x0 - gradient (finiteSumObjective f) x0) := by
    intro ω
    refine Prod.ext (hx0 ω) ?_
    funext i
    show g 0 i ω = gradient (f i) x0 - gradient (finiteSumObjective f) x0
    rw [hg0 i ω, hx0 ω]
  simp only [hs0] at key
  rw [lintegral_const, measure_univ, mul_one, ← ENNReal.ofReal_mul (pow_nonneg hc k)] at key
  have hint : Integrable (fun ω => finiteSumObjective f (x k ω) - finiteSumObjective f x_star) μ :=
    (hf_sum_x_int k).sub (integrable_const _)
  have hnn : 0 ≤ᵐ[μ] fun ω => finiteSumObjective f (x k ω) - finiteSumObjective f x_star :=
    Filter.Eventually.of_forall (fun ω => sub_nonneg.mpr (isMinOn_iff.mp hx_star _ (Set.mem_univ _)))
  have h1 : ∫ ω, finiteSumObjective f (x k ω) ∂μ - finiteSumObjective f x_star =
      ∫ ω, (finiteSumObjective f (x k ω) - finiteSumObjective f x_star) ∂μ := by
    rw [integral_sub (hf_sum_x_int k) (integrable_const _)]
    simp
  have h2 := ofReal_integral_eq_lintegral_ofReal hint hnn
  have h3 : ∫⁻ ω, ENNReal.ofReal (finiteSumObjective f (x k ω) - finiteSumObjective f x_star) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal (V (x k ω, fun i => g k i ω)) ∂μ :=
    lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (hdom (x k ω, fun i => g k i ω)))
  have h4 := (h2.le.trans h3).trans key
  rw [h1]
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (pow_nonneg hc k) (hVnn _))).mp h4


theorem sag_strongly_convex_linear_bound {k m n : ℕ} {Ω : Type*}
  [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (g : ℕ → Fin m → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → Ω → Fin m)
  (α β : ℝ)
  (x0 : EuclideanSpace ℝ (Fin n))
  (x_star : EuclideanSpace ℝ (Fin n))
  (hx0 : ∀ ω, x 0 ω = x0)
  (hβ_pos : β > 0)
  (hα_pos : α > 0)
  (hα_le_β : α ≤ β)
  (hm_pos : m > 0)
  (h_sag_seq : IsSAGSequence μ f x g I (1 / (16 * β)))
  (hf_differentiable : ∀ i, Differentiable ℝ (f i))
  (hf_convex : ∀ i, ConvexOn ℝ Set.univ (f i))
  (hf_smooth : ∀ i, LipschitzWith (Real.toNNReal β) (gradient (f i)))
  (hf_strongly_convex : StrongConvexOn Set.univ α (finiteSumObjective f))
  (hx_star : IsMinOn (finiteSumObjective f) Set.univ x_star)
  (hf_sum_x_int : ∀ t, Integrable (fun ω => finiteSumObjective f (x t ω)) μ) :
  let f_sum := finiteSumObjective f
  ∫ ω, f_sum (x k ω) ∂μ - f_sum x_star ≤
    (1 - min (α / (16 * β)) (1 / (8 * (m : ℝ)))) ^ k *
      ((3 / 2) * (f_sum x0 - f_sum x_star) +
        ((4 * β) / (m : ℝ)) * ‖x0 - x_star‖ ^ 2) := by
  intro f_sum
  show ∫ ω, finiteSumObjective f (x k ω) ∂μ - finiteSumObjective f x_star ≤
    (1 - min (α / (16 * β)) (1 / (8 * (m : ℝ)))) ^ k *
      ((3 / 2) * (finiteSumObjective f x0 - finiteSumObjective f x_star) +
        ((4 * β) / (m : ℝ)) * ‖x0 - x_star‖ ^ 2)
  have hM : (0 : ℝ) < m := by exact_mod_cast hm_pos
  have hMne : (m : ℝ) ≠ 0 := hM.ne'
  have hβne : β ≠ 0 := hβ_pos.ne'
  set a : ℝ := min α (2 * β / m) with ha_def
  have ha_pos : 0 < a := lt_min hα_pos (by positivity)
  have haα : a ≤ α := min_le_left _ _
  have haM : a ≤ 2 * β / m := min_le_right _ _
  have haβ : a ≤ β := haα.trans hα_le_β
  have hF' : StrongConvexOn Set.univ a (finiteSumObjective f) := hf_strongly_convex.mono haα
  have hrate : min (α / (16 * β)) (1 / (8 * (m : ℝ))) = a / (16 * β) := by
    have h8 : 1 / (8 * (m : ℝ)) = (2 * β / m) / (16 * β) := by
      field_simp
      ring
    rw [h8, min_div_div_right (by positivity)]
  have hc : 0 ≤ 1 - a / (16 * β) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    linarith
  have hFc : Continuous (finiteSumObjective f) := (differentiable_fso f hf_differentiable).continuous
  have hFmin : ∀ y, finiteSumObjective f x_star ≤ finiteSumObjective f y :=
    fun y => isMinOn_iff.mp hx_star y (Set.mem_univ y)
  rw [hrate]
  obtain rfl | hm2 : m = 1 ∨ 2 ≤ m := by omega
  · -- m = 1 : gradient descent
    have hdec := fun p => gd_step_bound f β a x_star hβ_pos ha_pos hf_differentiable hf_smooth
      hF' hx_star p
    have hVc : Continuous fun p : EuclideanSpace ℝ (Fin n) × (Fin 1 → EuclideanSpace ℝ (Fin n)) =>
        finiteSumObjective f p.1 - finiteSumObjective f x_star :=
      (hFc.comp continuous_fst).sub continuous_const
    have hmain := M_main_bound (k := k) μ f x g I β x0 x_star hx0 h_sag_seq hf_smooth hx_star
      hf_sum_x_int (fun p => finiteSumObjective f p.1 - finiteSumObjective f x_star)
      (1 - a / (16 * β)) hVc hc hdec (fun p => sub_nonneg.mpr (hFmin p.1)) (fun p => le_refl _)
    refine hmain.trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hc k))
    show finiteSumObjective f x0 - finiteSumObjective f x_star ≤
      (3 / 2) * (finiteSumObjective f x0 - finiteSumObjective f x_star) +
        ((4 * β) / ((1 : ℕ) : ℝ)) * ‖x0 - x_star‖ ^ 2
    have h0 := sub_nonneg.mpr (hFmin x0)
    have h1 : 0 ≤ ((4 * β) / ((1 : ℕ) : ℝ)) * ‖x0 - x_star‖ ^ 2 := by positivity
    linarith
  · -- m ≥ 2 : SAG Lyapunov function
    have hb := fun p => sag_state_bounds f β a x_star hm2 hβ_pos ha_pos haM hf_differentiable
      hf_convex hf_smooth hF' hx_star p
    have hVc : Continuous (sagV f β x_star) := by
      unfold sagV
      fun_prop
    have hmain := M_main_bound (k := k) μ f x g I β x0 x_star hx0 h_sag_seq hf_smooth hx_star
      hf_sum_x_int (sagV f β x_star) (1 - a / (16 * β)) hVc hc (fun p => (hb p).1)
      (fun p => (sub_nonneg.mpr (hFmin p.1)).trans (hb p).2) (fun p => (hb p).2)
    have hinit := sag_init_bound f β x_star x0 hm2 hβ_pos hf_differentiable hf_convex hf_smooth
      hx_star
    exact hmain.trans (mul_le_mul_of_nonneg_left hinit (pow_nonneg hc k))

end sag_strongly_convex_linear_bound
