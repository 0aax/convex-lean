import ConvexStarLib.Defs

/-!
# `stochastic_gradient_descent_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/stochastic_gradient_descent_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace stochastic_gradient_descent_bound`, so the main result is `stochastic_gradient_descent_bound.stochastic_gradient_descent_bound`.
-/

namespace stochastic_gradient_descent_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma sgd_aux_nonneg {c K : ℝ} (h : ∀ b : ℝ, 0 < b → b ≤ 1 → 0 ≤ c + b * K) : 0 ≤ c := by
  by_contra hc
  push_neg at hc
  rcases le_or_gt K 0 with hK | hK
  · have := h 1 one_pos le_rfl; linarith
  · have hb0 : 0 < min 1 (-c / (2 * K)) := lt_min one_pos (div_pos (by linarith) (by linarith))
    have hb1 : min 1 (-c / (2 * K)) ≤ 1 := min_le_left _ _
    have hb2 : min 1 (-c / (2 * K)) ≤ -c / (2 * K) := min_le_right _ _
    have h1 := h _ hb0 hb1
    have h2 : min 1 (-c / (2 * K)) * K ≤ -c / (2 * K) * K := mul_le_mul_of_nonneg_right hb2 hK.le
    have h3 : -c / (2 * K) * K = -c / 2 := by field_simp
    linarith

lemma sgd_bregman_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (z y : E) :
    bregmanDivergence (fun v : E => (1 / 2 : ℝ) * ‖v‖ ^ (2 : ℕ)) z y = (1 / 2) * ‖z - y‖ ^ 2 := by
  unfold bregmanDivergence
  have hd : HasFDerivAt (fun v : E => (1 / 2 : ℝ) * ‖v‖ ^ (2 : ℕ))
      ((1 / 2 : ℝ) • (2 • innerSL ℝ y)) y :=
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul (1 / 2)
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  rw [norm_sub_sq_real, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm]
  push_cast
  ring

lemma sgd_step_core {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : E →L[ℝ] ℝ) (η : ℝ) (hη : 0 ≤ η) (a d : E)
    (hFO : 0 ≤ η * L d + inner ℝ a d) :
    ‖d‖ ^ 2 ≤ ‖a + d‖ ^ 2 + 2 * η * L (a + d) + η ^ 2 * ‖L‖ ^ 2 := by
  rw [norm_add_sq_real, map_add]
  have hLa : -(‖L‖ * ‖a‖) ≤ L a := by
    have h := L.le_opNorm a
    rw [Real.norm_eq_abs] at h
    linarith [neg_abs_le (L a)]
  have h2 : η * (-(‖L‖ * ‖a‖)) ≤ η * L a := mul_le_mul_of_nonneg_left hLa hη
  nlinarith [sq_nonneg (‖a‖ - η * ‖L‖)]

lemma sgd_step_ineq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (𝓧 : Set E) (h𝓧 : Convex ℝ 𝓧) (L : E →L[ℝ] ℝ) (η : ℝ) (hη : 0 ≤ η) (y y' x_star : E)
    (hy' : y' ∈ 𝓧) (hxs : x_star ∈ 𝓧)
    (hmin : ∀ z ∈ 𝓧, η * L y' + (1 / 2) * ‖y' - y‖ ^ 2 ≤ η * L z + (1 / 2) * ‖z - y‖ ^ 2) :
    ‖y' - x_star‖ ^ 2 ≤ ‖y - x_star‖ ^ 2 - 2 * η * L (y - x_star) + η ^ 2 * ‖L‖ ^ 2 := by
  have hFO : 0 ≤ η * L (x_star - y') + inner ℝ (y' - y) (x_star - y') := by
    apply sgd_aux_nonneg (K := (1 / 2) * ‖x_star - y'‖ ^ 2)
    intro b hb0 hb1
    have hz : y' + b • (x_star - y') ∈ 𝓧 := h𝓧.add_smul_sub_mem hy' hxs ⟨hb0.le, hb1⟩
    have h := hmin _ hz
    have e1 : L (y' + b • (x_star - y')) = L y' + b * L (x_star - y') := by
      rw [map_add, map_smul, smul_eq_mul]
    have e2 : y' + b • (x_star - y') - y = (y' - y) + b • (x_star - y') := by abel
    rw [e1, e2, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hb0] at h
    have h' : 0 ≤ b * (η * L (x_star - y') + inner ℝ (y' - y) (x_star - y')
        + b * ((1 / 2) * ‖x_star - y'‖ ^ 2)) := by nlinarith
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_pos_of_neg hb0 hneg
    linarith
  have e3 : y' - x_star = -(x_star - y') := by abel
  have e4 : y - x_star = -((y' - y) + (x_star - y')) := by abel
  have hc := sgd_step_core L η hη (y' - y) (x_star - y') hFO
  rw [e3, e4, norm_neg, norm_neg, map_neg]
  linarith

lemma sgd_condexp_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → E) (hX : Measurable X) (G : Ω → E →L[ℝ] ℝ) (hG : Integrable G μ) (v : E)
    (hint : Integrable (fun ω => G ω (X ω - v)) μ) :
    ∫ ω, G ω (X ω - v) ∂μ = ∫ ω, condExpGivenIterate μ X G ω (X ω - v) ∂μ := by
  unfold condExpGivenIterate
  have hm : MeasurableSpace.comap X inferInstance ≤ mΩ := hX.comap_le
  have hXm : Measurable[MeasurableSpace.comap X inferInstance] X := comap_measurable X
  have hsm : StronglyMeasurable[MeasurableSpace.comap X inferInstance] (fun ω => X ω - v) := by
    have h1 : StronglyMeasurable[MeasurableSpace.comap X inferInstance] X :=
      hXm.stronglyMeasurable
    have h2 : StronglyMeasurable[MeasurableSpace.comap X inferInstance] (fun _ : Ω => v) :=
      stronglyMeasurable_const
    exact h1.sub h2
  have hfg : Integrable
      (fun ω => ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ) (G ω) (X ω - v)) μ := hint
  have h := condExp_bilin_of_stronglyMeasurable_right (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ))
    hsm hfg hG
  calc ∫ ω, G ω (X ω - v) ∂μ
      = ∫ ω, (μ[fun ω => ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ) (G ω) (X ω - v) |
          MeasurableSpace.comap X inferInstance]) ω ∂μ := (integral_condExp hm).symm
    _ = ∫ ω, ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)
          ((μ[G | MeasurableSpace.comap X inferInstance]) ω) (X ω - v) ∂μ := integral_congr_ae h
    _ = _ := rfl

lemma sgd_strong_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (𝓧 : Set E) (f : E → ℝ) (α : ℝ) (hsc : StrongConvexOn 𝓧 α f) (x_star y : E)
    (hy : y ∈ 𝓧) (hxs : x_star ∈ 𝓧) (w : E →L[ℝ] ℝ) (hw : IsSubgradientOn 𝓧 f y w) :
    f y - f x_star ≤ w (y - x_star) - α / 2 * ‖y - x_star‖ ^ 2 := by
  have key : 0 ≤ (f x_star - f y + w y - w x_star - α / 2 * ‖y - x_star‖ ^ 2) := by
    apply sgd_aux_nonneg (K := α / 2 * ‖y - x_star‖ ^ 2)
    intro b hb0 hb1
    have hz : (1 - b) • y + b • x_star ∈ 𝓧 :=
      hsc.1 hy hxs (by linarith) hb0.le (by ring)
    have h1 := hw _ hz
    have h2 := hsc.2 hy hxs (show (0:ℝ) ≤ 1 - b by linarith) hb0.le (by ring)
    simp only [smul_eq_mul] at h2
    rw [map_sub, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
    have h' : 0 ≤ b * (f x_star - f y + w y - w x_star - α / 2 * ‖y - x_star‖ ^ 2
        + b * (α / 2 * ‖y - x_star‖ ^ 2)) := by nlinarith
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_pos_of_neg hb0 hneg
    linarith
  rw [map_sub]
  linarith

set_option linter.unusedVariables false in
theorem stochastic_gradient_descent_bound
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {t : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (𝓧 : Set E)
  (f : E → ℝ)
  (x : ℕ → Ω → E)
  (g : ℕ → Ω → E →L[ℝ] ℝ)
  (α B : ℝ)
  (x_star : E)
  (x0 : E)
  (hx0 : ∀ ω, x 0 ω = x0)
  (hB_sq : ∀ t, ∫ ω, ‖g t ω‖ ^ (2 : ℕ) ∂μ ≤ B ^ 2)
  (hB_pos : B > 0) (hα_pos : α > 0)
  (hB_int : ∀ s, Integrable (fun ω => ‖g s ω‖ ^ (2 : ℕ)) μ)
  (ht : t > 0)
  (hf_ae_comp : ∀ s, AEMeasurable (fun ω => f (x s ω)) μ)
  (hweighted_ae :
      AEMeasurable
        (fun ω => f (∑ s ∈ Finset.range t,
           ((2 * ((s : ℝ) + 1)) / ((t : ℝ) * ((t : ℝ) + 1))) • x s ω)) μ)
  (h_sgd_seq :
    IsStochasticMirrorDescentSequence 𝓧 Set.univ
      (fun v => (1 / 2 : ℝ) * ‖v‖ ^ (2 : ℕ))
      x g
      (fun s => 2 / (α * ((s : ℝ) + 2))))
  (h_stoch_oracle : ∀ s, IsStochasticSubgradientOracle μ 𝓧 f (x s) (g s))
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (hf_convex : ConvexOn ℝ 𝓧 f)
  (hf_strongly_convex : StrongConvexOn 𝓧 α f)
  (hf_subgradients : ∀ x ∈ 𝓧, ∃ w : E →L[ℝ] ℝ, IsSubgradientOn 𝓧 f x w)
  (hx_star_mem : x_star ∈ 𝓧)
  (hx_star : IsMinOn f 𝓧 x_star) :
  ∫ ω,
    f (∑ s ∈ Finset.range t,
         ((2 * ((s : ℝ) + 1)) / ((t : ℝ) * ((t : ℝ) + 1))) • (x s ω))
      ∂μ
    - f x_star
    ≤ (2 * B ^ 2) / (α * ((t : ℝ) + 1)) := by
  obtain ⟨hx_meas, -, -, hx_mem, hx_step⟩ := h_sgd_seq
  have hxX : ∀ s ω, x s ω ∈ 𝓧 := fun s ω => (hx_mem s ω).1
  obtain ⟨R, hR⟩ := h𝓧_compact.isBounded.exists_norm_le
  have hdist : ∀ s ω, ‖x s ω - x_star‖ ≤ 2 * R := fun s ω => by
    calc ‖x s ω - x_star‖ ≤ ‖x s ω‖ + ‖x_star‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add (hR _ (hxX s ω)) (hR _ hx_star_mem)
      _ = 2 * R := by ring
  have hη_pos : ∀ s : ℕ, 0 < 2 / (α * ((s : ℝ) + 2)) := fun s => by positivity
  -- pointwise one-step inequality of projected SGD
  have hstep : ∀ s ω, ‖x (s + 1) ω - x_star‖ ^ 2 ≤ ‖x s ω - x_star‖ ^ 2
      - 2 * (2 / (α * ((s : ℝ) + 2))) * g s ω (x s ω - x_star)
      + (2 / (α * ((s : ℝ) + 2))) ^ 2 * ‖g s ω‖ ^ 2 := by
    intro s ω
    apply sgd_step_ineq 𝓧 h𝓧_convex (g s ω) _ (hη_pos s).le (x s ω) (x (s + 1) ω) x_star
      (hxX (s + 1) ω) hx_star_mem
    intro z hz
    have h := isMinOn_iff.mp (hx_step s ω) z ⟨hz, Set.mem_univ _⟩
    simp only [sgd_bregman_eq] at h
    exact h
  -- measurability / integrability
  have hx_sm : ∀ s, StronglyMeasurable (x s) := fun s => (hx_meas s).stronglyMeasurable
  have hg_int : ∀ s, Integrable (g s) μ := fun s => (h_stoch_oracle s).1
  have hD_int : ∀ s, Integrable (fun ω => ‖x s ω - x_star‖ ^ 2) μ := by
    intro s
    refine Integrable.of_bound ?_ ((2 * R) ^ 2) (ae_of_all _ fun ω => ?_)
    · exact (((hx_meas s).sub_const x_star).norm.pow_const 2).aestronglyMeasurable
    · have h0 : 0 ≤ ‖x s ω - x_star‖ ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact pow_le_pow_left₀ (norm_nonneg _) (hdist s ω) 2
  have hpair_int : ∀ s (G : Ω → E →L[ℝ] ℝ), Integrable G μ →
      Integrable (fun ω => G ω (x s ω - x_star)) μ := by
    intro s G hG
    refine Integrable.mono' (hG.norm.const_mul (2 * R)) ?_ (ae_of_all _ fun ω => ?_)
    · exact (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)).aestronglyMeasurable_comp₂
        hG.aestronglyMeasurable ((hx_sm s).sub stronglyMeasurable_const).aestronglyMeasurable
    · calc ‖G ω (x s ω - x_star)‖ ≤ ‖G ω‖ * ‖x s ω - x_star‖ := (G ω).le_opNorm _
        _ ≤ ‖G ω‖ * (2 * R) := mul_le_mul_of_nonneg_left (hdist s ω) (norm_nonneg _)
        _ = 2 * R * ‖G ω‖ := by ring
  -- conditional expectation identity
  have hce : ∀ s, ∫ ω, g s ω (x s ω - x_star) ∂μ
      = ∫ ω, condExpGivenIterate μ (x s) (g s) ω (x s ω - x_star) ∂μ := fun s =>
    sgd_condexp_pair μ (x s) (hx_meas s) (g s) (hg_int s) x_star (hpair_int s _ (hg_int s))
  have hcond_int : ∀ s, Integrable (condExpGivenIterate μ (x s) (g s)) μ :=
    fun s => integrable_condExp
  have hsub : ∀ s, ∀ᵐ ω ∂μ, f (x s ω) - f x_star ≤
      condExpGivenIterate μ (x s) (g s) ω (x s ω - x_star) - α / 2 * ‖x s ω - x_star‖ ^ 2 := by
    intro s
    filter_upwards [(h_stoch_oracle s).2] with ω hω
    exact sgd_strong_sub 𝓧 f α hf_strongly_convex x_star (x s ω) (hxX s ω) hx_star_mem _ hω
  have hf_int : ∀ s, Integrable (fun ω => f (x s ω)) μ := by
    intro s
    refine integrable_of_le_of_le (hf_ae_comp s).aestronglyMeasurable
      (g₁ := fun _ => f x_star)
      (g₂ := fun ω => f x_star + condExpGivenIterate μ (x s) (g s) ω (x s ω - x_star))
      ?_ ?_ (integrable_const _) ((integrable_const _).add (hpair_int s _ (hcond_int s)))
    · exact ae_of_all _ fun ω => isMinOn_iff.mp hx_star _ (hxX s ω)
    · filter_upwards [hsub s] with ω hω
      have : 0 ≤ α / 2 * ‖x s ω - x_star‖ ^ 2 := by positivity
      linarith
  -- expected one-step inequality
  have hexp : ∀ s : ℕ, ((s : ℝ) + 1) * (∫ ω, f (x s ω) ∂μ - f x_star) ≤
      α / 4 * ((s : ℝ) * ((s : ℝ) + 1) * ∫ ω, ‖x s ω - x_star‖ ^ 2 ∂μ
        - ((s : ℝ) + 1) * ((s : ℝ) + 2) * ∫ ω, ‖x (s + 1) ω - x_star‖ ^ 2 ∂μ) + B ^ 2 / α := by
    intro s
    have hP := hpair_int s _ (hg_int s)
    have ha : ∫ ω, ‖x (s + 1) ω - x_star‖ ^ 2 ∂μ ≤ ∫ ω, ‖x s ω - x_star‖ ^ 2 ∂μ
        - 2 * (2 / (α * ((s : ℝ) + 2))) * ∫ ω, g s ω (x s ω - x_star) ∂μ
        + (2 / (α * ((s : ℝ) + 2))) ^ 2 * B ^ 2 := by
      have hR_int : Integrable (fun ω => ‖x s ω - x_star‖ ^ 2
          - 2 * (2 / (α * ((s : ℝ) + 2))) * g s ω (x s ω - x_star)
          + (2 / (α * ((s : ℝ) + 2))) ^ 2 * ‖g s ω‖ ^ 2) μ :=
        ((hD_int s).sub (hP.const_mul _)).add ((hB_int s).const_mul _)
      have h1 := integral_mono (hD_int (s + 1)) hR_int (fun ω => hstep s ω)
      have hI3 : Integrable
          (fun ω => 2 * (2 / (α * ((s : ℝ) + 2))) * g s ω (x s ω - x_star)) μ := hP.const_mul _
      have hI1 : Integrable (fun ω => ‖x s ω - x_star‖ ^ 2
          - 2 * (2 / (α * ((s : ℝ) + 2))) * g s ω (x s ω - x_star)) μ := (hD_int s).sub hI3
      have hI2 : Integrable (fun ω => (2 / (α * ((s : ℝ) + 2))) ^ 2 * ‖g s ω‖ ^ 2) μ :=
        (hB_int s).const_mul _
      rw [integral_add hI1 hI2, integral_sub (hD_int s) hI3, integral_const_mul,
        integral_const_mul] at h1
      have h2 := hB_sq s
      have h3 : 0 ≤ (2 / (α * ((s : ℝ) + 2))) ^ 2 := by positivity
      nlinarith
    have hb : ∫ ω, f (x s ω) ∂μ - f x_star ≤ ∫ ω, g s ω (x s ω - x_star) ∂μ
        - α / 2 * ∫ ω, ‖x s ω - x_star‖ ^ 2 ∂μ := by
      rw [hce s]
      have hJ1 : Integrable (fun ω => f (x s ω) - f x_star) μ :=
        (hf_int s).sub (integrable_const (f x_star))
      have hJ0 : Integrable (fun ω => α / 2 * ‖x s ω - x_star‖ ^ 2) μ :=
        (hD_int s).const_mul (α / 2)
      have hJ2 : Integrable (fun ω => condExpGivenIterate μ (x s) (g s) ω (x s ω - x_star)
          - α / 2 * ‖x s ω - x_star‖ ^ 2) μ := (hpair_int s _ (hcond_int s)).sub hJ0
      have h2 := integral_mono_ae hJ1 hJ2 (hsub s)
      rw [integral_sub (hf_int s) (integrable_const _),
        integral_sub (hpair_int s _ (hcond_int s)) hJ0, integral_const_mul] at h2
      simpa using h2
    -- algebra
    set A0 := ∫ ω, ‖x s ω - x_star‖ ^ 2 ∂μ
    set A1 := ∫ ω, ‖x (s + 1) ω - x_star‖ ^ 2 ∂μ
    set Gs := ∫ ω, g s ω (x s ω - x_star) ∂μ
    set Fs := ∫ ω, f (x s ω) ∂μ - f x_star
    set e := 2 / (α * ((s : ℝ) + 2)) with he
    set k : ℝ := (s : ℝ) with hk
    have hk0 : 0 ≤ k := Nat.cast_nonneg s
    have he_eq : α * (k + 2) * e = 2 := by
      rw [he]; field_simp
    have he0 : 0 < e := hη_pos s
    have h3 : (k + 1) * Fs ≤ (k + 1) * (Gs - α / 2 * A0) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    have h4 : (α * (k + 1) * (k + 2) / 4) * (2 * e * Gs) ≤
        (α * (k + 1) * (k + 2) / 4) * (A0 - A1 + e ^ 2 * B ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h5 : (α * (k + 1) * (k + 2) / 4) * (2 * e * Gs) = (k + 1) * Gs := by
      calc (α * (k + 1) * (k + 2) / 4) * (2 * e * Gs) = (k + 1) * Gs * (α * (k + 2) * e) / 2 := by
            ring
        _ = (k + 1) * Gs := by rw [he_eq]; ring
    have h6 : (α * (k + 1) * (k + 2) / 4) * (e ^ 2 * B ^ 2) = (k + 1) * e / 2 * B ^ 2 := by
      calc (α * (k + 1) * (k + 2) / 4) * (e ^ 2 * B ^ 2)
          = (k + 1) * e * B ^ 2 * (α * (k + 2) * e) / 4 := by ring
        _ = (k + 1) * e / 2 * B ^ 2 := by rw [he_eq]; ring
    have h7 : (k + 1) * e / 2 * B ^ 2 ≤ B ^ 2 / α := by
      have h8 : (k + 1) * e / 2 ≤ 1 / α := by
        rw [le_div_iff₀ hα_pos]
        have : (k + 1) * e / 2 * α = (k + 1) / (k + 2) := by
          field_simp
          linarith [he_eq]
        rw [this, div_le_one (by positivity)]
        linarith
      calc (k + 1) * e / 2 * B ^ 2 ≤ 1 / α * B ^ 2 :=
            mul_le_mul_of_nonneg_right h8 (sq_nonneg B)
        _ = B ^ 2 / α := by ring
    linarith [h3, h4, h5, h6, h7]
  -- telescoping
  have htel : ∀ n : ℕ, ∑ s ∈ Finset.range n, ((s : ℝ) + 1) * (∫ ω, f (x s ω) ∂μ - f x_star)
      + α / 4 * ((n : ℝ) * ((n : ℝ) + 1) * ∫ ω, ‖x n ω - x_star‖ ^ 2 ∂μ) ≤ n * (B ^ 2 / α) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have := hexp n
      push_cast
      nlinarith
  have hsum_bound : ∑ s ∈ Finset.range t, ((s : ℝ) + 1) * (∫ ω, f (x s ω) ∂μ - f x_star)
      ≤ t * (B ^ 2 / α) := by
    have h1 := htel t
    have h2 : 0 ≤ α / 4 * ((t : ℝ) * ((t : ℝ) + 1) * ∫ ω, ‖x t ω - x_star‖ ^ 2 ∂μ) := by
      have : 0 ≤ ∫ ω, ‖x t ω - x_star‖ ^ 2 ∂μ := integral_nonneg (fun ω => by positivity)
      positivity
    linarith
  -- weights
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hsum_id : ∀ n : ℕ, ∑ s ∈ Finset.range n, ((s : ℝ) + 1) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  have hw_nonneg : ∀ s ∈ Finset.range t,
      0 ≤ (2 * ((s : ℝ) + 1)) / ((t : ℝ) * ((t : ℝ) + 1)) := fun s _ => by positivity
  have hw_sum : ∑ s ∈ Finset.range t, (2 * ((s : ℝ) + 1)) / ((t : ℝ) * ((t : ℝ) + 1)) = 1 := by
    rw [← Finset.sum_div, ← Finset.mul_sum, hsum_id]
    field_simp
  have havg_mem : ∀ ω, ∑ s ∈ Finset.range t,
      ((2 * ((s : ℝ) + 1)) / ((t : ℝ) * ((t : ℝ) + 1))) • x s ω ∈ 𝓧 := fun ω =>
    h𝓧_convex.sum_mem hw_nonneg hw_sum (fun s _ => hxX s ω)
  have hjensen : ∀ ω, f (∑ s ∈ Finset.range t,
      ((2 * ((s : ℝ) + 1)) / ((t : ℝ) * ((t : ℝ) + 1))) • x s ω) ≤
      ∑ s ∈ Finset.range t, (2 * ((s : ℝ) + 1)) / ((t : ℝ) * ((t : ℝ) + 1)) * f (x s ω) := by
    intro ω
    have h := hf_convex.map_sum_le hw_nonneg hw_sum (fun s _ => hxX s ω)
    simpa only [smul_eq_mul] using h
  have hlow : ∀ ω, f x_star ≤ f (∑ s ∈ Finset.range t,
      ((2 * ((s : ℝ) + 1)) / ((t : ℝ) * ((t : ℝ) + 1))) • x s ω) := fun ω =>
    isMinOn_iff.mp hx_star _ (havg_mem ω)
  have hterm_int : ∀ s ∈ Finset.range t, Integrable
      (fun ω => (2 * ((s : ℝ) + 1)) / ((t : ℝ) * ((t : ℝ) + 1)) * f (x s ω)) μ :=
    fun s _ => (hf_int s).const_mul _
  have hsum_int : Integrable (fun ω => ∑ s ∈ Finset.range t,
      (2 * ((s : ℝ) + 1)) / ((t : ℝ) * ((t : ℝ) + 1)) * f (x s ω)) μ :=
    integrable_finset_sum _ hterm_int
  have havg_int : Integrable (fun ω => f (∑ s ∈ Finset.range t,
      ((2 * ((s : ℝ) + 1)) / ((t : ℝ) * ((t : ℝ) + 1))) • x s ω)) μ :=
    integrable_of_le_of_le hweighted_ae.aestronglyMeasurable (ae_of_all _ hlow)
      (ae_of_all _ hjensen) (integrable_const _) hsum_int
  have hmono := integral_mono havg_int hsum_int hjensen
  rw [integral_finset_sum _ hterm_int] at hmono
  simp only [integral_const_mul] at hmono
  have hfinal_eq : ∑ s ∈ Finset.range t, (2 * ((s : ℝ) + 1)) / ((t : ℝ) * ((t : ℝ) + 1))
        * ∫ ω, f (x s ω) ∂μ - f x_star
      = 2 / ((t : ℝ) * ((t : ℝ) + 1)) *
        ∑ s ∈ Finset.range t, ((s : ℝ) + 1) * (∫ ω, f (x s ω) ∂μ - f x_star) := by
    have h1 : ∑ s ∈ Finset.range t, (2 * ((s : ℝ) + 1)) / ((t : ℝ) * ((t : ℝ) + 1))
          * ∫ ω, f (x s ω) ∂μ - f x_star
        = ∑ s ∈ Finset.range t, (2 * ((s : ℝ) + 1)) / ((t : ℝ) * ((t : ℝ) + 1))
          * (∫ ω, f (x s ω) ∂μ - f x_star) := by
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw_sum, one_mul]
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    ring
  have hfin : 2 / ((t : ℝ) * ((t : ℝ) + 1)) *
      ∑ s ∈ Finset.range t, ((s : ℝ) + 1) * (∫ ω, f (x s ω) ∂μ - f x_star)
      ≤ (2 * B ^ 2) / (α * ((t : ℝ) + 1)) := by
    calc 2 / ((t : ℝ) * ((t : ℝ) + 1)) *
          ∑ s ∈ Finset.range t, ((s : ℝ) + 1) * (∫ ω, f (x s ω) ∂μ - f x_star)
        ≤ 2 / ((t : ℝ) * ((t : ℝ) + 1)) * (t * (B ^ 2 / α)) :=
          mul_le_mul_of_nonneg_left hsum_bound (by positivity)
      _ = (2 * B ^ 2) / (α * ((t : ℝ) + 1)) := by
          field_simp
  linarith [hmono, hfinal_eq, hfin]

end stochastic_gradient_descent_bound
