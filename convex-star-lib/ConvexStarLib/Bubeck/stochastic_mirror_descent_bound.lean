import ConvexStarLib.Defs

/-!
# `stochastic_mirror_descent_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/stochastic_mirror_descent_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace stochastic_mirror_descent_bound`, so the main result is `stochastic_mirror_descent_bound.stochastic_mirror_descent_bound`.
-/

namespace stochastic_mirror_descent_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem stochastic_mirror_descent_bound
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {t : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (𝓧 : Set E)
  (𝓓 : Set E)
  (f : E → ℝ)
  (phi : E → ℝ)
  (x : ℕ → Ω → E)
  (g : ℕ → Ω → E →L[ℝ] ℝ)
  (B R : ℝ)
  (x0 : E)
  (hx0 : ∀ ω, x 0 ω = x0)
  (hR_sq : R ^ 2 = sSup {v | ∃ a ∈ 𝓧 ∩ 𝓓, phi a - phi x0 = v})
  (hR_pos : 0 < R)
  (hB_pos : 0 < B)
  (ht : 0 < t)
  (hf_ae_comp : ∀ s, AEMeasurable (fun ω => f (x s ω)) μ)
  (havg_ae :
      AEMeasurable
        (fun ω => f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x s ω)) μ)
  (h_mirror_seq :
    IsStochasticMirrorDescentSequence 𝓧 𝓓 phi x g
      (fun _ => (R / B) * Real.sqrt (2 / (t : ℝ))))
  (h_stoch_oracle : ∀ s, IsStochasticSubgradientOracle μ 𝓧 f (x s) (g s))
  (hB_int : ∀ s, Integrable (fun ω => ‖g s ω‖ ^ (2 : ℕ)) μ)
  (hB_sq : ∀ s, ∫ ω, ‖g s ω‖ ^ (2 : ℕ) ∂μ ≤ B ^ 2)
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (h𝓓_convex : Convex ℝ 𝓓)
  (h𝓓_open : IsOpen 𝓓)
  (h𝓓_contains : 𝓧 ⊆ closure 𝓓)
  (h_inter_nonempty : Set.Nonempty (𝓧 ∩ 𝓓))
  (hphi_differentiable : DifferentiableOn ℝ phi 𝓓)
  (hphi_mirror_map : IsMirrorMap 𝓓 phi)
  (hphi_strong_convex : StrongConvexOn (𝓧 ∩ 𝓓) 1 phi)
  (hf_convex : ConvexOn ℝ 𝓧 f) :
  ∫ ω, f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x s ω) ∂μ
    - sInf (f '' 𝓧)
    ≤ R * B * Real.sqrt (2 / (t : ℝ)) := by
  classical
  have hTpos : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht
  have hq_pos : 0 < Real.sqrt (2 / (t:ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hq_sq : Real.sqrt (2 / (t:ℝ)) ^ 2 = 2 / (t:ℝ) := Real.sq_sqrt (by positivity)
  set q : ℝ := Real.sqrt (2 / (t:ℝ)) with hq_def
  obtain ⟨hx_meas, hx0_mem, hx0_min, hx_mem, hx_step⟩ := h_mirror_seq
  set η : ℝ := R / B * q with hη_def
  have hη_pos : 0 < η := by positivity
  have hx_step' : ∀ s ω, IsMinOn (fun z => η * g s ω z + bregmanDivergence phi z (x s ω))
      (𝓧 ∩ 𝓓) (x (s + 1) ω) := hx_step
  clear hx_step
  have hS_convex : Convex ℝ (𝓧 ∩ 𝓓) := h𝓧_convex.inter h𝓓_convex
  have hdiff : ∀ y ∈ 𝓓, DifferentiableAt ℝ phi y := fun y hy =>
    hphi_differentiable.differentiableAt (h𝓓_open.mem_nhds hy)
  obtain ⟨ω0, hω0⟩ := (h_stoch_oracle 0).2.exists
  have hx0S : x0 ∈ 𝓧 ∩ 𝓓 := by rw [← hx0 ω0]; exact hx0_mem ω0
  -- one-dimensional first-order condition
  have key1D : ∀ (F : ℝ → ℝ) (d : ℝ), HasDerivAt F d 0 →
      (∀ τ ∈ Set.Icc (0:ℝ) 1, F τ ≤ F 0) → d ≤ 0 := by
    intro F d hF hle
    have hmax : IsLocalMaxOn F (Set.Icc 0 1) 0 := IsMaxOn.localize (isMaxOn_iff.mpr hle)
    have hcone : (1:ℝ) ∈ posTangentConeAt (Set.Icc (0:ℝ) 1) 0 := by
      apply mem_posTangentConeAt_of_segment_subset
      rw [zero_add, segment_eq_Icc zero_le_one]
    have := hmax.hasFDerivWithinAt_nonpos hF.hasFDerivAt.hasFDerivWithinAt hcone
    simpa using this
  -- strong convexity gives a lower bound on the Bregman divergence
  have hD_lower : ∀ y ∈ 𝓧 ∩ 𝓓, ∀ z ∈ 𝓧 ∩ 𝓓,
      1 / 2 * ‖z - y‖ ^ 2 ≤ bregmanDivergence phi z y := by
    intro y hy z hz
    set K := 1 / 2 * ‖z - y‖ ^ 2 with hK
    have hline : HasDerivAt (fun τ : ℝ => y + τ • (z - y)) (z - y) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const (z - y)).const_add y
    have hphi_line : HasDerivAt (fun τ : ℝ => phi (y + τ • (z - y))) (fderiv ℝ phi y (z - y)) 0 :=
      (hdiff y hy.2).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
    have hquad : HasDerivAt (fun τ : ℝ => τ * (1 - τ) * K) K 0 := by
      have := ((hasDerivAt_id (0:ℝ)).mul ((hasDerivAt_id (0:ℝ)).const_sub 1)).mul_const K
      simpa using this
    have hF : HasDerivAt (fun τ : ℝ => phi (y + τ • (z - y)) - phi y - τ * (phi z - phi y)
        + τ * (1 - τ) * K) (fderiv ℝ phi y (z - y) - (phi z - phi y) + K) 0 := by
      have := ((hphi_line.sub_const (phi y)).sub
        ((hasDerivAt_id (0:ℝ)).mul_const (phi z - phi y))).add hquad
      simpa using this
    have hle := key1D _ _ hF (by
      intro τ hτ
      simp only [zero_smul, add_zero, sub_self, zero_mul, sub_zero]
      have h1 := hphi_strong_convex.2 hz hy hτ.1 (sub_nonneg.mpr hτ.2) (by ring : τ + (1 - τ) = 1)
      have h2 : τ • z + (1 - τ) • y = y + τ • (z - y) := by
        rw [smul_sub, sub_smul, one_smul]; abel
      rw [h2] at h1
      simp only [smul_eq_mul] at h1
      rw [← hK] at h1
      linarith [h1])
    unfold bregmanDivergence
    linarith
  -- first-order optimality of x0
  have hx0_opt : ∀ y ∈ 𝓧 ∩ 𝓓, 0 ≤ fderiv ℝ phi x0 (y - x0) := by
    intro y hy
    have hmin : IsMinOn phi (𝓧 ∩ 𝓓) x0 := by rw [← hx0 ω0]; exact hx0_min ω0
    exact hmin.localize.hasFDerivWithinAt_nonneg (hdiff x0 hx0S.2).hasFDerivAt.hasFDerivWithinAt
      (sub_mem_posTangentConeAt_of_segment_subset (hS_convex.segment_subset hx0S hy))
  -- first-order optimality of each step
  have hstep_opt : ∀ s ω, ∀ y ∈ 𝓧 ∩ 𝓓, 0 ≤ η * g s ω (y - x (s+1) ω)
      + fderiv ℝ phi (x (s+1) ω) (y - x (s+1) ω) - fderiv ℝ phi (x s ω) (y - x (s+1) ω) := by
    intro s ω y hy
    have hbS : x (s+1) ω ∈ 𝓧 ∩ 𝓓 := hx_mem (s+1) ω
    have h3 : HasFDerivAt (fun z => fderiv ℝ phi (x s ω) (z - x s ω)) (fderiv ℝ phi (x s ω))
        (x (s+1) ω) := by
      have := (fderiv ℝ phi (x s ω)).hasFDerivAt.comp (x (s+1) ω)
        ((hasFDerivAt_id (x (s+1) ω)).sub_const (x s ω))
      rw [ContinuousLinearMap.comp_id] at this
      exact this
    have hd : HasFDerivAt (fun z => η * g s ω z + bregmanDivergence phi z (x s ω))
        (η • g s ω + (fderiv ℝ phi (x (s+1) ω) - fderiv ℝ phi (x s ω))) (x (s+1) ω) :=
      ((g s ω).hasFDerivAt.const_mul η).add
        (((hdiff _ hbS.2).hasFDerivAt.sub_const (phi (x s ω))).sub h3)
    have := (hx_step' s ω).localize.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt
      (sub_mem_posTangentConeAt_of_segment_subset (hS_convex.segment_subset hbS hy))
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul] at this
    linarith
  -- the bound R^2
  have hR_bound : ∀ a ∈ 𝓧 ∩ 𝓓, phi a - phi x0 ≤ R ^ 2 := by
    have hbdd : BddAbove {v | ∃ a ∈ 𝓧 ∩ 𝓓, phi a - phi x0 = v} := by
      by_contra hnb
      have h0 := Real.sSup_of_not_bddAbove hnb
      rw [← hR_sq] at h0
      have : 0 < R ^ 2 := by positivity
      linarith
    intro a ha
    rw [hR_sq]
    exact le_csSup hbdd ⟨a, ha, rfl⟩
  -- per-step inequality
  have hstep : ∀ s ω, ∀ y ∈ 𝓧 ∩ 𝓓, η * g s ω (x s ω - y) ≤ bregmanDivergence phi y (x s ω)
      - bregmanDivergence phi y (x (s+1) ω) + η ^ 2 / 2 * ‖g s ω‖ ^ 2 := by
    intro s ω y hy
    have hopt := hstep_opt s ω y hy
    have hDba := hD_lower (x s ω) (hx_mem s ω) (x (s+1) ω) (hx_mem (s+1) ω)
    have hLn : |g s ω (x s ω - x (s+1) ω)| ≤ ‖g s ω‖ * ‖x s ω - x (s+1) ω‖ := by
      rw [← Real.norm_eq_abs]; exact (g s ω).le_opNorm _
    have hyoung : η * g s ω (x s ω - x (s+1) ω)
        ≤ η ^ 2 / 2 * ‖g s ω‖ ^ 2 + 1 / 2 * ‖x s ω - x (s+1) ω‖ ^ 2 := by
      have h1 : η * g s ω (x s ω - x (s+1) ω) ≤ η * (‖g s ω‖ * ‖x s ω - x (s+1) ω‖) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans hLn) hη_pos.le
      nlinarith [sq_nonneg (η * ‖g s ω‖ - ‖x s ω - x (s+1) ω‖)]
    unfold bregmanDivergence at hDba ⊢
    rw [norm_sub_rev] at hDba
    simp only [map_sub] at hopt hDba hyoung ⊢
    linarith
  -- telescoping
  have htele : ∀ ω, ∀ y ∈ 𝓧 ∩ 𝓓, η * ∑ s ∈ Finset.range t, g s ω (x s ω - y)
      ≤ R ^ 2 + η ^ 2 / 2 * ∑ s ∈ Finset.range t, ‖g s ω‖ ^ 2 := by
    intro ω y hy
    have h1 : ∑ s ∈ Finset.range t, η * g s ω (x s ω - y) ≤ ∑ s ∈ Finset.range t,
        ((bregmanDivergence phi y (x s ω) - bregmanDivergence phi y (x (s+1) ω))
          + η ^ 2 / 2 * ‖g s ω‖ ^ 2) :=
      Finset.sum_le_sum (fun s _ => hstep s ω y hy)
    rw [Finset.sum_add_distrib, Finset.sum_range_sub' (fun s => bregmanDivergence phi y (x s ω)),
      ← Finset.mul_sum, ← Finset.mul_sum] at h1
    have h2 : bregmanDivergence phi y (x 0 ω) ≤ R ^ 2 := by
      rw [hx0 ω]; unfold bregmanDivergence
      have := hx0_opt y hy; have := hR_bound y hy; linarith
    have h3 : 0 ≤ bregmanDivergence phi y (x t ω) := by
      have := hD_lower (x t ω) (hx_mem t ω) y hy
      have : 0 ≤ 1 / 2 * ‖y - x t ω‖ ^ 2 := by positivity
      linarith
    linarith
  -- boundedness of 𝓧
  obtain ⟨C, hC⟩ := h𝓧_compact.isBounded.exists_norm_le
  have hxs_bound : ∀ s ω (y : E), ‖x s ω - y‖ ≤ C + ‖y‖ := fun s ω y =>
    (norm_sub_le _ _).trans (by linarith [hC _ (hx_mem s ω).1])
  -- integrability of pairings
  have hint_gen : ∀ (s : ℕ) (h : Ω → E →L[ℝ] ℝ), Integrable h μ → ∀ y : E,
      Integrable (fun ω => h ω (x s ω - y)) μ := by
    intro s h hh y
    refine Integrable.mono' (hh.norm.mul_const (C + ‖y‖)) ?_ ?_
    · exact (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)).continuous₂.comp_aestronglyMeasurable
        (hh.aestronglyMeasurable.prodMk ((hx_meas s).sub_const y).aestronglyMeasurable)
    · filter_upwards with ω
      calc ‖h ω (x s ω - y)‖ ≤ ‖h ω‖ * ‖x s ω - y‖ := (h ω).le_opNorm _
      _ ≤ ‖h ω‖ * (C + ‖y‖) := by gcongr; exact hxs_bound s ω y
  -- pull-out property
  have hpull : ∀ s (y : E), ∫ ω, condExpGivenIterate μ (x s) (g s) ω (x s ω - y) ∂μ
      = ∫ ω, g s ω (x s ω - y) ∂μ := by
    intro s y
    have hm : MeasurableSpace.comap (x s) inferInstance ≤ ‹MeasurableSpace Ω› :=
      (hx_meas s).comap_le
    have hc : StronglyMeasurable[MeasurableSpace.comap (x s) inferInstance]
        (fun ω => x s ω - y) :=
      ((continuous_id.sub continuous_const).measurable.comp
        (comap_measurable (x s))).stronglyMeasurable
    have hpo := condExp_bilin_of_stronglyMeasurable_right
      (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)) hc
      (hint_gen s (g s) (h_stoch_oracle s).1 y) (h_stoch_oracle s).1
    unfold condExpGivenIterate
    calc ∫ ω, (μ[g s | MeasurableSpace.comap (x s) inferInstance] ω) (x s ω - y) ∂μ
        = ∫ ω, (μ[fun ω => g s ω (x s ω - y) | MeasurableSpace.comap (x s) inferInstance]) ω ∂μ :=
          integral_congr_ae hpo.symm
      _ = ∫ ω, g s ω (x s ω - y) ∂μ := integral_condExp hm
  -- Jensen
  have hw0 : ∀ i ∈ Finset.range t, (0:ℝ) ≤ 1 / (t:ℝ) := fun _ _ => by positivity
  have hw1 : ∑ i ∈ Finset.range t, (1 / (t:ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
  have havg_mem : ∀ ω, (1 / (t:ℝ)) • ∑ s ∈ Finset.range t, x s ω ∈ 𝓧 := by
    intro ω; rw [Finset.smul_sum]; exact h𝓧_convex.sum_mem hw0 hw1 (fun s _ => (hx_mem s ω).1)
  have hjensen : ∀ ω, (t:ℝ) * f ((1 / (t:ℝ)) • ∑ s ∈ Finset.range t, x s ω)
      ≤ ∑ s ∈ Finset.range t, f (x s ω) := by
    intro ω
    have := hf_convex.map_sum_le hw0 hw1 (p := fun s => x s ω) (fun s _ => (hx_mem s ω).1)
    rw [← Finset.smul_sum] at this
    simp only [smul_eq_mul, ← Finset.mul_sum] at this
    rw [show ∑ s ∈ Finset.range t, f (x s ω)
      = (t:ℝ) * ((1 / (t:ℝ)) * ∑ s ∈ Finset.range t, f (x s ω)) by field_simp]
    exact mul_le_mul_of_nonneg_left this hTpos.le
  -- lower bound of f on 𝓧
  set L0 := condExpGivenIterate μ (x 0) (g 0) ω0 with hL0
  have hf_lower : ∀ z ∈ 𝓧, f x0 - ‖L0‖ * (C + ‖x0‖) ≤ f z := by
    intro z hz
    have h1 := hω0 z hz
    rw [hx0 ω0] at h1
    have h2 : |L0 (z - x0)| ≤ ‖L0‖ * (C + ‖x0‖) := by
      rw [← Real.norm_eq_abs]
      calc ‖L0 (z - x0)‖ ≤ ‖L0‖ * ‖z - x0‖ := L0.le_opNorm _
      _ ≤ ‖L0‖ * (C + ‖x0‖) := by gcongr; exact (norm_sub_le _ _).trans (by linarith [hC z hz])
    linarith [neg_abs_le (L0 (z - x0))]
  -- a.e. subgradient for all s
  have hsub_all : ∀ᵐ ω ∂μ, ∀ s, IsSubgradientOn 𝓧 f (x s ω)
      (condExpGivenIterate μ (x s) (g s) ω) :=
    ae_all_iff.mpr (fun s => (h_stoch_oracle s).2)
  have hG_int : ∀ s, Integrable (condExpGivenIterate μ (x s) (g s)) μ :=
    fun s => integrable_condExp
  have hbound : ∀ y ∈ 𝓧, ∀ᵐ ω ∂μ,
      (t:ℝ) * (f ((1 / (t:ℝ)) • ∑ s ∈ Finset.range t, x s ω) - f y)
      ≤ ∑ s ∈ Finset.range t, condExpGivenIterate μ (x s) (g s) ω (x s ω - y) := by
    intro y hy
    filter_upwards [hsub_all] with ω hω
    have h2 : ∀ s, f (x s ω) - f y ≤ condExpGivenIterate μ (x s) (g s) ω (x s ω - y) := by
      intro s
      have h4 := hω s y hy
      have h3 : condExpGivenIterate μ (x s) (g s) ω (x s ω - y)
          = - condExpGivenIterate μ (x s) (g s) ω (y - x s ω) := by rw [← map_neg, neg_sub]
      linarith
    have h3 : ∑ s ∈ Finset.range t, (f (x s ω) - f y)
        ≤ ∑ s ∈ Finset.range t, condExpGivenIterate μ (x s) (g s) ω (x s ω - y) :=
      Finset.sum_le_sum (fun s _ => h2 s)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h3
    have h1 := hjensen ω
    linarith
  -- integrability of f ∘ avg
  have hfavg_int : Integrable (fun ω => f ((1 / (t:ℝ)) • ∑ s ∈ Finset.range t, x s ω)) μ := by
    obtain ⟨y1, hy1⟩ := h_inter_nonempty
    refine integrable_of_le_of_le havg_ae.aestronglyMeasurable
      (g₁ := fun _ => f x0 - ‖L0‖ * (C + ‖x0‖))
      (g₂ := fun ω => f y1 + (1 / (t:ℝ)) * ∑ s ∈ Finset.range t,
        condExpGivenIterate μ (x s) (g s) ω (x s ω - y1)) ?_ ?_ (integrable_const _) ?_
    · exact ae_of_all _ (fun ω => hf_lower _ (havg_mem ω))
    · filter_upwards [hbound y1 hy1.1] with ω hω
      have : f ((1 / (t:ℝ)) • ∑ s ∈ Finset.range t, x s ω) - f y1
          ≤ (1 / (t:ℝ)) * ∑ s ∈ Finset.range t,
            condExpGivenIterate μ (x s) (g s) ω (x s ω - y1) := by
        calc f ((1 / (t:ℝ)) • ∑ s ∈ Finset.range t, x s ω) - f y1
            = (1 / (t:ℝ)) * ((t:ℝ) * (f ((1 / (t:ℝ)) • ∑ s ∈ Finset.range t, x s ω) - f y1)) := by
              field_simp
          _ ≤ _ := by gcongr
      linarith
    · exact (integrable_const _).add
        ((integrable_finset_sum _ (fun s _ => hint_gen s _ (hG_int s) y1)).const_mul _)
  -- main bound for comparison points in 𝓧 ∩ 𝓓
  have hqt : q ^ 2 * (t:ℝ) = 2 := by rw [hq_sq]; field_simp
  have hmain : ∀ y ∈ 𝓧 ∩ 𝓓,
      ∫ ω, f ((1 / (t:ℝ)) • ∑ s ∈ Finset.range t, x s ω) ∂μ - f y ≤ R * B * q := by
    intro y hy
    have hI1 : (t:ℝ) * (∫ ω, f ((1 / (t:ℝ)) • ∑ s ∈ Finset.range t, x s ω) ∂μ - f y)
        ≤ ∑ s ∈ Finset.range t, ∫ ω, condExpGivenIterate μ (x s) (g s) ω (x s ω - y) ∂μ := by
      rw [← integral_finset_sum _ (fun s _ => hint_gen s _ (hG_int s) y)]
      have : ∫ ω, (t:ℝ) * (f ((1 / (t:ℝ)) • ∑ s ∈ Finset.range t, x s ω) - f y) ∂μ
          = (t:ℝ) * (∫ ω, f ((1 / (t:ℝ)) • ∑ s ∈ Finset.range t, x s ω) ∂μ - f y) := by
        rw [integral_const_mul, integral_sub hfavg_int (integrable_const _), integral_const]
        simp
      rw [← this]
      exact integral_mono_ae ((hfavg_int.sub (integrable_const _)).const_mul _)
        (integrable_finset_sum _ (fun s _ => hint_gen s _ (hG_int s) y)) (hbound y hy.1)
    have hI2 : ∑ s ∈ Finset.range t, ∫ ω, condExpGivenIterate μ (x s) (g s) ω (x s ω - y) ∂μ
        = ∫ ω, ∑ s ∈ Finset.range t, g s ω (x s ω - y) ∂μ := by
      rw [integral_finset_sum _ (fun s _ => hint_gen s (g s) (h_stoch_oracle s).1 y)]
      exact Finset.sum_congr rfl (fun s _ => hpull s y)
    have hI3 : η * ∫ ω, ∑ s ∈ Finset.range t, g s ω (x s ω - y) ∂μ
        ≤ R ^ 2 + η ^ 2 / 2 * ((t:ℝ) * B ^ 2) := by
      rw [← integral_const_mul]
      calc ∫ ω, η * ∑ s ∈ Finset.range t, g s ω (x s ω - y) ∂μ
          ≤ ∫ ω, (R ^ 2 + η ^ 2 / 2 * ∑ s ∈ Finset.range t, ‖g s ω‖ ^ 2) ∂μ :=
            integral_mono ((integrable_finset_sum _
                (fun s _ => hint_gen s (g s) (h_stoch_oracle s).1 y)).const_mul _)
              ((integrable_const _).add
                ((integrable_finset_sum _ (fun s _ => hB_int s)).const_mul _))
              (fun ω => htele ω y hy)
        _ = R ^ 2 + η ^ 2 / 2 * ∑ s ∈ Finset.range t, ∫ ω, ‖g s ω‖ ^ 2 ∂μ := by
            rw [integral_add (integrable_const _)
                ((integrable_finset_sum _ (fun s _ => hB_int s)).const_mul _),
              integral_const, integral_const_mul, integral_finset_sum _ (fun s _ => hB_int s)]
            simp
        _ ≤ R ^ 2 + η ^ 2 / 2 * ((t:ℝ) * B ^ 2) := by
            gcongr
            calc ∑ s ∈ Finset.range t, ∫ ω, ‖g s ω‖ ^ 2 ∂μ ≤ ∑ s ∈ Finset.range t, B ^ 2 :=
                  Finset.sum_le_sum (fun s _ => hB_sq s)
              _ = (t:ℝ) * B ^ 2 := by simp
    have e1 : η ^ 2 / 2 * ((t:ℝ) * B ^ 2) = R ^ 2 := by
      calc η ^ 2 / 2 * ((t:ℝ) * B ^ 2) = (R / B * B) ^ 2 * (q ^ 2 * (t:ℝ)) / 2 := by
            rw [hη_def]; ring
        _ = R ^ 2 := by rw [div_mul_cancel₀ R hB_pos.ne', hqt]; ring
    have e2 : (t:ℝ) * η * (R * B * q) = 2 * R ^ 2 := by
      calc (t:ℝ) * η * (R * B * q) = R * (R / B * B) * (q ^ 2 * (t:ℝ)) := by
            rw [hη_def]; ring
        _ = 2 * R ^ 2 := by rw [div_mul_cancel₀ R hB_pos.ne', hqt]; ring
    have hkey : (t:ℝ) * η * (∫ ω, f ((1 / (t:ℝ)) • ∑ s ∈ Finset.range t, x s ω) ∂μ - f y)
        ≤ (t:ℝ) * η * (R * B * q) := by
      calc (t:ℝ) * η * (∫ ω, f ((1 / (t:ℝ)) • ∑ s ∈ Finset.range t, x s ω) ∂μ - f y)
          = η * ((t:ℝ) * (∫ ω, f ((1 / (t:ℝ)) • ∑ s ∈ Finset.range t, x s ω) ∂μ - f y)) := by
            ring
        _ ≤ η * ∫ ω, ∑ s ∈ Finset.range t, g s ω (x s ω - y) ∂μ := by
            rw [← hI2]; exact mul_le_mul_of_nonneg_left hI1 hη_pos.le
        _ ≤ R ^ 2 + η ^ 2 / 2 * ((t:ℝ) * B ^ 2) := hI3
        _ = (t:ℝ) * η * (R * B * q) := by rw [e1, e2]; ring
    exact le_of_mul_le_mul_left hkey (by positivity)
  -- extension to all comparison points in 𝓧
  have hext : ∀ y ∈ 𝓧,
      ∫ ω, f ((1 / (t:ℝ)) • ∑ s ∈ Finset.range t, x s ω) ∂μ - R * B * q ≤ f y := by
    intro y hy
    obtain ⟨y0, hy0⟩ := h_inter_nonempty
    have hlim : Filter.Tendsto (fun τ : ℝ => f y + τ * (f y0 - f y)) (𝓝[>] 0) (𝓝 (f y)) := by
      have : Filter.Tendsto (fun τ : ℝ => f y + τ * (f y0 - f y)) (𝓝 0)
          (𝓝 (f y + 0 * (f y0 - f y))) :=
        tendsto_const_nhds.add (Filter.tendsto_id.mul tendsto_const_nhds)
      rw [zero_mul, add_zero] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with τ hτ
    have ha : (0:ℝ) ≤ 1 - τ := by linarith [hτ.2]
    have hmemX : (1 - τ) • y + τ • y0 ∈ 𝓧 := h𝓧_convex hy hy0.1 ha hτ.1.le (by ring)
    have hmemD : (1 - τ) • y + τ • y0 ∈ 𝓓 := by
      have := h𝓓_convex.combo_closure_interior_mem_interior (h𝓓_contains hy)
        (by rw [h𝓓_open.interior_eq]; exact hy0.2) ha hτ.1 (by ring)
      rwa [h𝓓_open.interior_eq] at this
    have h1 := hmain _ ⟨hmemX, hmemD⟩
    have h2 := hf_convex.2 hy hy0.1 ha hτ.1.le (by ring)
    simp only [smul_eq_mul] at h2
    linarith
  have hfin := le_csInf (h𝓧_nonempty.image f) (by rintro _ ⟨y, hy, rfl⟩; exact hext y hy)
  linarith

end stochastic_mirror_descent_bound
