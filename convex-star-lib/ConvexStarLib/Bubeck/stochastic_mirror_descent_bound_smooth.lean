import ConvexStarLib.Defs

/-!
# `stochastic_mirror_descent_bound_smooth`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/stochastic_mirror_descent_bound_smooth` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace stochastic_mirror_descent_bound_smooth`, so the main result is `stochastic_mirror_descent_bound_smooth.stochastic_mirror_descent_bound_smooth`.
-/

namespace stochastic_mirror_descent_bound_smooth

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Descent lemma for smooth functions on a convex set. -/
lemma smd_descent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Set E} {f : E → ℝ} {β : ℝ} (hX : Convex ℝ X)
    (hdiff : ∀ z ∈ X, DifferentiableAt ℝ f z) (hsmooth : IsSmoothOn X f β)
    {x y : E} (hx : x ∈ X) (hy : y ∈ X) :
    f y ≤ f x + fderiv ℝ f x (y - x) + β / 2 * ‖y - x‖ ^ 2 := by
  obtain ⟨v, rfl⟩ : ∃ v, y = x + v := ⟨y - x, by abel⟩
  rw [add_sub_cancel_left]
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • v ∈ X := fun t ht => hX.add_smul_mem hx hy ht
  let ψ : ℝ → ℝ := fun t => f (x + t • v) - t * fderiv ℝ f x v - β / 2 * t ^ 2 * ‖v‖ ^ 2
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt ψ (fderiv ℝ f (x + t • v) v - fderiv ℝ f x v - β * t * ‖v‖ ^ 2) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => x + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have h2 : HasDerivAt (fun s : ℝ => f (x + s • v)) (fderiv ℝ f (x + t • v) v) t :=
      (hdiff _ (hmem t ht)).hasFDerivAt.comp_hasDerivAt t h1
    have h3 : HasDerivAt (fun s : ℝ => s * fderiv ℝ f x v) (fderiv ℝ f x v) t := by
      simpa using (hasDerivAt_id t).mul_const (fderiv ℝ f x v)
    have h4 : HasDerivAt (fun s : ℝ => β / 2 * s ^ 2 * ‖v‖ ^ 2) (β * t * ‖v‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (β / 2)).mul_const (‖v‖ ^ 2)
      convert this using 1
      push_cast
      ring
    exact (h2.sub h3).sub h4
  have hcont : ContinuousOn ψ (Set.Icc 0 1) := fun t ht =>
    (hderiv t ht).continuousAt.continuousWithinAt
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1) hcont
    · intro t ht
      exact (hderiv t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      have ht' := interior_subset ht
      rw [interior_Icc] at ht
      have hp := hmem t ht'
      have h1 : (fderiv ℝ f (x + t • v) - fderiv ℝ f x) v
          ≤ ‖fderiv ℝ f (x + t • v) - fderiv ℝ f x‖ * ‖v‖ :=
        le_trans (le_abs_self _)
          (by simpa [Real.norm_eq_abs] using (fderiv ℝ f (x + t • v) - fderiv ℝ f x).le_opNorm v)
      have h2 : ‖fderiv ℝ f (x + t • v) - fderiv ℝ f x‖ ≤ β * ‖x + t • v - x‖ :=
        hsmooth _ hp _ hx
      have h3 : ‖x + t • v - x‖ = t * ‖v‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1.le]
      rw [h3] at h2
      have h4 : ‖fderiv ℝ f (x + t • v) - fderiv ℝ f x‖ * ‖v‖ ≤ β * (t * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      rw [ContinuousLinearMap.sub_apply] at h1
      nlinarith
  have := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  simp only [ψ] at this
  simp at this
  linarith

/-- First-order optimality condition on a convex set. -/
lemma smd_first_order {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} {h : E → ℝ} {h' : E →L[ℝ] ℝ} {a z : E} (hC : Convex ℝ C) (ha : a ∈ C)
    (hz : z ∈ C) (hmin : IsMinOn h C a) (hd : HasFDerivAt h h' a) : 0 ≤ h' (z - a) :=
  hmin.localize.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset (hC.segment_subset ha hz))

/-- Strong convexity gives a quadratic lower bound on the Bregman divergence. -/
lemma smd_bregman_ge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} {phi : E → ℝ} (hsc : StrongConvexOn C 1 phi) {x y : E} (hx : x ∈ C)
    (hy : y ∈ C) (hd : DifferentiableAt ℝ phi x) :
    1 / 2 * ‖y - x‖ ^ 2 ≤ bregmanDivergence phi y x := by
  unfold bregmanDivergence
  have hT := (hd.hasFDerivAt.hasLineDerivAt (y - x)).tendsto_slope_zero_right
  have hR : Filter.Tendsto (fun t : ℝ => phi y - phi x - (1 - t) * (1 / 2 * ‖y - x‖ ^ 2))
      (𝓝[>] 0) (𝓝 (phi y - phi x - (1 - 0) * (1 / 2 * ‖y - x‖ ^ 2))) := by
    apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
    exact ((continuous_const.sub ((continuous_const.sub continuous_id).mul
      continuous_const)).tendsto 0)
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), t⁻¹ • (phi (x + t • (y - x)) - phi x) ≤
      phi y - phi x - (1 - t) * (1 / 2 * ‖y - x‖ ^ 2) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have h := hsc.2 hx hy (show (0:ℝ) ≤ 1 - t by linarith) ht0.le (by ring)
    have heq : (1 - t) • x + t • y = x + t • (y - x) := by
      rw [sub_smul, one_smul, smul_sub]; abel
    rw [heq] at h
    simp only [smul_eq_mul] at h ⊢
    rw [norm_sub_rev] at h
    rw [inv_mul_le_iff₀ ht0]
    nlinarith
  have := le_of_tendsto_of_tendsto hT hR hev
  simp only [sub_zero, one_mul] at this
  linarith

/-- Integrability of the pairing of an integrable dual-valued map with a bounded map. -/
lemma smd_integrable_pairing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {G : Ω → E →L[ℝ] ℝ} (hG : Integrable G μ) {v : Ω → E} (hv : AEStronglyMeasurable v μ)
    {C : ℝ} (hC : ∀ ω, ‖v ω‖ ≤ C) :
    Integrable (fun ω => G ω (v ω)) μ := by
  exact (ContinuousLinearMap.apply ℝ ℝ : E →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ).integrable_of_bilin_of_bdd_left
    C hv (ae_of_all _ hC) hG

/-- Tower property for the pairing with a function of the conditioning variable. -/
lemma smd_condExp_pairing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : Ω → E) (hx : Measurable x) (g : Ω → E →L[ℝ] ℝ) (hg : Integrable g μ)
    {C : ℝ} (hC : ∀ ω, ‖x ω‖ ≤ C) (z : E) :
    ∫ ω, condExpGivenIterate μ x g ω (x ω - z) ∂μ = ∫ ω, g ω (x ω - z) ∂μ := by
  unfold condExpGivenIterate
  have hm : MeasurableSpace.comap x (inferInstance : MeasurableSpace E)
      ≤ (inferInstance : MeasurableSpace Ω) := hx.comap_le
  have hxm : Measurable[MeasurableSpace.comap x (inferInstance : MeasurableSpace E)]
      (fun ω => x ω - z) := (comap_measurable x).sub_const z
  have hxsm : StronglyMeasurable[MeasurableSpace.comap x (inferInstance : MeasurableSpace E)]
      (fun ω => x ω - z) := hxm.stronglyMeasurable
  have hbound : ∀ ω, ‖x ω - z‖ ≤ C + ‖z‖ := fun ω =>
    (norm_sub_le _ _).trans (by linarith [hC ω])
  have hint : Integrable (fun ω => g ω (x ω - z)) μ :=
    smd_integrable_pairing hg ((hxsm.mono hm).aestronglyMeasurable) hbound
  have hpull := condExp_bilin_of_aestronglyMeasurable_left
    (ContinuousLinearMap.apply ℝ ℝ : E →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ)
    (m := MeasurableSpace.comap x (inferInstance : MeasurableSpace E)) (μ := μ)
    hxsm.aestronglyMeasurable (g := g) hint hg
  calc ∫ ω, (μ[g | MeasurableSpace.comap x (inferInstance : MeasurableSpace E)]) ω (x ω - z) ∂μ
        = ∫ ω, (μ[fun ω => g ω (x ω - z) |
            MeasurableSpace.comap x (inferInstance : MeasurableSpace E)]) ω ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hpull] with ω hω
        simpa using hω.symm
    _ = ∫ ω, g ω (x ω - z) ∂μ := integral_condExp hm

/-- Passing from comparators in `X ∩ D` to the infimum over `X`. -/
lemma smd_inf_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X D : Set E} {f : E → ℝ} (hX : Convex ℝ X) (hXc : IsCompact X) (hD : Convex ℝ D)
    (hDo : IsOpen D) (hXD : X ⊆ closure D) (hne : (X ∩ D).Nonempty)
    (hcont : ∀ z ∈ X, ContinuousAt f z)
    {A B : ℝ} (h : ∀ z ∈ X ∩ D, A - f z ≤ B) : A - sInf (f '' X) ≤ B := by
  have hfc : ContinuousOn f X := fun z hz => (hcont z hz).continuousWithinAt
  have hK : IsCompact (f '' X) := hXc.image_of_continuousOn hfc
  have hXne : X.Nonempty := hne.mono Set.inter_subset_left
  obtain ⟨x, hx, hfx⟩ := hK.sInf_mem (hXne.image f)
  rw [← hfx]
  obtain ⟨y, hyX, hyD⟩ := hne
  have hpc : Continuous (fun t : ℝ => t • y + (1 - t) • x) := by
    fun_prop
  have hpt : Filter.Tendsto (fun t : ℝ => t • y + (1 - t) • x) (𝓝[>] (0:ℝ)) (𝓝 x) := by
    have h0 := hpc.tendsto 0
    simp only [zero_smul, sub_zero, one_smul, zero_add] at h0
    exact tendsto_nhdsWithin_of_tendsto_nhds h0
  have hft : Filter.Tendsto (fun t : ℝ => f (t • y + (1 - t) • x)) (𝓝[>] (0:ℝ)) (𝓝 (f x)) :=
    (hcont x hx).tendsto.comp hpt
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), A - B ≤ f (t • y + (1 - t) • x) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    have ht0 : 0 < t := ht.1
    have ht1 : t < 1 := ht.2
    have hpX : t • y + (1 - t) • x ∈ X := hX hyX hx ht0.le (by linarith) (by ring)
    have hpD : t • y + (1 - t) • x ∈ D := by
      have hyD' : y ∈ interior D := by rwa [hDo.interior_eq]
      have := hD.combo_interior_closure_mem_interior hyD' (hXD hx) ht0
        (by linarith : (0:ℝ) ≤ 1 - t) (by ring)
      rwa [hDo.interior_eq] at this
    have := h _ ⟨hpX, hpD⟩
    linarith
  have := ge_of_tendsto hft hev
  linarith

/-- One step of the stochastic mirror descent analysis (deterministic part). -/
lemma smd_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X D : Set E} {f phi : E → ℝ} {β c : ℝ} (hβ : 0 < β) (hc : 0 < c)
    (hX : Convex ℝ X) (hD : Convex ℝ D)
    (hphi_diff : ∀ y ∈ D, DifferentiableAt ℝ phi y)
    (hsc : StrongConvexOn (X ∩ D) 1 phi)
    (hf_smooth : IsSmoothOn X f β) (hf_diff : ∀ z ∈ X, DifferentiableAt ℝ f z)
    {x x' z : E} {G w : E →L[ℝ] ℝ}
    (hx : x ∈ X ∩ D) (hx' : x' ∈ X ∩ D) (hz : z ∈ X ∩ D)
    (hmin : IsMinOn (fun u => (1 / (β + c)) * G u + bregmanDivergence phi u x) (X ∩ D) x')
    (hw : IsSubgradientOn X f x w) :
    f x' - f z ≤ (β + c) * (bregmanDivergence phi z x - bregmanDivergence phi z x')
      + ‖fderiv ℝ f x - G‖ ^ 2 / (2 * c) + (w (x - z) - G (x - z)) := by
  obtain ⟨hxX, hxD⟩ := hx
  obtain ⟨hx'X, hx'D⟩ := hx'
  obtain ⟨hzX, hzD⟩ := hz
  have hγ : 0 < β + c := by linarith
  -- descent lemma
  have h1 := smd_descent hX hf_diff hf_smooth hxX hx'X
  -- subgradient inequality
  have h2 := hw z hzX
  -- first-order optimality of the mirror step
  have hd' : HasFDerivAt (fun u => (1 / (β + c)) * G u + bregmanDivergence phi u x)
      ((1 / (β + c)) • G + (fderiv ℝ phi x' - fderiv ℝ phi x)) x' := by
    have hA : HasFDerivAt (fun u => (1 / (β + c)) * G u) ((1 / (β + c)) • G) x' := by
      simpa [smul_eq_mul] using (G.hasFDerivAt (x := x')).const_smul (1 / (β + c))
    have hB : HasFDerivAt (fun u => bregmanDivergence phi u x)
        (fderiv ℝ phi x' - fderiv ℝ phi x) x' := by
      unfold bregmanDivergence
      have h1 : HasFDerivAt (fun u => fderiv ℝ phi x (u - x)) (fderiv ℝ phi x) x' := by
        have h2 := (fderiv ℝ phi x).hasFDerivAt.comp x' ((hasFDerivAt_id x').sub_const x)
        rw [ContinuousLinearMap.comp_id] at h2
        exact h2
      exact ((hphi_diff x' hx'D).hasFDerivAt.sub_const (phi x)).sub h1
    exact hA.add hB
  have h3 := smd_first_order (hX.inter hD) ⟨hx'X, hx'D⟩ ⟨hzX, hzD⟩ hmin hd'
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, smul_eq_mul] at h3
  have h3' : 0 ≤ G (z - x') + (β + c) * (fderiv ℝ phi x' (z - x') - fderiv ℝ phi x (z - x')) := by
    have := mul_nonneg hγ.le h3
    have e : (β + c) * (1 / (β + c) * G (z - x') +
        (fderiv ℝ phi x' (z - x') - fderiv ℝ phi x (z - x'))) =
        G (z - x') + (β + c) * (fderiv ℝ phi x' (z - x') - fderiv ℝ phi x (z - x')) := by
      field_simp
    linarith
  -- strong convexity
  have h4 := smd_bregman_ge hsc ⟨hxX, hxD⟩ ⟨hx'X, hx'D⟩ (hphi_diff x hxD)
  unfold bregmanDivergence at h4
  have P1 := mul_le_mul_of_nonneg_left h4 hγ.le
  -- Young's inequality
  have h5 : (fderiv ℝ f x - G) (x' - x) ≤ ‖fderiv ℝ f x - G‖ * ‖x' - x‖ := by
    have := (fderiv ℝ f x - G).le_opNorm (x' - x)
    rw [Real.norm_eq_abs] at this
    exact le_trans (le_abs_self _) this
  have hY : ‖fderiv ℝ f x - G‖ * ‖x' - x‖ ≤
      ‖fderiv ℝ f x - G‖ ^ 2 / (2 * c) + c / 2 * ‖x' - x‖ ^ 2 := by
    have h := sq_nonneg (‖fderiv ℝ f x - G‖ - c * ‖x' - x‖)
    have e : ‖fderiv ℝ f x - G‖ ^ 2 / (2 * c) + c / 2 * ‖x' - x‖ ^ 2
        - ‖fderiv ℝ f x - G‖ * ‖x' - x‖ = (‖fderiv ℝ f x - G‖ - c * ‖x' - x‖) ^ 2 / (2 * c) := by
      field_simp
      ring
    have : 0 ≤ (‖fderiv ℝ f x - G‖ - c * ‖x' - x‖) ^ 2 / (2 * c) := by positivity
    linarith
  -- linear identities
  have e1 : fderiv ℝ phi x (z - x) = fderiv ℝ phi x (z - x') + fderiv ℝ phi x (x' - x) := by
    rw [← map_add]; congr 1; abel
  have e2 : w (x - z) = - w (z - x) := by
    rw [← map_neg]; congr 1; abel
  have e3 : G (x' - x) = - G (z - x') - G (x - z) := by
    rw [← map_neg, ← map_sub]; congr 1; abel
  have e4 : (fderiv ℝ f x - G) (x' - x) = fderiv ℝ f x (x' - x) - G (x' - x) :=
    ContinuousLinearMap.sub_apply _ _ _
  unfold bregmanDivergence
  rw [e1]
  nlinarith [h1, h2, h3', P1, h5, hY, e2, e3, e4]


set_option linter.unusedVariables false in
theorem stochastic_mirror_descent_bound_smooth
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
  (σ β R : ℝ)
  (x0 : E)
  (hx0 : ∀ ω, x 0 ω = x0)
  (hR_sq : R ^ 2 = sSup {v | ∃ a ∈ 𝓧 ∩ 𝓓, phi a - phi x0 = v})
  (hσ_sq : ∀ s,
    ∫ ω, ‖fderiv ℝ f (x s ω) - g s ω‖ ^ (2 : ℕ) ∂μ ≤ σ ^ 2)
  (hσ_noise_int : ∀ s, Integrable
    (fun ω => ‖fderiv ℝ f (x s ω) - g s ω‖ ^ (2 : ℕ)) μ)
  (hR_pos : R > 0)
  (hβ_pos : β > 0)
  (hσ_pos : σ > 0)
  (ht : t > 0)
  (hf_ae_comp : ∀ s, AEMeasurable (fun ω => f (x s ω)) μ)
  (havg_succ_ae :
      AEMeasurable
        (fun ω => f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x (s + 1) ω)) μ)
  (h_mirror_seq :
    IsStochasticMirrorDescentSequence 𝓧 𝓓 phi x g
      (fun _ => 1 / (β + (σ / R) * Real.sqrt ((t : ℝ) / 2))))
  (h_stoch_oracle : ∀ s, IsStochasticSubgradientOracle μ 𝓧 f (x s) (g s))
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
  (hf_convex : ConvexOn ℝ 𝓧 f)
  (hf_smooth : IsSmoothOn 𝓧 f β)
  (hf_differentiable : ∀ z ∈ 𝓧, DifferentiableAt ℝ f z) :
  ∫ ω, f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x (s + 1) ω) ∂μ -
    sInf (f '' 𝓧) ≤
    R * σ * Real.sqrt (2 / (t : ℝ)) + (β * R ^ 2) / (t : ℝ) := by
  obtain ⟨hx_meas, hx0_mem, hx0_min, hx_mem, hx_step⟩ := h_mirror_seq
  set c : ℝ := σ / R * Real.sqrt ((t : ℝ) / 2) with hc_def
  have ht_pos : (0 : ℝ) < t := by exact_mod_cast ht
  have hsqrt_pos : 0 < Real.sqrt ((t : ℝ) / 2) := Real.sqrt_pos.mpr (by positivity)
  have hc_pos : 0 < c := by positivity
  have hγ : 0 < β + c := by linarith
  have hXD_convex : Convex ℝ (𝓧 ∩ 𝓓) := h𝓧_convex.inter h𝓓_convex
  have hphi_diff : ∀ y ∈ 𝓓, DifferentiableAt ℝ phi y := fun y hy =>
    (hphi_differentiable y hy).differentiableAt (h𝓓_open.mem_nhds hy)
  have hf_cont : ∀ z ∈ 𝓧, ContinuousAt f z := fun z hz => (hf_differentiable z hz).continuousAt
  obtain ⟨Cx, hCx⟩ : ∃ Cx, ∀ z ∈ 𝓧, ‖z‖ ≤ Cx := h𝓧_compact.isBounded.exists_norm_le
  obtain ⟨Cf, hCf⟩ : ∃ Cf, ∀ z ∈ 𝓧, ‖f z‖ ≤ Cf :=
    h𝓧_compact.exists_bound_of_continuousOn (fun z hz => (hf_cont z hz).continuousWithinAt)
  -- the bound `phi z - phi x0 ≤ R ^ 2`
  have hbdd : BddAbove {v | ∃ a ∈ 𝓧 ∩ 𝓓, phi a - phi x0 = v} := by
    by_contra hnb
    rw [Real.sSup_of_not_bddAbove hnb] at hR_sq
    have : 0 < R ^ 2 := by positivity
    linarith
  have hR_bound : ∀ z ∈ 𝓧 ∩ 𝓓, phi z - phi x0 ≤ R ^ 2 := by
    intro z hz
    rw [hR_sq]
    exact le_csSup hbdd ⟨z, hz, rfl⟩
  have hD0 : ∀ ω, ∀ z ∈ 𝓧 ∩ 𝓓, bregmanDivergence phi z (x 0 ω) ≤ R ^ 2 := by
    intro ω z hz
    have hmem := hx0_mem ω
    have hfo := smd_first_order hXD_convex hmem hz (hx0_min ω) (hphi_diff _ hmem.2).hasFDerivAt
    have := hR_bound z hz
    rw [hx0 ω] at hfo ⊢
    unfold bregmanDivergence
    linarith
  have hD_nonneg : ∀ y ∈ 𝓧 ∩ 𝓓, ∀ z ∈ 𝓧 ∩ 𝓓, 0 ≤ bregmanDivergence phi z y := by
    intro y hy z hz
    have := smd_bregman_ge hphi_strong_convex hy hz (hphi_diff y hy.2)
    have : 0 ≤ 1 / 2 * ‖z - y‖ ^ 2 := by positivity
    linarith
  -- the average lies in `𝓧`
  have havg_mem : ∀ ω, (1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x (s + 1) ω ∈ 𝓧 := by
    intro ω
    rw [Finset.smul_sum]
    apply h𝓧_convex.sum_mem (fun _ _ => by positivity)
    · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    · exact fun s _ => (hx_mem (s + 1) ω).1
  have hint_avg : Integrable
      (fun ω => f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x (s + 1) ω)) μ :=
    Integrable.of_bound havg_succ_ae.aestronglyMeasurable Cf
      (ae_of_all _ (fun ω => hCf _ (havg_mem ω)))
  have key : ∀ z ∈ 𝓧 ∩ 𝓓,
      ∫ ω, f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x (s + 1) ω) ∂μ - f z ≤
      R * σ * Real.sqrt (2 / (t : ℝ)) + (β * R ^ 2) / (t : ℝ) := by
    intro z hz
    set w : ℕ → Ω → E →L[ℝ] ℝ := fun s => condExpGivenIterate μ (x s) (g s) with hw_def
    set N : ℕ → Ω → ℝ := fun s ω => ‖fderiv ℝ f (x s ω) - g s ω‖ ^ 2 with hN_def
    set M : ℕ → Ω → ℝ := fun s ω => w s ω (x s ω - z) - g s ω (x s ω - z) with hM_def
    have hsub : ∀ᵐ ω ∂μ, ∀ s, IsSubgradientOn 𝓧 f (x s ω) (w s ω) := by
      rw [ae_all_iff]; intro s; exact (h_stoch_oracle s).2
    -- pointwise bound
    have hpt : ∀ᵐ ω ∂μ, f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x (s + 1) ω) - f z ≤
        (1 / (t : ℝ)) * ((β + c) * R ^ 2 +
          ∑ s ∈ Finset.range t, (N s ω / (2 * c) + M s ω)) := by
      filter_upwards [hsub] with ω hω
      have hstep : ∀ s, f (x (s + 1) ω) - f z ≤
          (β + c) * (bregmanDivergence phi z (x s ω) - bregmanDivergence phi z (x (s + 1) ω))
          + (N s ω / (2 * c) + M s ω) := by
        intro s
        have := smd_step hβ_pos hc_pos h𝓧_convex h𝓓_convex hphi_diff hphi_strong_convex
          hf_smooth hf_differentiable (hx_mem s ω) (hx_mem (s + 1) ω) hz (hx_step s ω) (hω s)
        simp only [hN_def, hM_def]
        linarith
      have hsum := Finset.sum_le_sum (fun s (_ : s ∈ Finset.range t) => hstep s)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_range_sub' (fun s => bregmanDivergence phi z (x s ω)),
        Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
      have hjensen : f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x (s + 1) ω) ≤
          (1 / (t : ℝ)) * ∑ s ∈ Finset.range t, f (x (s + 1) ω) := by
        rw [Finset.smul_sum, Finset.mul_sum]
        have := hf_convex.map_sum_le (t := Finset.range t) (w := fun _ => 1 / (t : ℝ))
          (p := fun s => x (s + 1) ω) (fun _ _ => by positivity)
          (by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp)
          (fun s _ => (hx_mem (s + 1) ω).1)
        simpa [smul_eq_mul] using this
      have hD0' := hD0 ω z hz
      have hDt := hD_nonneg (x t ω) (hx_mem t ω) z hz
      have hA : ∑ s ∈ Finset.range t, f (x (s + 1) ω) - (t : ℝ) * f z ≤
          (β + c) * R ^ 2 + ∑ s ∈ Finset.range t, (N s ω / (2 * c) + M s ω) := by
        have : (β + c) * (bregmanDivergence phi z (x 0 ω) - bregmanDivergence phi z (x t ω))
            ≤ (β + c) * R ^ 2 := mul_le_mul_of_nonneg_left (by linarith) hγ.le
        linarith
      calc f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x (s + 1) ω) - f z
          ≤ (1 / (t : ℝ)) * ∑ s ∈ Finset.range t, f (x (s + 1) ω) - f z := by linarith
        _ = (1 / (t : ℝ)) * (∑ s ∈ Finset.range t, f (x (s + 1) ω) - (t : ℝ) * f z) := by
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hA (by positivity)
    -- integrability
    have hNint : ∀ s, Integrable (N s) μ := fun s => hσ_noise_int s
    have hbound_v : ∀ s ω, ‖x s ω - z‖ ≤ Cx + ‖z‖ := fun s ω =>
      (norm_sub_le _ _).trans (by linarith [hCx _ (hx_mem s ω).1])
    have hv_meas : ∀ s, AEStronglyMeasurable (fun ω => x s ω - z) μ := fun s =>
      ((hx_meas s).sub_const z).aestronglyMeasurable
    have hW1 : ∀ s, Integrable (fun ω => condExpGivenIterate μ (x s) (g s) ω (x s ω - z)) μ :=
      fun s => smd_integrable_pairing integrable_condExp (hv_meas s) (hbound_v s)
    have hW2 : ∀ s, Integrable (fun ω => g s ω (x s ω - z)) μ :=
      fun s => smd_integrable_pairing (h_stoch_oracle s).1 (hv_meas s) (hbound_v s)
    have hMint : ∀ s, Integrable (M s) μ := fun s => (hW1 s).sub (hW2 s)
    have hM0 : ∀ s, ∫ ω, M s ω ∂μ = 0 := by
      intro s
      have hC' : ∀ ω, ‖x s ω‖ ≤ Cx := fun ω => hCx _ (hx_mem s ω).1
      have hpair := smd_condExp_pairing μ (x s) (hx_meas s) (g s) (h_stoch_oracle s).1 hC' z
      show ∫ ω, (condExpGivenIterate μ (x s) (g s) ω (x s ω - z) - g s ω (x s ω - z)) ∂μ = 0
      rw [integral_sub (hW1 s) (hW2 s), hpair, sub_self]
    have hFint : Integrable (fun ω => (1 / (t : ℝ)) * ((β + c) * R ^ 2 +
          ∑ s ∈ Finset.range t, (N s ω / (2 * c) + M s ω))) μ := by
      apply Integrable.const_mul
      apply (integrable_const _).add
      apply integrable_finset_sum
      intro s _
      exact ((hNint s).div_const _).add (hMint s)
    have hFeq : ∫ ω, (1 / (t : ℝ)) * ((β + c) * R ^ 2 +
          ∑ s ∈ Finset.range t, (N s ω / (2 * c) + M s ω)) ∂μ =
        (1 / (t : ℝ)) * ((β + c) * R ^ 2 +
          ∑ s ∈ Finset.range t, ((∫ ω, N s ω ∂μ) / (2 * c) + ∫ ω, M s ω ∂μ)) := by
      rw [integral_const_mul, integral_add (integrable_const _), integral_const,
        integral_finset_sum]
      · congr 2
        · simp
        · apply Finset.sum_congr rfl
          intro s _
          rw [integral_add ((hNint s).div_const _) (hMint s), integral_div]
      · intro s _; exact ((hNint s).div_const _).add (hMint s)
      · exact integrable_finset_sum _ (fun s _ => ((hNint s).div_const _).add (hMint s))
    have hsumN : ∑ s ∈ Finset.range t, ((∫ ω, N s ω ∂μ) / (2 * c) + ∫ ω, M s ω ∂μ) ≤
        (t : ℝ) * (σ ^ 2 / (2 * c)) := by
      calc ∑ s ∈ Finset.range t, ((∫ ω, N s ω ∂μ) / (2 * c) + ∫ ω, M s ω ∂μ)
          ≤ ∑ s ∈ Finset.range t, (σ ^ 2 / (2 * c)) := by
            apply Finset.sum_le_sum
            intro s _
            rw [hM0 s, add_zero]
            have := hσ_sq s
            gcongr
        _ = (t : ℝ) * (σ ^ 2 / (2 * c)) := by simp
    have hfinal : (1 / (t : ℝ)) * ((β + c) * R ^ 2 + (t : ℝ) * (σ ^ 2 / (2 * c))) =
        R * σ * Real.sqrt (2 / (t : ℝ)) + (β * R ^ 2) / (t : ℝ) := by
      have ha2 : Real.sqrt ((t : ℝ) / 2) ^ 2 = (t : ℝ) / 2 := Real.sq_sqrt (by positivity)
      have hb : Real.sqrt (2 / (t : ℝ)) = 1 / Real.sqrt ((t : ℝ) / 2) := by
        rw [show (2 : ℝ) / t = ((t : ℝ) / 2)⁻¹ by rw [inv_div], Real.sqrt_inv, one_div]
      rw [hb, hc_def]
      set a := Real.sqrt ((t : ℝ) / 2) with ha_def
      have ht2 : (t : ℝ) = 2 * a ^ 2 := by linarith
      have ha_ne : a ≠ 0 := ne_of_gt hsqrt_pos
      have hR_ne : R ≠ 0 := ne_of_gt hR_pos
      have hσ_ne : σ ≠ 0 := ne_of_gt hσ_pos
      rw [ht2]
      field_simp
      ring
    calc ∫ ω, f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x (s + 1) ω) ∂μ - f z
        = ∫ ω, (f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x (s + 1) ω) - f z) ∂μ := by
          rw [integral_sub hint_avg (integrable_const _)]; simp
      _ ≤ ∫ ω, (1 / (t : ℝ)) * ((β + c) * R ^ 2 +
          ∑ s ∈ Finset.range t, (N s ω / (2 * c) + M s ω)) ∂μ :=
          integral_mono_ae (hint_avg.sub (integrable_const _)) hFint hpt
      _ = _ := hFeq
      _ ≤ (1 / (t : ℝ)) * ((β + c) * R ^ 2 + (t : ℝ) * (σ ^ 2 / (2 * c))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      _ = _ := hfinal
  exact smd_inf_step h𝓧_convex h𝓧_compact h𝓓_convex h𝓓_open h𝓓_contains h_inter_nonempty
    hf_cont key

end stochastic_mirror_descent_bound_smooth
