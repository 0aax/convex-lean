import ConvexStarLib.Defs

/-!
# `RW_chap_8_21`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_8_21` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_8_21`, so the main result is `RW_chap_8_21.RW_chap_8_21`.
-/

namespace RW_chap_8_21

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section RW_8_21_aux

open Filter Set

lemma RW_8_21_effDom_convex {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : F → EReal) (hf : ConvexEReal f) (hbot : ∀ x, ⊥ < f x) : Convex ℝ (effDom f) := by
  intro x hx y hy a b ha hb hab
  have h1 : ((x, (f x).toReal) : F × ℝ) ∈ epigraph f := by
    show f x ≤ ((f x).toReal : EReal)
    rw [EReal.coe_toReal (ne_of_lt hx) (hbot x).ne']
  have h2 : ((y, (f y).toReal) : F × ℝ) ∈ epigraph f := by
    show f y ≤ ((f y).toReal : EReal)
    rw [EReal.coe_toReal (ne_of_lt hy) (hbot y).ne']
  have h3 := hf h1 h2 ha hb hab
  have h4 : f (a • x + b • y) ≤ ((a * (f x).toReal + b * (f y).toReal : ℝ) : EReal) := by
    simpa [epigraph] using h3
  exact lt_of_le_of_lt h4 (EReal.coe_lt_top _)

lemma RW_8_21_toReal_convexOn {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : F → EReal) (hf : ConvexEReal f) (hbot : ∀ x, ⊥ < f x) :
    ConvexOn ℝ (effDom f) (fun x => (f x).toReal) := by
  refine ⟨RW_8_21_effDom_convex f hf hbot, ?_⟩
  intro x hx y hy a b ha hb hab
  have h1 : ((x, (f x).toReal) : F × ℝ) ∈ epigraph f := by
    show f x ≤ ((f x).toReal : EReal)
    rw [EReal.coe_toReal (ne_of_lt hx) (hbot x).ne']
  have h2 : ((y, (f y).toReal) : F × ℝ) ∈ epigraph f := by
    show f y ≤ ((f y).toReal : EReal)
    rw [EReal.coe_toReal (ne_of_lt hy) (hbot y).ne']
  have h3 := hf h1 h2 ha hb hab
  have h4 : f (a • x + b • y) ≤ ((a * (f x).toReal + b * (f y).toReal : ℝ) : EReal) := by
    simpa [epigraph] using h3
  have hmem : a • x + b • y ∈ effDom f := RW_8_21_effDom_convex f hf hbot hx hy ha hb hab
  simp only [smul_eq_mul]
  rw [← EReal.coe_le_coe_iff, EReal.coe_toReal (ne_of_lt hmem) (hbot _).ne']
  exact h4

lemma RW_8_21_slope_mono {F : Type*} [AddCommGroup F] [Module ℝ F] {C : Set F} {g : F → ℝ}
    (hg : ConvexOn ℝ C g) {x w : F} {s t : ℝ} (hx : x ∈ C) (ht : x + t • w ∈ C)
    (hs : 0 < s) (hst : s ≤ t) :
    (g (x + s • w) - g x) / s ≤ (g (x + t • w) - g x) / t := by
  have htpos : 0 < t := lt_of_lt_of_le hs hst
  have hst' : s / t ≤ 1 := (div_le_one htpos).2 hst
  have key := hg.2 hx ht (sub_nonneg.2 hst') (div_nonneg hs.le htpos.le) (by ring)
  have heq : (1 - s / t) • x + (s / t) • (x + t • w) = x + s • w := by
    have h1 : (1 - s / t) • x + (s / t) • (x + t • w) = x + (s / t * t) • w := by module
    rw [h1, div_mul_cancel₀ _ htpos.ne']
  rw [heq, smul_eq_mul, smul_eq_mul] at key
  rw [div_le_div_iff₀ hs htpos]
  have h1 : g (x + s • w) - g x ≤ s / t * (g (x + t • w) - g x) := by linarith
  have h2 : s / t * (g (x + t • w) - g x) * t = (g (x + t • w) - g x) * s := by
    field_simp
  calc (g (x + s • w) - g x) * t ≤ s / t * (g (x + t • w) - g x) * t :=
        mul_le_mul_of_nonneg_right h1 htpos.le
    _ = (g (x + t • w) - g x) * s := h2

lemma RW_8_21_slope_back {F : Type*} [AddCommGroup F] [Module ℝ F] {C : Set F} {g : F → ℝ}
    (hg : ConvexOn ℝ C g) {x w : F} {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (h1 : x + (-t) • w ∈ C) (h2 : x + s • w ∈ C) :
    (g x - g (x + (-t) • w)) / t ≤ (g (x + s • w) - g x) / s := by
  have hst : 0 < s + t := add_pos hs ht
  have hab : s / (s + t) + t / (s + t) = 1 := by field_simp
  have key := hg.2 h1 h2 (div_nonneg hs.le hst.le) (div_nonneg ht.le hst.le) hab
  have heq : (s / (s + t)) • (x + (-t) • w) + (t / (s + t)) • (x + s • w) = x := by
    have e1 : (s / (s + t)) • (x + (-t) • w) + (t / (s + t)) • (x + s • w)
        = (s / (s + t) + t / (s + t)) • x + (s / (s + t) * -t + t / (s + t) * s) • w := by module
    have e2 : s / (s + t) * -t + t / (s + t) * s = 0 := by ring
    rw [e1, e2, hab, one_smul, zero_smul, add_zero]
  rw [heq, smul_eq_mul, smul_eq_mul] at key
  rw [div_le_div_iff₀ ht hs]
  have h3 : (s + t) * g x ≤ s * g (x + (-t) • w) + t * g (x + s • w) := by
    have := mul_le_mul_of_nonneg_left key hst.le
    calc (s + t) * g x ≤ (s + t) * (s / (s + t) * g (x + (-t) • w) + t / (s + t) * g (x + s • w)) :=
          this
      _ = s * g (x + (-t) • w) + t * g (x + s • w) := by field_simp
  linarith

lemma RW_8_21_exists_tendsto {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {C : Set F}
    {g : F → ℝ} (hg : ConvexOn ℝ C g) {x : F} (hx : x ∈ interior C) (w : F) :
    ∃ L, Tendsto (fun τ : ℝ => (g (x + τ • w) - g x) / τ) (𝓝[>] 0) (𝓝 L) := by
  have hcont : Tendsto (fun τ : ℝ => x + τ • w) (𝓝 0) (𝓝 x) := by
    have := ((continuous_const.add (continuous_id.smul continuous_const)) :
      Continuous (fun τ : ℝ => x + τ • w)).tendsto 0
    simpa using this
  have hev : ∀ᶠ τ in 𝓝 (0:ℝ), x + τ • w ∈ C :=
    hcont.eventually (mem_interior_iff_mem_nhds.1 hx)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hxC : x ∈ C := interior_subset hx
  have hmemC : ∀ τ : ℝ, |τ| < ε → x + τ • w ∈ C := by
    intro τ hτ
    apply hball
    rw [Real.dist_eq, sub_zero]
    exact hτ
  refine ⟨_, MonotoneOn.tendsto_nhdsWithin_Ioo_right (y := ε) ?_ ?_ ?_⟩
  · exact ⟨ε / 2, by linarith, by linarith⟩
  · intro s hs t ht hst
    exact RW_8_21_slope_mono hg hxC (hmemC t (by rw [abs_of_pos ht.1]; exact ht.2)) hs.1 hst
  · refine ⟨(g x - g (x + (-(ε / 2)) • w)) / (ε / 2), ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    refine RW_8_21_slope_back hg hs.1 (by linarith) (hmemC _ ?_) (hmemC _ ?_)
    · rw [abs_neg, abs_of_pos (by linarith)]; linarith
    · rw [abs_of_pos hs.1]; exact hs.2

end RW_8_21_aux

set_option linter.unusedVariables false in
theorem RW_chap_8_21
  (f : E → EReal)
  (x_bar : E)
  (hf_convex : ConvexEReal f)
  (hf_ne_bot : ∀ x, ⊥ < f x)
  (hx_bar : ⊥ < f x_bar ∧ f x_bar < ⊤)
  (hx_bar_dom : x_bar ∈ interior (effDom f)) :
  let W := {w | ∃ (τ : ℝ), 0 < τ ∧ x_bar + τ • w ∈ interior (effDom f)}
  ∃ (h : E → EReal),
    (IsSublinearRW h) ∧
    (∀ (w : E),
        Filter.Tendsto
        (fun (τ : ℝ) => (f (x_bar + τ • w) - f x_bar) / (τ : EReal))
        (𝓝[>] 0)
        (𝓝 (h w))) ∧
    (∀ (w : E), ∀ (τ : ℝ), 0 ≤ τ →
      f x_bar + (τ : EReal) * h w ≤ f (x_bar + τ • w)) ∧
    (∀ (w : E),
      regularSubderivative f x_bar w = subderivative f x_bar w ∧
      subderivative f x_bar w = Filter.liminf h (𝓝 w)) ∧
    (∀ (w : E), w ∈ W →
      Filter.liminf h (𝓝 w) = h w) ∧
    (W = interior (effDom (regularSubderivative f x_bar)) ∧
      W = interior (effDom (subderivative f x_bar)) ∧
      W = interior (effDom h)) := by
  intro W
  set D := effDom f with hD_def
  set g : E → ℝ := fun x => (f x).toReal with hg_def
  have hDconv : Convex ℝ D := RW_8_21_effDom_convex f hf_convex hf_ne_bot
  have hgconv : ConvexOn ℝ D g := RW_8_21_toReal_convexOn f hf_convex hf_ne_bot
  have hfg : ∀ x ∈ D, f x = (g x : EReal) := fun x hx =>
    (EReal.coe_toReal (ne_of_lt hx) (hf_ne_bot x).ne').symm
  have hxD : x_bar ∈ D := interior_subset hx_bar_dom
  have hgcont : ∀ x ∈ interior D, ContinuousAt g x := fun x hx =>
    hgconv.continuousOn_interior.continuousAt (isOpen_interior.mem_nhds hx)
  -- points along rays from `x_bar`
  have hray : ∀ w : E, ∀ᶠ τ in 𝓝 (0:ℝ), x_bar + τ • w ∈ interior D := by
    intro w
    have : Filter.Tendsto (fun τ : ℝ => x_bar + τ • w) (𝓝 0) (𝓝 x_bar) := by
      have := ((continuous_const.add (continuous_id.smul continuous_const)) :
        Continuous (fun τ : ℝ => x_bar + τ • w)).tendsto 0
      simpa using this
    exact this.eventually (isOpen_interior.mem_nhds hx_bar_dom)
  have hray' : ∀ w : E, ∀ᶠ τ in 𝓝[>] (0:ℝ), 0 < τ ∧ x_bar + τ • w ∈ interior D := fun w =>
    (eventually_mem_nhdsWithin).and (nhdsWithin_le_nhds (hray w))
  -- joint continuity near `(0, w)`
  have hcp : ∀ w : E, Filter.Tendsto (fun p : ℝ × E => x_bar + p.1 • p.2) (𝓝[>] 0 ×ˢ 𝓝 w) (𝓝 x_bar) := by
    intro w
    have : Filter.Tendsto (fun p : ℝ × E => x_bar + p.1 • p.2) (𝓝 ((0:ℝ), w)) (𝓝 (x_bar + (0:ℝ) • w)) :=
      (continuous_const.add (continuous_fst.smul continuous_snd)).tendsto _
    rw [zero_smul, add_zero, nhds_prod_eq] at this
    exact this.mono_left (Filter.prod_mono nhdsWithin_le_nhds le_rfl)
  -- the directional derivative
  set q : E → ℝ → ℝ := fun w τ => (g (x_bar + τ • w) - g x_bar) / τ with hq_def
  have hex : ∀ w, ∃ L, Filter.Tendsto (q w) (𝓝[>] 0) (𝓝 L) := fun w =>
    RW_8_21_exists_tendsto hgconv hx_bar_dom w
  set hr : E → ℝ := fun w => limUnder (𝓝[>] (0:ℝ)) (q w) with hhr_def
  have hr_tendsto : ∀ w, Filter.Tendsto (q w) (𝓝[>] 0) (𝓝 (hr w)) := fun w =>
    tendsto_nhds_limUnder (hex w)
  have hr_le : ∀ w τ, 0 < τ → x_bar + τ • w ∈ D → hr w ≤ q w τ := by
    intro w τ hτ hmem
    refine le_of_tendsto (hr_tendsto w) ?_
    filter_upwards [Ioo_mem_nhdsGT hτ] with s hs
    exact RW_8_21_slope_mono hgconv hxD hmem hs.1 hs.2.le
  have hr_smul : ∀ w (t : ℝ), 0 < t → hr (t • w) = t * hr w := by
    intro w t ht
    have h1 : Filter.Tendsto (fun τ : ℝ => τ * t) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Filter.Tendsto (fun τ : ℝ => τ * t) (𝓝 0) (𝓝 (0 * t)) :=
          (continuous_id.mul continuous_const).tendsto 0
        rw [zero_mul] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [eventually_mem_nhdsWithin] with τ hτ
        exact mul_pos hτ ht
    have h2 : Filter.Tendsto (fun τ => t * q w (τ * t)) (𝓝[>] 0) (𝓝 (t * hr w)) :=
      ((hr_tendsto w).comp h1).const_mul t
    have h3 : (fun τ => t * q w (τ * t)) = q (t • w) := by
      funext τ
      simp only [hq_def, smul_smul]
      rcases eq_or_ne τ 0 with rfl | hτ
      · simp
      · field_simp
    rw [h3] at h2
    exact tendsto_nhds_unique (hr_tendsto (t • w)) h2
  have hr_convex : ConvexOn ℝ Set.univ hr := by
    refine ⟨convex_univ, ?_⟩
    intro w1 _ w2 _ a b ha hb hab
    simp only [smul_eq_mul]
    have hA := hr_tendsto (a • w1 + b • w2)
    have hB : Filter.Tendsto (fun τ => a * q w1 τ + b * q w2 τ) (𝓝[>] 0)
        (𝓝 (a * hr w1 + b * hr w2)) :=
      ((hr_tendsto w1).const_mul a).add ((hr_tendsto w2).const_mul b)
    refine le_of_tendsto_of_tendsto hA hB ?_
    filter_upwards [hray' w1, hray' w2] with τ h1 h2
    have m1 : x_bar + τ • w1 ∈ D := interior_subset h1.2
    have m2 : x_bar + τ • w2 ∈ D := interior_subset h2.2
    have key := hgconv.2 m1 m2 ha hb hab
    have heq : a • (x_bar + τ • w1) + b • (x_bar + τ • w2) = x_bar + τ • (a • w1 + b • w2) := by
      calc a • (x_bar + τ • w1) + b • (x_bar + τ • w2)
          = (a + b) • x_bar + τ • (a • w1 + b • w2) := by module
        _ = _ := by rw [hab, one_smul]
    rw [heq, smul_eq_mul, smul_eq_mul] at key
    show (g (x_bar + τ • (a • w1 + b • w2)) - g x_bar) / τ ≤
      a * ((g (x_bar + τ • w1) - g x_bar) / τ) + b * ((g (x_bar + τ • w2) - g x_bar) / τ)
    have hb' : b = 1 - a := by linarith
    subst hb'
    calc (g (x_bar + τ • (a • w1 + (1 - a) • w2)) - g x_bar) / τ
        ≤ (a * g (x_bar + τ • w1) + (1 - a) * g (x_bar + τ • w2) - g x_bar) / τ :=
          div_le_div_of_nonneg_right (by linarith) h1.1.le
      _ = a * ((g (x_bar + τ • w1) - g x_bar) / τ) +
          (1 - a) * ((g (x_bar + τ • w2) - g x_bar) / τ) := by ring
  have hr_cont : Continuous hr := hr_convex.locallyLipschitz.continuous
  -- EReal-level consequences
  have hq_ge : ∀ w (τ : ℝ), 0 < τ →
      ((hr w : ℝ) : EReal) ≤ (f (x_bar + τ • w) - f x_bar) / (τ : EReal) := by
    intro w τ hτ
    by_cases hmem : x_bar + τ • w ∈ D
    · rw [hfg _ hmem, hfg _ hxD, ← EReal.coe_sub, ← EReal.coe_div, EReal.coe_le_coe_iff]
      exact hr_le w τ hτ hmem
    · have htop : f (x_bar + τ • w) = ⊤ := not_lt_top_iff.1 hmem
      rw [htop, hfg _ hxD, EReal.top_sub_coe,
        EReal.top_div_of_pos_ne_top (EReal.coe_pos.2 hτ) (EReal.coe_ne_top τ)]
      exact le_top
  have hM2 : ∀ w, Filter.Tendsto (fun τ : ℝ => (f (x_bar + τ • w) - f x_bar) / (τ : EReal)) (𝓝[>] 0)
      (𝓝 ((hr w : ℝ) : EReal)) := by
    intro w
    have h1 : Filter.Tendsto (fun τ => ((q w τ : ℝ) : EReal)) (𝓝[>] 0) (𝓝 ((hr w : ℝ) : EReal)) :=
      (continuous_coe_real_ereal.tendsto _).comp (hr_tendsto w)
    refine h1.congr' ?_
    filter_upwards [hray' w] with τ hτ
    rw [hfg _ (interior_subset hτ.2), hfg _ hxD, ← EReal.coe_sub, ← EReal.coe_div]
  have hM3 : ∀ w (τ : ℝ), 0 ≤ τ →
      f x_bar + (τ : EReal) * ((hr w : ℝ) : EReal) ≤ f (x_bar + τ • w) := by
    intro w τ hτ
    rcases hτ.eq_or_lt with rfl | hτpos
    · simp
    · by_cases hmem : x_bar + τ • w ∈ D
      · rw [hfg _ hmem, hfg _ hxD, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
        have := hr_le w τ hτpos hmem
        rw [le_div_iff₀ hτpos] at this
        show g x_bar + τ * hr w ≤ g (x_bar + τ • w)
        linarith
      · have htop : f (x_bar + τ • w) = ⊤ := not_lt_top_iff.1 hmem
        rw [htop]
        exact le_top
  have hliminf : ∀ w, Filter.liminf (fun w => ((hr w : ℝ) : EReal)) (𝓝 w) = ((hr w : ℝ) : EReal) :=
    fun w => ((continuous_coe_real_ereal.comp hr_cont).tendsto w).liminf_eq
  -- the subderivative
  have hsub : ∀ w, subderivative f x_bar w = ((hr w : ℝ) : EReal) := by
    intro w
    have hT : Filter.Tendsto (fun p : ℝ × E => q p.2 p.1) (𝓝[>] 0 ×ˢ 𝓝 w) (𝓝 (hr w)) := by
      refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
      · have e1 : ∀ᶠ w' in 𝓝 w, a < hr w' := (hr_cont.tendsto w).eventually_const_lt ha
        have e2 : ∀ᶠ p : ℝ × E in 𝓝[>] 0 ×ˢ 𝓝 w, x_bar + p.1 • p.2 ∈ interior D :=
          (hcp w).eventually (isOpen_interior.mem_nhds hx_bar_dom)
        have e3 : ∀ᶠ τ in 𝓝[>] (0:ℝ), 0 < τ := eventually_mem_nhdsWithin
        filter_upwards [e3.prod_mk e1, e2] with p hp1 hp2
        exact lt_of_lt_of_le hp1.2 (hr_le p.2 p.1 hp1.1 (interior_subset hp2))
      · obtain ⟨τ0, hτ0q, hτ0pos, hτ0D⟩ : ∃ τ0, q w τ0 < a ∧ 0 < τ0 ∧ x_bar + τ0 • w ∈ interior D :=
          (((hr_tendsto w).eventually_lt_const ha).and (hray' w)).exists.imp
            fun τ h => ⟨h.1, h.2.1, h.2.2⟩
        have hcw : ContinuousAt (fun w' : E => x_bar + τ0 • w') w :=
          (continuous_const.add (continuous_const.smul continuous_id)).continuousAt
        have hc : ContinuousAt (fun w' => q w' τ0) w := by
          show ContinuousAt (fun w' => (g (x_bar + τ0 • w') - g x_bar) / τ0) w
          exact ((ContinuousAt.comp_of_eq (hgcont _ hτ0D) hcw rfl).sub continuousAt_const).div_const τ0
        have e1 : ∀ᶠ w' in 𝓝 w, q w' τ0 < a := hc.tendsto.eventually_lt_const hτ0q
        have e2 : ∀ᶠ w' in 𝓝 w, x_bar + τ0 • w' ∈ D :=
          (hcw.tendsto.eventually (isOpen_interior.mem_nhds hτ0D)).mono fun _ h => interior_subset h
        have e3 : ∀ᶠ τ in 𝓝[>] (0:ℝ), τ ∈ Set.Ioo 0 τ0 := Ioo_mem_nhdsGT hτ0pos
        filter_upwards [e3.prod_mk (e1.and e2)] with p hp
        exact lt_of_le_of_lt (RW_8_21_slope_mono hgconv hxD hp.2.2 hp.1.1 hp.1.2.le) hp.2.1
    have hT' : Filter.Tendsto (fun p : ℝ × E => differenceQuotient f x_bar p.2 p.1) (𝓝[>] 0 ×ˢ 𝓝 w)
        (𝓝 ((hr w : ℝ) : EReal)) := by
      refine ((continuous_coe_real_ereal.tendsto _).comp hT).congr' ?_
      filter_upwards [(hcp w).eventually (isOpen_interior.mem_nhds hx_bar_dom)] with p hp
      simp only [Function.comp, differenceQuotient]
      rw [hfg _ (interior_subset hp), hfg _ hxD, ← EReal.coe_sub, ← EReal.coe_div]
    exact hT'.liminf_eq
  -- the regular subderivative
  have hreg : ∀ w, regularSubderivative f x_bar w = ((hr w : ℝ) : EReal) := by
    intro w
    unfold regularSubderivative
    apply le_antisymm
    · refine Filter.limsup_le_of_le (h := ?_)
      filter_upwards [eventually_mem_nhdsWithin] with δ hδ
      refine EReal.le_of_forall_lt_iff_le.1 (fun z hz => ?_)
      have hz' : hr w < z := EReal.coe_lt_coe_iff.1 hz
      refine Filter.limsup_le_of_le (h := ?_)
      obtain ⟨τ0, hτ0q, hτ0pos, hτ0D⟩ : ∃ τ0, q w τ0 < z ∧ 0 < τ0 ∧ x_bar + τ0 • w ∈ interior D :=
        (((hr_tendsto w).eventually_lt_const hz').and (hray' w)).exists.imp
          fun τ h => ⟨h.1, h.2.1, h.2.2⟩
      have hcx : ContinuousAt (fun x : E => x + τ0 • w) x_bar :=
        (continuous_id.add continuous_const).continuousAt
      have hc : ContinuousAt (fun x => (g (x + τ0 • w) - g x) / τ0) x_bar :=
        ((ContinuousAt.comp_of_eq (hgcont _ hτ0D) hcx rfl).sub (hgcont _ hx_bar_dom)).div_const τ0
      have e1 : ∀ᶠ x in 𝓝 x_bar, (g (x + τ0 • w) - g x) / τ0 < z :=
        hc.tendsto.eventually_lt_const hτ0q
      have e2 : ∀ᶠ x in 𝓝 x_bar, x ∈ D :=
        Filter.mem_of_superset (isOpen_interior.mem_nhds hx_bar_dom) interior_subset
      have e3 : ∀ᶠ x in 𝓝 x_bar, x + τ0 • w ∈ D :=
        (hcx.tendsto.eventually (isOpen_interior.mem_nhds hτ0D)).mono fun _ h => interior_subset h
      have e4 : ∀ᶠ τ in 𝓝[>] (0:ℝ), τ ∈ Set.Ioo 0 τ0 := Ioo_mem_nhdsGT hτ0pos
      have hle : fApproach f x_bar ×ˢ 𝓝[>] (0:ℝ) ≤ 𝓝 x_bar ×ˢ 𝓝[>] 0 :=
        Filter.prod_mono inf_le_left le_rfl
      filter_upwards [hle ((e1.and (e2.and e3)).prod_mk e4)] with p hp
      obtain ⟨⟨hq1, hxD', hxtD⟩, hτ⟩ := hp
      refine le_trans (sInf_le (Set.mem_image_of_mem _ (Metric.mem_closedBall_self (le_of_lt hδ)))) ?_
      have hmem : p.1 + p.2 • w ∈ D := by
        have := hDconv.add_smul_mem hxD' (y := τ0 • w) hxtD
          ⟨div_nonneg hτ.1.le hτ0pos.le, (div_le_one hτ0pos).2 hτ.2.le⟩
        rwa [smul_smul, div_mul_cancel₀ _ hτ0pos.ne'] at this
      show (f (p.1 + p.2 • w) - f p.1) / ((p.2 : ℝ) : EReal) ≤ z
      rw [hfg _ hmem, hfg _ hxD', ← EReal.coe_sub, ← EReal.coe_div, EReal.coe_le_coe_iff]
      exact le_trans (RW_8_21_slope_mono hgconv hxD' hxtD hτ.1 hτ.2.le) hq1.le
    · refine EReal.ge_of_forall_gt_iff_ge.1 (fun z hz => ?_)
      have hz' : z < hr w := EReal.coe_lt_coe_iff.1 hz
      obtain ⟨δ0, hδ0, hball⟩ :=
        Metric.eventually_nhds_iff.1 ((hr_cont.tendsto w).eventually_const_lt hz')
      refine Filter.le_limsup_of_frequently_le ?_
      refine Filter.Eventually.frequently ?_
      filter_upwards [Ioo_mem_nhdsGT hδ0] with δ hδ
      refine Filter.le_limsup_of_frequently_le ?_
      have hle : pure x_bar ×ˢ 𝓝[>] (0:ℝ) ≤ fApproach f x_bar ×ˢ 𝓝[>] 0 := by
        refine Filter.prod_mono ?_ le_rfl
        refine le_inf (pure_le_nhds x_bar) ?_
        rw [← Filter.map_le_iff_le_comap, Filter.map_pure]
        exact pure_le_nhds _
      refine Filter.Frequently.filter_mono ?_ hle
      refine Filter.Eventually.frequently ?_
      have e1 : ∀ᶠ x in pure x_bar, x = x_bar := Filter.eventually_pure.2 rfl
      have e2 : ∀ᶠ τ in 𝓝[>] (0:ℝ), 0 < τ := eventually_mem_nhdsWithin
      filter_upwards [e1.prod_mk e2] with p hp
      obtain ⟨hp1, hp2⟩ := hp
      refine le_sInf ?_
      rintro _ ⟨w', hw', rfl⟩
      have hw'b : dist w' w < δ0 := lt_of_le_of_lt (Metric.mem_closedBall.1 hw') hδ.2
      have hzw : z < hr w' := hball hw'b
      show (z : EReal) ≤ (f (p.1 + p.2 • w') - f p.1) / ((p.2 : ℝ) : EReal)
      rw [hp1]
      exact le_trans (EReal.coe_le_coe_iff.2 hzw.le) (hq_ge w' p.2 hp2)
  -- the set `W` is everything
  have hW : W = Set.univ := by
    refine Set.eq_univ_of_forall (fun w => ?_)
    obtain ⟨τ, hτ⟩ := (hray' w).exists
    exact ⟨τ, hτ.1, hτ.2⟩
  refine ⟨fun w => ((hr w : ℝ) : EReal), ⟨⟨?_, ?_⟩, ?_⟩, hM2, hM3, ?_, ?_, ?_⟩
  · exact EReal.coe_lt_top _
  · intro x t ht
    show ((hr (t • x) : ℝ) : EReal) = (t : EReal) * ((hr x : ℝ) : EReal)
    rw [hr_smul x t ht, EReal.coe_mul]
  · have hconv := hr_convex.convex_epigraph
    have heq : epigraph (fun w => ((hr w : ℝ) : EReal)) =
        {p : E × ℝ | p.1 ∈ Set.univ ∧ hr p.1 ≤ p.2} := by
      ext p
      simp [epigraph]
    unfold ConvexEReal
    rw [heq]
    exact hconv
  · intro w
    rw [hreg w, hsub w, hliminf w]
    exact ⟨rfl, rfl⟩
  · intro w _
    exact hliminf w
  · have hreg_dom : effDom (regularSubderivative f x_bar) = Set.univ :=
      Set.eq_univ_of_forall (fun w => by
        show regularSubderivative f x_bar w < ⊤
        rw [hreg w]
        exact EReal.coe_lt_top _)
    have hsub_dom : effDom (subderivative f x_bar) = Set.univ :=
      Set.eq_univ_of_forall (fun w => by
        show subderivative f x_bar w < ⊤
        rw [hsub w]
        exact EReal.coe_lt_top _)
    have hh_dom : effDom (fun w => ((hr w : ℝ) : EReal)) = Set.univ :=
      Set.eq_univ_of_forall (fun w => EReal.coe_lt_top _)
    rw [hW, hreg_dom, hsub_dom, hh_dom, interior_univ]
    exact ⟨rfl, rfl, rfl⟩

end RW_chap_8_21
