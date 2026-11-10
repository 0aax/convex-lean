import ConvexStarLib.Defs

/-!
# `RW_chap_8_11`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_8_11` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_8_11`, so the main result is `RW_chap_8_11.RW_chap_8_11`.
-/

namespace RW_chap_8_11

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open Filter Metric

/-! ### Auxiliary lemmas -/

-- L1: regular subgradients are bounded by the subderivative
lemma L1_regSub_inner_le_subderiv (f : E → EReal) (x_bar v : E)
    (hv : IsRegularSubgradientAt f x_bar v) (w : E) :
    ((inner ℝ v w : ℝ) : EReal) ≤ subderivative f x_bar w := by
  obtain ⟨h1, h2, r, hr, V, hVmem, hV⟩ := hv
  obtain ⟨y, hy⟩ : ∃ y : ℝ, f x_bar = y :=
    ⟨(f x_bar).toReal, (EReal.coe_toReal h2.ne h1.ne').symm⟩
  have key : ∀ b : ℝ, b < inner ℝ v w → (b : EReal) ≤ subderivative f x_bar w := by
    intro b hb
    set c : ℝ := (inner ℝ v w - b) / (2 * (‖w‖ + 1)) with hc_def
    have hc : 0 < c := div_pos (by linarith) (by positivity)
    have hcw : b < inner ℝ v w - c * ‖w‖ := by
      have : c * ‖w‖ < inner ℝ v w - b := by
        rw [hc_def, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg w]
      linarith
    have hg : Tendsto (fun p : ℝ × E => x_bar + p.1 • p.2) (𝓝[>] (0:ℝ) ×ˢ 𝓝 w) (𝓝 x_bar) := by
      have hcont : Continuous (fun p : ℝ × E => x_bar + p.1 • p.2) := by fun_prop
      have h0 := hcont.tendsto ((0:ℝ), w)
      simp only [zero_smul, add_zero] at h0
      refine h0.mono_left ?_
      rw [nhds_prod_eq]
      exact Filter.prod_mono nhdsWithin_le_nhds le_rfl
    have e1 : ∀ᶠ p in 𝓝[>] (0:ℝ) ×ˢ 𝓝 w, 0 < p.1 :=
      Filter.Eventually.prod_inl (self_mem_nhdsWithin : Set.Ioi (0:ℝ) ∈ 𝓝[>] (0:ℝ)) (𝓝 w)
    have e2 : ∀ᶠ p in 𝓝[>] (0:ℝ) ×ˢ 𝓝 w, x_bar + p.1 • p.2 ∈ V := hg hVmem
    have e3 : ∀ᶠ p in 𝓝[>] (0:ℝ) ×ˢ 𝓝 w,
        ‖r (x_bar + p.1 • p.2)‖ ≤ c * ‖‖x_bar + p.1 • p.2 - x_bar‖‖ :=
      hg.eventually (hr.def hc)
    have e4 : ∀ᶠ p in 𝓝[>] (0:ℝ) ×ˢ 𝓝 w, b < inner ℝ v p.2 - c * ‖p.2‖ := by
      have hcont : Continuous (fun w' : E => inner ℝ v w' - c * ‖w'‖) := by fun_prop
      exact Filter.Eventually.prod_inr ((hcont.tendsto w).eventually_const_lt hcw) _
    unfold subderivative
    refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [e1, e2, e3, e4] with p hp1 hp2 hp3 hp4
    obtain ⟨τ, w'⟩ := p
    simp only at hp1 hp2 hp3 hp4 ⊢
    have hfV := hV _ hp2
    rw [add_sub_cancel_left, real_inner_smul_right, hy] at hfV
    rw [add_sub_cancel_left, norm_norm, norm_smul, Real.norm_of_nonneg hp1.le, Real.norm_eq_abs] at hp3
    have hreal : b * τ ≤ τ * inner ℝ v w' + r (x_bar + τ • w') := by
      have h5 := neg_abs_le (r (x_bar + τ • w'))
      have h6 := mul_lt_mul_of_pos_left hp4 hp1
      nlinarith [norm_nonneg w']
    unfold differenceQuotient
    rw [hy, EReal.le_div_iff_mul_le (by exact_mod_cast hp1) (EReal.coe_ne_top τ)]
    have hsub : ((τ * inner ℝ v w' + r (x_bar + τ • w') : ℝ) : EReal)
        ≤ f (x_bar + τ • w') - (y : EReal) := by
      have h7 := add_le_add hfV (le_refl (-(y : EReal)))
      rw [sub_eq_add_neg]
      refine le_trans (le_of_eq ?_) h7
      norm_cast
      ring
    calc ((b : EReal) * (τ : EReal)) = ((b * τ : ℝ) : EReal) := by norm_cast
      _ ≤ ((τ * inner ℝ v w' + r (x_bar + τ • w') : ℝ) : EReal) := by exact_mod_cast hreal
      _ ≤ _ := hsub
  by_contra hcon
  push_neg at hcon
  obtain ⟨b, hb1, hb2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  exact absurd ((key b (by exact_mod_cast hb2)).trans_lt hb1) (lt_irrefl _)

omit [FiniteDimensional ℝ E] in
lemma L2_aux_local (f : E → EReal) (x_bar v : E)
    (hv : ∀ w, ((inner ℝ v w : ℝ) : EReal) ≤ subderivative f x_bar w)
    (c : ℝ) (hc : 0 < c) (u : E) :
    ∀ᶠ z : ℝ × E in 𝓝 ((0:ℝ), u),
      0 < z.1 → (((inner ℝ v z.2 : ℝ) - c : ℝ) : EReal) < differenceQuotient f x_bar z.2 z.1 := by
  have hA : ∀ᶠ p : ℝ × E in 𝓝[>] (0:ℝ) ×ˢ 𝓝 u,
      (((inner ℝ v u : ℝ) - c/2 : ℝ) : EReal) < differenceQuotient f x_bar p.2 p.1 := by
    refine Filter.eventually_lt_of_lt_liminf ?_
    calc (((inner ℝ v u : ℝ) - c/2 : ℝ) : EReal) < ((inner ℝ v u : ℝ) : EReal) := by
          exact_mod_cast (by linarith : (inner ℝ v u : ℝ) - c/2 < inner ℝ v u)
      _ ≤ subderivative f x_bar u := hv u
  have hB : ∀ᶠ w in 𝓝 u, (inner ℝ v w : ℝ) - c < (inner ℝ v u : ℝ) - c/2 := by
    have hcont : Continuous (fun w => (inner ℝ v w : ℝ)) := continuous_const.inner continuous_id
    have : ∀ᶠ w in 𝓝 u, (inner ℝ v w : ℝ) < (inner ℝ v u : ℝ) + c/2 :=
      hcont.continuousAt.eventually (gt_mem_nhds (by linarith))
    filter_upwards [this] with w hw
    linarith
  have hC : ∀ᶠ p : ℝ × E in 𝓝[>] (0:ℝ) ×ˢ 𝓝 u,
      (((inner ℝ v p.2 : ℝ) - c : ℝ) : EReal) < differenceQuotient f x_bar p.2 p.1 := by
    have hB' : ∀ᶠ p : ℝ × E in 𝓝[>] (0:ℝ) ×ˢ 𝓝 u,
        (inner ℝ v p.2 : ℝ) - c < (inner ℝ v u : ℝ) - c/2 :=
      hB.prod_inr _
    filter_upwards [hA, hB'] with p hpA hpB
    calc _ < (((inner ℝ v u : ℝ) - c/2 : ℝ) : EReal) := by exact_mod_cast hpB
      _ < _ := hpA
  have heq : 𝓝[>] (0:ℝ) ×ˢ 𝓝 u = 𝓝[Set.Ioi 0 ×ˢ Set.univ] ((0:ℝ), u) := by
    rw [nhdsWithin_prod_eq, nhdsWithin_univ]
  rw [heq, eventually_nhdsWithin_iff] at hC
  filter_upwards [hC] with z hz hz1
  exact hz ⟨hz1, trivial⟩

lemma L2_aux_key (f : E → EReal) (x_bar v : E)
    (h1 : ⊥ < f x_bar) (h2 : f x_bar < ⊤)
    (hv : ∀ w, ((inner ℝ v w : ℝ) : EReal) ≤ subderivative f x_bar w)
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x in 𝓝 x_bar,
      f x_bar + (((inner ℝ v (x - x_bar) : ℝ) - c * ‖x - x_bar‖ : ℝ) : EReal) ≤ f x := by
  have hK := (isCompact_sphere (0:E) 1).eventually_forall_of_forall_eventually (x₀ := (0:ℝ))
    (P := fun τ w => 0 < τ →
      (((inner ℝ v w : ℝ) - c : ℝ) : EReal) < differenceQuotient f x_bar w τ)
    (fun u _ => L2_aux_local f x_bar v hv c hc u)
  have htend : Tendsto (fun x => ‖x - x_bar‖) (𝓝 x_bar) (𝓝 0) := by
    have h : Continuous (fun x : E => ‖x - x_bar‖) := (continuous_id.sub continuous_const).norm
    simpa using h.tendsto x_bar
  obtain ⟨y, hy⟩ : ∃ y : ℝ, f x_bar = y := ⟨(f x_bar).toReal, (EReal.coe_toReal h2.ne h1.ne').symm⟩
  filter_upwards [htend.eventually hK] with x hx
  by_cases hxx : x = x_bar
  · subst hxx; simp
  set τ := ‖x - x_bar‖ with hτ
  have hτpos : 0 < τ := norm_pos_iff.mpr (sub_ne_zero.mpr hxx)
  set u := τ⁻¹ • (x - x_bar) with hu_def
  have hu : u ∈ sphere (0:E) 1 := by
    rw [mem_sphere_zero_iff_norm, hu_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hτpos.ne']
  have hlt := hx u hu hτpos
  unfold differenceQuotient at hlt
  have hxu : x_bar + τ • u = x := by
    rw [hu_def, smul_smul, mul_inv_cancel₀ hτpos.ne', one_smul, add_sub_cancel]
  have hinner : (inner ℝ v u : ℝ) * τ = inner ℝ v (x - x_bar) := by
    rw [hu_def, inner_smul_right, mul_comm, ← mul_assoc, mul_inv_cancel₀ hτpos.ne', one_mul]
  rw [hxu, hy] at hlt
  rw [hy]
  generalize f x = F at hlt ⊢
  induction F using EReal.rec with
  | bot =>
    rw [EReal.bot_sub, EReal.bot_div_of_pos_ne_top (by exact_mod_cast hτpos)
      (EReal.coe_ne_top _)] at hlt
    exact absurd hlt (not_lt_bot)
  | coe z =>
    rw [← EReal.coe_sub, ← EReal.coe_div, EReal.coe_lt_coe_iff, lt_div_iff₀ hτpos] at hlt
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    nlinarith
  | top => exact le_top

lemma L2_aux_ne_bot (y a : ℝ) (F : EReal) (h : (y : EReal) + (a : EReal) ≤ F) : F ≠ ⊥ := by
  intro hb
  rw [hb, ← EReal.coe_add] at h
  exact EReal.coe_ne_bot _ (le_bot_iff.mp h)

-- L2: converse (finite dimensions)
lemma L2_regSub_of_inner_le (f : E → EReal) (x_bar v : E)
    (h1 : ⊥ < f x_bar) (h2 : f x_bar < ⊤)
    (hv : ∀ w, ((inner ℝ v w : ℝ) : EReal) ≤ subderivative f x_bar w) :
    IsRegularSubgradientAt f x_bar v := by
  obtain ⟨y, hy⟩ : ∃ y : ℝ, f x_bar = y :=
    ⟨(f x_bar).toReal, (EReal.coe_toReal h2.ne h1.ne').symm⟩
  refine ⟨h1, h2, fun x => if f x = ⊤ then 0 else
    min 0 ((f x).toReal - y - inner ℝ v (x - x_bar)), ?_, ?_⟩
  · rw [Asymptotics.isLittleO_iff]
    intro c hc
    filter_upwards [L2_aux_key f x_bar v h1 h2 hv c hc] with x hx
    rw [hy] at hx
    rw [Real.norm_eq_abs, norm_norm]
    split_ifs with htop
    · simp only [abs_zero]; positivity
    · obtain ⟨z, hz⟩ : ∃ z : ℝ, f x = z :=
        ⟨(f x).toReal, (EReal.coe_toReal htop (L2_aux_ne_bot _ _ _ hx)).symm⟩
      rw [hz, ← EReal.coe_add, EReal.coe_le_coe_iff] at hx
      rw [hz, EReal.toReal_coe, abs_le]
      constructor
      · apply le_min
        · nlinarith [norm_nonneg (x - x_bar)]
        · linarith
      · exact (min_le_left _ _).trans (by positivity)
  · refine ⟨{x | f x_bar + (((inner ℝ v (x - x_bar) : ℝ) - 1 * ‖x - x_bar‖ : ℝ) : EReal) ≤ f x},
      L2_aux_key f x_bar v h1 h2 hv 1 one_pos, ?_⟩
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    rw [hy] at hx ⊢
    dsimp only
    split_ifs with htop
    · rw [htop]; exact le_top
    · obtain ⟨z, hz⟩ : ∃ z : ℝ, f x = z :=
        ⟨(f x).toReal, (EReal.coe_toReal htop (L2_aux_ne_bot _ _ _ hx)).symm⟩
      rw [hz, EReal.toReal_coe, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have := min_le_right 0 (z - y - inner ℝ v (x - x_bar))
      linarith

-- L3: subderivative ≤ regular subderivative
lemma L3_subderiv_le_regSubderiv (f : E → EReal) (x_bar : E)
    (w : E) :
    subderivative f x_bar w ≤ regularSubderivative f x_bar w := by
  have key : ∀ b : ℝ, (b : EReal) < subderivative f x_bar w →
      (b : EReal) ≤ regularSubderivative f x_bar w := by
    intro b hb
    have hev := Filter.eventually_lt_of_lt_liminf hb
    obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := Filter.mem_prod_iff.1 hev
    obtain ⟨δ0, hδ0, hball⟩ := Metric.mem_nhds_iff.1 ht₂
    have hφ : Tendsto (fun τ : ℝ => (x_bar, τ)) (𝓝[>] (0:ℝ))
        (fApproach f x_bar ×ˢ 𝓝[>] (0:ℝ)) := by
      apply Filter.Tendsto.prodMk
      · unfold fApproach
        exact tendsto_inf.2 ⟨tendsto_const_nhds, tendsto_comap_iff.2 tendsto_const_nhds⟩
      · exact tendsto_id
    have hinner : ∀ δ : ℝ, 0 < δ → δ < δ0 → (b : EReal) ≤
        limsup (fun p : E × ℝ => sInf ((delta f p.1 p.2) '' closedBall w δ))
          (fApproach f x_bar ×ˢ 𝓝[>] (0:ℝ)) := by
      intro δ hδ hδδ0
      refine Filter.le_limsup_of_frequently_le ?_ (by isBoundedDefault)
      apply hφ.frequently
      apply Filter.Eventually.frequently
      filter_upwards [ht₁] with τ hτ
      apply le_sInf
      rintro _ ⟨w', hw', rfl⟩
      have hw'2 : w' ∈ t₂ := hball (Metric.closedBall_subset_ball hδδ0 hw')
      exact (hsub (Set.mk_mem_prod hτ hw'2)).le
    unfold regularSubderivative
    refine Filter.le_limsup_of_frequently_le ?_ (by isBoundedDefault)
    apply Filter.Eventually.frequently
    filter_upwards [Ioo_mem_nhdsGT hδ0] with δ hδ
    exact hinner δ hδ.1 hδ.2
  by_contra hcon
  push_neg at hcon
  obtain ⟨b, hb1, hb2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  exact absurd ((key b hb2).trans_lt hb1) (lt_irrefl _)

-- LC: lower bound on the inner limsup from regular subgradients along an f-attentive sequence
lemma LC_inner_limsup_ge (f : E → EReal) (x_bar w_bar : E) (δ b η : ℝ) (hη : 0 < η)
    (x vs : ℕ → E) (hx : Tendsto x atTop (𝓝 x_bar))
    (hfx : Tendsto (fun n => f (x n)) atTop (𝓝 (f x_bar)))
    (hreg : ∀ n, IsRegularSubgradientAt f (x n) (vs n))
    (hb : ∃ᶠ n in atTop, ∀ w ∈ closedBall w_bar δ, b + η ≤ inner ℝ (vs n) w) :
    (b : EReal) ≤ limsup (fun p : E × ℝ => sInf ((delta f p.1 p.2) '' closedBall w_bar δ))
      (fApproach f x_bar ×ˢ 𝓝[>] (0 : ℝ)) := by
  refine Filter.le_limsup_of_frequently_le ?_
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨s, hs, t, ht, hst⟩ := Filter.mem_prod_iff.1 hU
  have hxA : Tendsto x atTop (fApproach f x_bar) :=
    tendsto_inf.2 ⟨hx, tendsto_comap_iff.2 hfx⟩
  obtain ⟨n, hn, hxs⟩ := (hb.and_eventually (hxA.eventually_mem hs)).exists
  obtain ⟨hbot, htop, r, hr, V, hV, hfV⟩ := hreg n
  set K : ℝ := ‖w_bar‖ + |δ| + 1 with hK
  have hKpos : 0 < K := by positivity
  have hcpos : 0 < η / K := div_pos hη hKpos
  have hev : ∀ᶠ y in 𝓝 (x n), ‖r y‖ ≤ (η / K) * ‖‖y - x n‖‖ ∧ y ∈ V :=
    (Asymptotics.isLittleO_iff.1 hr hcpos).and hV
  obtain ⟨ε, hε, hεball⟩ := Metric.eventually_nhds_iff.1 hev
  have hεK : 0 < ε / K := div_pos hε hKpos
  obtain ⟨τ, hτt, hτ0, hτε⟩ := Filter.nonempty_of_mem (Filter.inter_mem ht (Ioo_mem_nhdsGT hεK))
  refine ⟨(x n, τ), hst ⟨hxs, hτt⟩, ?_⟩
  apply le_sInf
  rintro _ ⟨w, hw, rfl⟩
  show (b : EReal) ≤ (f (x n + τ • w) - f (x n)) / τ
  have hwK : ‖w‖ < K := by
    have h1 := norm_le_of_mem_closedBall hw
    have h2 := le_abs_self δ
    linarith
  have hnorm : ‖(x n + τ • w) - x n‖ = τ * ‖w‖ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ0.le]
  have hlt : ‖(x n + τ • w) - x n‖ < ε := by
    rw [hnorm]
    calc τ * ‖w‖ ≤ τ * K := by gcongr
      _ < (ε / K) * K := by gcongr
      _ = ε := div_mul_cancel₀ ε hKpos.ne'
  obtain ⟨hry, hyV⟩ := hεball (by rw [dist_eq_norm]; exact hlt)
  have hfy := hfV _ hyV
  have hinner : inner ℝ (vs n) (x n + τ • w - x n) = τ * inner ℝ (vs n) w := by
    rw [add_sub_cancel_left, real_inner_smul_right]
  have hbw := hn w hw
  have hreal : b * τ ≤ inner ℝ (vs n) (x n + τ • w - x n) + r (x n + τ • w) := by
    rw [hinner]
    have h1 : |r (x n + τ • w)| ≤ (η / K) * (τ * ‖w‖) := by
      rw [← Real.norm_eq_abs, ← hnorm]
      simpa using hry
    have h2 : (η / K) * (τ * ‖w‖) ≤ η * τ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hKpos]
      calc η * (τ * ‖w‖) = (η * τ) * ‖w‖ := by ring
        _ ≤ (η * τ) * K := by gcongr
    have h3 := neg_abs_le (r (x n + τ • w))
    nlinarith
  set a : ℝ := (f (x n)).toReal with ha
  have hfa : f (x n) = (a : EReal) := (EReal.coe_toReal htop.ne hbot.ne').symm
  rw [hfa] at hfy ⊢
  have hcomb : ((b * τ + a : ℝ) : EReal) ≤ f (x n + τ • w) := by
    refine le_trans ?_ hfy
    rw [← EReal.coe_add]
    have : b * τ + a ≤ a + (inner ℝ (vs n) (x n + τ • w - x n) + r (x n + τ • w)) := by linarith
    exact_mod_cast this
  rw [EReal.le_div_iff_mul_le (by exact_mod_cast hτ0) (EReal.coe_ne_top τ)]
  rw [EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot a)) (Or.inl (EReal.coe_ne_top a))]
  rw [← EReal.coe_mul, ← EReal.coe_add]
  exact hcomb

-- helper: lower bound on the regular subderivative from regular subgradient sequences
lemma L45_aux_le_regSubderiv (f : E → EReal) (x_bar w : E) (b η δ0 : ℝ) (hη : 0 < η)
    (hδ0 : 0 < δ0) (x vs : ℕ → E) (hx : Tendsto x atTop (𝓝 x_bar))
    (hfx : Tendsto (fun n => f (x n)) atTop (𝓝 (f x_bar)))
    (hreg : ∀ n, IsRegularSubgradientAt f (x n) (vs n))
    (hb : ∀ δ : ℝ, 0 < δ → δ < δ0 →
      ∃ᶠ n in atTop, ∀ w' ∈ closedBall w δ, b + η ≤ inner ℝ (vs n) w') :
    (b : EReal) ≤ regularSubderivative f x_bar w := by
  unfold regularSubderivative
  refine Filter.le_limsup_of_frequently_le ?_
  apply Filter.Eventually.frequently
  filter_upwards [Ioo_mem_nhdsGT hδ0] with δ hδ
  exact LC_inner_limsup_ge f x_bar w δ b η hη x vs hx hfx hreg (hb δ hδ.1 hδ.2)

-- L4: limiting subgradients are bounded by the regular subderivative
lemma L4_subgrad_inner_le_regSubderiv (f : E → EReal) (x_bar v : E)
    (hv : v ∈ subdifferential f x_bar) (w : E) :
    ((inner ℝ v w : ℝ) : EReal) ≤ regularSubderivative f x_bar w := by
  obtain ⟨_, _, x, vs, hx, hfx, hvs, hreg⟩ := hv
  have key : ∀ b : ℝ, b < inner ℝ v w → (b : EReal) ≤ regularSubderivative f x_bar w := by
    intro b hb
    set η := (inner ℝ v w - b) / 3 with hη_def
    have hη : 0 < η := by rw [hη_def]; linarith
    set δ0 := η / (‖v‖ + 1) with hδ0_def
    have hv1 : 0 < ‖v‖ + 1 := by positivity
    have hδ0 : 0 < δ0 := div_pos hη hv1
    apply L45_aux_le_regSubderiv f x_bar w b η δ0 hη hδ0 x vs hx hfx hreg
    intro δ hδpos hδlt
    apply Filter.Eventually.frequently
    have hK : 0 < ‖w‖ + δ0 + 1 := by positivity
    have hε : 0 < η / (‖w‖ + δ0 + 1) := div_pos hη hK
    filter_upwards [(Metric.tendsto_nhds.mp hvs) _ hε] with n hn
    intro w' hw'
    have h1 : inner ℝ (vs n) w' = inner ℝ v w + inner ℝ v (w' - w) + inner ℝ (vs n - v) w' := by
      rw [inner_sub_right, inner_sub_left]; ring
    have hw'w : ‖w' - w‖ ≤ δ := by rw [← dist_eq_norm]; exact mem_closedBall.mp hw'
    have hw'n : ‖w'‖ ≤ ‖w‖ + δ0 := by
      calc ‖w'‖ = ‖w + (w' - w)‖ := by congr 1; abel
        _ ≤ ‖w‖ + ‖w' - w‖ := norm_add_le _ _
        _ ≤ ‖w‖ + δ0 := by linarith
    have h2 : |inner ℝ v (w' - w)| ≤ ‖v‖ * ‖w' - w‖ := abs_real_inner_le_norm _ _
    have h3 : |inner ℝ (vs n - v) w'| ≤ ‖vs n - v‖ * ‖w'‖ := abs_real_inner_le_norm _ _
    have hvn : ‖vs n - v‖ < η / (‖w‖ + δ0 + 1) := by rw [← dist_eq_norm]; exact hn
    have h4 : ‖v‖ * ‖w' - w‖ ≤ η := by
      calc ‖v‖ * ‖w' - w‖ ≤ ‖v‖ * δ0 :=
            mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ ≤ (‖v‖ + 1) * δ0 := by nlinarith
        _ = η := by rw [hδ0_def]; field_simp
    have h5 : ‖vs n - v‖ * ‖w'‖ ≤ η := by
      calc ‖vs n - v‖ * ‖w'‖ ≤ (η / (‖w‖ + δ0 + 1)) * (‖w‖ + δ0 + 1) :=
            mul_le_mul hvn.le (by linarith) (norm_nonneg _) hε.le
        _ = η := by field_simp
    have h6 := (abs_le.mp h2).1
    have h7 := (abs_le.mp h3).1
    rw [h1]
    linarith
  by_contra hcon
  push_neg at hcon
  obtain ⟨b, hb1, hb2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
  have hb' : b < inner ℝ v w := by exact_mod_cast hb2
  exact absurd (lt_of_lt_of_le hb1 (key b hb')) (lt_irrefl _)

-- L5: horizon subgradients are nonpositive on dom of the regular subderivative
lemma L5_horizon_inner_nonpos (f : E → EReal) (x_bar v : E)
    (hv : v ∈ horizonSubdifferential f x_bar) (w : E)
    (hw : regularSubderivative f x_bar w < ⊤) :
    inner ℝ v w ≤ 0 := by
  obtain ⟨_, _, x, vs, l, hx, hfx, hl, hlv, hreg⟩ := hv
  by_contra hcon
  push_neg at hcon
  set c := inner ℝ v w with hc_def
  have key : ∀ B : ℝ, (B : EReal) ≤ regularSubderivative f x_bar w := by
    intro B
    set δ0 := c / (4 * (‖v‖ + 1)) with hδ0_def
    have hv1 : 0 < ‖v‖ + 1 := by positivity
    have hδ0 : 0 < δ0 := div_pos hcon (by positivity)
    apply L45_aux_le_regSubderiv f x_bar w B 1 δ0 one_pos hδ0 x vs hx hfx hreg
    intro δ hδpos hδlt
    apply Filter.Eventually.frequently
    have hK : 0 < ‖w‖ + δ0 + 1 := by positivity
    have hε : 0 < c / (4 * (‖w‖ + δ0 + 1)) := div_pos hcon (by positivity)
    have hB1 : 0 < |B| + 1 := by positivity
    have hB : 0 < c / (2 * (|B| + 1)) := div_pos hcon (by positivity)
    have hl0 : Tendsto l atTop (𝓝 0) := hl.mono_right nhdsWithin_le_nhds
    have hlpos : ∀ᶠ n in atTop, 0 < l n := (tendsto_nhdsWithin_iff.mp hl).2
    have hlsmall : ∀ᶠ n in atTop, l n < c / (2 * (|B| + 1)) :=
      hl0.eventually (gt_mem_nhds hB)
    filter_upwards [hlpos, hlsmall, (Metric.tendsto_nhds.mp hlv) _ hε] with n hpos hsmall hn
    intro w' hw'
    have h1 : inner ℝ (l n • vs n) w' =
        inner ℝ v w + inner ℝ v (w' - w) + inner ℝ (l n • vs n - v) w' := by
      rw [inner_sub_right, inner_sub_left]; ring
    have hsm : inner ℝ (l n • vs n) w' = l n * inner ℝ (vs n) w' := real_inner_smul_left _ _ _
    have hw'w : ‖w' - w‖ ≤ δ := by rw [← dist_eq_norm]; exact mem_closedBall.mp hw'
    have hw'n : ‖w'‖ ≤ ‖w‖ + δ0 := by
      calc ‖w'‖ = ‖w + (w' - w)‖ := by congr 1; abel
        _ ≤ ‖w‖ + ‖w' - w‖ := norm_add_le _ _
        _ ≤ ‖w‖ + δ0 := by linarith
    have h2 : |inner ℝ v (w' - w)| ≤ ‖v‖ * ‖w' - w‖ := abs_real_inner_le_norm _ _
    have h3 : |inner ℝ (l n • vs n - v) w'| ≤ ‖l n • vs n - v‖ * ‖w'‖ :=
      abs_real_inner_le_norm _ _
    have hvn : ‖l n • vs n - v‖ < c / (4 * (‖w‖ + δ0 + 1)) := by
      rw [← dist_eq_norm]; exact hn
    have h4 : ‖v‖ * ‖w' - w‖ ≤ c / 4 := by
      calc ‖v‖ * ‖w' - w‖ ≤ ‖v‖ * δ0 :=
            mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ ≤ (‖v‖ + 1) * δ0 := by nlinarith
        _ = c / 4 := by rw [hδ0_def]; field_simp
    have h5 : ‖l n • vs n - v‖ * ‖w'‖ ≤ c / 4 := by
      calc ‖l n • vs n - v‖ * ‖w'‖ ≤ (c / (4 * (‖w‖ + δ0 + 1))) * (‖w‖ + δ0 + 1) :=
            mul_le_mul hvn.le (by linarith) (norm_nonneg _) hε.le
        _ = c / 4 := by field_simp
    have h6 := (abs_le.mp h2).1
    have h7 := (abs_le.mp h3).1
    have hmain : c / 2 ≤ l n * inner ℝ (vs n) w' := by
      rw [← hsm, h1]; linarith
    have hsmall' : l n * (2 * (|B| + 1)) < c := (lt_div_iff₀ (by positivity)).mp hsmall
    have h8 : l n * (|B| + 1) < l n * inner ℝ (vs n) w' := by linarith
    have h9 : |B| + 1 < inner ℝ (vs n) w' := lt_of_mul_lt_mul_left h8 hpos.le
    have h10 : B ≤ |B| := le_abs_self B
    linarith
  obtain ⟨B, hB1, hB2⟩ := EReal.lt_iff_exists_real_btwn.mp hw
  exact absurd (lt_of_lt_of_le hB1 (key B)) (lt_irrefl _)



-- L6a: extraction from the regular subderivative
lemma L6a_extract (f : E → EReal) (x_bar w_bar : E) (β : ℝ)
    (h : (β : EReal) < regularSubderivative f x_bar w_bar) :
    ∃ δ > 0, ∃ᶠ p in fApproach f x_bar ×ˢ 𝓝[>] (0 : ℝ),
      (β : EReal) < sInf ((delta f p.1 p.2) '' closedBall w_bar δ) := by
  unfold regularSubderivative at h
  have h1 := Filter.frequently_lt_of_lt_limsup (by isBoundedDefault) h
  have h2 : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hδ1, hδ2⟩ := (h1.and_eventually h2).exists
  exact ⟨δ, hδ2, Filter.frequently_lt_of_lt_limsup (by isBoundedDefault) hδ1⟩

lemma Lcore_aux_sep (g : E → ℝ) (hg : LowerSemicontinuous g) (x0 w_bar : E) (δ τ a : ℝ)
    (hY : ∀ w ∈ closedBall w_bar δ, a < g (x0 + τ • w)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ w ∈ closedBall w_bar δ, ∀ z, g z ≤ a → ρ ≤ ‖x0 + τ • w - z‖ := by
  have hYc : IsCompact ((fun w => x0 + τ • w) '' closedBall w_bar δ) :=
    (isCompact_closedBall w_bar δ).image (by fun_prop)
  have hAc : IsClosed (g ⁻¹' Set.Iic a) := hg.isClosed_preimage a
  have hdisj : Disjoint ((fun w => x0 + τ • w) '' closedBall w_bar δ) (g ⁻¹' Set.Iic a) := by
    rw [Set.disjoint_left]
    rintro _ ⟨w, hw, rfl⟩ hz
    exact absurd (hY w hw) (not_lt.2 hz)
  obtain ⟨r, hr, hr'⟩ := Metric.exists_pos_forall_lt_edist hYc hAc hdisj
  refine ⟨r, by exact_mod_cast hr, fun w hw z hz => ?_⟩
  have h1 := hr' _ ⟨w, hw, rfl⟩ z hz
  rw [edist_nndist, ENNReal.coe_lt_coe] at h1
  have h2 : (r : ℝ) < dist (x0 + τ • w) z := by
    rw [← coe_nndist]; exact_mod_cast h1
  rw [dist_eq_norm] at h2
  exact h2.le

-- core mean value inequality for a real-valued lsc function
lemma Lcore_mvi (g : E → ℝ) (hg : LowerSemicontinuous g) (c : E) (R m : ℝ)
    (hm : ∀ z, m ≤ g z)
    (x0 w_bar : E) (δ τ β : ℝ) (hδ : 0 < δ) (hτ : 0 < τ)
    (hx0 : dist x0 c + τ * (‖w_bar‖ + δ) < R)
    (hY : ∀ w ∈ closedBall w_bar δ, g x0 + τ * β < g (x0 + τ • w)) :
    ∃ z ζ : E, ∃ M : ℝ, 0 ≤ M ∧ dist z c < R ∧ g z ≤ g x0 + τ * |β| ∧
      (∀ y ∈ ball c R, g z + inner ℝ ζ (y - z) - M * ‖y - z‖ ^ 2 ≤ g y) ∧
      ∀ w ∈ closedBall w_bar δ, β ≤ inner ℝ ζ w := by
  have hτβ : 0 ≤ τ * |β| := mul_nonneg hτ.le (abs_nonneg β)
  have hwb : 0 ≤ τ * (‖w_bar‖ + δ) := mul_nonneg hτ.le (add_nonneg (norm_nonneg _) hδ.le)
  obtain ⟨B0, hB0, hB0def⟩ : ∃ B0 : ℝ, 0 < B0 ∧ B0 = g x0 + τ * |β| - m + 1 :=
    ⟨_, by linarith [hm x0], rfl⟩
  obtain ⟨margin, hmargin, hmargin_def⟩ :
      ∃ margin : ℝ, 0 < margin ∧ margin = R - (dist x0 c + τ * (‖w_bar‖ + δ)) :=
    ⟨_, by linarith, rfl⟩
  obtain ⟨ρ, hρ, hsep⟩ := Lcore_aux_sep g hg x0 w_bar δ τ (g x0 + τ * β) hY
  obtain ⟨M, hM, hMρ, hMm⟩ : ∃ M : ℝ, 0 < M ∧ B0 < M * ρ ^ 2 ∧ B0 < M * margin ^ 2 := by
    refine ⟨B0 / ρ ^ 2 + B0 / margin ^ 2 + 1, by positivity, ?_, ?_⟩
    · have h1 : B0 / ρ ^ 2 * ρ ^ 2 = B0 := div_mul_cancel₀ _ (by positivity)
      have h2 : 0 ≤ B0 / margin ^ 2 * ρ ^ 2 := by positivity
      have h3 : 0 < ρ ^ 2 := by positivity
      nlinarith
    · have h1 : B0 / margin ^ 2 * margin ^ 2 = B0 := div_mul_cancel₀ _ (by positivity)
      have h2 : 0 ≤ B0 / ρ ^ 2 * margin ^ 2 := by positivity
      have h3 : 0 < margin ^ 2 := by positivity
      nlinarith
  -- the functional
  have hGlsc : LowerSemicontinuous (fun p : ℝ × E × E =>
      g p.2.2 + (M * ‖x0 + (p.1 * τ) • p.2.1 - p.2.2‖ ^ 2 - p.1 * τ * β)) := by
    apply LowerSemicontinuous.add
    · exact hg.comp continuous_snd.snd
    · apply Continuous.lowerSemicontinuous
      fun_prop
  have hK : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ closedBall w_bar δ ×ˢ closedBall c R) :=
    isCompact_Icc.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hx0c : x0 ∈ closedBall c R := by
    rw [mem_closedBall]; linarith
  have hKne : (Set.Icc (0:ℝ) 1 ×ˢ closedBall w_bar δ ×ˢ closedBall c R).Nonempty :=
    ⟨(0, w_bar, x0), Set.mk_mem_prod (Set.left_mem_Icc.2 zero_le_one)
      (Set.mk_mem_prod (mem_closedBall_self hδ.le) hx0c)⟩
  obtain ⟨⟨t, ws, z⟩, hpK, hmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn hKne hK (hGlsc.lowerSemicontinuousOn _)
  rw [isMinOn_iff] at hmin
  obtain ⟨⟨ht0, ht1⟩, hws, hz⟩ :
      (0 ≤ t ∧ t ≤ 1) ∧ ws ∈ closedBall w_bar δ ∧ z ∈ closedBall c R := hpK
  have hG : ∀ t' w' z', t' ∈ Set.Icc (0:ℝ) 1 → w' ∈ closedBall w_bar δ → z' ∈ closedBall c R →
      g z + (M * ‖x0 + (t * τ) • ws - z‖ ^ 2 - t * τ * β) ≤
        g z' + (M * ‖x0 + (t' * τ) • w' - z'‖ ^ 2 - t' * τ * β) :=
    fun t' w' z' h1 h2 h3 => hmin (t', w', z') (Set.mk_mem_prod h1 (Set.mk_mem_prod h2 h3))
  clear hmin
  obtain ⟨cs, hcs⟩ : ∃ cs, x0 + (t * τ) • ws = cs := ⟨_, rfl⟩
  rw [hcs] at hG
  have h5 : g z + (M * ‖cs - z‖ ^ 2 - t * τ * β) ≤ g x0 := by
    have h := hG 0 w_bar x0 (Set.left_mem_Icc.2 zero_le_one) (mem_closedBall_self hδ.le) hx0c
    have e : g x0 + (M * ‖x0 + ((0:ℝ) * τ) • w_bar - x0‖ ^ 2 - 0 * τ * β) = g x0 := by simp
    linarith
  have htb : t * τ * β ≤ τ * |β| := by
    have h1 : t * τ * β ≤ t * τ * |β| :=
      mul_le_mul_of_nonneg_left (le_abs_self β) (mul_nonneg ht0 hτ.le)
    nlinarith [abs_nonneg β]
  have hN0 : 0 ≤ ‖cs - z‖ ^ 2 := by positivity
  have hMN0 : 0 ≤ M * ‖cs - z‖ ^ 2 := mul_nonneg hM.le hN0
  have hgz := hm z
  have hMN : M * ‖cs - z‖ ^ 2 < B0 := by linarith
  have hnorm_lt : ‖cs - z‖ < margin := by
    by_contra hcon
    push_neg at hcon
    have : margin ^ 2 ≤ ‖cs - z‖ ^ 2 := pow_le_pow_left₀ hmargin.le hcon 2
    nlinarith
  have hws_norm : ‖ws‖ ≤ ‖w_bar‖ + δ := by
    have := norm_sub_norm_le ws w_bar
    rw [mem_closedBall, dist_eq_norm] at hws
    linarith
  have hcs_dist : dist cs c ≤ dist x0 c + τ * (‖w_bar‖ + δ) := by
    rw [← hcs, dist_eq_norm, dist_eq_norm]
    have e : x0 + (t * τ) • ws - c = (x0 - c) + (t * τ) • ws := by abel
    rw [e]
    calc ‖(x0 - c) + (t * τ) • ws‖ ≤ ‖x0 - c‖ + ‖(t * τ) • ws‖ := norm_add_le _ _
      _ = ‖x0 - c‖ + t * τ * ‖ws‖ := by
          rw [norm_smul, Real.norm_of_nonneg (mul_nonneg ht0 hτ.le)]
      _ ≤ ‖x0 - c‖ + τ * (‖w_bar‖ + δ) := by
          have h1 : t * ‖ws‖ ≤ 1 * (‖w_bar‖ + δ) :=
            mul_le_mul ht1 hws_norm (norm_nonneg _) zero_le_one
          nlinarith
  have hzc : dist z c < R := by
    have h1 := dist_triangle z cs c
    have e : dist z cs = ‖cs - z‖ := by rw [_root_.dist_comm, dist_eq_norm]
    linarith
  have hgz_le : g z ≤ g x0 + τ * |β| := by linarith
  have ht1' : t < 1 := by
    by_contra hcon
    have ht_eq : t = 1 := le_antisymm ht1 (not_lt.1 hcon)
    subst ht_eq
    by_cases hA : g z ≤ g x0 + τ * β
    · have h1 := hsep ws hws z hA
      have e : x0 + τ • ws = cs := by rw [← hcs, one_mul]
      rw [e] at h1
      have : M * ρ ^ 2 ≤ M * ‖cs - z‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ.le h1 2) hM.le
      linarith
    · push_neg at hA
      linarith
  refine ⟨z, (2 * M) • (cs - z), M, hM.le, hzc, hgz_le, ?_, ?_⟩
  · intro y hy
    have hyc : y ∈ closedBall c R := ball_subset_closedBall hy
    have h := hG t ws y ⟨ht0, ht1⟩ hws hyc
    rw [hcs] at h
    have e : cs - y = (cs - z) - (y - z) := by abel
    rw [e, norm_sub_sq_real (cs - z) (y - z)] at h
    rw [real_inner_smul_left]
    linarith
  · intro w hw
    have hW : 0 ≤ ‖w‖ ^ 2 := by positivity
    have hkey : ∀ s : ℝ, 0 < s → s ≤ 1 - t →
        β ≤ inner ℝ ((2 * M) • (cs - z)) w + M * s * τ * ‖w‖ ^ 2 := by
      intro s hs hs1
      have hts : 0 < t + s := by linarith
      have hab : t / (t + s) + s / (t + s) = 1 := by
        rw [← add_div, div_self hts.ne']
      have hmem : (t / (t + s)) • ws + (s / (t + s)) • w ∈ closedBall w_bar δ :=
        convex_closedBall w_bar δ hws hw (div_nonneg ht0 hts.le) (div_nonneg hs.le hts.le) hab
      have h := hG (t + s) ((t / (t + s)) • ws + (s / (t + s)) • w) z
        ⟨by linarith, by linarith⟩ hmem hz
      have e : x0 + ((t + s) * τ) • ((t / (t + s)) • ws + (s / (t + s)) • w) - z
          = (cs - z) + (s * τ) • w := by
        rw [← hcs, smul_add, smul_smul, smul_smul]
        have e1 : (t + s) * τ * (t / (t + s)) = t * τ := by field_simp
        have e2 : (t + s) * τ * (s / (t + s)) = s * τ := by field_simp
        rw [e1, e2]
        abel
      have hst : 0 < s * τ := mul_pos hs hτ
      rw [e, norm_add_sq_real, real_inner_smul_right, norm_smul,
        Real.norm_of_nonneg hst.le] at h
      rw [real_inner_smul_left]
      have : s * τ * β ≤ s * τ * (2 * M * inner ℝ (cs - z) w + M * s * τ * ‖w‖ ^ 2) := by
        nlinarith
      exact le_of_mul_le_mul_left this hst
    apply _root_.le_of_forall_pos_le_add
    intro ε hε
    have hK'0 : 0 ≤ M * τ * ‖w‖ ^ 2 := by positivity
    have h1t : 0 < 1 - t := by linarith
    obtain ⟨s, hs, hs1, hs2⟩ :
        ∃ s : ℝ, 0 < s ∧ s ≤ 1 - t ∧ s * (M * τ * ‖w‖ ^ 2 + 1) ≤ ε := by
      refine ⟨min (1 - t) (ε / (M * τ * ‖w‖ ^ 2 + 1)), lt_min h1t (by positivity),
        min_le_left _ _, ?_⟩
      calc min (1 - t) (ε / (M * τ * ‖w‖ ^ 2 + 1)) * (M * τ * ‖w‖ ^ 2 + 1)
          ≤ ε / (M * τ * ‖w‖ ^ 2 + 1) * (M * τ * ‖w‖ ^ 2 + 1) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        _ = ε := div_mul_cancel₀ _ (by positivity)
    have h1 := hkey s hs hs1
    have e : M * s * τ * ‖w‖ ^ 2 = s * (M * τ * ‖w‖ ^ 2 + 1) - s := by ring
    linarith

-- L6s: single step of the mean value argument for f
lemma L6s_mvi_step (f : E → EReal) (x_bar w_bar : E) (δ β : ℝ) (hδ : 0 < δ)
    (hlsc : LocalLscAt f x_bar) :
    ∀ η > 0, ∃ ρ > 0, ∀ x : E, ∀ τ : ℝ, dist x x_bar < ρ → 0 < τ → τ < ρ →
      f x_bar - ((ρ : ℝ) : EReal) < f x → f x < f x_bar + ((ρ : ℝ) : EReal) →
      (β : EReal) < sInf ((delta f x τ) '' closedBall w_bar δ) →
      ∃ z ζ : E, dist z x_bar < η ∧ f x_bar - ((η : ℝ) : EReal) < f z ∧
        f z < f x_bar + ((η : ℝ) : EReal) ∧
        IsRegularSubgradientAt f z ζ ∧ ∀ w ∈ closedBall w_bar δ, β ≤ inner ℝ ζ w := by
  classical
  obtain ⟨hbot, htop, ε, hε⟩ := hlsc
  obtain ⟨a, ha⟩ : ∃ a : ℝ, f x_bar = (a : EReal) :=
    ⟨(f x_bar).toReal, (EReal.coe_toReal htop.ne hbot.ne').symm⟩
  have hεpos : 0 < ε := (hε (a + ε) (by rw [ha, EReal.coe_add])).1
  have hclosed : ∀ α : ℝ, α ≤ a + ε →
      IsClosed {x | x ∈ closedBall x_bar ε ∧ f x ≤ (α : EReal)} := by
    intro α hα
    refine (hε α ?_).2
    rw [ha, ← EReal.coe_add]
    exact EReal.coe_le_coe_iff.2 hα
  intro η hη
  have hS : IsClosed {x | x ∈ closedBall x_bar ε ∧ f x ≤ ((a - η : ℝ) : EReal)} :=
    hclosed (a - η) (by linarith)
  have hxS : x_bar ∈ {x | x ∈ closedBall x_bar ε ∧ f x ≤ ((a - η : ℝ) : EReal)}ᶜ := by
    intro h
    have h2 := h.2
    rw [ha, EReal.coe_le_coe_iff] at h2
    linarith
  obtain ⟨r, hr, hrS⟩ := Metric.isOpen_iff.1 hS.isOpen_compl x_bar hxS
  obtain ⟨R0, hR0_def⟩ : ∃ R0 : ℝ, R0 = min (min (r / 2) ε) η := ⟨_, rfl⟩
  have hR0 : 0 < R0 := by
    rw [hR0_def]; exact lt_min (lt_min (by linarith) hεpos) hη
  have hR0r : R0 ≤ r / 2 := by rw [hR0_def]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hR0ε : R0 ≤ ε := by rw [hR0_def]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hR0η : R0 ≤ η := by rw [hR0_def]; exact min_le_right _ _
  have hlow : ∀ z ∈ closedBall x_bar R0, ((a - η : ℝ) : EReal) < f z := by
    intro z hz
    rw [mem_closedBall] at hz
    have hzr : z ∈ ball x_bar r := by rw [mem_ball]; linarith
    have hzS := hrS hzr
    have hzε : z ∈ closedBall x_bar ε := by rw [mem_closedBall]; linarith
    by_contra hcon
    exact hzS ⟨hzε, not_lt.1 hcon⟩
  obtain ⟨L, hL_def⟩ : ∃ L : ℝ, L = a + ε := ⟨_, rfl⟩
  have hLlow : ((a - η : ℝ) : EReal) < (L : EReal) :=
    EReal.coe_lt_coe_iff.2 (by rw [hL_def]; linarith)
  obtain ⟨g, hg_def⟩ : ∃ g : E → ℝ, ∀ z, g z =
      if z ∈ closedBall x_bar R0 then (min (f z) (L : EReal)).toReal else L := ⟨_, fun z => rfl⟩
  have hg_in : ∀ z ∈ closedBall x_bar R0, ((g z : ℝ) : EReal) = min (f z) (L : EReal) := by
    intro z hz
    rw [hg_def z, if_pos hz]
    exact EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top L) (min_le_right _ _))
      (ne_bot_of_gt (lt_min (hlow z hz) hLlow))
  have hg_out : ∀ z ∉ closedBall x_bar R0, g z = L := by
    intro z hz
    rw [hg_def z, if_neg hz]
  have hg_le_L : ∀ z, g z ≤ L := by
    intro z
    by_cases hz : z ∈ closedBall x_bar R0
    · have h2 : ((g z : ℝ) : EReal) ≤ (L : EReal) := by
        rw [hg_in z hz]; exact min_le_right _ _
      exact EReal.coe_le_coe_iff.1 h2
    · rw [hg_out z hz]
  have hg_le_f : ∀ z ∈ closedBall x_bar R0, ((g z : ℝ) : EReal) ≤ f z := by
    intro z hz
    rw [hg_in z hz]
    exact min_le_left _ _
  have hm : ∀ z, a - η ≤ g z := by
    intro z
    by_cases hz : z ∈ closedBall x_bar R0
    · have h2 : ((a - η : ℝ) : EReal) < ((g z : ℝ) : EReal) := by
        rw [hg_in z hz]; exact lt_min (hlow z hz) hLlow
      exact (EReal.coe_lt_coe_iff.1 h2).le
    · rw [hg_out z hz, hL_def]; linarith
  have hg_lsc : LowerSemicontinuous g := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro y
    by_cases hy : L ≤ y
    · have : g ⁻¹' Set.Iic y = Set.univ := by
        ext z
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
        exact (hg_le_L z).trans hy
      rw [this]; exact isClosed_univ
    · push_neg at hy
      have : g ⁻¹' Set.Iic y =
          closedBall x_bar R0 ∩ {x | x ∈ closedBall x_bar ε ∧ f x ≤ (y : EReal)} := by
        ext z
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · intro hz
          by_cases hzR : z ∈ closedBall x_bar R0
          · refine ⟨hzR, closedBall_subset_closedBall hR0ε hzR, ?_⟩
            have h2 : min (f z) (L : EReal) ≤ (y : EReal) := by
              rw [← hg_in z hzR]; exact EReal.coe_le_coe_iff.2 hz
            rcases min_le_iff.1 h2 with h3 | h3
            · exact h3
            · exact absurd (EReal.coe_le_coe_iff.1 h3) (not_le.2 hy)
          · rw [hg_out z hzR] at hz; linarith
        · rintro ⟨hzR, -, hfz⟩
          exact EReal.coe_le_coe_iff.1 ((hg_le_f z hzR).trans hfz)
      rw [this]
      exact isClosed_closedBall.inter (hclosed y (by rw [← hL_def]; exact hy.le))
  -- choose ρ
  obtain ⟨K, hK_def⟩ : ∃ K : ℝ, K = (1 + ‖w_bar‖ + δ) * (1 + |β|) := ⟨_, rfl⟩
  have hK : 0 < K := by rw [hK_def]; positivity
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ : ℝ, ρ = R0 / K := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρ_def]; exact div_pos hR0 hK
  have hρK : ρ * K = R0 := by rw [hρ_def]; exact div_mul_cancel₀ R0 hK.ne'
  have hρ1 : ρ * (1 + ‖w_bar‖ + δ) ≤ R0 := by
    rw [← hρK, hK_def]
    nlinarith [mul_nonneg (mul_nonneg hρ.le (by positivity : (0:ℝ) ≤ 1 + ‖w_bar‖ + δ))
      (abs_nonneg β)]
  have hρ2 : ρ * (1 + |β|) ≤ R0 := by
    rw [← hρK, hK_def]
    nlinarith [mul_nonneg (mul_nonneg hρ.le (by positivity : (0:ℝ) ≤ 1 + |β|))
      (add_nonneg (norm_nonneg w_bar) hδ.le)]
  refine ⟨ρ, hρ, ?_⟩
  intro x τ hx hτ hτρ hfx1 hfx2 hβ
  rw [ha, ← EReal.coe_sub] at hfx1
  rw [ha, ← EReal.coe_add] at hfx2
  obtain ⟨b, hb⟩ : ∃ b : ℝ, f x = (b : EReal) :=
    ⟨(f x).toReal, (EReal.coe_toReal (ne_top_of_lt hfx2) (ne_bot_of_gt hfx1)).symm⟩
  rw [hb, EReal.coe_lt_coe_iff] at hfx1 hfx2
  have hxR : x ∈ closedBall x_bar R0 := by
    rw [mem_closedBall]
    nlinarith [mul_nonneg hρ.le (add_nonneg (norm_nonneg w_bar) hδ.le)]
  have hbL : b ≤ L := by
    rw [hL_def]
    nlinarith [mul_nonneg hρ.le (abs_nonneg β)]
  have hgx : g x = b := by
    have h1 := hg_in x hxR
    rw [hb, min_eq_left (EReal.coe_le_coe_iff.2 hbL)] at h1
    exact_mod_cast h1
  have hx0 : dist x x_bar + τ * (‖w_bar‖ + δ) < R0 := by
    have : τ * (‖w_bar‖ + δ) ≤ ρ * (‖w_bar‖ + δ) :=
      mul_le_mul_of_nonneg_right hτρ.le (by positivity)
    nlinarith
  have hτβ : τ * |β| ≤ ρ * |β| := mul_le_mul_of_nonneg_right hτρ.le (abs_nonneg β)
  have hY : ∀ w ∈ closedBall w_bar δ, g x + τ * β < g (x + τ • w) := by
    intro w hw
    have hβw : (β : EReal) < delta f x τ w :=
      lt_of_lt_of_le hβ (sInf_le (Set.mem_image_of_mem _ hw))
    simp only [delta, differenceQuotient] at hβw
    rw [EReal.lt_div_iff (EReal.coe_pos.2 hτ) (EReal.coe_ne_top τ), hb,
      EReal.lt_sub_iff_add_lt (Or.inl (EReal.coe_ne_bot b)) (Or.inl (EReal.coe_ne_top b)),
      ← EReal.coe_mul, ← EReal.coe_add] at hβw
    have hxw : x + τ • w ∈ closedBall x_bar R0 := by
      rw [mem_closedBall]
      calc dist (x + τ • w) x_bar ≤ dist x x_bar + ‖τ • w‖ := by
            rw [dist_eq_norm, dist_eq_norm]
            calc ‖x + τ • w - x_bar‖ = ‖(x - x_bar) + τ • w‖ := by congr 1; abel
            _ ≤ ‖x - x_bar‖ + ‖τ • w‖ := norm_add_le _ _
        _ = dist x x_bar + τ * ‖w‖ := by rw [norm_smul, Real.norm_of_nonneg hτ.le]
        _ ≤ dist x x_bar + τ * (‖w_bar‖ + δ) := by
            gcongr; exact norm_le_of_mem_closedBall hw
        _ ≤ R0 := hx0.le
    have h1 := hg_in _ hxw
    have hββ : β * τ ≤ |β| * τ := mul_le_mul_of_nonneg_right (le_abs_self β) hτ.le
    have h2 : ((β * τ + b : ℝ) : EReal) < min (f (x + τ • w)) (L : EReal) := by
      refine lt_min hβw (EReal.coe_lt_coe_iff.2 ?_)
      rw [hL_def]
      nlinarith
    rw [← h1, EReal.coe_lt_coe_iff] at h2
    rw [hgx]; linarith
  obtain ⟨z, ζ, M, hM, hz, hgz, hsub, hζ⟩ :=
    Lcore_mvi g hg_lsc x_bar R0 (a - η) hm x w_bar δ τ β hδ hτ hx0 hY
  have hzR : z ∈ closedBall x_bar R0 := ball_subset_closedBall (mem_ball.2 hz)
  have hgzL : g z < a + R0 := by
    rw [hgx] at hgz
    nlinarith
  have hfz_eq : f z = ((g z : ℝ) : EReal) := by
    have h1 := hg_in z hzR
    have h2 : f z < (L : EReal) := by
      have h3 : ((g z : ℝ) : EReal) < (L : EReal) :=
        EReal.coe_lt_coe_iff.2 (by rw [hL_def]; linarith)
      rw [h1] at h3
      rcases min_lt_iff.1 h3 with h4 | h4
      · exact h4
      · exact absurd h4 (lt_irrefl _)
    rw [h1, min_eq_left h2.le]
  refine ⟨z, ζ, ?_, ?_, ?_, ?_, hζ⟩
  · linarith
  · rw [ha, ← EReal.coe_sub]; exact hlow z hzR
  · rw [ha, ← EReal.coe_add, hfz_eq, EReal.coe_lt_coe_iff]; linarith
  · refine ⟨by rw [hfz_eq]; exact EReal.bot_lt_coe _, by rw [hfz_eq]; exact EReal.coe_lt_top _,
      fun y => -(M * ‖y - z‖ ^ 2), ?_, ball x_bar R0, isOpen_ball.mem_nhds (mem_ball.2 hz), ?_⟩
    · rw [Asymptotics.isLittleO_iff]
      intro c hc
      filter_upwards [ball_mem_nhds z (div_pos hc (by linarith : (0:ℝ) < M + 1))] with y hy
      rw [mem_ball, dist_eq_norm] at hy
      rw [norm_neg, Real.norm_of_nonneg (mul_nonneg hM (sq_nonneg _)), norm_norm]
      have h1 : M * ‖y - z‖ ≤ c := by
        have h2 : M * ‖y - z‖ ≤ M * (c / (M + 1)) := mul_le_mul_of_nonneg_left hy.le hM
        have h3 : M * (c / (M + 1)) ≤ c := by
          rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
        linarith
      nlinarith [norm_nonneg (y - z)]
    · intro y hy
      rw [hfz_eq, ← EReal.coe_add]
      refine le_trans ?_ (hg_le_f y (ball_subset_closedBall hy))
      rw [EReal.coe_le_coe_iff]
      have := hsub y hy
      linarith

lemma L6b_aux_step (f : E → EReal) (x_bar w_bar : E) (δ β : ℝ) (hδ : 0 < δ)
    (hlsc : LocalLscAt f x_bar)
    (hfreq : ∃ᶠ p in fApproach f x_bar ×ˢ 𝓝[>] (0 : ℝ),
      (β : EReal) < sInf ((delta f p.1 p.2) '' closedBall w_bar δ))
    (η : ℝ) (hη : 0 < η) :
    ∃ z ζ : E, dist z x_bar < η ∧ f x_bar - ((η : ℝ) : EReal) < f z ∧
      f z < f x_bar + ((η : ℝ) : EReal) ∧
      IsRegularSubgradientAt f z ζ ∧ ∀ w ∈ closedBall w_bar δ, β ≤ inner ℝ ζ w := by
  obtain ⟨ρ, hρ, hstep⟩ := L6s_mvi_step f x_bar w_bar δ β hδ hlsc η hη
  set a : ℝ := (f x_bar).toReal with ha_def
  have ha : f x_bar = (a : EReal) := (EReal.coe_toReal hlsc.2.1.ne hlsc.1.ne').symm
  have hA : ∀ᶠ x in fApproach f x_bar, dist x x_bar < ρ :=
    (inf_le_left : fApproach f x_bar ≤ 𝓝 x_bar) (Metric.ball_mem_nhds x_bar hρ)
  have hIoo : Set.Ioo (f x_bar - ((ρ : ℝ) : EReal)) (f x_bar + ((ρ : ℝ) : EReal))
      ∈ 𝓝 (f x_bar) := by
    apply Ioo_mem_nhds
    · rw [ha, ← EReal.coe_sub, EReal.coe_lt_coe_iff]; linarith
    · rw [ha, ← EReal.coe_add, EReal.coe_lt_coe_iff]; linarith
  have hB : ∀ᶠ x in fApproach f x_bar,
      f x_bar - ((ρ : ℝ) : EReal) < f x ∧ f x < f x_bar + ((ρ : ℝ) : EReal) :=
    (inf_le_right : fApproach f x_bar ≤ Filter.comap f (𝓝 (f x_bar)))
      (Filter.Eventually.comap hIoo f)
  have hC : ∀ᶠ τ in 𝓝[>] (0 : ℝ), 0 < τ ∧ τ < ρ :=
    Ioo_mem_nhdsGT hρ
  have h3 := (hA.and hB).prod_mk hC
  obtain ⟨p, hp1, hp2⟩ := (hfreq.and_eventually h3).exists
  exact hstep p.1 p.2 hp2.1.1 hp2.2.1 hp2.2.2 hp2.1.2.1 hp2.1.2.2 hp1

-- L6b: sequences from the mean value argument
lemma L6b_mvi_seq (f : E → EReal) (x_bar w_bar : E) (δ β : ℝ) (hδ : 0 < δ)
    (hlsc : LocalLscAt f x_bar)
    (hfreq : ∃ᶠ p in fApproach f x_bar ×ˢ 𝓝[>] (0 : ℝ),
      (β : EReal) < sInf ((delta f p.1 p.2) '' closedBall w_bar δ)) :
    ∃ z ζ : ℕ → E, Tendsto z atTop (𝓝 x_bar) ∧
      Tendsto (fun n => f (z n)) atTop (𝓝 (f x_bar)) ∧
      (∀ n, IsRegularSubgradientAt f (z n) (ζ n)) ∧
      ∀ n, ∀ w ∈ closedBall w_bar δ, β ≤ inner ℝ (ζ n) w := by
  have hη : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have key := fun n : ℕ => L6b_aux_step f x_bar w_bar δ β hδ hlsc hfreq _ (hη n)
  choose z ζ hdist hlo hhi hreg hζ using key
  set a : ℝ := (f x_bar).toReal with ha_def
  have ha : f x_bar = (a : EReal) := (EReal.coe_toReal hlsc.2.1.ne hlsc.1.ne').symm
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨z, ζ, ?_, ?_, hreg, hζ⟩
  · rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hdist n).le) h0
  · have hlo' : Tendsto (fun n : ℕ => (((a - 1 / ((n : ℝ) + 1)) : ℝ) : EReal)) atTop
        (𝓝 (f x_bar)) := by
      rw [ha, EReal.tendsto_coe]
      simpa using (tendsto_const_nhds (x := a)).sub h0
    have hhi' : Tendsto (fun n : ℕ => (((a + 1 / ((n : ℝ) + 1)) : ℝ) : EReal)) atTop
        (𝓝 (f x_bar)) := by
      rw [ha, EReal.tendsto_coe]
      simpa using (tendsto_const_nhds (x := a)).add h0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo' hhi' (fun n => ?_) (fun n => ?_)
    · have := (hlo n).le
      rw [ha, ← EReal.coe_sub] at this
      exact this
    · have := (hhi n).le
      rw [ha, ← EReal.coe_add] at this
      exact this

-- L6c: compactness and contradiction
omit [FiniteDimensional ℝ E] in
lemma L6c_aux_bound (w_bar ζ : E) (δ β : ℝ) (hδ : 0 < δ)
    (hζ : ∀ w ∈ closedBall w_bar δ, β ≤ inner ℝ ζ w) :
    β + δ * ‖ζ‖ ≤ inner ℝ ζ w_bar := by
  by_cases h0 : ζ = 0
  · subst h0
    have := hζ w_bar (mem_closedBall_self hδ.le)
    simpa using this
  · have hn : 0 < ‖ζ‖ := norm_pos_iff.mpr h0
    have hw : w_bar - (δ / ‖ζ‖) • ζ ∈ closedBall w_bar δ := by
      rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_pos (div_pos hδ hn), div_mul_cancel₀ _ hn.ne']
    have h1 := hζ _ hw
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at h1
    have h2 : δ / ‖ζ‖ * ‖ζ‖ ^ 2 = δ * ‖ζ‖ := by field_simp
    linarith

lemma L6c_contra (f : E → EReal) (x_bar w_bar : E) (δ β : ℝ) (hδ : 0 < δ)
    (hfx : ⊥ < f x_bar ∧ f x_bar < ⊤)
    (hsub : subdifferential f x_bar ⊆ regularSubdifferential f x_bar)
    (hhor : horizonSubdifferential f x_bar ⊆ horizonCone (regularSubdifferential f x_bar))
    (hC : ∀ v ∈ regularSubdifferential f x_bar, inner ℝ v w_bar < β)
    (z ζ : ℕ → E) (hz : Tendsto z atTop (𝓝 x_bar))
    (hfz : Tendsto (fun n => f (z n)) atTop (𝓝 (f x_bar)))
    (hreg : ∀ n, IsRegularSubgradientAt f (z n) (ζ n))
    (hζ : ∀ n, ∀ w ∈ closedBall w_bar δ, β ≤ inner ℝ (ζ n) w) : False := by
  set b : ℕ → E := fun n => (1 + ‖ζ n‖)⁻¹ • ζ n with hb_def
  have hpos : ∀ n, 0 < 1 + ‖ζ n‖ := fun n => by positivity
  have hbnorm : ∀ n, ‖b n‖ = 1 - (1 + ‖ζ n‖)⁻¹ := by
    intro n
    simp only [hb_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hpos n)]
    field_simp
    ring
  have hbmem : ∀ n, b n ∈ closedBall (0 : E) 1 := by
    intro n
    rw [mem_closedBall_zero_iff, hbnorm n]
    have := inv_pos.mpr (hpos n)
    linarith
  obtain ⟨B, hBmem, ψ, hψ, hψlim⟩ := (isCompact_closedBall (0 : E) 1).tendsto_subseq hbmem
  have hψtop : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  have hBn : ‖B‖ ≤ 1 := by simpa using hBmem
  have ha_lim : Tendsto (fun n => (1 + ‖ζ (ψ n)‖)⁻¹) atTop (𝓝 (1 - ‖B‖)) := by
    have h1 : Tendsto (fun n => ‖b (ψ n)‖) atTop (𝓝 ‖B‖) := hψlim.norm
    have h2 : Tendsto (fun n => 1 - ‖b (ψ n)‖) atTop (𝓝 (1 - ‖B‖)) :=
      tendsto_const_nhds.sub h1
    refine h2.congr (fun n => ?_)
    rw [hbnorm]; ring
  have hzψ : Tendsto (z ∘ ψ) atTop (𝓝 x_bar) := hz.comp hψtop
  have hfzψ : Tendsto (fun n => f ((z ∘ ψ) n)) atTop (𝓝 (f x_bar)) := hfz.comp hψtop
  rcases lt_or_eq_of_le hBn with hlt | heq
  · -- bounded case
    have hA : 0 < 1 - ‖B‖ := by linarith
    have hζlim : Tendsto (ζ ∘ ψ) atTop (𝓝 ((1 - ‖B‖)⁻¹ • B)) := by
      have h3 : Tendsto (fun n => ((1 + ‖ζ (ψ n)‖)⁻¹)⁻¹) atTop (𝓝 ((1 - ‖B‖)⁻¹)) :=
        ha_lim.inv₀ hA.ne'
      have h4 := h3.smul hψlim
      refine h4.congr (fun n => ?_)
      simp only [Function.comp, hb_def, smul_smul]
      rw [inv_mul_cancel₀ (inv_pos.mpr (hpos (ψ n))).ne', one_smul]
    have hv : (1 - ‖B‖)⁻¹ • B ∈ subdifferential f x_bar :=
      ⟨hfx.1, hfx.2, z ∘ ψ, ζ ∘ ψ, hzψ, hfzψ, hζlim, fun i => hreg (ψ i)⟩
    have hlt2 := hC _ (hsub hv)
    have hge : β ≤ inner ℝ ((1 - ‖B‖)⁻¹ • B) w_bar := by
      have h5 : Tendsto (fun n => inner ℝ ((ζ ∘ ψ) n) w_bar) atTop
          (𝓝 (inner ℝ ((1 - ‖B‖)⁻¹ • B) w_bar)) :=
        hζlim.inner tendsto_const_nhds
      exact ge_of_tendsto' h5 (fun n => hζ (ψ n) w_bar (mem_closedBall_self hδ.le))
    linarith
  · -- unbounded case
    have hl : Tendsto (fun n => (1 + ‖ζ (ψ n)‖)⁻¹) atTop (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall (fun n => inv_pos.mpr (hpos _))⟩
      simpa [heq] using ha_lim
    have hBh : B ∈ horizonSubdifferential f x_bar :=
      ⟨hfx.1, hfx.2, z ∘ ψ, ζ ∘ ψ, fun n => (1 + ‖ζ (ψ n)‖)⁻¹, hzψ, hfzψ, hl, hψlim,
        fun n => hreg (ψ n)⟩
    obtain ⟨c, l', hc, hl', hlc⟩ := hhor hBh
    have hle : inner ℝ B w_bar ≤ 0 := by
      have h6 : Tendsto (fun k => inner ℝ (l' k • c k) w_bar) atTop (𝓝 (inner ℝ B w_bar)) :=
        hlc.inner tendsto_const_nhds
      have h7 : Tendsto (fun k => l' k * β) atTop (𝓝 (0 * β)) :=
        (tendsto_nhdsWithin_iff.mp hl').1.mul_const β
      have h8 : ∀ᶠ k in atTop, inner ℝ (l' k • c k) w_bar ≤ l' k * β := by
        filter_upwards [(tendsto_nhdsWithin_iff.mp hl').2] with k hk
        rw [real_inner_smul_left]
        exact mul_le_mul_of_nonneg_left (hC _ (hc k)).le (le_of_lt hk)
      have := le_of_tendsto_of_tendsto h6 h7 h8
      simpa using this
    have hge : δ ≤ inner ℝ B w_bar := by
      have hbound : ∀ n, (1 + ‖ζ n‖)⁻¹ * β + δ * ‖b n‖ ≤ inner ℝ (b n) w_bar := by
        intro n
        have h := L6c_aux_bound w_bar (ζ n) δ β hδ (hζ n)
        have hapos := inv_pos.mpr (hpos n)
        simp only [hb_def, norm_smul, real_inner_smul_left, norm_inv, Real.norm_eq_abs,
          abs_of_pos (hpos n)]
        nlinarith
      have h9 : Tendsto (fun n => inner ℝ (b (ψ n)) w_bar - (1 + ‖ζ (ψ n)‖)⁻¹ * β
          - δ * ‖b (ψ n)‖) atTop (𝓝 (inner ℝ B w_bar - (1 - ‖B‖) * β - δ * ‖B‖)) :=
        ((hψlim.inner tendsto_const_nhds).sub (ha_lim.mul_const β)).sub
          (hψlim.norm.const_mul δ)
      have h10 : (0 : ℝ) ≤ inner ℝ B w_bar - (1 - ‖B‖) * β - δ * ‖B‖ :=
        ge_of_tendsto' h9 (fun n => by have := hbound (ψ n); linarith)
      rw [heq] at h10
      linarith
    linarith

lemma L6_regSubderiv_le_subderiv (f : E → EReal) (x_bar : E)
    (hfx : ⊥ < f x_bar ∧ f x_bar < ⊤) (hlsc : LocalLscAt f x_bar)
    (hsub : subdifferential f x_bar = regularSubdifferential f x_bar)
    (hhor : horizonSubdifferential f x_bar = horizonCone (regularSubdifferential f x_bar))
    (w : E) : regularSubderivative f x_bar w ≤ subderivative f x_bar w := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨β, hβ1, hβ2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have hC : ∀ v ∈ regularSubdifferential f x_bar, inner ℝ v w < β := fun v hv =>
    EReal.coe_lt_coe_iff.1 ((L1_regSub_inner_le_subderiv f x_bar v hv w).trans_lt hβ1)
  obtain ⟨δ, hδ, hfreq⟩ := L6a_extract f x_bar w β hβ2
  obtain ⟨z, ζ, hz, hfz, hreg, hζ⟩ := L6b_mvi_seq f x_bar w δ β hδ hlsc hfreq
  exact L6c_contra f x_bar w δ β hδ hfx hsub.le hhor.le hC z ζ hz hfz hreg hζ

-- L7: regular subgradients are subgradients
lemma L7_reg_sub (f : E → EReal) (x_bar v : E)
    (hv : IsRegularSubgradientAt f x_bar v) : v ∈ subdifferential f x_bar := by
  exact ⟨hv.1, hv.2.1, fun _ => x_bar, fun _ => v, tendsto_const_nhds, tendsto_const_nhds,
    tendsto_const_nhds, fun _ => hv⟩

-- L8: horizon cone of regular subgradients is in the horizon subdifferential
lemma L8_cone_horizon (f : E → EReal) (x_bar : E) (hfx : ⊥ < f x_bar ∧ f x_bar < ⊤)
    (v : E) (hv : v ∈ horizonCone (regularSubdifferential f x_bar)) :
    v ∈ horizonSubdifferential f x_bar := by
  obtain ⟨xseq, l, hmem, hl, hlim⟩ := hv
  exact ⟨hfx.1, hfx.2, fun _ => x_bar, xseq, l, tendsto_const_nhds, tendsto_const_nhds, hl, hlim,
    hmem⟩

-- L9: under regularity, horizon subgradients lie in the horizon cone
lemma L9_horizon_sub_cone (f : E → EReal) (x_bar : E) (hfx : ⊥ < f x_bar ∧ f x_bar < ⊤)
    (heq : ∀ w, subderivative f x_bar w = regularSubderivative f x_bar w)
    (u : E) (hu : u ∈ regularSubdifferential f x_bar)
    (v : E) (hv : v ∈ horizonSubdifferential f x_bar) :
    v ∈ horizonCone (regularSubdifferential f x_bar) := by
  have hmem : ∀ n : ℕ, u + ((n : ℝ) + 1) • v ∈ regularSubdifferential f x_bar := by
    intro n
    apply L2_regSub_of_inner_le f x_bar _ hfx.1 hfx.2
    intro w
    by_cases htop : subderivative f x_bar w = ⊤
    · rw [htop]; exact le_top
    · have hlt : regularSubderivative f x_bar w < ⊤ := by
        rw [← heq w]; exact lt_top_iff_ne_top.2 htop
      have h5 := L5_horizon_inner_nonpos f x_bar v hv w hlt
      have h1 := L1_regSub_inner_le_subderiv f x_bar u hu w
      refine le_trans ?_ h1
      rw [EReal.coe_le_coe_iff, inner_add_left, real_inner_smul_left]
      have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      nlinarith
  refine ⟨fun n => u + ((n : ℝ) + 1) • v, fun n => 1 / ((n : ℝ) + 1), hmem, ?_, ?_⟩
  · rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Filter.Eventually.of_forall (fun n => by simp only [Set.mem_Ioi]; positivity)
  · have hfun : (fun n : ℕ => (1 / ((n : ℝ) + 1)) • (u + ((n : ℝ) + 1) • v)) =
        fun n : ℕ => (1 / ((n : ℝ) + 1)) • u + v := by
      funext n
      rw [smul_add, smul_smul]
      have hne : (n : ℝ) + 1 ≠ 0 := by positivity
      rw [one_div_mul_cancel hne, one_smul]
    rw [hfun]
    have h0 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) • u) atTop (𝓝 ((0 : ℝ) • u)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.smul tendsto_const_nhds
    rw [zero_smul] at h0
    have h1 := h0.add (tendsto_const_nhds : Tendsto (fun _ : ℕ => v) atTop (𝓝 v))
    rw [zero_add] at h1
    exact h1





theorem RW_chap_8_11
  (f : E → EReal)
  (x_bar : E)
  (hx_bar : ⊥ < f x_bar ∧ f x_bar < ⊤)
  (hx_bar_subdiff : Set.Nonempty (subdifferential f x_bar)) :
  IsRegularAt f x_bar ↔
  LocalLscAt f x_bar ∧
    subdifferential f x_bar = regularSubdifferential f x_bar ∧
    horizonSubdifferential f x_bar =
      horizonCone (regularSubdifferential f x_bar) := by
  constructor
  · rintro ⟨-, hlsc, heq⟩
    have hsub : subdifferential f x_bar = regularSubdifferential f x_bar := by
      apply Set.Subset.antisymm
      · intro v hv
        apply L2_regSub_of_inner_le f x_bar v hx_bar.1 hx_bar.2
        intro w
        rw [heq w]
        exact L4_subgrad_inner_le_regSubderiv f x_bar v hv w
      · intro v hv
        exact L7_reg_sub f x_bar v hv
    refine ⟨hlsc, hsub, ?_⟩
    obtain ⟨u, hu⟩ := hx_bar_subdiff
    rw [hsub] at hu
    apply Set.Subset.antisymm
    · intro v hv
      exact L9_horizon_sub_cone f x_bar hx_bar heq u hu v hv
    · intro v hv
      exact L8_cone_horizon f x_bar hx_bar v hv
  · rintro ⟨hlsc, hsub, hhor⟩
    refine ⟨hx_bar, hlsc, fun w => le_antisymm ?_ ?_⟩
    · exact L3_subderiv_le_regSubderiv f x_bar w
    · exact L6_regSubderiv_le_subderiv f x_bar hx_bar hlsc hsub hhor w

end RW_chap_8_11
