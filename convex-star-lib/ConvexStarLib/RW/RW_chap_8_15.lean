import ConvexStarLib.Defs

/-!
# `RW_chap_8_15`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_8_15` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_8_15`, so the main result is `RW_chap_8_15.RW_chap_8_15`.
-/

namespace RW_chap_8_15

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma p3_tendsto_line {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x d : E) : Filter.Tendsto (fun t : ℝ => x + t • d) (𝓝[>] (0:ℝ)) (𝓝 x) := by
  have : Filter.Tendsto (fun t : ℝ => x + t • d) (𝓝 0) (𝓝 (x + (0:ℝ) • d)) :=
    ((continuous_const.add (continuous_id.smul continuous_const)).tendsto 0)
  rw [zero_smul, add_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

lemma p3_littleo_core {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {r : E → ℝ} {x : E} (hr : r =o[𝓝 x] (fun y => ‖y - x‖)) (d : E) (c : ℝ)
    (h : ∀ᶠ t in 𝓝[>] (0:ℝ), t * c ≤ |r (x + t • d)|) : c ≤ 0 := by
  by_contra hc
  push_neg at hc
  set γ : ℝ := c / (‖d‖ + 1) with hγ
  have hd1 : 0 < ‖d‖ + 1 := by positivity
  have hγpos : 0 < γ := div_pos hc hd1
  have hγd : γ * (‖d‖ + 1) = c := by rw [hγ]; field_simp
  have h1 := hr.def hγpos
  have h2 := (p3_tendsto_line x d).eventually h1
  obtain ⟨t, ⟨ht1, ht2⟩, ht3'⟩ := ((h.and h2).and self_mem_nhdsWithin).exists
  have ht3 : 0 < t := ht3'
  have e : ‖‖x + t • d - x‖‖ = t * ‖d‖ := by
    rw [norm_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht3]
  rw [e, Real.norm_eq_abs] at ht2
  have h3 : t * c ≤ t * (γ * ‖d‖) := by linarith
  have h4 : c ≤ γ * ‖d‖ := le_of_mul_le_mul_left h3 ht3
  nlinarith

lemma p3_epi_comb {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → EReal} (hf : ConvexEReal f) {x z : E} {a b : ℝ}
    (hx : f x ≤ (b : EReal)) (hz : f z ≤ (a : EReal)) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f (x + t • (z - x)) ≤ (((1 - t) * b + t * a : ℝ) : EReal) := by
  have hxm : (x, b) ∈ epigraph f := hx
  have hzm : (z, a) ∈ epigraph f := hz
  have hmem := hf hxm hzm (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
  have heq : x + t • (z - x) = (1 - t) • x + t • z := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [heq]
  exact hmem

lemma p3_regSub_global {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → EReal} (hf : ConvexEReal f) {x v : E}
    (hv : IsRegularSubgradientAt f x v) (z : E) {a : ℝ} (ha : f z = a) :
    (f x).toReal + inner ℝ v (z - x) ≤ a := by
  obtain ⟨hxbot, hxtop, r, hr, V, hV, hineq⟩ := hv
  set b := (f x).toReal with hb_def
  have hb : f x = (b : EReal) := (EReal.coe_toReal hxtop.ne hxbot.ne').symm
  have key : inner ℝ v (z - x) - (a - b) ≤ 0 := by
    apply p3_littleo_core hr (z - x)
    filter_upwards [(p3_tendsto_line x (z - x)).eventually hV,
      Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t htV ht
    obtain ⟨ht0, ht1⟩ := ht
    have h1 := hineq _ htV
    have h2 := p3_epi_comb hf (le_of_eq hb) (le_of_eq ha) ht0.le ht1.le
    have h3 := le_trans h1 h2
    rw [hb, ← EReal.coe_add, EReal.coe_le_coe_iff] at h3
    simp only [add_sub_cancel_left, real_inner_smul_right] at h3
    have := neg_abs_le (r (x + t • (z - x)))
    linarith
  linarith

lemma p3_regNormal_global {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : Set E} (hC : Convex ℝ C) {y v : E} (hv : v ∈ regularNormalCone C y) {z : E}
    (hz : z ∈ C) : inner ℝ v (z - y) ≤ 0 := by
  obtain ⟨hyC, r, hr, V, hV, hineq⟩ := hv
  apply p3_littleo_core hr (z - y)
  filter_upwards [(p3_tendsto_line y (z - y)).eventually hV,
    Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t htV ht
  obtain ⟨ht0, ht1⟩ := ht
  have hmem : y + t • (z - y) ∈ C := hC.add_smul_sub_mem hyC hz ⟨ht0.le, ht1.le⟩
  have h1 := hineq _ htV hmem
  simp only [add_sub_cancel_left, real_inner_smul_right] at h1
  exact le_trans h1 (le_abs_self _)

lemma p3_subdiff_global {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → EReal} (hf : ConvexEReal f) {x v : E}
    (hv : v ∈ subdifferential f x) (z : E) {a : ℝ} (ha : f z = a) :
    (f x).toReal + inner ℝ v (z - x) ≤ a := by
  obtain ⟨hxbot, hxtop, xs, vs, hxs, hfxs, hvs, hreg⟩ := hv
  have h1 : ∀ k, (f (xs k)).toReal + inner ℝ (vs k) (z - xs k) ≤ a := fun k =>
    p3_regSub_global hf (hreg k) z ha
  have h2 : Filter.Tendsto (fun k => (f (xs k)).toReal) Filter.atTop (𝓝 (f x).toReal) :=
    (EReal.tendsto_toReal hxtop.ne hxbot.ne').comp hfxs
  have h3 : Filter.Tendsto (fun k => (f (xs k)).toReal + inner ℝ (vs k) (z - xs k))
      Filter.atTop (𝓝 ((f x).toReal + inner ℝ v (z - x))) :=
    h2.add (hvs.inner (tendsto_const_nhds.sub hxs))
  exact le_of_tendsto' h3 h1

lemma p3_normal_global {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : Set E} (hC : Convex ℝ C) {x n : E} (hn : n ∈ normalCone C x) {z : E} (hz : z ∈ C) :
    inner ℝ n (z - x) ≤ 0 := by
  obtain ⟨xs, ns, hxs, hns, hreg⟩ := hn
  have h1 : ∀ k, inner ℝ (ns k) (z - xs k) ≤ 0 := fun k => p3_regNormal_global hC (hreg k) hz
  have h3 : Filter.Tendsto (fun k => inner ℝ (ns k) (z - xs k)) Filter.atTop
      (𝓝 (inner ℝ n (z - x))) :=
    hns.inner (tendsto_const_nhds.sub hxs)
  exact le_of_tendsto' h3 h1

lemma p3_subderiv_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → EReal} (hf : ConvexEReal f) (hbot : ∀ y, ⊥ < f y) {x z : E} {a b : ℝ}
    (hb : f x = b) (ha : f z = a) :
    subderivative f x (z - x) ≤ ((a - b : ℝ) : EReal) := by
  unfold subderivative
  apply Filter.liminf_le_of_frequently_le'
  have hev : ∀ᶠ p in 𝓝[>] (0:ℝ) ×ˢ pure (z - x),
      differenceQuotient f x p.2 p.1 ≤ ((a - b : ℝ) : EReal) := by
    rw [Filter.prod_pure, Filter.eventually_map]
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have h2 := p3_epi_comb hf (le_of_eq hb) (le_of_eq ha) ht0.le ht1.le
    have hne_top : f (x + t • (z - x)) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h2
    obtain ⟨c, hc⟩ : ∃ c : ℝ, f (x + t • (z - x)) = c :=
      ⟨_, (EReal.coe_toReal hne_top (hbot _).ne').symm⟩
    rw [hc, EReal.coe_le_coe_iff] at h2
    show (f (x + t • (z - x)) - f x) / (t : EReal) ≤ ((a - b : ℝ) : EReal)
    rw [hc, hb, ← EReal.coe_sub, ← EReal.coe_div, EReal.coe_le_coe_iff, div_le_iff₀ ht0]
    linarith
  exact hev.frequently.filter_mono (Filter.prod_mono le_rfl (pure_le_nhds _))

theorem p3_main
  (f : E → EReal) (x_bar : E) (C : Set E) (hx_bar : x_bar ∈ C)
  (hf_proper : IsProper f) :
  ((ConvexEReal f ∧ Convex ℝ C ∧ ⊥ < f x_bar ∧ f x_bar < ⊤) →
    (((∃ v ∈ subdifferential f x_bar,
          ∃ n ∈ normalCone C x_bar,
            v + n = 0) ∨
        (∀ w ∈ posTangentConeAt C x_bar,
          0 ≤ subderivative f x_bar w)) →
      IsGloballyOptimal f C x_bar)) := by
  rintro ⟨hf, hC, hbot, htop⟩ h
  refine ⟨htop, fun z hz => ?_⟩
  by_cases hztop : f z = ⊤
  · rw [hztop]; exact le_top
  obtain ⟨a, ha⟩ : ∃ a : ℝ, f z = a :=
    ⟨(f z).toReal, (EReal.coe_toReal hztop (hf_proper.1 z).ne').symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, f x_bar = b :=
    ⟨(f x_bar).toReal, (EReal.coe_toReal htop.ne hbot.ne').symm⟩
  rw [ha, hb, EReal.coe_le_coe_iff]
  rcases h with ⟨v, hv, n, hn, hvn⟩ | h
  · have h1 := p3_subdiff_global hf hv z ha
    rw [hb, EReal.toReal_coe] at h1
    have h2 := p3_normal_global hC hn hz
    have hn' : n = -v := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hvn
    rw [hn', inner_neg_left] at h2
    linarith
  · have hw : z - x_bar ∈ posTangentConeAt C x_bar :=
      sub_mem_posTangentConeAt_of_segment_subset (hC.segment_subset hx_bar hz)
    have h1 := h _ hw
    have h2 := p3_subderiv_le hf hf_proper.1 hb ha
    have h3 := le_trans h1 h2
    have h4 : (0:ℝ) ≤ a - b := by exact_mod_cast h3
    linarith

lemma p2f_step1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : Set E} {x_bar n w : E} (hn : IsRegularNormalAt C x_bar n)
    (hw : w ∈ posTangentConeAt C x_bar) : inner ℝ n w ≤ 0 := by
  obtain ⟨_, r, hr, V, hV, hrV⟩ := hn
  obtain ⟨α, l, hl, c, d, hd0, hdC, hcd⟩ := exists_fun_of_mem_tangentConeAt hw
  have key : ∀ γ : ℝ, 0 < γ → inner ℝ n w ≤ γ * ‖w‖ := by
    intro γ hγ
    have h1 : ∀ᶠ y in 𝓝 x_bar, ‖r y‖ ≤ γ * ‖‖y - x_bar‖‖ := hr.def hγ
    have hxd : Filter.Tendsto (fun a => x_bar + d a) l (𝓝 x_bar) := by
      simpa using (tendsto_const_nhds (x := x_bar)).add hd0
    have h2 : ∀ᶠ a in l, inner ℝ n (c a • d a) ≤ γ * ‖c a • d a‖ := by
      filter_upwards [hxd.eventually h1, hxd.eventually hV, hdC] with a ha1 ha2 ha3
      have h4 := hrV _ ha2 ha3
      simp only [add_sub_cancel_left, norm_norm] at h4 ha1
      rw [NNReal.smul_def, inner_smul_right, norm_smul]
      have hc : (0:ℝ) ≤ (c a : ℝ) := (c a).2
      calc (c a : ℝ) * inner ℝ n (d a) ≤ (c a : ℝ) * (γ * ‖d a‖) := by
            apply mul_le_mul_of_nonneg_left _ hc
            exact h4.trans ((le_abs_self _).trans (by simpa using ha1))
        _ = γ * (‖(c a : ℝ)‖ * ‖d a‖) := by rw [Real.norm_of_nonneg hc]; ring
    have h3 : Filter.Tendsto (fun a => inner ℝ n (c a • d a)) l (𝓝 (inner ℝ n w)) :=
      (tendsto_const_nhds (x := n)).inner hcd
    have h4 : Filter.Tendsto (fun a => γ * ‖c a • d a‖) l (𝓝 (γ * ‖w‖)) :=
      (tendsto_const_nhds (x := γ)).mul hcd.norm
    exact le_of_tendsto_of_tendsto h3 h4 h2
  have hlim : Filter.Tendsto (fun γ : ℝ => γ * ‖w‖) (𝓝[>] 0) (𝓝 0) := by
    have : Filter.Tendsto (fun γ : ℝ => γ * ‖w‖) (𝓝 0) (𝓝 (0 * ‖w‖)) :=
      Filter.tendsto_id.mul_const _
    simpa using this.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun γ hγ => key γ hγ)

lemma p2f_local {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → EReal} {z u : E} (h : IsRegularSubgradientAt f z u) {ε R : ℝ}
    (hε : 0 < ε) (hR : 0 ≤ R) :
    ∃ T > 0, ∀ t : ℝ, 0 < t → t < T → ∀ w' : E, ‖w'‖ ≤ R →
      (((inner ℝ u w' - ε * R : ℝ)) : EReal) ≤ delta f z t w' := by
  obtain ⟨hbot, htop, r, hr, V, hV, hfV⟩ := h
  have h1 : ∀ᶠ y in 𝓝 z, ‖r y‖ ≤ ε * ‖‖y - z‖‖ := hr.def hε
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 (h1.and hV)
  refine ⟨ρ / (R + 1), by positivity, ?_⟩
  intro t ht htT w' hw'
  have hdist : dist (z + t • w') z < ρ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le]
    rw [lt_div_iff₀ (by linarith)] at htT
    calc t * ‖w'‖ ≤ t * R := mul_le_mul_of_nonneg_left hw' ht.le
      _ < ρ := by nlinarith
  obtain ⟨hr1, hV1⟩ := hball hdist
  have hineq := hfV _ hV1
  simp only [add_sub_cancel_left, norm_norm] at hineq hr1
  obtain ⟨a, ha⟩ : ∃ a : ℝ, f z = a := ⟨(f z).toReal, (EReal.coe_toReal htop.ne hbot.ne').symm⟩
  have hlow : (inner ℝ u w' - ε * R) * t ≤ inner ℝ u (t • w') + r (z + t • w') := by
    rw [inner_smul_right]
    have h5 : |r (z + t • w')| ≤ ε * (t * R) := by
      rw [← Real.norm_eq_abs]
      calc _ ≤ ε * ‖t • w'‖ := hr1
        _ ≤ ε * (t * R) := by
          rw [norm_smul, Real.norm_of_nonneg ht.le]
          gcongr
    have h6 := neg_abs_le (r (z + t • w'))
    nlinarith
  unfold delta differenceQuotient
  rw [ha] at hineq ⊢
  generalize f (z + t • w') = F at hineq ⊢
  induction F using EReal.rec with
  | bot =>
    exfalso
    rw [le_bot_iff, ← EReal.coe_add] at hineq
    exact EReal.coe_ne_bot _ hineq
  | coe b =>
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hineq
    rw [← EReal.coe_sub, ← EReal.coe_div, EReal.coe_le_coe_iff, le_div_iff₀ ht]
    linarith
  | top =>
    rw [EReal.top_sub_coe, EReal.top_div_of_pos_ne_top (by exact_mod_cast ht)
      (EReal.coe_ne_top _)]
    exact le_top

lemma p2f_step2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → EReal} {x_bar v : E} (hv : v ∈ subdifferential f x_bar) (w : E) :
    ((inner ℝ v w : ℝ) : EReal) ≤ regularSubderivative f x_bar w := by
  obtain ⟨hbot, htop, x, vseq, hx, hfx, hvseq, hreg⟩ := hv
  refine EReal.ge_of_forall_gt_iff_ge.1 ?_
  intro c hc
  have hc' : c < inner ℝ v w := EReal.coe_lt_coe_iff.1 hc
  set δ0 := (inner ℝ v w - c) / (‖v‖ + 1) with hδ0
  have hδ0pos : 0 < δ0 := div_pos (by linarith) (by positivity)
  refine Filter.le_limsup_of_frequently_le' ?_
  refine Filter.Eventually.frequently ?_
  filter_upwards [Ioo_mem_nhdsGT hδ0pos] with δ hδ
  obtain ⟨hδpos, hδlt⟩ := hδ
  refine Filter.le_limsup_of_frequently_le' ?_
  set R := ‖w‖ + δ with hR
  have hRnn : 0 ≤ R := by positivity
  have hloc : ∀ k : ℕ, ∃ T > 0, ∀ t : ℝ, 0 < t → t < T → ∀ w' : E, ‖w'‖ ≤ R →
      (((inner ℝ (vseq k) w' - (1 / ((k:ℝ) + 1)) * R : ℝ)) : EReal) ≤ delta f (x k) t w' :=
    fun k => p2f_local (hreg k) (by positivity) hRnn
  choose T hTpos hT using hloc
  set t : ℕ → ℝ := fun k => min (T k / 2) (1 / ((k:ℝ) + 1)) with ht_def
  have htpos : ∀ k, 0 < t k := fun k => lt_min (by linarith [hTpos k]) (by positivity)
  have htT : ∀ k, t k < T k := fun k => (min_le_left _ _).trans_lt (by linarith [hTpos k])
  have htle : ∀ k, t k ≤ 1 / ((k:ℝ) + 1) := fun k => min_le_right _ _
  have htend : Filter.Tendsto (fun k => (x k, t k)) Filter.atTop
      (fApproach f x_bar ×ˢ 𝓝[>] (0:ℝ)) := by
    apply Filter.Tendsto.prodMk
    · exact Filter.tendsto_inf.2 ⟨hx, Filter.tendsto_comap_iff.2 hfx⟩
    · refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall htpos⟩
      exact squeeze_zero (fun k => (htpos k).le) htle tendsto_one_div_add_atTop_nhds_zero_nat
  refine htend.frequently (Filter.Eventually.frequently ?_)
  have hL : Filter.Tendsto
      (fun k : ℕ => inner ℝ (vseq k) w - ‖vseq k‖ * δ - (1 / ((k:ℝ) + 1)) * R)
      Filter.atTop (𝓝 (inner ℝ v w - ‖v‖ * δ - 0 * R)) :=
    ((hvseq.inner tendsto_const_nhds).sub (hvseq.norm.mul_const δ)).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const R)
  have hgt : c < inner ℝ v w - ‖v‖ * δ - 0 * R := by
    have h7 : (‖v‖ + 1) * δ < inner ℝ v w - c := by
      rw [hδ0, lt_div_iff₀ (by positivity)] at hδlt
      linarith
    nlinarith [norm_nonneg v]
  filter_upwards [hL.eventually_const_lt hgt] with k hk
  apply le_sInf
  rintro _ ⟨w', hw', rfl⟩
  have hw'' : ‖w' - w‖ ≤ δ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hw'
  have hw'R : ‖w'‖ ≤ R := by
    calc ‖w'‖ = ‖w + (w' - w)‖ := by congr 1; abel
      _ ≤ ‖w‖ + ‖w' - w‖ := norm_add_le _ _
      _ ≤ R := by rw [hR]; linarith
  refine le_trans ?_ (hT k (t k) (htpos k) (htT k) w' hw'R)
  rw [EReal.coe_le_coe_iff]
  have hin : inner ℝ (vseq k) w - ‖vseq k‖ * δ ≤ inner ℝ (vseq k) w' := by
    have h1 : inner ℝ (vseq k) w' = inner ℝ (vseq k) w + inner ℝ (vseq k) (w' - w) := by
      rw [← inner_add_right]; congr 1; abel
    have h2 : |inner ℝ (vseq k) (w' - w)| ≤ ‖vseq k‖ * ‖w' - w‖ := abs_real_inner_le_norm _ _
    have h3 : ‖vseq k‖ * ‖w' - w‖ ≤ ‖vseq k‖ * δ :=
      mul_le_mul_of_nonneg_left hw'' (norm_nonneg _)
    have h4 := neg_abs_le (inner ℝ (vseq k) (w' - w))
    linarith
  linarith

theorem p2f_main
  (f : E → EReal) (x_bar : E) (C : Set E)
  (hreg : IsRegularAt f x_bar) (hCreg : IsRegularSetAt C x_bar) :
  (∃ v ∈ subdifferential f x_bar, ∃ n ∈ normalCone C x_bar, v + n = 0) →
  ∀ w ∈ posTangentConeAt C x_bar, 0 ≤ subderivative f x_bar w := by
  rintro ⟨v, hv, n, hn, hvn⟩ w hw
  rw [hreg.2.2 w]
  have hn' : n ∈ regularNormalCone C x_bar := by rw [hCreg]; exact hn
  have h1 : inner ℝ n w ≤ 0 := p2f_step1 hn' hw
  have hnv : n = -v := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hvn
  rw [hnv, inner_neg_left] at h1
  have h2 := p2f_step2 hv w
  calc (0 : EReal) = ((0 : ℝ) : EReal) := rfl
    _ ≤ ((inner ℝ v w : ℝ) : EReal) := EReal.coe_le_coe_iff.2 (by linarith)
    _ ≤ _ := h2

lemma sd_dq_le (a b : EReal) (t ε : ℝ) (ht : 0 < t) (ha : a ≠ ⊤) (ha' : a ≠ ⊥)
    (h : b + ((ε * t : ℝ) : EReal) < a) :
    (b - a) / ((t : ℝ) : EReal) ≤ ((-ε : ℝ) : EReal) := by
  obtain ⟨a', rfl⟩ : ∃ a' : ℝ, a = a' := ⟨a.toReal, (EReal.coe_toReal ha ha').symm⟩
  induction b with
  | bot =>
    rw [EReal.bot_sub, EReal.bot_div_of_pos_ne_top (by exact_mod_cast ht) (EReal.coe_ne_top t)]
    exact bot_le
  | top =>
    rw [EReal.top_add_coe] at h
    exact absurd h (not_lt.mpr le_top)
  | coe b' =>
    have h' : b' + ε * t < a' := by exact_mod_cast h
    rw [← EReal.coe_sub, ← EReal.coe_div, EReal.coe_le_coe_iff, div_le_iff₀ ht]
    linarith

theorem sd_main
  (f : E → EReal) (x_bar : E) (C : Set E) (hfx : ⊥ < f x_bar) (hfx' : f x_bar < ⊤)
  (h : ∀ w ∈ posTangentConeAt C x_bar, 0 ≤ subderivative f x_bar w) :
  ∀ ε > 0, ∃ δ > 0, ∀ y ∈ C, ‖y - x_bar‖ ≤ δ →
    f x_bar ≤ f y + ((ε * ‖y - x_bar‖ : ℝ) : EReal) := by
  intro ε hε
  by_contra hcon
  push_neg at hcon
  have hδ : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  choose y hyC hyd hylt using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (hδ n)
  have hyne : ∀ n, y n ≠ x_bar := by
    intro n hn
    have := hylt n
    rw [hn, sub_self, norm_zero, mul_zero, EReal.coe_zero, add_zero] at this
    exact lt_irrefl _ this
  have htpos : ∀ n, 0 < ‖y n - x_bar‖ := fun n => norm_pos_iff.mpr (sub_ne_zero.mpr (hyne n))
  have hu_norm : ∀ n, (fun n => ‖y n - x_bar‖⁻¹ • (y n - x_bar)) n ∈ Metric.sphere (0 : E) 1 := by
    intro n
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (htpos n).ne'
  obtain ⟨d, -, ns, hns, hnsd⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq hu_norm
  have hy0 : Filter.Tendsto (fun n => y n - x_bar) Filter.atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => hyd n) tendsto_one_div_add_atTop_nhds_zero_nat
  have hy0ns : Filter.Tendsto (fun n => y (ns n) - x_bar) Filter.atTop (𝓝 0) :=
    hy0.comp hns.tendsto_atTop
  have hd_tan : d ∈ posTangentConeAt C x_bar := by
    apply mem_tangentConeAt_of_seq Filter.atTop
      (fun n => (⟨‖y (ns n) - x_bar‖⁻¹, inv_nonneg.mpr (htpos (ns n)).le⟩ : NNReal))
      (fun n => y (ns n) - x_bar) hy0ns
    · exact Filter.Eventually.of_forall fun n => by simpa using hyC (ns n)
    · exact Filter.Tendsto.congr (fun n => rfl) hnsd
  have h0 := h d hd_tan
  have hp : Filter.Tendsto (fun n => (‖y (ns n) - x_bar‖, ‖y (ns n) - x_bar‖⁻¹ • (y (ns n) - x_bar)))
      Filter.atTop (𝓝[>] (0 : ℝ) ×ˢ 𝓝 d) := by
    apply Filter.Tendsto.prodMk
    · rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Filter.Eventually.of_forall fun n => htpos (ns n)⟩
      simpa using hy0ns.norm
    · exact hnsd
  have hle : subderivative f x_bar d ≤ ((-ε : ℝ) : EReal) := by
    unfold subderivative
    apply Filter.liminf_le_of_frequently_le'
    apply hp.frequently
    apply Filter.Frequently.of_forall
    intro n
    show (f (x_bar + ‖y (ns n) - x_bar‖ • (‖y (ns n) - x_bar‖⁻¹ • (y (ns n) - x_bar))) - f x_bar)
      / ((‖y (ns n) - x_bar‖ : ℝ) : EReal) ≤ ((-ε : ℝ) : EReal)
    have hx : x_bar + ‖y (ns n) - x_bar‖ • (‖y (ns n) - x_bar‖⁻¹ • (y (ns n) - x_bar)) = y (ns n) := by
      rw [smul_smul, mul_inv_cancel₀ (htpos (ns n)).ne', one_smul]
      abel
    rw [hx]
    exact sd_dq_le _ _ _ _ (htpos (ns n)) hfx'.ne hfx.ne' (hylt (ns n))
  have hneg : ((-ε : ℝ) : EReal) < 0 := by exact_mod_cast neg_neg_of_pos hε
  exact absurd (h0.trans hle) (not_le.mpr hneg)

theorem lo_main
  (f : E → EReal) (x_bar : E) (C : Set E)
  (h : IsLocallyOptimal f C x_bar) :
  ∀ ε > 0, ∃ δ > 0, ∀ y ∈ C, ‖y - x_bar‖ ≤ δ →
    f x_bar ≤ f y + ((ε * ‖y - x_bar‖ : ℝ) : EReal) := by
  intro ε hε
  obtain ⟨_, V, hV, hmin⟩ := h
  obtain ⟨δ, hδ, hδV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hV
  refine ⟨δ, hδ, fun y hy hyd => ?_⟩
  have hyV : y ∈ V := hδV (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hyd)
  calc f x_bar ≤ f y := hmin y ⟨hyV, hy⟩
    _ ≤ f y + ((ε * ‖y - x_bar‖ : ℝ) : EReal) := by
      apply le_add_of_nonneg_right
      exact_mod_cast mul_nonneg hε.le (norm_nonneg _)

omit [FiniteDimensional ℝ E] in
theorem lim_smul_mem_regularNormalCone {C : Set E} {y w : E}
    (hw : w ∈ regularNormalCone C y) {s : ℝ} (hs : 0 < s) :
    s • w ∈ regularNormalCone C y := by
  obtain ⟨hyC, r, hr, V, hV, hle⟩ := hw
  refine ⟨hyC, fun x => s * r x, hr.const_mul_left s, V, hV, fun x hx hxC => ?_⟩
  rw [inner_smul_left]
  simp only [conj_trivial]
  exact mul_le_mul_of_nonneg_left (hle x hx hxC) hs.le

theorem lim_main
  (f : E → EReal) (x_bar : E) (C : Set E) (hfx : ⊥ < f x_bar) (hfx' : f x_bar < ⊤)
  (hCQ : ConstraintQualification f C x_bar)
  (happrox : ∀ η > 0, ∃ x y v w : E, ‖x - x_bar‖ < η ∧ ‖y - x_bar‖ < η ∧
    (∃ a : ℝ, f x = (a : EReal) ∧ |a - (f x_bar).toReal| < η) ∧
    IsRegularSubgradientAt f x v ∧ w ∈ regularNormalCone C y ∧ ‖v + w‖ < η) :
  ∃ v ∈ subdifferential f x_bar, ∃ n ∈ normalCone C x_bar, v + n = 0 := by
  have hη : ∀ n : ℕ, (1 / ((n : ℝ) + 1)) > 0 := fun n => by positivity
  choose x y v w hx hy ha hv hw hvw using fun n : ℕ => happrox (1 / ((n : ℝ) + 1)) (hη n)
  choose a hfa ha' using ha
  have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hxt : Filter.Tendsto x Filter.atTop (𝓝 x_bar) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hx n).le) h0
  have hyt : Filter.Tendsto y Filter.atTop (𝓝 x_bar) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hy n).le) h0
  have hat : Filter.Tendsto a Filter.atTop (𝓝 (f x_bar).toReal) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => by rw [Real.norm_eq_abs]; exact (ha' n).le) h0
  have hft : Filter.Tendsto (fun n => f (x n)) Filter.atTop (𝓝 (f x_bar)) := by
    have h1 : Filter.Tendsto (fun n => ((a n : ℝ) : EReal)) Filter.atTop
        (𝓝 (((f x_bar).toReal : ℝ) : EReal)) := EReal.tendsto_coe.mpr hat
    rw [EReal.coe_toReal hfx'.ne hfx.ne'] at h1
    exact h1.congr (fun n => (hfa n).symm)
  have hvwt : Filter.Tendsto (fun n => v n + w n) Filter.atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hvw n).le) h0
  obtain ⟨μ, hμ⟩ : ∃ μ : ℕ → ℝ, ∀ n, μ n = (1 + ‖w n‖)⁻¹ := ⟨_, fun n => rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℕ → E, ∀ n, u n = μ n • w n := ⟨_, fun n => rfl⟩
  have hμpos : ∀ n, 0 < μ n := fun n => by rw [hμ]; positivity
  have hsum : ∀ n, ‖u n‖ + μ n = 1 := by
    intro n
    have hpos : (0 : ℝ) < 1 + ‖w n‖ := by positivity
    rw [hu, norm_smul, Real.norm_eq_abs, abs_of_pos (hμpos n), hμ]
    have h2 : (1 + ‖w n‖)⁻¹ * ‖w n‖ + (1 + ‖w n‖)⁻¹ = (1 + ‖w n‖)⁻¹ * (1 + ‖w n‖) := by ring
    rw [h2, inv_mul_cancel₀ hpos.ne']
  have hK : IsCompact (Metric.closedBall (0 : E) 1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    (isCompact_closedBall 0 1).prod isCompact_Icc
  have hmem : ∀ n, (u n, μ n) ∈ Metric.closedBall (0 : E) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro n
    have h1 := hsum n
    have h2 := hμpos n
    have h3 := norm_nonneg (u n)
    refine ⟨?_, ?_, ?_⟩
    · show u n ∈ Metric.closedBall (0 : E) 1
      rw [mem_closedBall_zero_iff]; linarith
    · linarith
    · linarith
  obtain ⟨⟨u0, μ0⟩, hmem0, ns, hns, hlim⟩ := hK.tendsto_subseq hmem
  have hut : Filter.Tendsto (fun n => u (ns n)) Filter.atTop (𝓝 u0) :=
    (continuous_fst.tendsto _).comp hlim
  have hμt : Filter.Tendsto (fun n => μ (ns n)) Filter.atTop (𝓝 μ0) :=
    (continuous_snd.tendsto _).comp hlim
  have hsum0 : ‖u0‖ + μ0 = 1 := by
    have h1 : Filter.Tendsto (fun n => ‖u (ns n)‖ + μ (ns n)) Filter.atTop (𝓝 (‖u0‖ + μ0)) :=
      hut.norm.add hμt
    have h2 : (fun n => ‖u (ns n)‖ + μ (ns n)) = fun _ => (1 : ℝ) := funext fun n => hsum (ns n)
    rw [h2] at h1
    exact (tendsto_nhds_unique tendsto_const_nhds h1).symm
  have hnst : Filter.Tendsto ns Filter.atTop Filter.atTop := hns.tendsto_atTop
  have hxns : Filter.Tendsto (fun n => x (ns n)) Filter.atTop (𝓝 x_bar) := hxt.comp hnst
  have hyns : Filter.Tendsto (fun n => y (ns n)) Filter.atTop (𝓝 x_bar) := hyt.comp hnst
  have hfns : Filter.Tendsto (fun n => f (x (ns n))) Filter.atTop (𝓝 (f x_bar)) := hft.comp hnst
  have hvwns : Filter.Tendsto (fun n => v (ns n) + w (ns n)) Filter.atTop (𝓝 0) := hvwt.comp hnst
  have hμ0nn : 0 ≤ μ0 := hmem0.2.1
  rcases hμ0nn.lt_or_eq with hμ0 | hμ0
  · -- μ0 > 0
    have hwns : Filter.Tendsto (fun n => w (ns n)) Filter.atTop (𝓝 (μ0⁻¹ • u0)) := by
      refine ((hμt.inv₀ hμ0.ne').smul hut).congr (fun n => ?_)
      rw [hu, smul_smul, inv_mul_cancel₀ (hμpos _).ne', one_smul]
    have hvns : Filter.Tendsto (fun n => v (ns n)) Filter.atTop (𝓝 (-(μ0⁻¹ • u0))) := by
      have h := (hvwns.sub hwns).congr (fun n => add_sub_cancel_right (v (ns n)) (w (ns n)))
      rwa [zero_sub] at h
    exact ⟨-(μ0⁻¹ • u0), ⟨hfx, hfx', fun n => x (ns n), fun n => v (ns n), hxns, hfns, hvns,
      fun n => hv (ns n)⟩, μ0⁻¹ • u0, ⟨fun n => y (ns n), fun n => w (ns n), hyns, hwns,
      fun n => hw (ns n)⟩, neg_add_cancel _⟩
  · -- μ0 = 0
    exfalso
    subst hμ0
    have hu0 : ‖u0‖ = 1 := by linarith
    have hu0ne : u0 ≠ 0 := by
      intro h
      rw [h, norm_zero] at hu0
      exact zero_ne_one hu0
    have hl : Filter.Tendsto (fun n => μ (ns n)) Filter.atTop (𝓝[>] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hμt, Filter.Eventually.of_forall fun n => hμpos (ns n)⟩
    have hlv : Filter.Tendsto (fun n => μ (ns n) • v (ns n)) Filter.atTop (𝓝 (-u0)) := by
      have h3 := (hμt.smul hvwns).sub hut
      rw [zero_smul, zero_sub] at h3
      refine h3.congr (fun n => ?_)
      rw [hu, smul_add, add_sub_cancel_right]
    apply hCQ
    refine ⟨-u0, ⟨hfx, hfx', fun n => x (ns n), fun n => v (ns n), fun n => μ (ns n), hxns, hfns,
      hl, hlv, fun n => hv (ns n)⟩, neg_ne_zero.mpr hu0ne, ?_⟩
    rw [neg_neg]
    exact ⟨fun n => y (ns n), fun n => u (ns n), hyns, hut, fun n => by
      show u (ns n) ∈ regularNormalCone C (y (ns n))
      rw [hu]; exact lim_smul_mem_regularNormalCone (hw (ns n)) (hμpos (ns n))⟩

theorem core_sq_isLittleO (x : E) (K : ℝ) :
    (fun z => K * ‖z - x‖ ^ 2) =o[𝓝 x] (fun z => ‖z - x‖) := by
  have h : Filter.Tendsto (fun z => ‖z - x‖) (𝓝 x) (𝓝 0) := by
    have := ((continuous_id.sub (continuous_const (y := x))).norm).tendsto x
    simpa using this
  exact ((Asymptotics.isLittleO_pow_id one_lt_two).comp_tendsto h).const_mul_left K

theorem core_quad_id (x y z c : E) (k α : ℝ) :
    k * ‖x - y‖ ^ 2 + α * ‖x - c‖ ^ 2 - (k * ‖z - y‖ ^ 2 + α * ‖z - c‖ ^ 2) =
      inner ℝ (-((2 * k) • (x - y) + (2 * α) • (x - c))) (z - x) + (-(k + α) * ‖z - x‖ ^ 2) := by
  have h1 : z - y = (z - x) + (x - y) := by abel
  have h2 : z - c = (z - x) + (x - c) := by abel
  rw [h1, h2, norm_add_sq_real, norm_add_sq_real]
  simp only [inner_neg_left, inner_add_left, real_inner_smul_left]
  rw [real_inner_comm (x - y) (z - x), real_inner_comm (x - c) (z - x)]
  ring

theorem core_quad_id2 (x y z : E) (k : ℝ) :
    k * ‖x - z‖ ^ 2 - k * ‖x - y‖ ^ 2 =
      - inner ℝ ((2 * k) • (x - y)) (z - y) + k * ‖z - y‖ ^ 2 := by
  have h1 : x - z = (x - y) - (z - y) := by abel
  rw [h1, norm_sub_sq_real]
  simp only [real_inner_smul_left]
  ring

theorem core_ereal_aux {a : ℝ} {u : EReal} {p q : ℝ} (hu : ⊥ < u)
    (h : (a : EReal) + p ≤ u + q) : (a : EReal) + ((p - q : ℝ) : EReal) ≤ u := by
  induction u using EReal.rec with
  | bot => exact absurd hu (lt_irrefl _)
  | coe c =>
    have : a + p ≤ c + q := by exact_mod_cast h
    exact_mod_cast (by linarith : a + (p - q) ≤ c)
  | top => exact le_top

theorem core_lsc_add (f : E → EReal) (hf : LowerSemicontinuous f) (g : E → ℝ) (hg : Continuous g) :
    LowerSemicontinuous (fun z => f z + ((g z : ℝ) : EReal)) := by
  refine LowerSemicontinuous.add' hf (continuous_coe_real_ereal.comp hg).lowerSemicontinuous ?_
  intro z
  exact EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))

theorem core_lsc_add2 (f : E → EReal) (hf : LowerSemicontinuous f) (g : E × E → ℝ) (hg : Continuous g) :
    LowerSemicontinuous (fun p : E × E => f p.1 + ((g p : ℝ) : EReal)) := by
  refine LowerSemicontinuous.add' (hf.comp continuous_fst) (continuous_coe_real_ereal.comp hg).lowerSemicontinuous ?_
  intro z
  exact EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))

theorem approx_main
  (f : E → EReal) (x_bar : E) (C : Set E) (hx_bar : x_bar ∈ C) (hC_closed : IsClosed C)
  (hf_proper : IsProper f) (hf_lsc : LowerSemicontinuous f) (hfx' : f x_bar < ⊤)
  (heps : ∀ ε > 0, ∃ δ > 0, ∀ y ∈ C, ‖y - x_bar‖ ≤ δ →
    f x_bar ≤ f y + ((ε * ‖y - x_bar‖ : ℝ) : EReal)) :
  ∀ η > 0, ∃ x y v w : E, ‖x - x_bar‖ < η ∧ ‖y - x_bar‖ < η ∧
    (∃ a : ℝ, f x = (a : EReal) ∧ |a - (f x_bar).toReal| < η) ∧
    IsRegularSubgradientAt f x v ∧ w ∈ regularNormalCone C y ∧ ‖v + w‖ < η := by
  intro η hη
  obtain ⟨b, hfb⟩ : ∃ b : ℝ, f x_bar = (b : EReal) :=
    ⟨(f x_bar).toReal, (EReal.coe_toReal hfx'.ne (hf_proper.1 x_bar).ne').symm⟩
  have hbtr : (f x_bar).toReal = b := by rw [hfb]; rfl
  rw [hbtr]
  obtain ⟨δ, hδ, hδopt⟩ := heps (η / 8) (by positivity)
  obtain ⟨ρ, hρpos, hρδ, hρη, hρ1⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ δ ∧ ρ ≤ η ∧ ρ ≤ 1 :=
    ⟨min δ (min η 1), lt_min hδ (lt_min hη one_pos), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  obtain ⟨α, hαpos, hαρ⟩ : ∃ α : ℝ, 0 < α ∧ α * ρ = η / 2 :=
    ⟨η / (2 * ρ), by positivity, by field_simp⟩
  have hBc : IsCompact (Metric.closedBall x_bar ρ) := isCompact_closedBall _ _
  have hK : IsCompact (Metric.closedBall x_bar ρ ×ˢ (C ∩ Metric.closedBall x_bar ρ)) :=
    hBc.prod (hBc.inter_left hC_closed)
  have hxbB : x_bar ∈ Metric.closedBall x_bar ρ := Metric.mem_closedBall_self hρpos.le
  have hK0 : (x_bar, x_bar) ∈ Metric.closedBall x_bar ρ ×ˢ (C ∩ Metric.closedBall x_bar ρ) :=
    ⟨hxbB, hx_bar, hxbB⟩
  -- lower bound m
  obtain ⟨z0, hz0B, hz0min⟩ :=
    LowerSemicontinuousOn.exists_isMinOn ⟨x_bar, hxbB⟩ hBc (hf_lsc.lowerSemicontinuousOn _)
  have hz0min' : ∀ z ∈ Metric.closedBall x_bar ρ, f z0 ≤ f z := fun z hz => isMinOn_iff.mp hz0min z hz
  obtain ⟨m, hfm⟩ : ∃ m : ℝ, f z0 = (m : EReal) :=
    ⟨(f z0).toReal, (EReal.coe_toReal ((hz0min' x_bar hxbB).trans_lt hfx').ne
      (hf_proper.1 z0).ne').symm⟩
  have hmb : m ≤ b := by
    have := hz0min' x_bar hxbB
    rw [hfm, hfb] at this
    exact_mod_cast this
  -- penalized problems
  have hmin : ∀ k : ℕ, ∃ p ∈ Metric.closedBall x_bar ρ ×ˢ (C ∩ Metric.closedBall x_bar ρ),
      ∀ q ∈ Metric.closedBall x_bar ρ ×ˢ (C ∩ Metric.closedBall x_bar ρ),
        f p.1 + (((k : ℝ) * ‖p.1 - p.2‖ ^ 2 + α * ‖p.1 - x_bar‖ ^ 2 : ℝ) : EReal) ≤
          f q.1 + (((k : ℝ) * ‖q.1 - q.2‖ ^ 2 + α * ‖q.1 - x_bar‖ ^ 2 : ℝ) : EReal) := by
    intro k
    have hlsc := core_lsc_add2 f hf_lsc
      (fun q : E × E => (k : ℝ) * ‖q.1 - q.2‖ ^ 2 + α * ‖q.1 - x_bar‖ ^ 2) (by fun_prop)
    obtain ⟨p, hp, hpm⟩ := LowerSemicontinuousOn.exists_isMinOn ⟨_, hK0⟩ hK (hlsc.lowerSemicontinuousOn _)
    exact ⟨p, hp, fun q hq => isMinOn_iff.mp hpm q hq⟩
  choose p hpK hpmin using hmin
  -- bounds
  have hFb : ∀ k : ℕ, f (p k).1 + (((k : ℝ) * ‖(p k).1 - (p k).2‖ ^ 2 +
      α * ‖(p k).1 - x_bar‖ ^ 2 : ℝ) : EReal) ≤ (b : EReal) := by
    intro k
    have := hpmin k _ hK0
    simpa [hfb] using this
  have hreal : ∀ k : ℕ, m + ((k : ℝ) * ‖(p k).1 - (p k).2‖ ^ 2 + α * ‖(p k).1 - x_bar‖ ^ 2) ≤ b := by
    intro k
    have h1 : (m : EReal) ≤ f (p k).1 := by rw [← hfm]; exact hz0min' _ (hpK k).1
    have h2 : (m : EReal) + (((k : ℝ) * ‖(p k).1 - (p k).2‖ ^ 2 +
      α * ‖(p k).1 - x_bar‖ ^ 2 : ℝ) : EReal) ≤ (b : EReal) := (add_le_add h1 le_rfl).trans (hFb k)
    exact_mod_cast h2
  -- subsequence
  obtain ⟨ps, hpsK, ns, hns, hnslim⟩ := hK.tendsto_subseq hpK
  have hx1 : Filter.Tendsto (fun k => (p (ns k)).1) Filter.atTop (𝓝 ps.1) :=
    (continuous_fst.tendsto _).comp hnslim
  have hy1 : Filter.Tendsto (fun k => (p (ns k)).2) Filter.atTop (𝓝 ps.2) :=
    (continuous_snd.tendsto _).comp hnslim
  have hxy : ps.1 = ps.2 := by
    have h1 : Filter.Tendsto (fun k => ‖(p (ns k)).1 - (p (ns k)).2‖ ^ 2) Filter.atTop
        (𝓝 (‖ps.1 - ps.2‖ ^ 2)) := ((hx1.sub hy1).norm).pow 2
    have h2 : Filter.Tendsto (fun k : ℕ => (b - m) / (k : ℝ)) Filter.atTop (𝓝 0) :=
      _root_.tendsto_const_div_atTop_nhds_zero_nat _
    have h3 : ∀ᶠ k in Filter.atTop, ‖(p (ns k)).1 - (p (ns k)).2‖ ^ 2 ≤ (b - m) / (k : ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with k hk
      have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hnsk : (k : ℝ) ≤ (ns k : ℝ) := by exact_mod_cast hns.id_le k
      have hbound := hreal (ns k)
      rw [le_div_iff₀ (by linarith)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hnsk) (sq_nonneg ‖(p (ns k)).1 - (p (ns k)).2‖),
        mul_nonneg hαpos.le (sq_nonneg ‖(p (ns k)).1 - x_bar‖)]
    have h4 : ‖ps.1 - ps.2‖ ^ 2 ≤ 0 := le_of_tendsto_of_tendsto h1 h2 h3
    have h5 : ‖ps.1 - ps.2‖ = 0 := by nlinarith [norm_nonneg (ps.1 - ps.2)]
    exact sub_eq_zero.mp (norm_eq_zero.mp h5)
  have hpsC : ps.1 ∈ C := by rw [hxy]; exact hpsK.2.1
  have hpsB : ‖ps.1 - x_bar‖ ≤ ρ := by
    have := hpsK.1
    rwa [Metric.mem_closedBall, dist_eq_norm] at this
  have hopt := hδopt ps.1 hpsC (hpsB.trans hρδ)
  -- g ps.1 ≤ b
  have hg : f ps.1 + ((α * ‖ps.1 - x_bar‖ ^ 2 : ℝ) : EReal) ≤ (b : EReal) := by
    by_contra hcon
    push_neg at hcon
    have hglsc := core_lsc_add f hf_lsc (fun z => α * ‖z - x_bar‖ ^ 2) (by fun_prop)
    have hev := hx1.eventually (hglsc ps.1 _ hcon)
    obtain ⟨k, hk⟩ := hev.exists
    have hle : f (p (ns k)).1 + ((α * ‖(p (ns k)).1 - x_bar‖ ^ 2 : ℝ) : EReal) ≤ (b : EReal) := by
      refine le_trans ?_ (hFb (ns k))
      exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by
          nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (ns k)) (sq_nonneg ‖(p (ns k)).1 - (p (ns k)).2‖)]))
    exact absurd hk (not_lt.mpr hle)
  obtain ⟨c, hfc⟩ : ∃ c : ℝ, f ps.1 = (c : EReal) := by
    have hne : f ps.1 ≠ ⊤ := by
      intro h
      rw [h, EReal.top_add_coe] at hg
      exact absurd hg (not_le.mpr (EReal.coe_lt_top b))
    exact ⟨(f ps.1).toReal, (EReal.coe_toReal hne (hf_proper.1 _).ne').symm⟩
  rw [hfc] at hg
  rw [hfc, hfb] at hopt
  have hg' : c + α * ‖ps.1 - x_bar‖ ^ 2 ≤ b := by exact_mod_cast hg
  have hopt' : b ≤ c + η / 8 * ‖ps.1 - x_bar‖ := by exact_mod_cast hopt
  have hr0 : 0 ≤ ‖ps.1 - x_bar‖ := norm_nonneg _
  have hrlt : ‖ps.1 - x_bar‖ < ρ / 2 := by
    by_contra hge
    push_neg at hge
    have hrpos : 0 < ‖ps.1 - x_bar‖ := lt_of_lt_of_le (by linarith) hge
    nlinarith [mul_nonneg (mul_nonneg hαpos.le hr0) (sub_nonneg.mpr hge), mul_pos hη hrpos]
  have hcb : b - η / 2 < c := by nlinarith
  -- eventually conditions
  have E1 : ∀ᶠ k in Filter.atTop, ‖(p (ns k)).1 - x_bar‖ < ρ / 2 :=
    ((hx1.sub_const x_bar).norm).eventually_lt_const hrlt
  have E2 : ∀ᶠ k in Filter.atTop, ‖(p (ns k)).2 - x_bar‖ < ρ / 2 := by
    rw [hxy] at hrlt
    exact ((hy1.sub_const x_bar).norm).eventually_lt_const hrlt
  have E3 : ∀ᶠ k in Filter.atTop, (((b - η / 2 : ℝ)) : EReal) < f (p (ns k)).1 := by
    have hlt : ((b - η / 2 : ℝ) : EReal) < f ps.1 := by rw [hfc]; exact_mod_cast hcb
    have h := hf_lsc ps.1 _ hlt
    exact hx1.eventually h
  obtain ⟨k0, hk1, hk2, hk3⟩ := (E1.and (E2.and E3)).exists
  -- the chosen point
  set k : ℕ := ns k0 with hk_def
  set x : E := (p k).1 with hx_def
  set y : E := (p k).2 with hy_def
  have hFbk := hFb k
  have hmink := hpmin k
  have hpk : p k = (x, y) := rfl
  have hyK : y ∈ C ∩ Metric.closedBall x_bar ρ := (hpK k).2
  obtain ⟨a, hfa⟩ : ∃ a : ℝ, f x = (a : EReal) := by
    have hne : f x ≠ ⊤ := by
      intro h
      rw [h, EReal.top_add_coe] at hFbk
      exact absurd hFbk (not_le.mpr (EReal.coe_lt_top b))
    exact ⟨(f x).toReal, (EReal.coe_toReal hne (hf_proper.1 _).ne').symm⟩
  rw [hfa] at hFbk hk3
  have hab : a + ((k : ℝ) * ‖x - y‖ ^ 2 + α * ‖x - x_bar‖ ^ 2) ≤ b := by exact_mod_cast hFbk
  have hab' : b - η / 2 < a := by exact_mod_cast hk3
  have hxball : x ∈ Metric.ball x_bar ρ := by
    rw [Metric.mem_ball, dist_eq_norm]; linarith
  have hyball : y ∈ Metric.ball x_bar ρ := by
    rw [Metric.mem_ball, dist_eq_norm]; linarith
  refine ⟨x, y, -(((2 : ℝ) * k) • (x - y) + ((2 : ℝ) * α) • (x - x_bar)), ((2 : ℝ) * k) • (x - y),
    by linarith, by linarith, ⟨a, hfa, ?_⟩, ?_, ?_, ?_⟩
  · rw [abs_lt]
    constructor
    · linarith
    · nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (sq_nonneg ‖x - y‖),
        mul_nonneg hαpos.le (sq_nonneg ‖x - x_bar‖)]
  · -- regular subgradient
    refine ⟨hf_proper.1 x, by rw [hfa]; exact EReal.coe_lt_top a,
      fun z => -((k : ℝ) + α) * ‖z - x‖ ^ 2, core_sq_isLittleO x _, Metric.ball x_bar ρ,
      Metric.isOpen_ball.mem_nhds hxball, ?_⟩
    intro z hz
    have hzK : (z, y) ∈ Metric.closedBall x_bar ρ ×ˢ (C ∩ Metric.closedBall x_bar ρ) :=
      ⟨Metric.ball_subset_closedBall hz, hyK⟩
    have h1 := hmink (z, y) hzK
    rw [hpk] at h1
    simp only at h1
    rw [hfa] at h1 ⊢
    have h2 := core_ereal_aux (hf_proper.1 z) h1
    have hid := core_quad_id x y z x_bar (k : ℝ) α
    rw [hid] at h2
    exact h2
  · -- regular normal
    refine ⟨hyK.1, fun z => (k : ℝ) * ‖z - y‖ ^ 2, core_sq_isLittleO y _, Metric.ball x_bar ρ,
      Metric.isOpen_ball.mem_nhds hyball, ?_⟩
    intro z hz hzC
    have hzK : (x, z) ∈ Metric.closedBall x_bar ρ ×ˢ (C ∩ Metric.closedBall x_bar ρ) :=
      ⟨(hpK k).1, hzC, Metric.ball_subset_closedBall hz⟩
    have h1 := hmink (x, z) hzK
    rw [hpk] at h1
    simp only at h1
    rw [hfa] at h1
    have h2 : (k : ℝ) * ‖x - y‖ ^ 2 + α * ‖x - x_bar‖ ^ 2 ≤
        (k : ℝ) * ‖x - z‖ ^ 2 + α * ‖x - x_bar‖ ^ 2 := by
      have : a + ((k : ℝ) * ‖x - y‖ ^ 2 + α * ‖x - x_bar‖ ^ 2) ≤
          a + ((k : ℝ) * ‖x - z‖ ^ 2 + α * ‖x - x_bar‖ ^ 2) := by exact_mod_cast h1
      linarith
    have hid := core_quad_id2 x y z (k : ℝ)
    linarith
  · -- norm bound
    have hvw : -(((2 : ℝ) * k) • (x - y) + ((2 : ℝ) * α) • (x - x_bar)) + ((2 : ℝ) * k) • (x - y) =
        -(((2 : ℝ) * α) • (x - x_bar)) := by abel
    rw [hvw, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    nlinarith [norm_nonneg (x - x_bar)]

theorem RW_chap_8_15
  (f : E → EReal)
  (x_bar : E)
  (C : Set E)
  (hx_bar : x_bar ∈ C)
  (hC_closed : IsClosed C)
  (hf_proper : IsProper f)
  (hf_lsc : LowerSemicontinuous f) :
  (ConstraintQualification f C x_bar →
    (IsLocallyOptimal f C x_bar →
      ∃ v ∈ subdifferential f x_bar,
        ∃ n ∈ normalCone C x_bar,
          v + n = 0) ∧
    ((IsRegularAt f x_bar ∧ IsRegularSetAt C x_bar) →
      ((∃ v ∈ subdifferential f x_bar,
          ∃ n ∈ normalCone C x_bar,
            v + n = 0) ↔
        (∀ w ∈ posTangentConeAt C x_bar,
          0 ≤ subderivative f x_bar w)))) ∧
  ((ConvexEReal f ∧ Convex ℝ C ∧ ⊥ < f x_bar ∧ f x_bar < ⊤) →
    (((∃ v ∈ subdifferential f x_bar,
          ∃ n ∈ normalCone C x_bar,
            v + n = 0) ∨
        (∀ w ∈ posTangentConeAt C x_bar,
          0 ≤ subderivative f x_bar w)) →
      IsGloballyOptimal f C x_bar)) := by
  refine ⟨fun hCQ => ⟨fun hopt => ?_, fun hreg => ⟨p2f_main f x_bar C hreg.1 hreg.2, fun h => ?_⟩⟩,
    p3_main f x_bar C hx_bar hf_proper⟩
  · exact lim_main f x_bar C (hf_proper.1 x_bar) hopt.1 hCQ
      (approx_main f x_bar C hx_bar hC_closed hf_proper hf_lsc hopt.1
        (lo_main f x_bar C hopt))
  · have hfx := hreg.1.1
    exact lim_main f x_bar C hfx.1 hfx.2 hCQ
      (approx_main f x_bar C hx_bar hC_closed hf_proper hf_lsc hfx.2
        (sd_main f x_bar C hfx.1 hfx.2 h))

end RW_chap_8_15
