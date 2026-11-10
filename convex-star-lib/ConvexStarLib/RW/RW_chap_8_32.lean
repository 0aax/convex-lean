import ConvexStarLib.Defs

/-!
# `RW_chap_8_32`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_8_32` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_8_32`, so the main result is `RW_chap_8_32.RW_chap_8_32`.
-/

namespace RW_chap_8_32

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Aux

open Filter Set Metric

lemma ereal_dq_le_iff {a : EReal} {c t b : ℝ} (ht : 0 < t) :
    (a - (c : EReal)) / (t : EReal) ≤ (b : EReal) ↔ a ≤ ((c + b * t : ℝ) : EReal) := by
  rw [EReal.div_le_iff_le_mul (by exact_mod_cast ht) (EReal.coe_ne_top t),
    EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))]
  rw [show ((c + b * t : ℝ) : EReal) = (t : EReal) * (b : EReal) + (c : EReal) by
    rw [← EReal.coe_mul, ← EReal.coe_add]; congr 1; ring]

lemma ereal_dq_lt_iff {a : EReal} {c t b : ℝ} (ht : 0 < t) :
    (a - (c : EReal)) / (t : EReal) < (b : EReal) ↔ a < ((c + b * t : ℝ) : EReal) := by
  rw [EReal.div_lt_iff (by exact_mod_cast ht) (EReal.coe_ne_top t),
    EReal.sub_lt_iff (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))]
  rw [show ((c + b * t : ℝ) : EReal) = (b : EReal) * (t : EReal) + (c : EReal) by
    rw [← EReal.coe_mul, ← EReal.coe_add]; congr 1; ring]

lemma localLsc_unpack {f : E → EReal} {x_bar : E} (h : LocalLscAt f x_bar) :
    ∃ c ε : ℝ, f x_bar = (c : EReal) ∧ 0 < ε ∧
      ∀ α : ℝ, α ≤ c + ε → IsClosed {x | x ∈ Metric.closedBall x_bar ε ∧ f x ≤ (α : EReal)} := by
  obtain ⟨h1, h2, ε, hε⟩ := h
  set c := (f x_bar).toReal with hc_def
  have hc : f x_bar = (c : EReal) := (EReal.coe_toReal h2.ne h1.ne').symm
  refine ⟨c, ε, hc, ?_, ?_⟩
  · exact (hε (c + ε) (by rw [hc]; exact_mod_cast le_refl _)).1
  · intro α hα
    exact (hε α (by rw [hc]; exact_mod_cast hα)).2

/-! ### Part A: basic subderivative facts -/

lemma subderiv_zero_le (f : E → EReal) (x_bar : E) : subderivative f x_bar 0 ≤ 0 := by
  unfold subderivative
  apply Filter.liminf_le_of_frequently_le'
  have hT : Tendsto (fun t : ℝ => (t, (0:E))) (𝓝[>] (0:ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 (0:E)) :=
    tendsto_id.prodMk tendsto_const_nhds
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), differenceQuotient f x_bar (0:E) t ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    unfold differenceQuotient
    simp only [smul_zero, add_zero]
    exact EReal.div_nonpos_of_nonpos_of_nonneg EReal.sub_self_le_zero
      (by exact_mod_cast le_of_lt (show (0:ℝ) < t from ht))
  exact hT.frequently hev.frequently

lemma subderiv_ge_of_calm {f : E → EReal} {x_bar : E} {κ : ℝ}
    (h : IsCalmFromBelowAtWith f x_bar κ) (w : E) :
    (((-(κ * ‖w‖)) : ℝ) : EReal) ≤ subderivative f x_bar w := by
  obtain ⟨hκ, hbot, htop, V, hV, hVf⟩ := h
  set c := (f x_bar).toReal with hc_def
  have hc : f x_bar = (c : EReal) := (EReal.coe_toReal htop.ne hbot.ne').symm
  unfold subderivative
  have hcont : Tendsto (fun p : ℝ × E => x_bar + p.1 • p.2) (𝓝[>] (0:ℝ) ×ˢ 𝓝 w)
      (𝓝 x_bar) := by
    have h1 : Tendsto (fun p : ℝ × E => x_bar + p.1 • p.2) (𝓝 ((0:ℝ), w))
        (𝓝 (x_bar + (0:ℝ) • w)) := by
      apply Continuous.tendsto
      fun_prop
    rw [zero_smul, add_zero] at h1
    refine h1.mono_left ?_
    rw [nhds_prod_eq]
    exact Filter.prod_mono nhdsWithin_le_nhds le_rfl
  have hpos : ∀ᶠ p in 𝓝[>] (0:ℝ) ×ˢ 𝓝 w, (0:ℝ) < p.1 :=
    Filter.Eventually.prod_inl (self_mem_nhdsWithin : Set.Ioi (0:ℝ) ∈ 𝓝[>] (0:ℝ)) _
  have hev : ∀ᶠ p in 𝓝[>] (0:ℝ) ×ˢ 𝓝 w,
      (((-(κ * ‖p.2‖)) : ℝ) : EReal) ≤ differenceQuotient f x_bar p.2 p.1 := by
    filter_upwards [hcont hV, hpos] with p hp1 hp2
    have hle := hVf _ hp1
    unfold differenceQuotient
    rw [hc, ← not_lt, ereal_dq_lt_iff hp2, not_lt]
    rw [hc] at hle
    refine le_trans (le_of_eq ?_) hle
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hp2.le, ← EReal.coe_mul,
      ← EReal.coe_sub]
    congr 1
    ring
  have hlim : Tendsto (fun p : ℝ × E => (((-(κ * ‖p.2‖)) : ℝ) : EReal)) (𝓝[>] (0:ℝ) ×ˢ 𝓝 w)
      (𝓝 (((-(κ * ‖w‖)) : ℝ) : EReal)) := by
    apply continuous_coe_real_ereal.continuousAt.tendsto.comp
    have h2 : Tendsto (fun p : ℝ × E => -(κ * ‖p.2‖)) (𝓝 ((0:ℝ), w))
        (𝓝 (-(κ * ‖w‖))) := by
      apply Continuous.tendsto'
      · fun_prop
      · rfl
    refine h2.mono_left ?_
    rw [nhds_prod_eq]
    exact Filter.prod_mono nhdsWithin_le_nhds le_rfl
  calc (((-(κ * ‖w‖)) : ℝ) : EReal)
      = liminf (fun p : ℝ × E => (((-(κ * ‖p.2‖)) : ℝ) : EReal)) (𝓝[>] (0:ℝ) ×ˢ 𝓝 w) :=
        hlim.liminf_eq.symm
    _ ≤ liminf (fun p : ℝ × E => differenceQuotient f x_bar p.2 p.1) (𝓝[>] (0:ℝ) ×ˢ 𝓝 w) :=
        Filter.liminf_le_liminf hev

lemma subderiv_zero_eq_bot_of_not_calm {f : E → EReal} {x_bar : E}
    (h : ¬ IsCalmFromBelowAt f x_bar) : subderivative f x_bar 0 = ⊥ := by
  have hT : Tendsto (fun t : ℝ => (t, (0:E))) (𝓝[>] (0:ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 (0:E)) :=
    tendsto_id.prodMk tendsto_const_nhds
  by_cases hfin : ⊥ < f x_bar ∧ f x_bar < ⊤
  · obtain ⟨hbot, htop⟩ := hfin
    set c := (f x_bar).toReal with hc_def
    have hc : f x_bar = (c : EReal) := (EReal.coe_toReal htop.ne hbot.ne').symm
    have key : ∀ M : ℝ, 0 < M → subderivative f x_bar 0 ≤ ((-M : ℝ) : EReal) := by
      intro M hM
      unfold subderivative
      apply Filter.liminf_le_of_frequently_le'
      rw [Filter.frequently_iff]
      intro S hS
      obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.mp hS
      obtain ⟨a, ha, hAa⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hA
      obtain ⟨b, hb, hBb⟩ := Metric.mem_nhds_iff.mp hB
      have ha' : (0:ℝ) < a := ha
      have hκ : 0 ≤ 2 * M / b := by positivity
      have hex : ∃ x ∈ Metric.ball x_bar (a * b / 2),
          f x < f x_bar - ((2 * M / b : ℝ) : EReal) * ‖x - x_bar‖ := by
        by_contra hcon
        push_neg at hcon
        exact h ⟨2 * M / b, hκ, hbot, htop, Metric.ball x_bar (a * b / 2),
          Metric.ball_mem_nhds _ (by positivity), hcon⟩
      obtain ⟨x, hx, hfx⟩ := hex
      rw [Metric.mem_ball, dist_eq_norm] at hx
      rw [hc, ← EReal.coe_mul, ← EReal.coe_sub] at hfx
      have hxne : x ≠ x_bar := by
        intro hxx
        rw [hxx, sub_self, norm_zero, mul_zero, sub_zero, hc] at hfx
        exact lt_irrefl _ hfx
      have hs : 0 < ‖x - x_bar‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxne)
      have ht : 0 < 2 * ‖x - x_bar‖ / b := by positivity
      have hta : 2 * ‖x - x_bar‖ / b < a := by
        rw [div_lt_iff₀ hb]; linarith
      have hw'norm : ‖(2 * ‖x - x_bar‖ / b)⁻¹ • (x - x_bar)‖ = b / 2 := by
        rw [norm_smul, norm_inv, Real.norm_of_nonneg ht.le]
        field_simp
      have hxeq : x_bar + (2 * ‖x - x_bar‖ / b) • ((2 * ‖x - x_bar‖ / b)⁻¹ • (x - x_bar)) = x := by
        rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul, add_sub_cancel]
      refine ⟨(2 * ‖x - x_bar‖ / b, (2 * ‖x - x_bar‖ / b)⁻¹ • (x - x_bar)),
        hAB ⟨hAa ⟨ht, hta⟩, hBb ?_⟩, ?_⟩
      · show (2 * ‖x - x_bar‖ / b)⁻¹ • (x - x_bar) ∈ Metric.ball (0:E) b
        rw [Metric.mem_ball, _root_.dist_zero_right, hw'norm]; linarith
      · show differenceQuotient f x_bar ((2 * ‖x - x_bar‖ / b)⁻¹ • (x - x_bar))
          (2 * ‖x - x_bar‖ / b) ≤ ((-M : ℝ) : EReal)
        unfold differenceQuotient
        rw [hxeq, hc, ereal_dq_le_iff ht]
        refine le_of_lt (lt_of_lt_of_le hfx (le_of_eq ?_))
        congr 1
        field_simp
        ring
    apply le_antisymm _ bot_le
    by_contra hne
    rw [not_le] at hne
    obtain ⟨r, _, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp hne
    have h1 := key (|r| + 1) (by positivity)
    have h3 : ((-(|r| + 1) : ℝ) : EReal) < (r : EReal) := by
      exact_mod_cast (by linarith [neg_abs_le r] : -(|r| + 1) < r)
    exact lt_irrefl _ (lt_trans (lt_of_le_of_lt h1 h3) hr2)
  · apply le_antisymm _ bot_le
    unfold subderivative
    apply Filter.liminf_le_of_frequently_le'
    have hsub : f x_bar - f x_bar = ⊥ := by
      rcases not_and_or.mp hfin with h1 | h1
      · rw [not_lt, le_bot_iff] at h1
        rw [h1]; simp
      · rw [not_lt, top_le_iff] at h1
        rw [h1]; simp
    have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), differenceQuotient f x_bar (0:E) t ≤ ⊥ := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      unfold differenceQuotient
      simp only [smul_zero, add_zero]
      rw [hsub, EReal.bot_div_of_pos_ne_top (by exact_mod_cast (show (0:ℝ) < t from ht))
        (EReal.coe_ne_top t)]
    exact hT.frequently hev.frequently

lemma B_calm_of_lt {f : E → EReal} {x_bar : E} {c : ℝ} (hc : f x_bar = (c : EReal)) {κ : ℝ}
    (hκ : 0 ≤ κ)
    (hlt : ((-κ : ℝ) : EReal) < sInf ((fun (w : E) => subderivative f x_bar w) '' unitBall)) :
    IsCalmFromBelowAtWith f x_bar κ := by
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  refine ⟨hκ, by rw [hc]; exact EReal.bot_lt_coe c, by rw [hc]; exact EReal.coe_lt_top c, ?_⟩
  by_contra hne
  push_neg at hne
  have hseq : ∀ n : ℕ, ∃ x ∈ Metric.ball x_bar (1 / ((n : ℝ) + 1)),
      f x < f x_bar - (κ : EReal) * ((‖x - x_bar‖ : ℝ) : EReal) := by
    intro n
    exact hne _ (Metric.ball_mem_nhds x_bar (by positivity))
  choose x hxball hxlt using hseq
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℝ, ∀ n, t n = ‖x n - x_bar‖ := ⟨_, fun n => rfl⟩
  have hxlt' : ∀ n, f (x n) < ((c + (-κ) * t n : ℝ) : EReal) := by
    intro n
    have h1 := hxlt n
    rw [hc] at h1
    have h2 : ((c + (-κ) * t n : ℝ) : EReal) = (c : EReal) - (κ : EReal) * ((‖x n - x_bar‖ : ℝ) : EReal) := by
      rw [← EReal.coe_mul, ← EReal.coe_sub, ht n]
      congr 1
      ring
    rw [h2]
    exact h1
  have htpos : ∀ n, 0 < t n := by
    intro n
    by_contra hle
    push_neg at hle
    have h0 : t n = 0 := le_antisymm hle (by rw [ht n]; exact norm_nonneg _)
    have h1 := hxlt' n
    rw [h0, mul_zero, add_zero, ← hc] at h1
    have hxn : x n = x_bar := by
      have h3 : ‖x n - x_bar‖ = 0 := by rw [← ht n]; exact h0
      exact sub_eq_zero.mp (norm_eq_zero.mp h3)
    rw [hxn] at h1
    exact lt_irrefl _ h1
  have htlt : ∀ n, t n < 1 / ((n : ℝ) + 1) := by
    intro n
    have h1 := hxball n
    rw [Metric.mem_ball, dist_eq_norm] at h1
    rw [ht n]
    exact h1
  obtain ⟨w, hw⟩ : ∃ w : ℕ → E, ∀ n, w n = (t n)⁻¹ • (x n - x_bar) := ⟨_, fun n => rfl⟩
  have hw_sphere : ∀ n, w n ∈ Metric.sphere (0 : E) 1 := by
    intro n
    rw [mem_sphere_zero_iff_norm, hw n, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos (htpos n), ← ht n]
    exact inv_mul_cancel₀ (htpos n).ne'
  have hxw : ∀ n, x_bar + t n • w n = x n := by
    intro n
    rw [hw n, smul_smul, mul_inv_cancel₀ (htpos n).ne', one_smul]
    abel
  obtain ⟨w₀, hw₀, ns, hns, hlim⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq hw_sphere
  have ht0 : Tendsto t atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (htpos n).le) (fun n => (htlt n).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have ht0' : Tendsto (t ∘ ns) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨ht0.comp hns.tendsto_atTop, Eventually.of_forall (fun k => htpos (ns k))⟩
  have hprod : Tendsto (fun k => ((t ∘ ns) k, (w ∘ ns) k)) atTop (𝓝[>] (0:ℝ) ×ˢ 𝓝 w₀) :=
    ht0'.prodMk hlim
  have hfreq : ∃ᶠ p in (𝓝[>] (0:ℝ) ×ˢ 𝓝 w₀),
      (fun p : ℝ × E => differenceQuotient f x_bar p.2 p.1) p ≤ ((-κ : ℝ) : EReal) := by
    refine hprod.frequently (Frequently.of_forall fun k => ?_)
    show differenceQuotient f x_bar (w (ns k)) (t (ns k)) ≤ ((-κ : ℝ) : EReal)
    rw [differenceQuotient, hxw (ns k), hc]
    exact ((ereal_dq_lt_iff (htpos (ns k))).mpr (hxlt' (ns k))).le
  have hsub : subderivative f x_bar w₀ ≤ ((-κ : ℝ) : EReal) :=
    Filter.liminf_le_of_frequently_le' hfreq
  have hw₀ball : w₀ ∈ (unitBall : Set E) := Metric.sphere_subset_closedBall hw₀
  have hm : sInf ((fun (w : E) => subderivative f x_bar w) '' unitBall) ≤
      subderivative f x_bar w₀ := sInf_le ⟨w₀, hw₀ball, rfl⟩
  exact lt_irrefl _ (lt_of_lt_of_le hlt (hm.trans hsub))

lemma modulus_eq_of_calm {f : E → EReal} {x_bar : E} (h : IsCalmFromBelowAt f x_bar) :
    exactCalmFromBelowModulus f x_bar =
      -sInf ((fun (w : E) => subderivative f x_bar w) '' unitBall) := by
  obtain ⟨κ₀, hκ₀⟩ := h
  have h0ball : (0 : E) ∈ (unitBall : Set E) := by simp [unitBall]
  have hm0 : sInf ((fun (w : E) => subderivative f x_bar w) '' unitBall) ≤ 0 := by
    have h1 : sInf ((fun (w : E) => subderivative f x_bar w) '' unitBall) ≤
        subderivative f x_bar 0 := sInf_le ⟨0, h0ball, rfl⟩
    exact h1.trans (subderiv_zero_le f x_bar)
  have ha : ∀ κ, IsCalmFromBelowAtWith f x_bar κ →
      ((-κ : ℝ) : EReal) ≤ sInf ((fun (w : E) => subderivative f x_bar w) '' unitBall) := by
    intro κ hκ
    apply le_sInf
    rintro _ ⟨w, hw, rfl⟩
    refine le_trans ?_ (subderiv_ge_of_calm hκ w)
    have hw' : ‖w‖ ≤ 1 := by simpa [unitBall] using hw
    have h1 : κ * ‖w‖ ≤ κ := by nlinarith [hκ.1, norm_nonneg w]
    exact_mod_cast (by linarith : -κ ≤ -(κ * ‖w‖))
  have hc : f x_bar = (((f x_bar).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal hκ₀.2.2.1.ne hκ₀.2.1.ne').symm
  unfold exactCalmFromBelowModulus
  apply le_antisymm
  · rw [← EReal.le_of_forall_lt_iff_le]
    intro z hz
    apply sInf_le
    refine ⟨z, ?_, rfl⟩
    have hz' : ((-z : ℝ) : EReal) <
        sInf ((fun (w : E) => subderivative f x_bar w) '' unitBall) := by
      rw [EReal.coe_neg]
      exact EReal.neg_lt_comm.mp hz
    have hz0 : 0 ≤ z := by
      have h1 : (0 : EReal) ≤ -sInf ((fun (w : E) => subderivative f x_bar w) '' unitBall) :=
        EReal.neg_nonneg.mpr hm0
      exact_mod_cast h1.trans hz.le
    exact B_calm_of_lt hc hz0 hz'
  · apply le_sInf
    rintro _ ⟨κ, hκ, rfl⟩
    rw [EReal.neg_le, ← EReal.coe_neg]
    exact ha κ hκ

lemma regSubderiv_zero_le (f : E → EReal) (x_bar : E) :
    regularSubderivative f x_bar 0 ≤ 0 := by
  unfold regularSubderivative
  refine Filter.limsup_le_of_le (h := ?_)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  refine Filter.limsup_le_of_le (h := ?_)
  have hev : ∀ᶠ p : E × ℝ in fApproach f x_bar ×ˢ 𝓝[>] (0:ℝ), 0 < p.2 :=
    tendsto_snd.eventually (self_mem_nhdsWithin (s := Set.Ioi (0:ℝ)) (a := 0))
  filter_upwards [hev] with p hp
  apply sInf_le_of_le (b := delta f p.1 p.2 0)
  · exact ⟨0, Metric.mem_closedBall_self (le_of_lt hδ), rfl⟩
  · simp only [delta, differenceQuotient, smul_zero, add_zero]
    exact EReal.div_nonpos_of_nonpos_of_nonneg EReal.sub_self_le_zero (by exact_mod_cast le_of_lt hp)

lemma C_inner_bound {f : E → EReal} {x_bar v : E}
    (hv : v ∈ subdifferential f x_bar) (w : E) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ((inner ℝ v w - ‖v‖ * δ - ε : ℝ) : EReal) ≤
      Filter.limsup (fun p : E × ℝ => sInf ((delta f p.1 p.2) '' Metric.closedBall w δ))
        ((fApproach f x_bar) ×ˢ (𝓝[>] (0 : ℝ))) := by
  obtain ⟨_, _, xs, vs, hxs, hfxs, hvs, hreg⟩ := hv
  apply le_limsup_of_frequently_le'
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.1 hU
  set K : ℝ := ‖w‖ + δ + 1 with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  set ε' : ℝ := ε / (2 * K) with hε'
  have hε'pos : 0 < ε' := by rw [hε']; positivity
  have hxsA : Tendsto xs atTop (fApproach f x_bar) := by
    unfold fApproach
    exact tendsto_inf.2 ⟨hxs, tendsto_comap_iff.2 hfxs⟩
  obtain ⟨n, hnA, hnv⟩ :=
    ((hxsA.eventually_mem hA).and (hvs.eventually_mem (Metric.ball_mem_nhds v hε'pos))).exists
  obtain ⟨hb, ht, r, hr, V, hV, hineq⟩ := hreg n
  set x := xs n with hx
  set u := vs n with hu
  set a := (f x).toReal with ha
  have hfx : f x = (a : EReal) := (EReal.coe_toReal ht.ne hb.ne').symm
  have hr' := hr.def hε'pos
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hV hr')
  have hτ : ∀ᶠ τ in 𝓝[>] (0:ℝ), τ ∈ B ∧ 0 < τ ∧ τ < ρ / K :=
    Filter.Eventually.and hB (Filter.Eventually.and self_mem_nhdsWithin
      (nhdsWithin_le_nhds (Iio_mem_nhds (div_pos hρ hKpos))))
  obtain ⟨τ, hτB, hτpos, hτρ⟩ := hτ.exists
  refine ⟨(x, τ), hAB (Set.mk_mem_prod hnA hτB), ?_⟩
  apply le_sInf
  rintro _ ⟨w', hw', rfl⟩
  simp only [delta, differenceQuotient]
  rw [hfx]
  apply not_lt.1
  rw [ereal_dq_lt_iff hτpos, not_lt]
  set y := x + τ • w' with hy
  have hyx : y - x = τ • w' := by rw [hy]; abel
  have hw'norm : ‖w' - w‖ ≤ δ := by rw [← dist_eq_norm]; exact hw'
  have hw'le : ‖w'‖ ≤ ‖w‖ + δ := by
    calc ‖w'‖ = ‖w + (w' - w)‖ := by congr 1; abel
    _ ≤ ‖w‖ + ‖w' - w‖ := norm_add_le _ _
    _ ≤ ‖w‖ + δ := by linarith
  have hynorm : ‖y - x‖ = τ * ‖w'‖ := by rw [hyx, norm_smul, Real.norm_of_nonneg hτpos.le]
  have hτK : τ * K < ρ := by rwa [lt_div_iff₀ hKpos] at hτρ
  have hyball : y ∈ Metric.ball x ρ := by
    rw [Metric.mem_ball, dist_eq_norm, hynorm]
    have h1 : τ * ‖w'‖ ≤ τ * K := mul_le_mul_of_nonneg_left (by rw [hK]; linarith) hτpos.le
    linarith
  obtain ⟨hyV, hry⟩ := hball hyball
  have hmain := hineq y hyV
  rw [hfx, ← EReal.coe_add] at hmain
  refine le_trans ?_ hmain
  rw [EReal.coe_le_coe_iff]
  have hry' : -(ε' * (τ * ‖w'‖)) ≤ r y := by
    have hry2 : ‖r y‖ ≤ ε' * ‖‖y - x‖‖ := hry
    rw [norm_norm, hynorm, Real.norm_eq_abs] at hry2
    linarith [neg_abs_le (r y)]
  have hinner : inner ℝ u (y - x) = τ * inner ℝ u w' := by rw [hyx, real_inner_smul_right]
  have h1 : inner ℝ u w' = inner ℝ v w + inner ℝ v (w' - w) + inner ℝ (u - v) w' := by
    rw [inner_sub_right, inner_sub_left]; ring
  have h2 : -(‖v‖ * δ) ≤ inner ℝ v (w' - w) := by
    have h21 := abs_real_inner_le_norm v (w' - w)
    have h22 := neg_abs_le (inner ℝ v (w' - w))
    have h23 : ‖v‖ * ‖w' - w‖ ≤ ‖v‖ * δ := mul_le_mul_of_nonneg_left hw'norm (norm_nonneg v)
    linarith
  have huv : ‖u - v‖ < ε' := by rw [← dist_eq_norm]; exact hnv
  have h3 : -(ε' * ‖w'‖) ≤ inner ℝ (u - v) w' := by
    have h31 := abs_real_inner_le_norm (u - v) w'
    have h32 := neg_abs_le (inner ℝ (u - v) w')
    have h33 : ‖u - v‖ * ‖w'‖ ≤ ε' * ‖w'‖ := mul_le_mul_of_nonneg_right huv.le (norm_nonneg w')
    linarith
  have h4 : 2 * ε' * ‖w'‖ ≤ ε := by
    have hεK : 2 * ε' * K = ε := by rw [hε']; field_simp
    have h41 : 2 * ε' * ‖w'‖ ≤ 2 * ε' * K :=
      mul_le_mul_of_nonneg_left (by rw [hK]; linarith) (by positivity)
    linarith
  have key : inner ℝ v w - ‖v‖ * δ - ε ≤ inner ℝ u w' - ε' * ‖w'‖ := by linarith
  have key2 : (inner ℝ v w - ‖v‖ * δ - ε) * τ ≤ (inner ℝ u w' - ε' * ‖w'‖) * τ :=
    mul_le_mul_of_nonneg_right key hτpos.le
  have key3 : (inner ℝ u w' - ε' * ‖w'‖) * τ = τ * inner ℝ u w' - ε' * (τ * ‖w'‖) := by ring
  rw [hinner]
  linarith

lemma regSubderiv_ge_of_mem {f : E → EReal} {x_bar v : E}
    (hv : v ∈ subdifferential f x_bar) (w : E) :
    ((inner ℝ v w : ℝ) : EReal) ≤ regularSubderivative f x_bar w := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  have hq2' : q < inner ℝ v w := EReal.coe_lt_coe_iff.1 hq2
  set ε := (inner ℝ v w - q) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hev : ∀ᶠ δ in 𝓝[>] (0:ℝ), ((q : ℝ) : EReal) ≤
      Filter.limsup (fun p : E × ℝ => sInf ((delta f p.1 p.2) '' Metric.closedBall w δ))
        ((fApproach f x_bar) ×ˢ (𝓝[>] (0 : ℝ))) := by
    have h1 : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧ δ < ε / (‖v‖ + 1) :=
      Filter.Eventually.and self_mem_nhdsWithin
        (nhdsWithin_le_nhds (Iio_mem_nhds (div_pos hεpos (by positivity))))
    filter_upwards [h1] with δ hδ
    obtain ⟨hδpos, hδε⟩ := hδ
    refine le_trans ?_ (C_inner_bound hv w hδpos hεpos)
    rw [EReal.coe_le_coe_iff]
    have h2 : δ * (‖v‖ + 1) < ε := by rwa [lt_div_iff₀ (by positivity)] at hδε
    have h3 : ‖v‖ * δ ≤ ε := by nlinarith
    linarith
  have key : ((q : ℝ) : EReal) ≤ regularSubderivative f x_bar w := by
    unfold regularSubderivative
    exact le_limsup_of_frequently_le' hev.frequently
  exact absurd (lt_of_le_of_lt key hq1) (lt_irrefl _)

lemma core_min {f : E → EReal} {x_bar : E} {ε c : ℝ}
    (hclosed : ∀ α : ℝ, α ≤ c + ε →
      IsClosed {x | x ∈ Metric.closedBall x_bar ε ∧ f x ≤ (α : EReal)})
    {x₀ v₀ : E} {R η a₀ : ℝ} (hR : 0 < R) (hη : 0 ≤ η)
    (hball : Metric.closedBall x₀ R ⊆ Metric.closedBall x_bar ε)
    (hfx₀ : f x₀ = (a₀ : EReal)) (ha₀ : a₀ + ‖v₀‖ * R < c + ε)
    (hlow : ∀ y ∈ Metric.closedBall x₀ R,
      ((a₀ + inner ℝ v₀ (y - x₀) - η : ℝ) : EReal) ≤ f y) :
    ∃ z v : E, ∃ b : ℝ, ‖z - x₀‖ < R ∧ IsRegularSubgradientAt f z v ∧
      ‖v - v₀‖ ≤ 4 * η / R + R ∧ f z = (b : EReal) ∧
      a₀ - η - ‖v₀‖ * R ≤ b ∧ b ≤ a₀ + ‖v₀‖ * R := by
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  obtain ⟨M, hM_def⟩ : ∃ M : ℝ, M = 2 * η / R ^ 2 + 1 / 2 := ⟨_, rfl⟩
  have hR2 : 0 < R ^ 2 := by positivity
  have hM : 0 < M := by rw [hM_def]; positivity
  have hMR : M * R ^ 2 = 2 * η + R ^ 2 / 2 := by
    rw [hM_def]; field_simp
  have hMR' : 2 * M * R = 4 * η / R + R := by
    rw [hM_def]; field_simp; ring
  obtain ⟨g, hg⟩ : ∃ g : E → ℝ, ∀ y, g y = -inner ℝ v₀ (y - x₀) + M * ‖y - x₀‖ ^ 2 :=
    ⟨fun y => -inner ℝ v₀ (y - x₀) + M * ‖y - x₀‖ ^ 2, fun _ => rfl⟩
  have hg_cont : Continuous g := by
    have : g = fun y => -inner ℝ v₀ (y - x₀) + M * ‖y - x₀‖ ^ 2 := funext hg
    rw [this]
    exact ((continuous_const.inner (continuous_id.sub continuous_const)).neg).add
      (continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2))
  obtain ⟨K, hK⟩ : ∃ K : EReal, K = ((c + ε : ℝ) : EReal) := ⟨_, rfl⟩
  obtain ⟨χ, hχ⟩ : ∃ χ : E → EReal, ∀ y, χ y = min (f y) K + ((g y : ℝ) : EReal) :=
    ⟨fun y => min (f y) K + ((g y : ℝ) : EReal), fun _ => rfl⟩
  -- Step 1: lower semicontinuity of the truncation
  have hlsc1 : LowerSemicontinuousOn (fun y => min (f y) K) (Metric.closedBall x_bar ε) := by
    intro y hy α hα
    change α < min (f y) K at hα
    obtain ⟨β, hαβ, hβ⟩ := EReal.lt_iff_exists_real_btwn.1 hα
    have hβK : (β : EReal) < K := lt_of_lt_of_le hβ (min_le_right _ _)
    have hβK' : β ≤ c + ε := by
      have h := hβK.le
      rw [hK] at h
      exact EReal.coe_le_coe_iff.1 h
    have hβf : (β : EReal) < f y := lt_of_lt_of_le hβ (min_le_left _ _)
    have hS := hclosed β hβK'
    have hyS : y ∉ {x | x ∈ Metric.closedBall x_bar ε ∧ f x ≤ (β : EReal)} := by
      rintro ⟨_, h⟩
      exact absurd h (not_le.2 hβf)
    have hmem : {x | x ∈ Metric.closedBall x_bar ε ∧ f x ≤ (β : EReal)}ᶜ ∈ 𝓝 y :=
      hS.isOpen_compl.mem_nhds hyS
    have h1 : ∀ᶠ y' in 𝓝[Metric.closedBall x_bar ε] y, y' ∈ Metric.closedBall x_bar ε :=
      self_mem_nhdsWithin
    have h2 : ∀ᶠ y' in 𝓝[Metric.closedBall x_bar ε] y,
        y' ∈ {x | x ∈ Metric.closedBall x_bar ε ∧ f x ≤ (β : EReal)}ᶜ :=
      mem_nhdsWithin_of_mem_nhds hmem
    filter_upwards [h1, h2] with y' hy'1 hy'2
    have hfy' : (β : EReal) < f y' := by
      by_contra hcon
      exact hy'2 ⟨hy'1, not_lt.1 hcon⟩
    show α < min (f y') K
    exact lt_of_lt_of_le hαβ (le_min hfy'.le hβK.le)
  -- Step 2: lower semicontinuity of χ
  have hlsc2 : LowerSemicontinuousOn χ (Metric.closedBall x₀ R) := by
    have h1 := hlsc1.mono hball
    have h2 : LowerSemicontinuousOn (fun y => ((g y : ℝ) : EReal)) (Metric.closedBall x₀ R) :=
      (EReal.continuous_coe_iff.2 hg_cont).continuousOn.lowerSemicontinuousOn
    have h3 := h1.add' h2 (fun x _ => EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _))
      (Or.inr (EReal.coe_ne_top _)))
    have : χ = fun y => min (f y) K + ((g y : ℝ) : EReal) := funext hχ
    rw [this]
    exact h3
  -- Step 3: a minimizer
  obtain ⟨z, hz, hmin⟩ := hlsc2.exists_isMinOn (Metric.nonempty_closedBall.2 hR.le)
    (isCompact_closedBall x₀ R)
  rw [isMinOn_iff] at hmin
  -- the truncation is real-valued on the ball
  have hlowmin : ∀ y ∈ Metric.closedBall x₀ R,
      ((min (a₀ + inner ℝ v₀ (y - x₀) - η) (c + ε) : ℝ) : EReal) ≤ min (f y) K := by
    intro y hy
    apply le_min
    · exact le_trans (EReal.coe_le_coe_iff.2 (min_le_left _ _)) (hlow y hy)
    · rw [hK]; exact EReal.coe_le_coe_iff.2 (min_le_right _ _)
  have hreal : ∀ y ∈ Metric.closedBall x₀ R,
      min (f y) K = (((min (f y) K).toReal : ℝ) : EReal) := by
    intro y hy
    have hne_top : min (f y) K ≠ ⊤ := by
      apply ne_top_of_le_ne_top _ (min_le_right _ _)
      rw [hK]; exact EReal.coe_ne_top _
    have hne_bot : min (f y) K ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hlowmin y hy)
    exact (EReal.coe_toReal hne_top hne_bot).symm
  have hm_low : ∀ y ∈ Metric.closedBall x₀ R,
      min (a₀ + inner ℝ v₀ (y - x₀) - η) (c + ε) ≤ (min (f y) K).toReal := by
    intro y hy
    have h := hlowmin y hy
    rw [hreal y hy] at h
    exact EReal.coe_le_coe_iff.1 h
  have hχreal : ∀ y ∈ Metric.closedBall x₀ R,
      χ y = (((min (f y) K).toReal + g y : ℝ) : EReal) := by
    intro y hy
    rw [hχ y, EReal.coe_add, ← hreal y hy]
  have hminreal : ∀ y ∈ Metric.closedBall x₀ R,
      (min (f z) K).toReal + g z ≤ (min (f y) K).toReal + g y := by
    intro y hy
    have h := hmin y hy
    rw [hχreal z hz, hχreal y hy] at h
    exact EReal.coe_le_coe_iff.1 h
  -- Step 4: the minimizer lies in the open ball
  have hx₀mem : x₀ ∈ Metric.closedBall x₀ R := Metric.mem_closedBall_self hR.le
  have hgx₀ : g x₀ = 0 := by rw [hg]; simp
  have hvR : 0 ≤ ‖v₀‖ * R := mul_nonneg (norm_nonneg _) hR.le
  have ha₀le : a₀ ≤ c + ε := by linarith
  have hmx₀ : (min (f x₀) K).toReal = a₀ := by
    rw [hfx₀, hK, min_eq_left (EReal.coe_le_coe_iff.2 ha₀le), EReal.toReal_coe]
  have hbound : ∀ y ∈ Metric.closedBall x₀ R,
      a₀ - η + M * ‖y - x₀‖ ^ 2 ≤ (min (f y) K).toReal + g y := by
    intro y hy
    have hyR : ‖y - x₀‖ ≤ R := by rwa [Metric.mem_closedBall, dist_eq_norm] at hy
    have hinner : inner ℝ v₀ (y - x₀) ≤ ‖v₀‖ * R :=
      (real_inner_le_norm v₀ (y - x₀)).trans (mul_le_mul_of_nonneg_left hyR (norm_nonneg _))
    have h1 := hm_low y hy
    rw [hg y]
    rcases min_cases (a₀ + inner ℝ v₀ (y - x₀) - η) (c + ε) with ⟨h, _⟩ | ⟨h, _⟩ <;>
      rw [h] at h1 <;> linarith
  have hzx₀ := hminreal x₀ hx₀mem
  rw [hmx₀, hgx₀] at hzx₀
  have hz_lt : ‖z - x₀‖ < R := by
    have h1 := hbound z hz
    by_contra hcon
    push_neg at hcon
    have h3 : R * R ≤ ‖z - x₀‖ * ‖z - x₀‖ := mul_le_mul hcon hcon hR.le (norm_nonneg _)
    have h3' : R ^ 2 ≤ ‖z - x₀‖ ^ 2 := by nlinarith
    have h4 : M * R ^ 2 ≤ M * ‖z - x₀‖ ^ 2 := mul_le_mul_of_nonneg_left h3' hM.le
    linarith
  have hzR : ‖z - x₀‖ ≤ R := hz_lt.le
  -- Step 5: f z is real and bounds
  have hgz_ge : -(‖v₀‖ * R) ≤ g z := by
    rw [hg z]
    have h1 := real_inner_le_norm v₀ (z - x₀)
    have h2 : ‖v₀‖ * ‖z - x₀‖ ≤ ‖v₀‖ * R := mul_le_mul_of_nonneg_left hzR (norm_nonneg _)
    have h3 : 0 ≤ M * ‖z - x₀‖ ^ 2 := by positivity
    linarith
  have hmz_lt : (min (f z) K).toReal < c + ε := by linarith
  have hfz_lt : f z < K := by
    by_contra hcon
    push_neg at hcon
    have : min (f z) K = K := min_eq_right hcon
    rw [this, hK, EReal.toReal_coe] at hmz_lt
    exact lt_irrefl _ hmz_lt
  have hfz_eq : f z = (((min (f z) K).toReal : ℝ) : EReal) := by
    rw [← hreal z hz, min_eq_left hfz_lt.le]
  -- Step 6: the subgradient
  have hv : ‖(v₀ - (2 * M) • (z - x₀)) - v₀‖ ≤ 4 * η / R + R := by
    have e : (v₀ - (2 * M) • (z - x₀)) - v₀ = -((2 * M) • (z - x₀)) := by abel
    rw [e, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 2 * M)]
    have h1 : 2 * M * ‖z - x₀‖ ≤ 2 * M * R := mul_le_mul_of_nonneg_left hzR (by positivity)
    linarith
  refine ⟨z, v₀ - (2 * M) • (z - x₀), (min (f z) K).toReal, hz_lt, ?_, hv, hfz_eq, ?_, ?_⟩
  · -- Step 7: regular subgradient
    refine ⟨?_, ?_, ?_⟩
    · rw [hfz_eq]; exact EReal.bot_lt_coe _
    · rw [hfz_eq]; exact EReal.coe_lt_top _
    refine ⟨fun y => -(M * ‖y - z‖ ^ 2), ?_, Metric.closedBall x₀ R, ?_, ?_⟩
    · rw [Asymptotics.isLittleO_iff]
      intro c' hc'
      have hball' : Metric.ball z (c' / M) ∈ 𝓝 z := Metric.ball_mem_nhds z (by positivity)
      filter_upwards [hball'] with y hy
      rw [Metric.mem_ball, dist_eq_norm, lt_div_iff₀ hM] at hy
      show ‖-(M * ‖y - z‖ ^ 2)‖ ≤ c' * ‖‖y - z‖‖
      have e1 : ‖-(M * ‖y - z‖ ^ 2)‖ = M * ‖y - z‖ ^ 2 := by
        rw [norm_neg, Real.norm_of_nonneg (by positivity)]
      rw [e1, norm_norm]
      have h2 : 0 ≤ ‖y - z‖ := norm_nonneg _
      nlinarith
    · exact Metric.closedBall_mem_nhds_of_mem (by rw [Metric.mem_ball, dist_eq_norm]; exact hz_lt)
    · intro y hy
      show f z + ((inner ℝ (v₀ - (2 * M) • (z - x₀)) (y - z) + -(M * ‖y - z‖ ^ 2) : ℝ) : EReal)
        ≤ f y
      have h1 := hminreal y hy
      have h2 : (((min (f y) K).toReal : ℝ) : EReal) ≤ f y := by
        rw [← hreal y hy]; exact min_le_left _ _
      have hkey : g z - g y =
          inner ℝ (v₀ - (2 * M) • (z - x₀)) (y - z) + -(M * ‖y - z‖ ^ 2) := by
        rw [hg z, hg y]
        have e1 : y - x₀ = (y - z) + (z - x₀) := by abel
        have e2 : inner ℝ v₀ (y - x₀) = inner ℝ v₀ (y - z) + inner ℝ v₀ (z - x₀) := by
          rw [e1, inner_add_right]
        have e3 : ‖y - x₀‖ ^ 2 =
            ‖y - z‖ ^ 2 + 2 * inner ℝ (y - z) (z - x₀) + ‖z - x₀‖ ^ 2 := by
          rw [e1, norm_add_sq_real]
        have e4 : inner ℝ (v₀ - (2 * M) • (z - x₀)) (y - z) =
            inner ℝ v₀ (y - z) - 2 * M * inner ℝ (z - x₀) (y - z) := by
          rw [inner_sub_left, real_inner_smul_left]
        have e5 : inner ℝ (z - x₀) (y - z) = inner ℝ (y - z) (z - x₀) := real_inner_comm _ _
        rw [e2, e3, e4, e5]
        ring
      rw [hfz_eq, ← EReal.coe_add]
      refine le_trans ?_ h2
      apply EReal.coe_le_coe_iff.2
      linarith
  · have h1 := hlow z hz
    rw [hfz_eq] at h1
    have h1' := EReal.coe_le_coe_iff.1 h1
    have h2 : -(‖v₀‖ * R) ≤ inner ℝ v₀ (z - x₀) := by
      have h3 := abs_real_inner_le_norm v₀ (z - x₀)
      have h4 : ‖v₀‖ * ‖z - x₀‖ ≤ ‖v₀‖ * R := mul_le_mul_of_nonneg_left hzR (norm_nonneg _)
      have h5 := neg_abs_le (inner ℝ v₀ (z - x₀))
      linarith
    linarith
  · linarith

lemma mem_subdiff_of_seq {f : E → EReal} {x_bar : E} {c : ℝ} (hc : f x_bar = (c : EReal))
    (z v : ℕ → E) (b : ℕ → ℝ) (hfz : ∀ n, f (z n) = (b n : EReal))
    (hz : Tendsto z atTop (𝓝 x_bar)) (hb : Tendsto b atTop (𝓝 c))
    (hreg : ∀ n, IsRegularSubgradientAt f (z n) (v n)) {C : ℝ} (hbdd : ∀ n, ‖v n‖ ≤ C) :
    ∃ v_bar ∈ subdifferential f x_bar, ∃ ns : ℕ → ℕ, StrictMono ns ∧
      Tendsto (v ∘ ns) atTop (𝓝 v_bar) := by
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  have hmem : ∀ n, v n ∈ Metric.closedBall (0 : E) C := by
    intro n
    rw [Metric.mem_closedBall, _root_.dist_zero_right]
    exact hbdd n
  obtain ⟨v_bar, _, ns, hns, hlim⟩ := (isCompact_closedBall (0 : E) C).tendsto_subseq hmem
  refine ⟨v_bar, ?_, ns, hns, hlim⟩
  refine ⟨?_, ?_, z ∘ ns, v ∘ ns, hz.comp hns.tendsto_atTop, ?_, hlim, fun i => hreg (ns i)⟩
  · rw [hc]; exact EReal.bot_lt_coe c
  · rw [hc]; exact EReal.coe_lt_top c
  · rw [hc]
    have hfun : (fun n => f ((z ∘ ns) n)) = fun n => ((b (ns n) : ℝ) : EReal) := by
      funext n
      exact hfz (ns n)
    rw [hfun]
    exact EReal.tendsto_coe.mpr (hb.comp hns.tendsto_atTop)

lemma R_step {f : E → EReal} {x_bar : E} {c ε δ β : ℝ} (hc : f x_bar = (c : EReal))
    (hε : 0 < ε)
    (hclosed : ∀ α : ℝ, α ≤ c + ε →
      IsClosed {x | x ∈ Metric.closedBall x_bar ε ∧ f x ≤ (α : EReal)})
    (hδ : 0 < δ)
    (hfreq : ∃ᶠ p in (fApproach f x_bar) ×ˢ (𝓝[>] (0 : ℝ)),
      (β : EReal) < sInf ((delta f p.1 p.2) '' Metric.closedBall (0 : E) δ))
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ z v : E, ∃ b : ℝ, ‖z - x_bar‖ ≤ r ∧ |b - c| ≤ r ∧
      f z = (b : EReal) ∧ IsRegularSubgradientAt f z v ∧ ‖v‖ ≤ 4 * |β| / δ + 1 := by
  -- choice of the auxiliary radius r'
  set s := min r ε with hs
  have hs0 : 0 < s := lt_min hr hε
  have hsr : s ≤ r := min_le_left _ _
  have hsε : s ≤ ε := min_le_right _ _
  have hβ0 : 0 ≤ |β| := abs_nonneg β
  set K := 1 + δ + |β| with hK
  have hK0 : 0 < K := by rw [hK]; linarith
  set r' := s / K with hr'
  have hr'0 : 0 < r' := div_pos hs0 hK0
  have hr'K : r' * K = s := by rw [hr']; field_simp
  have hr'K' : r' + r' * δ + r' * |β| = s := by rw [← hr'K, hK]; ring
  have hr'β : 0 ≤ r' * |β| := mul_nonneg hr'0.le hβ0
  have hr'δ : 0 ≤ r' * δ := mul_nonneg hr'0.le hδ.le
  -- eventually-statement in the product filter
  have hev : ∀ᶠ p in (fApproach f x_bar) ×ˢ (𝓝[>] (0 : ℝ)),
      (‖p.1 - x_bar‖ < r' ∧ f p.1 ∈ Set.Ioo (((c - r' : ℝ)) : EReal) ((c + r' : ℝ) : EReal)) ∧
      (p.2 ∈ Set.Ioo 0 r') := by
    have h1 : ∀ᶠ x in 𝓝 x_bar, ‖x - x_bar‖ < r' := by
      filter_upwards [Metric.ball_mem_nhds x_bar hr'0] with x hx
      rwa [Metric.mem_ball, dist_eq_norm] at hx
    have h2 : ∀ᶠ x in Filter.comap f (𝓝 (f x_bar)),
        f x ∈ Set.Ioo (((c - r' : ℝ)) : EReal) ((c + r' : ℝ) : EReal) := by
      apply Filter.preimage_mem_comap
      apply Ioo_mem_nhds
      · rw [hc]; exact_mod_cast (by linarith : c - r' < c)
      · rw [hc]; exact_mod_cast (by linarith : c < c + r')
    have h12 : ∀ᶠ x in fApproach f x_bar,
        ‖x - x_bar‖ < r' ∧ f x ∈ Set.Ioo (((c - r' : ℝ)) : EReal) ((c + r' : ℝ) : EReal) :=
      (h1.filter_mono inf_le_left).and (h2.filter_mono inf_le_right)
    have h3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioo 0 r' := Ioo_mem_nhdsGT hr'0
    exact h12.prod_mk h3
  obtain ⟨p, hβ, ⟨hx, hfx⟩, hτ⟩ := (hfreq.and_eventually hev).exists
  set x := p.1 with hxdef
  set τ := p.2 with hτdef
  obtain ⟨hτ0, hτr⟩ := hτ
  have hfx_ne_top : f x ≠ ⊤ := ne_top_of_lt hfx.2
  have hfx_ne_bot : f x ≠ ⊥ := ne_bot_of_gt hfx.1
  set a₀ := (f x).toReal with ha₀
  have hfa : f x = (a₀ : EReal) := (EReal.coe_toReal hfx_ne_top hfx_ne_bot).symm
  have ha1 : c - r' < a₀ := by
    have := hfx.1; rw [hfa] at this; exact_mod_cast this
  have ha2 : a₀ < c + r' := by
    have := hfx.2; rw [hfa] at this; exact_mod_cast this
  have hR : 0 < τ * δ := mul_pos hτ0 hδ
  have hη : 0 ≤ |β| * τ := mul_nonneg hβ0 hτ0.le
  have hτδ : τ * δ ≤ r' * δ := mul_le_mul_of_nonneg_right hτr.le hδ.le
  have hτβ : |β| * τ ≤ r' * |β| := by
    rw [mul_comm r']; exact mul_le_mul_of_nonneg_left hτr.le hβ0
  have hball : Metric.closedBall x (τ * δ) ⊆ Metric.closedBall x_bar ε := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy ⊢
    calc ‖y - x_bar‖ = ‖(y - x) + (x - x_bar)‖ := by congr 1; abel
      _ ≤ ‖y - x‖ + ‖x - x_bar‖ := norm_add_le _ _
      _ ≤ ε := by linarith
  have ha₀' : a₀ + ‖(0:E)‖ * (τ * δ) < c + ε := by
    rw [norm_zero, zero_mul, add_zero]; linarith
  have hlow : ∀ y ∈ Metric.closedBall x (τ * δ),
      ((a₀ + inner ℝ (0:E) (y - x) - |β| * τ : ℝ) : EReal) ≤ f y := by
    intro y hy
    rw [inner_zero_left, add_zero]
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    have hw : τ⁻¹ • (y - x) ∈ Metric.closedBall (0:E) δ := by
      rw [Metric.mem_closedBall, _root_.dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos hτ0, inv_mul_le_iff₀ hτ0]
      exact hy
    have hxy : x + τ • (τ⁻¹ • (y - x)) = y := by
      rw [smul_smul, mul_inv_cancel₀ hτ0.ne', one_smul]; abel
    have h1 : (β : EReal) < delta f x τ (τ⁻¹ • (y - x)) :=
      lt_of_lt_of_le hβ (sInf_le ⟨_, hw, rfl⟩)
    unfold delta differenceQuotient at h1
    rw [hxy, hfa] at h1
    have h2 : ¬ (f y ≤ ((a₀ + β * τ : ℝ) : EReal)) := by
      rw [← ereal_dq_le_iff hτ0]; exact not_le.mpr h1
    have h3 : ((a₀ - |β| * τ : ℝ) : EReal) ≤ ((a₀ + β * τ : ℝ) : EReal) := by
      have h4 := neg_abs_le β
      have h5 : -|β| * τ ≤ β * τ := mul_le_mul_of_nonneg_right h4 hτ0.le
      exact_mod_cast (by linarith : a₀ - |β| * τ ≤ a₀ + β * τ)
    exact le_trans h3 (not_le.mp h2).le
  obtain ⟨z, v, b, hz, hreg, hv, hfz, hb1, hb2⟩ := core_min hclosed hR hη hball hfa ha₀' hlow
  refine ⟨z, v, b, ?_, ?_, hfz, hreg, ?_⟩
  · calc ‖z - x_bar‖ = ‖(z - x) + (x - x_bar)‖ := by congr 1; abel
      _ ≤ ‖z - x‖ + ‖x - x_bar‖ := norm_add_le _ _
      _ ≤ r := by linarith
  · rw [norm_zero, zero_mul, sub_zero] at hb1
    rw [norm_zero, zero_mul, add_zero] at hb2
    rw [abs_le]; constructor <;> linarith
  · rw [sub_zero] at hv
    have h6 : 4 * (|β| * τ) / (τ * δ) = 4 * |β| / δ := by
      field_simp
    rw [h6] at hv
    have h7 : τ * δ ≤ 1 := by linarith
    linarith

lemma subdiff_nonempty_of_regSubderiv {f : E → EReal} {x_bar : E} (hlsc : LocalLscAt f x_bar)
    (h : ⊥ < regularSubderivative f x_bar 0) : (subdifferential f x_bar).Nonempty := by
  obtain ⟨c, ε, hc, hε, hclosed⟩ := localLsc_unpack hlsc
  -- Step 2: some δ > 0 with ⊥ < inner limsup
  have hδex : ∃ δ : ℝ, 0 < δ ∧ ⊥ < Filter.limsup
      (fun p : E × ℝ => sInf ((delta f p.1 p.2) '' Metric.closedBall (0 : E) δ))
      ((fApproach f x_bar) ×ˢ (𝓝[>] (0 : ℝ))) := by
    by_contra hcon
    push_neg at hcon
    have hle : regularSubderivative f x_bar 0 ≤ ⊥ := by
      unfold regularSubderivative
      refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact hcon δ hδ
    exact absurd h (not_lt.mpr hle)
  obtain ⟨δ, hδ, hHδ⟩ := hδex
  -- Step 3: a real β below the inner limsup
  obtain ⟨β, -, hβ⟩ := EReal.lt_iff_exists_real_btwn.mp hHδ
  have hfreq := Filter.frequently_lt_of_lt_limsup (by isBoundedDefault) hβ
  -- Step 4: the sequence
  have hstep : ∀ n : ℕ, ∃ z v : E, ∃ b : ℝ, ‖z - x_bar‖ ≤ 1 / ((n : ℝ) + 1) ∧
      |b - c| ≤ 1 / ((n : ℝ) + 1) ∧ f z = (b : EReal) ∧ IsRegularSubgradientAt f z v ∧
      ‖v‖ ≤ 4 * |β| / δ + 1 := by
    intro n
    have hn0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
    have hn1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact R_step hc hε hclosed hδ hfreq hn0 hn1
  choose z v b hz hb hfz hreg hv using hstep
  -- Step 5: limit
  have hzt : Tendsto z atTop (𝓝 x_bar) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) hz tendsto_one_div_add_atTop_nhds_zero_nat
  have hbt : Tendsto b atTop (𝓝 c) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Real.norm_eq_abs]; exact hb n
  obtain ⟨v_bar, hv_bar, -⟩ := mem_subdiff_of_seq hc z v b hfz hzt hbt hreg hv
  exact ⟨v_bar, hv_bar⟩

lemma modulus_real_of_calm {f : E → EReal} {x_bar : E} (h : IsCalmFromBelowAt f x_bar) :
    ∃ κb : ℝ, 0 ≤ κb ∧ exactCalmFromBelowModulus f x_bar = (κb : EReal) ∧
      (∀ κ : ℝ, κb < κ → IsCalmFromBelowAtWith f x_bar κ) ∧
      (∀ κ : ℝ, κ < κb → ¬ IsCalmFromBelowAtWith f x_bar κ) := by
  set K := {κ : ℝ | IsCalmFromBelowAtWith f x_bar κ} with hK
  obtain ⟨κ₀, hκ₀⟩ := h
  have hne : K.Nonempty := ⟨κ₀, hκ₀⟩
  have hbdd : BddBelow K := ⟨0, fun κ hκ => hκ.1⟩
  have hupc : ∀ κ₁ κ₂ : ℝ, κ₁ ∈ K → κ₁ ≤ κ₂ → κ₂ ∈ K := by
    intro κ₁ κ₂ h1 h12
    obtain ⟨h0, hb, ht, V, hV, hVx⟩ := h1
    refine ⟨le_trans h0 h12, hb, ht, V, hV, fun x hx => le_trans ?_ (hVx x hx)⟩
    apply EReal.sub_le_sub le_rfl
    have hn := norm_nonneg (x - x_bar)
    have hle : κ₁ * ‖x - x_bar‖ ≤ κ₂ * ‖x - x_bar‖ := mul_le_mul_of_nonneg_right h12 hn
    exact_mod_cast hle
  refine ⟨sInf K, le_csInf hne (fun κ hκ => hκ.1), ?_, ?_, ?_⟩
  · unfold exactCalmFromBelowModulus
    rw [← hK]
    exact (Monotone.map_csInf_of_continuousAt
      continuous_coe_real_ereal.continuousAt EReal.coe_strictMono.monotone hne hbdd).symm
  · intro κ hκ
    obtain ⟨κ₁, h1, h1lt⟩ := exists_lt_of_csInf_lt hne hκ
    exact hupc κ₁ κ h1 h1lt.le
  · intro κ hκ hmem
    exact absurd (csInf_le hbdd hmem) (not_le.mpr hκ)

lemma M_norm_le {w u : E} {t : ℝ} (hw : ‖w‖ = 1) (ht : 0 < t) :
    ‖t • w + u‖ ≤ t + inner ℝ w u + ‖u‖ ^ 2 / t := by
  have hwu : |inner ℝ w u| ≤ ‖u‖ := by
    have := abs_real_inner_le_norm w u
    rwa [hw, one_mul] at this
  have hsq : ‖t • w + u‖ ^ 2 = t ^ 2 + 2 * t * inner ℝ w u + ‖u‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, real_inner_smul_left, hw, Real.norm_eq_abs, abs_of_pos ht]
    ring
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = ‖u‖ ^ 2 / t := ⟨_, rfl⟩
  rw [← hq]
  have hqt : q * t = ‖u‖ ^ 2 := by rw [hq, div_mul_cancel₀ _ ht.ne']
  have hab := abs_le.mp hwu
  have hS : 0 ≤ t + inner ℝ w u + q := by
    have h1 : 0 ≤ (t + inner ℝ w u + q) * t := by
      have h2 : (t + inner ℝ w u + q) * t = t ^ 2 + inner ℝ w u * t + ‖u‖ ^ 2 := by
        rw [← hqt]; ring
      rw [h2]
      nlinarith [norm_nonneg u, sq_nonneg (t - ‖u‖), mul_le_mul_of_nonneg_right hab.1 ht.le,
        mul_nonneg ht.le (norm_nonneg u)]
    nlinarith
  have hS2 : ‖t • w + u‖ ^ 2 ≤ (t + inner ℝ w u + q) ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg (inner ℝ w u + q), sq_nonneg ‖u‖]
  nlinarith [norm_nonneg (t • w + u)]

lemma M_calm_ball {f : E → EReal} {x_bar : E} {c κ : ℝ} (hc : f x_bar = (c : EReal))
    (h : IsCalmFromBelowAtWith f x_bar κ) :
    ∃ r > 0, ∀ y, ‖y - x_bar‖ < r → ((c - κ * ‖y - x_bar‖ : ℝ) : EReal) ≤ f y := by
  obtain ⟨_, _, _, V, hV, hVf⟩ := h
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨r, hr, fun y hy => ?_⟩
  have := hVf y (hrV (by rw [Metric.mem_ball, dist_eq_norm]; exact hy))
  rw [hc] at this
  rw [EReal.coe_sub, EReal.coe_mul]
  exact this

lemma M_not_calm {f : E → EReal} {x_bar : E} {c κ : ℝ} (hc : f x_bar = (c : EReal))
    (hκ : 0 ≤ κ) (h : ¬ IsCalmFromBelowAtWith f x_bar κ) {r : ℝ} (hr : 0 < r) :
    ∃ x, ‖x - x_bar‖ < r ∧ f x < ((c - κ * ‖x - x_bar‖ : ℝ) : EReal) := by
  by_contra hne
  push_neg at hne
  apply h
  refine ⟨hκ, by rw [hc]; exact EReal.bot_lt_coe c, by rw [hc]; exact EReal.coe_lt_top c,
    Metric.ball x_bar r, Metric.ball_mem_nhds x_bar hr, fun x hx => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have := hne x hx
  rw [hc, ← EReal.coe_mul, ← EReal.coe_sub]
  exact this

lemma approx_subgrad_modulus {f : E → EReal} {x_bar : E} {c ε : ℝ} (hc : f x_bar = (c : EReal))
    (hε : 0 < ε)
    (hclosed : ∀ α : ℝ, α ≤ c + ε →
      IsClosed {x | x ∈ Metric.closedBall x_bar ε ∧ f x ≤ (α : EReal)})
    {κb : ℝ} (hκb : 0 ≤ κb)
    (hup : ∀ κ : ℝ, κb < κ → IsCalmFromBelowAtWith f x_bar κ)
    (hlow : ∀ κ : ℝ, κ < κb → ¬ IsCalmFromBelowAtWith f x_bar κ)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ z v : E, ∃ b : ℝ, ‖z - x_bar‖ < ζ ∧ |b - c| < ζ ∧ f z = (b : EReal) ∧
      IsRegularSubgradientAt f z v ∧ |‖v‖ - κb| ≤ ζ := by
  rcases hκb.eq_or_lt with h0 | hpos
  · -- case κb = 0
    subst h0
    have he_pos : 0 < ζ / 8 := by positivity
    obtain ⟨r₁, hr₁, hV⟩ := M_calm_ball hc (hup (ζ / 8) he_pos)
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = min (r₁ / 2) (min ε (min 1 (ζ / 2))) := ⟨_, rfl⟩
    have ht_pos : 0 < t := by
      rw [ht]; exact lt_min (by positivity) (lt_min hε (lt_min one_pos (by positivity)))
    have ht1 : t ≤ r₁ / 2 := by rw [ht]; exact min_le_left _ _
    have ht2 : t ≤ ε := by rw [ht]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have ht3 : t ≤ 1 := by
      rw [ht]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have ht4 : t ≤ ζ / 2 := by
      rw [ht]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    have hlow0 : ∀ y ∈ Metric.closedBall x_bar t,
        ((c + inner ℝ (0 : E) (y - x_bar) - ζ / 8 * t : ℝ) : EReal) ≤ f y := by
      intro y hy
      rw [Metric.mem_closedBall, dist_eq_norm] at hy
      refine le_trans ?_ (hV y (by linarith))
      rw [EReal.coe_le_coe_iff, inner_zero_left, add_zero]
      have := mul_le_mul_of_nonneg_left hy he_pos.le
      linarith
    obtain ⟨z, v, b, hz, hreg, hv, hfz, hb1, hb2⟩ :=
      core_min (x₀ := x_bar) (v₀ := (0 : E)) (R := t) (η := ζ / 8 * t) (a₀ := c) hclosed ht_pos
        (by positivity) (Metric.closedBall_subset_closedBall ht2) hc
        (by rw [norm_zero, zero_mul, add_zero]; linarith) hlow0
    simp only [norm_zero, zero_mul, sub_zero, add_zero] at hb1 hb2 hv
    have h4 : 4 * (ζ / 8 * t) / t = ζ / 2 := by rw [div_eq_iff ht_pos.ne']; ring
    rw [h4] at hv
    refine ⟨z, v, b, by linarith, ?_, hfz, hreg, ?_⟩
    · have := mul_le_mul_of_nonneg_left ht3 he_pos.le
      rw [abs_lt]; constructor <;> linarith
    · rw [sub_zero, abs_of_nonneg (norm_nonneg _)]
      linarith
  · -- case κb > 0
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = min (1 / 2) (ζ / (4 * κb + 17)) := ⟨_, rfl⟩
    have hρ_pos : 0 < ρ := by rw [hρ]; exact lt_min (by norm_num) (by positivity)
    have hρ1 : ρ ≤ 1 / 2 := by rw [hρ]; exact min_le_left _ _
    have hρ2 : ρ * (4 * κb + 17) ≤ ζ := by
      have : ρ ≤ ζ / (4 * κb + 17) := by rw [hρ]; exact min_le_right _ _
      rwa [le_div_iff₀ (by positivity)] at this
    obtain ⟨e, he⟩ : ∃ e : ℝ, e = ρ ^ 2 := ⟨_, rfl⟩
    have he_pos : 0 < e := by rw [he]; positivity
    have he1 : e ≤ 1 / 4 := by rw [he]; nlinarith
    obtain ⟨r₁, hr₁, hV⟩ := M_calm_ball hc (hup (κb + e) (by linarith))
    obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = max 0 (κb - e) := ⟨_, rfl⟩
    have hκ0 : 0 ≤ κ := by rw [hκ]; exact le_max_left _ _
    have hκ1 : κb - e ≤ κ := by rw [hκ]; exact le_max_right _ _
    have hκlt : κ < κb := by rw [hκ]; exact max_lt hpos (by linarith)
    obtain ⟨m, hm⟩ : ∃ m : ℝ, m = min (min r₁ ε) (min 1 ζ) := ⟨_, rfl⟩
    have hm_pos : 0 < m := by rw [hm]; exact lt_min (lt_min hr₁ hε) (lt_min one_pos hζ)
    have hm1 : m ≤ r₁ := by rw [hm]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    have hm2 : m ≤ ε := by rw [hm]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hm3 : m ≤ 1 := by rw [hm]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hm4 : m ≤ ζ := by rw [hm]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    obtain ⟨r₂, hr₂⟩ : ∃ r₂ : ℝ, r₂ = m / (6 * κb + 10) := ⟨_, rfl⟩
    have hr₂_pos : 0 < r₂ := by rw [hr₂]; positivity
    have hr₂m : r₂ * (6 * κb + 10) = m := by rw [hr₂, div_mul_cancel₀ _ (by positivity)]
    have hr₂κ : 0 ≤ r₂ * κb := mul_nonneg hr₂_pos.le hκb
    have hr₂10 : 10 * r₂ ≤ m := by linarith
    obtain ⟨x, hx, hfx⟩ := M_not_calm hc hκ0 (hlow κ hκlt) hr₂_pos
    obtain ⟨t, ht⟩ : ∃ t : ℝ, ‖x - x_bar‖ = t := ⟨_, rfl⟩
    rw [ht] at hx hfx
    have ht_pos : 0 < t := by
      rcases (norm_nonneg (x - x_bar)).eq_or_lt with h | h
      · exfalso
        have hxx : x = x_bar := by rw [← sub_eq_zero, ← norm_eq_zero]; exact h.symm
        rw [ht] at h
        rw [← h, mul_zero, sub_zero, hxx, hc] at hfx
        exact lt_irrefl _ hfx
      · rwa [ht] at h
    have hfx_low := hV x (by rw [ht]; linarith)
    rw [ht] at hfx_low
    obtain ⟨a₀, hfa⟩ : ∃ a : ℝ, f x = (a : EReal) :=
      ⟨(f x).toReal, (EReal.coe_toReal (ne_top_of_lt hfx)
        ((EReal.bot_lt_coe _).trans_le hfx_low).ne').symm⟩
    rw [hfa, EReal.coe_lt_coe_iff] at hfx
    rw [hfa, EReal.coe_le_coe_iff] at hfx_low
    have ha_up : a₀ < c - (κb - e) * t := by
      have := mul_le_mul_of_nonneg_right hκ1 ht_pos.le
      linarith
    obtain ⟨w, hw⟩ : ∃ w : E, w = t⁻¹ • (x - x_bar) := ⟨_, rfl⟩
    have hw1 : ‖w‖ = 1 := by
      rw [hw, norm_smul, ht, norm_inv, Real.norm_eq_abs, abs_of_pos ht_pos,
        inv_mul_cancel₀ ht_pos.ne']
    have hxw : x - x_bar = t • w := by
      rw [hw, smul_smul, mul_inv_cancel₀ ht_pos.ne', one_smul]
    obtain ⟨v₀, hv₀⟩ : ∃ v₀ : E, v₀ = -(κb • w) := ⟨_, rfl⟩
    have hv₀n : ‖v₀‖ = κb := by
      rw [hv₀, norm_neg, norm_smul, hw1, Real.norm_eq_abs, abs_of_nonneg hκb, mul_one]
    have hρt : ρ * t ≤ 1 / 2 * t := mul_le_mul_of_nonneg_right hρ1 ht_pos.le
    have het : e * t ≤ 1 / 4 * t := mul_le_mul_of_nonneg_right he1 ht_pos.le
    have hκt : κb * (ρ * t) ≤ κb * (1 / 2 * t) := mul_le_mul_of_nonneg_left hρt hκb
    have hetκ : e * (t * κb) ≤ 1 / 4 * (t * κb) :=
      mul_le_mul_of_nonneg_right he1 (mul_nonneg ht_pos.le hκb)
    have htr : κb * t ≤ κb * r₂ := mul_le_mul_of_nonneg_left hx.le hκb
    have hball : Metric.closedBall x (ρ * t) ⊆ Metric.closedBall x_bar ε := by
      intro y hy
      rw [Metric.mem_closedBall, dist_eq_norm] at hy ⊢
      have := norm_sub_le_norm_sub_add_norm_sub y x x_bar
      rw [ht] at this
      linarith
    have hκt0 : 0 ≤ κb * t := mul_nonneg hκb ht_pos.le
    have ha₀' : a₀ + ‖v₀‖ * (ρ * t) < c + ε := by
      rw [hv₀n]
      linarith
    have hlow' : ∀ y ∈ Metric.closedBall x (ρ * t),
        ((a₀ + inner ℝ v₀ (y - x) - t * e * (κb + 4) : ℝ) : EReal) ≤ f y := by
      intro y hy
      rw [Metric.mem_closedBall, dist_eq_norm] at hy
      have hyx : y - x_bar = t • w + (y - x) := by rw [← hxw]; abel
      have hnorm := M_norm_le (u := y - x) hw1 ht_pos
      rw [← hyx] at hnorm
      have htri := norm_sub_le_norm_sub_add_norm_sub y x x_bar
      rw [ht] at htri
      have hfy := hV y (by linarith)
      refine le_trans ?_ hfy
      rw [EReal.coe_le_coe_iff]
      have hinner : inner ℝ v₀ (y - x) = -(κb * inner ℝ w (y - x)) := by
        rw [hv₀, inner_neg_left, real_inner_smul_left]
      have hwu : |inner ℝ w (y - x)| ≤ ‖y - x‖ := by
        have := abs_real_inner_le_norm w (y - x)
        rwa [hw1, one_mul] at this
      have hab := abs_le.mp hwu
      have hq : ‖y - x‖ ^ 2 / t ≤ e * t := by
        rw [div_le_iff₀ ht_pos, he]
        have : ‖y - x‖ ^ 2 ≤ (ρ * t) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
        nlinarith
      have hq0 : 0 ≤ ‖y - x‖ ^ 2 / t := by positivity
      rw [hinner]
      have k1 : (κb + e) * ‖y - x_bar‖ ≤
          (κb + e) * (t + inner ℝ w (y - x) + ‖y - x‖ ^ 2 / t) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
      have k2 : 0 ≤ κb * (e * t - ‖y - x‖ ^ 2 / t) := mul_nonneg hκb (by linarith)
      have k3 : 0 ≤ e * (2 * t - inner ℝ w (y - x) - ‖y - x‖ ^ 2 / t) :=
        mul_nonneg he_pos.le (by linarith)
      linarith
    obtain ⟨z, v, b, hz, hreg, hv, hfz, hb1, hb2⟩ :=
      core_min (x₀ := x) (v₀ := v₀) (R := ρ * t) (η := t * e * (κb + 4)) (a₀ := a₀) hclosed
        (by positivity) (by positivity) hball hfa ha₀' hlow'
    rw [hv₀n] at hb1 hb2
    have h4 : 4 * (t * e * (κb + 4)) / (ρ * t) = 4 * ρ * (κb + 4) := by
      rw [div_eq_iff (by positivity), he]; ring
    rw [h4] at hv
    refine ⟨z, v, b, ?_, ?_, hfz, hreg, ?_⟩
    · have := norm_sub_le_norm_sub_add_norm_sub z x x_bar
      rw [ht] at this
      linarith
    · rw [abs_lt]; constructor <;> linarith
    · have h5 := abs_norm_sub_norm_le v v₀
      rw [hv₀n] at h5
      have h6 : ρ * t ≤ ρ * 1 := mul_le_mul_of_nonneg_left (by linarith) hρ_pos.le
      linarith

lemma exists_subgrad_norm_eq_modulus {f : E → EReal} {x_bar : E} (hlsc : LocalLscAt f x_bar)
    (hcalm : IsCalmFromBelowAt f x_bar) :
    ∃ v_bar ∈ subdifferential f x_bar,
      ((‖v_bar‖ : ℝ) : EReal) = exactCalmFromBelowModulus f x_bar := by
  obtain ⟨c, ε, hc, hε, hclosed⟩ := localLsc_unpack hlsc
  obtain ⟨κb, hκb0, hmod, hup, hlow⟩ := modulus_real_of_calm hcalm
  have key : ∀ n : ℕ, ∃ z v : E, ∃ b : ℝ, ‖z - x_bar‖ < 1 / ((n : ℝ) + 1) ∧
      |b - c| < 1 / ((n : ℝ) + 1) ∧ f z = (b : EReal) ∧
      IsRegularSubgradientAt f z v ∧ |‖v‖ - κb| ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    exact approx_subgrad_modulus hc hε hclosed hκb0 hup hlow (by positivity)
  choose z v b hz hb hfz hreg hv using key
  have hζ : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hzt : Tendsto z atTop (𝓝 x_bar) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hz n).le) hζ
  have hbt : Tendsto b atTop (𝓝 c) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => by rw [Real.norm_eq_abs]; exact (hb n).le) hζ
  have hbdd : ∀ n, ‖v n‖ ≤ κb + 1 := by
    intro n
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have h3 := (abs_le.mp (hv n)).2
    linarith
  obtain ⟨v_bar, hv_bar, ns, hns, hlim⟩ := mem_subdiff_of_seq hc z v b hfz hzt hbt hreg hbdd
  refine ⟨v_bar, hv_bar, ?_⟩
  rw [hmod]
  have h1 : Tendsto (fun k => ‖v (ns k)‖) atTop (𝓝 ‖v_bar‖) :=
    (continuous_norm.tendsto v_bar).comp hlim
  have hvt : Tendsto (fun n => ‖v n‖) atTop (𝓝 κb) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => by rw [Real.norm_eq_abs]; exact hv n) hζ
  have h2 : Tendsto (fun k => ‖v (ns k)‖) atTop (𝓝 κb) := hvt.comp hns.tendsto_atTop
  have heq : ‖v_bar‖ = κb := tendsto_nhds_unique h1 h2
  rw [heq]

lemma modulus_le_of_subderiv_ge {f : E → EReal} {x_bar : E} (hc : IsCalmFromBelowAt f x_bar)
    {L : ℝ} (h : ∀ w ∈ (unitBall : Set E), ((-L : ℝ) : EReal) ≤ subderivative f x_bar w) :
    exactCalmFromBelowModulus f x_bar ≤ (L : EReal) := by
  rw [modulus_eq_of_calm hc, EReal.neg_le]
  apply le_sInf
  rintro _ ⟨w, hw, rfl⟩
  have := h w hw
  rwa [EReal.coe_neg] at this

lemma modulus_eq_top_of_not_calm {f : E → EReal} {x_bar : E} (hc : ¬ IsCalmFromBelowAt f x_bar) :
    exactCalmFromBelowModulus f x_bar = ⊤ := by
  unfold exactCalmFromBelowModulus
  have : {κ : ℝ | IsCalmFromBelowAtWith f x_bar κ} = ∅ := by
    ext κ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    exact hc ⟨κ, h⟩
  rw [this, Set.image_empty, _root_.sInf_empty]


end Aux

theorem RW_chap_8_32
  (f : E → EReal)
  (x_bar : E) :
  ((IsCalmFromBelowAt f x_bar) ↔
      subderivative f x_bar 0 = 0) ∧
  ((IsCalmFromBelowAt f x_bar) ↔
      ∀ (w : E), subderivative f x_bar w > ⊥) ∧
  (exactCalmFromBelowModulus f x_bar =
      (-1 : EReal) *
        sInf ((fun (w : E) => subderivative f x_bar w) '' unitBall)) ∧
  ((LocalLscAt f x_bar) →
    (((Set.Nonempty (subdifferential f x_bar)) ↔
        regularSubderivative f x_bar 0 = 0) ∧
      ((Set.Nonempty (subdifferential f x_bar)) ↔
        ∀ (w : E), regularSubderivative f x_bar w > ⊥))) ∧
  ((LocalLscAt f x_bar ∧ IsCalmFromBelowAt f x_bar) →
    ∃ v_bar ∈ subdifferential f x_bar,
      (((‖v_bar‖ : ℝ) : EReal) = exactCalmFromBelowModulus f x_bar)) ∧
  ((IsRegularAt f x_bar) →
    ((IsCalmFromBelowAt f x_bar) ↔
        Set.Nonempty (subdifferential f x_bar)) ∧
    (exactCalmFromBelowModulus f x_bar =
      distToSetEReal (0 : E) (subdifferential f x_bar))) := by
  have hP1 : IsCalmFromBelowAt f x_bar ↔ subderivative f x_bar 0 = 0 := by
    constructor
    · rintro ⟨κ, hκ⟩
      apply le_antisymm (subderiv_zero_le f x_bar)
      have := subderiv_ge_of_calm hκ 0
      simpa using this
    · intro h
      by_contra hc
      rw [subderiv_zero_eq_bot_of_not_calm hc] at h
      exact EReal.bot_ne_zero h
  have hP2 : IsCalmFromBelowAt f x_bar ↔ ∀ w, subderivative f x_bar w > ⊥ := by
    constructor
    · rintro ⟨κ, hκ⟩ w
      exact lt_of_lt_of_le (EReal.bot_lt_coe _) (subderiv_ge_of_calm hκ w)
    · intro h
      by_contra hc
      have := h 0
      rw [subderiv_zero_eq_bot_of_not_calm hc] at this
      exact lt_irrefl _ this
  have hP3 : exactCalmFromBelowModulus f x_bar =
      (-1 : EReal) * sInf ((fun (w : E) => subderivative f x_bar w) '' unitBall) := by
    rw [EReal.neg_mul, one_mul]
    by_cases hc : IsCalmFromBelowAt f x_bar
    · exact modulus_eq_of_calm hc
    · have h2 : sInf ((fun (w : E) => subderivative f x_bar w) '' unitBall) = ⊥ := by
        apply le_antisymm _ bot_le
        have h0 : (0 : E) ∈ (unitBall : Set E) := by
          simp [unitBall]
        calc sInf ((fun (w : E) => subderivative f x_bar w) '' unitBall)
            ≤ subderivative f x_bar 0 := sInf_le ⟨0, h0, rfl⟩
          _ = ⊥ := subderiv_zero_eq_bot_of_not_calm hc
      rw [modulus_eq_top_of_not_calm hc, h2, EReal.neg_bot]
  have hP4 : LocalLscAt f x_bar →
      (((subdifferential f x_bar).Nonempty ↔ regularSubderivative f x_bar 0 = 0) ∧
      ((subdifferential f x_bar).Nonempty ↔ ∀ w, regularSubderivative f x_bar w > ⊥)) := by
    intro hlsc
    refine ⟨⟨fun ⟨v, hv⟩ => ?_, fun h => ?_⟩, ⟨fun ⟨v, hv⟩ w => ?_, fun h => ?_⟩⟩
    · apply le_antisymm (regSubderiv_zero_le f x_bar)
      simpa using regSubderiv_ge_of_mem hv 0
    · apply subdiff_nonempty_of_regSubderiv hlsc
      rw [h]
      exact EReal.bot_lt_zero
    · exact lt_of_lt_of_le (EReal.bot_lt_coe _) (regSubderiv_ge_of_mem hv w)
    · exact subdiff_nonempty_of_regSubderiv hlsc (h 0)
  refine ⟨hP1, hP2, hP3, hP4, fun ⟨hlsc, hcalm⟩ => exists_subgrad_norm_eq_modulus hlsc hcalm, ?_⟩
  rintro ⟨_, hlsc, heq⟩
  have hiff : IsCalmFromBelowAt f x_bar ↔ (subdifferential f x_bar).Nonempty := by
    rw [hP1, heq 0, (hP4 hlsc).1]
  refine ⟨hiff, ?_⟩
  by_cases hc : IsCalmFromBelowAt f x_bar
  · obtain ⟨v₀, hv₀, hnorm⟩ := exists_subgrad_norm_eq_modulus hlsc hc
    apply le_antisymm
    · unfold distToSetEReal
      apply le_sInf
      rintro _ ⟨v, hv, rfl⟩
      simp only [zero_sub, norm_neg]
      apply modulus_le_of_subderiv_ge hc
      intro w hw
      rw [heq w]
      refine le_trans ?_ (regSubderiv_ge_of_mem hv w)
      have hw' : ‖w‖ ≤ 1 := by simpa [unitBall] using hw
      have h1 : -(‖v‖ * ‖w‖) ≤ inner ℝ v w := by
        have := abs_real_inner_le_norm v w
        linarith [neg_abs_le (inner ℝ v w)]
      have h2 : ‖v‖ * ‖w‖ ≤ ‖v‖ := by
        have := norm_nonneg v
        nlinarith [norm_nonneg w]
      exact_mod_cast (by linarith : -‖v‖ ≤ inner ℝ v w)
    · rw [← hnorm]
      unfold distToSetEReal
      apply sInf_le
      exact ⟨v₀, hv₀, by simp⟩
  · rw [modulus_eq_top_of_not_calm hc]
    have hempty : subdifferential f x_bar = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty, ← hiff]
      exact hc
    unfold distToSetEReal
    rw [hempty, Set.image_empty, _root_.sInf_empty]

end RW_chap_8_32
