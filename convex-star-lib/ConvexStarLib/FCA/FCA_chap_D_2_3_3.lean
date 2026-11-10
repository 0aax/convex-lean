import ConvexStarLib.Defs

/-!
# `FCA_chap_D_2_3_3`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_2_3_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_2_3_3`, so the main result is `FCA_chap_D_2_3_3.FCA_chap_D_2_3_3`.
-/

namespace FCA_chap_D_2_3_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem FCA_chap_D_2_3_3
    (f : E → ℝ) (x y : E) (hf_convex : ConvexOn ℝ Set.univ f)
    (_hxy : x ≠ y) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      ∃ s ∈ directionalSubdifferential (liftRealtoEReal f) (t • y + (1 - t) • x),
        f y - f x = inner ℝ s (y - x) := by
  -- the (real-valued) difference quotient of `f` at `p` in direction `v`
  set Q : E → E → ℝ → ℝ := fun p v t => (f (p + t • v) - f p) / t with hQ
  have hQmono : ∀ p v, MonotoneOn (Q p v) (Set.Ioi 0) := by
    intro p v a ha b hb hab
    simp only [Set.mem_Ioi] at ha hb
    have hab' : 0 ≤ 1 - a / b := by rw [sub_nonneg, div_le_one hb]; exact hab
    have hconv := hf_convex.2 (Set.mem_univ p) (Set.mem_univ (p + b • v)) hab'
      (div_nonneg ha.le hb.le) (by ring)
    have heq : (1 - a / b) • p + (a / b) • (p + b • v) = p + a • v := by
      rw [smul_add, smul_smul, div_mul_cancel₀ a hb.ne']; module
    rw [heq, smul_eq_mul, smul_eq_mul] at hconv
    simp only [hQ]
    rw [div_le_div_iff₀ ha hb]
    have : a * (f (p + b • v) - f p) = b * ((a / b) * f (p + b • v) - (a / b) * f p) := by
      field_simp
    nlinarith
  have hQbdd : ∀ p v t, 0 < t → f p - f (p - v) ≤ Q p v t := by
    intro p v t ht
    have h1 : 0 ≤ 1 / (1 + t) := by positivity
    have h2 : 0 ≤ t / (1 + t) := by positivity
    have hconv := hf_convex.2 (Set.mem_univ (p + t • v)) (Set.mem_univ (p - v)) h1 h2
      (by field_simp)
    have heq : (1 / (1 + t)) • (p + t • v) + (t / (1 + t)) • (p - v) = p := by
      match_scalars
      · field_simp
      · ring
    rw [heq, smul_eq_mul, smul_eq_mul] at hconv
    simp only [hQ]
    rw [le_div_iff₀ ht]
    have h3 : (1 + t) * f p ≤ f (p + t • v) + t * f (p - v) := by
      have := mul_le_mul_of_nonneg_left hconv (by linarith : (0:ℝ) ≤ 1 + t)
      have e : (1 + t) * (1 / (1 + t) * f (p + t • v) + t / (1 + t) * f (p - v))
          = f (p + t • v) + t * f (p - v) := by
        field_simp
      linarith
    nlinarith
  -- the (real-valued) one-sided directional derivative
  set N : E → E → ℝ := fun p v => sInf (Q p v '' Set.Ioi 0) with hN
  have hBdd : ∀ p v, BddBelow (Q p v '' Set.Ioi 0) := fun p v =>
    ⟨f p - f (p - v), by rintro _ ⟨t, ht, rfl⟩; exact hQbdd p v t ht⟩
  have hNtends : ∀ p v, Filter.Tendsto (Q p v) (𝓝[>] 0) (𝓝 (N p v)) := fun p v =>
    (hQmono p v).tendsto_nhdsGT (hBdd p v)
  have hdd : ∀ p v, directionalDeriv (liftRealtoEReal f) p v = (N p v : EReal) := by
    intro p v
    apply Filter.Tendsto.limUnder_eq
    have : Filter.Tendsto (fun t => ((Q p v t : ℝ) : EReal)) (𝓝[>] 0) (𝓝 (N p v : EReal)) :=
      (continuous_coe_real_ereal.tendsto _).comp (hNtends p v)
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp [differenceQuotient, liftRealtoEReal, hQ, EReal.coe_div, EReal.coe_sub]
  have hle_N : ∀ p v a, (∀ t, 0 < t → a ≤ Q p v t) → a ≤ N p v := fun p v a h =>
    le_csInf ⟨Q p v 1, 1, Set.mem_Ioi.2 one_pos, rfl⟩ (by rintro _ ⟨t, ht, rfl⟩; exact h t ht)
  have hscale : ∀ c : ℝ, 0 < c → Filter.Tendsto (fun t => c * t) (𝓝[>] 0) (𝓝[>] 0) := by
    intro c hc
    have := ((continuous_mul_left c).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    rw [mul_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ this
      (by filter_upwards [self_mem_nhdsWithin] with t ht; exact mul_pos hc ht)
  have hN_smul : ∀ p v (c : ℝ), 0 < c → N p (c • v) = c * N p v := by
    intro p v c hc
    have h2 : Filter.Tendsto (fun t => c * Q p v (c * t)) (𝓝[>] 0) (𝓝 (c * N p v)) :=
      ((hNtends p v).comp (hscale c hc)).const_mul c
    refine tendsto_nhds_unique ((hNtends p (c • v)).congr' ?_) h2
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ne_of_gt ht
    have hc' : c ≠ 0 := hc.ne'
    simp only [hQ, smul_smul]
    rw [mul_comm t c]
    field_simp
  have hN_add : ∀ p v w, N p (v + w) ≤ N p v + N p w := by
    intro p v w
    have h1 : Filter.Tendsto (fun t => Q p v (2 * t) + Q p w (2 * t)) (𝓝[>] 0)
        (𝓝 (N p v + N p w)) :=
      ((hNtends p v).comp (hscale 2 two_pos)).add ((hNtends p w).comp (hscale 2 two_pos))
    refine le_of_tendsto_of_tendsto (hNtends p (v + w)) h1 ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0:ℝ) < t := ht
    have hconv := hf_convex.2 (Set.mem_univ (p + (2 * t) • v)) (Set.mem_univ (p + (2 * t) • w))
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    have heq : (1/2 : ℝ) • (p + (2 * t) • v) + (1/2 : ℝ) • (p + (2 * t) • w)
        = p + t • (v + w) := by
      module
    rw [heq, smul_eq_mul, smul_eq_mul] at hconv
    simp only [hQ]
    rw [← add_div, div_le_div_iff₀ ht' (by positivity)]
    nlinarith
  -- an interior minimizer of `Φ` on `[0, 1]`
  set d := y - x with hd
  set c := f y - f x with hc
  set Φ : ℝ → ℝ := fun t => f (t • y + (1 - t) • x) - f x - t * c with hΦ
  have hfcont : Continuous f := hf_convex.locallyLipschitz.continuous
  have hΦcont : Continuous Φ := by
    simp only [hΦ]; fun_prop
  obtain ⟨t0, ht0, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 zero_le_one) hΦcont.continuousOn
  have hexists : ∃ ts ∈ Set.Ioo (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, Φ ts ≤ Φ t := by
    by_cases h : t0 ∈ Set.Ioo (0:ℝ) 1
    · exact ⟨t0, h, fun t ht => isMinOn_iff.mp hmin t ht⟩
    · have hΦt0 : Φ t0 = 0 := by
        have : t0 = 0 ∨ t0 = 1 := by
          simp only [Set.mem_Ioo, not_and_or, not_lt] at h
          rcases ht0 with ⟨h0, h1⟩
          rcases h with h | h
          · left; linarith
          · right; linarith
        rcases this with rfl | rfl
        · simp [hΦ]
        · simp [hΦ, hc]
      have hhalf : Φ (1/2) ≤ 0 := by
        have hconv := hf_convex.2 (Set.mem_univ y) (Set.mem_univ x)
          (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
        have e : (1:ℝ) - 1/2 = 1/2 := by norm_num
        simp only [hΦ, hc, e]
        rw [smul_eq_mul, smul_eq_mul] at hconv
        linarith
      refine ⟨1/2, ⟨by norm_num, by norm_num⟩, fun t ht => ?_⟩
      have := isMinOn_iff.mp hmin t ht
      linarith
  obtain ⟨ts, hts, hmin'⟩ := hexists
  set xs := ts • y + (1 - ts) • x with hxs
  have hNd : c ≤ N xs d := by
    refine ge_of_tendsto (hNtends xs d) ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 - ts by linarith [hts.2])] with h hh
    have h1 := hmin' (ts + h) ⟨by linarith [hts.1, hh.1], by linarith [hh.2]⟩
    have hxsd : xs + h • d = (ts + h) • y + (1 - (ts + h)) • x := by
      simp only [hxs, hd]; module
    simp only [hQ, hxsd]
    rw [le_div_iff₀ hh.1]
    simp only [hΦ] at h1
    nlinarith
  have hNnd : -c ≤ N xs (-d) := by
    refine ge_of_tendsto (hNtends xs (-d)) ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < ts by linarith [hts.1])] with h hh
    have h1 := hmin' (ts - h) ⟨by linarith [hh.2], by linarith [hts.2, hh.1]⟩
    have hxsd : xs + h • (-d) = (ts - h) • y + (1 - (ts - h)) • x := by
      simp only [hxs, hd]; module
    simp only [hQ, hxsd]
    rw [le_div_iff₀ hh.1]
    simp only [hΦ] at h1
    nlinarith
  -- Hahn–Banach
  have hd0 : d ≠ 0 := sub_ne_zero.2 (Ne.symm _hxy)
  have hdom : ∀ z : (LinearPMap.mkSpanSingleton (K := ℝ) d c hd0).domain,
      LinearPMap.mkSpanSingleton (K := ℝ) d c hd0 z ≤ N xs z := by
    rintro ⟨z, hz⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [LinearPMap.mkSpanSingleton'_apply]
    simp only [smul_eq_mul]
    rcases lt_trichotomy a 0 with ha | ha | ha
    · have : a • d = (-a) • (-d) := by rw [neg_smul_neg]
      rw [this, hN_smul xs (-d) (-a) (by linarith)]
      nlinarith
    · subst ha
      simp only [zero_smul, zero_mul]
      apply hle_N
      intro t ht
      simp [hQ]
    · rw [hN_smul xs d a ha]
      nlinarith
  obtain ⟨g, hg_eq, hg_le⟩ := exists_extension_of_le_sublinear
    (LinearPMap.mkSpanSingleton (K := ℝ) d c hd0) (N xs) (fun c hc v => hN_smul xs v c hc)
    (hN_add xs) hdom
  refine ⟨ts, hts, (InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap g),
    ?_, ?_⟩
  · intro v
    show _ ≤ directionalDeriv (liftRealtoEReal f) xs v
    rw [hdd, InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap']
    exact EReal.coe_le_coe_iff.2 (hg_le v)
  · rw [InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap']
    have := hg_eq ⟨d, Submodule.mem_span_singleton_self d⟩
    rw [LinearPMap.mkSpanSingleton_apply] at this
    exact this.symm

end FCA_chap_D_2_3_3
