import ConvexStarLib.Defs

/-!
# `FCA_chap_E_4_1_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_4_1_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_4_1_1`, so the main result is `FCA_chap_E_4_1_1.FCA_chap_E_4_1_1`.
-/

namespace FCA_chap_E_4_1_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_E_4_1_1
  (f : E → EReal)
  (hf_closed_convex : InClosedConvRn f)
  (hf_proper : ∃ x, f x < ⊤)
  (hf_strict : ∀ x y, x ≠ y → f x < ⊤ → f y < ⊤ →
    ∀ (α : ℝ), α ∈ Set.Ioo 0 1 →
    f (α • x + (1 - α) • y) < α * (f x) + (1 - α) * (f y))
  (f_ne_bot : ∀ x, ⊥ < f x) :
  let domConj := effDom ((conjugate f))
  Set.Nonempty (interior domConj)∧
  (∃ (g : E → ℝ),
  ((∀ s ∈ interior domConj, (conjugate f s) = (g s : EReal))) ∧
  (ContDiffOn ℝ 1 g (interior domConj))) := by
  intro domConj
  obtain ⟨⟨_, _, hconvex⟩, hlsc⟩ := hf_closed_convex
  set D : Set E := {x | f x < ⊤} with hD_def
  set F : E → ℝ := fun x => (f x).toReal with hF_def
  have hfF : ∀ x ∈ D, f x = (F x : EReal) := fun x hx =>
    (EReal.coe_toReal hx.ne (f_ne_bot x).ne').symm
  obtain ⟨x0, hx0⟩ := hf_proper
  have hconvF : ∀ x ∈ D, ∀ y ∈ D, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      a • x + b • y ∈ D ∧ F (a • x + b • y) ≤ a * F x + b * F y := by
    intro x hx y hy a b ha hb hab
    have hconv' : Convex ℝ (epigraph f) := hconvex
    have hmem : a • ((x, F x) : E × ℝ) + b • ((y, F y) : E × ℝ) ∈ epigraph f :=
      hconv' (show ((x, F x) : E × ℝ) ∈ epigraph f from le_of_eq (hfF x hx))
        (show ((y, F y) : E × ℝ) ∈ epigraph f from le_of_eq (hfF y hy)) ha hb hab
    simp only [epigraph, Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hmem
    have hD' : a • x + b • y ∈ D := lt_of_le_of_lt hmem (EReal.coe_lt_top _)
    refine ⟨hD', ?_⟩
    rw [hfF _ hD'] at hmem
    exact_mod_cast hmem
  have hstrictF : ∀ x ∈ D, ∀ y ∈ D, x ≠ y →
      F ((1/2 : ℝ) • x + (1/2 : ℝ) • y) < (1/2) * F x + (1/2) * F y := by
    intro x hx y hy hxy
    have h := hf_strict x y hxy hx hy (1/2) ⟨by norm_num, by norm_num⟩
    have h12 : (1 : ℝ) - 1/2 = 1/2 := by norm_num
    rw [h12, hfF x hx, hfF y hy, ← EReal.coe_one, ← EReal.coe_sub, h12, ← EReal.coe_mul,
      ← EReal.coe_mul, ← EReal.coe_add] at h
    have hmD := (hconvF x hx y hy (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)).1
    rw [hfF _ hmD] at h
    exact_mod_cast h
  have hconj_ge : ∀ t, ∀ y ∈ D, ((inner ℝ (t) (y) - F y : ℝ) : EReal) ≤ conjugate f t := by
    intro t y hy
    unfold conjugate
    apply le_sSup
    refine ⟨y, Set.mem_univ _, ?_⟩
    show (↑(inner ℝ t y) : EReal) - f y = _
    rw [hfF y hy, EReal.coe_sub]
  have hconj_le : ∀ t (M : ℝ), (∀ y ∈ D, inner ℝ (t) (y) - F y ≤ M) → conjugate f t ≤ M := by
    intro t M hM
    unfold conjugate
    apply sSup_le
    rintro _ ⟨y, -, rfl⟩
    show (↑(inner ℝ t y) : EReal) - f y ≤ M
    by_cases hy : y ∈ D
    · rw [hfF y hy, ← EReal.coe_sub]
      exact_mod_cast hM y hy
    · have : f y = ⊤ := not_lt_top_iff.mp hy
      rw [this, EReal.sub_top]
      exact bot_le
  have hdom_iff : ∀ t, t ∈ domConj ↔ ∃ M : ℝ, ∀ y ∈ D, inner ℝ (t) (y) - F y ≤ M := by
    intro t
    constructor
    · intro ht
      have ht' : conjugate f t < ⊤ := ht
      obtain ⟨M, hM, -⟩ := EReal.lt_iff_exists_real_btwn.mp ht'
      refine ⟨M, fun y hy => ?_⟩
      have := (hconj_ge t y hy).trans hM.le
      exact_mod_cast this
    · rintro ⟨M, hM⟩
      exact lt_of_le_of_lt (hconj_le t M hM) (EReal.coe_lt_top M)
  have hexmin : ∀ c : E → ℝ, Continuous c → ∀ y0 ∈ D, ∀ R : ℝ,
      (∀ y ∈ D, R < ‖y‖ → F y0 + c y0 < F y + c y) → ∃ p ∈ D, ∀ y ∈ D, F p + c p ≤ F y + c y := by
    intro c hc y0 hy0 R hR
    set h : E → EReal := fun y => f y + (c y : EReal) with hh
    have hlsc_h : LowerSemicontinuous h := by
      apply LowerSemicontinuous.add' hlsc
      · exact (continuous_coe_real_ereal.comp hc).lowerSemicontinuous
      · intro x
        apply EReal.continuousAt_add
        · right; exact EReal.coe_ne_bot _
        · right; exact EReal.coe_ne_top _
    set K := Metric.closedBall (0 : E) (max R ‖y0‖) with hK_def
    have hK : IsCompact K := isCompact_closedBall _ _
    have hy0K : y0 ∈ K := by rw [hK_def, mem_closedBall_zero_iff]; exact le_max_right _ _
    obtain ⟨p, hpK, hpmin⟩ :=
      LowerSemicontinuousOn.exists_isMinOn ⟨y0, hy0K⟩ hK (hlsc_h.lowerSemicontinuousOn K)
    have hhD : ∀ z ∈ D, h z = ((F z + c z : ℝ) : EReal) := fun z hz => by
      simp only [hh, hfF z hz, EReal.coe_add]
    have hp_le : h p ≤ h y0 := isMinOn_iff.mp hpmin y0 hy0K
    have hpD : p ∈ D := by
      by_contra hpD
      have : f p = ⊤ := not_lt_top_iff.mp hpD
      have h1 : h p = ⊤ := by simp only [hh, this, EReal.top_add_coe]
      rw [h1, hhD y0 hy0] at hp_le
      exact absurd hp_le (not_le.mpr (EReal.coe_lt_top _))
    refine ⟨p, hpD, fun y hy => ?_⟩
    rw [hhD p hpD, hhD y0 hy0] at hp_le
    have h2 : F p + c p ≤ F y0 + c y0 := by exact_mod_cast hp_le
    by_cases hyK : y ∈ K
    · have := isMinOn_iff.mp hpmin y hyK
      rw [hhD p hpD, hhD y hy] at this
      exact_mod_cast this
    · have hRy : R < ‖y‖ := by
        rw [hK_def, mem_closedBall_zero_iff, not_le] at hyK
        exact lt_of_le_of_lt (le_max_left _ _) hyK
      have h1 := hR y hy hRy
      linarith
  have hlin : ∃ a b : ℝ, 0 ≤ b ∧ ∀ y ∈ D, a - b * ‖y‖ ≤ F y := by
    have hx0D : x0 ∈ D := hx0
    have hx0K : x0 ∈ Metric.closedBall x0 1 := Metric.mem_closedBall_self zero_le_one
    obtain ⟨k, hkK, hkmin⟩ := LowerSemicontinuousOn.exists_isMinOn ⟨x0, hx0K⟩
      (isCompact_closedBall x0 1) (hlsc.lowerSemicontinuousOn (Metric.closedBall x0 1))
    have hkle : ∀ y ∈ Metric.closedBall x0 1, f k ≤ f y := isMinOn_iff.mp hkmin
    have hkD : k ∈ D := lt_of_le_of_lt (hkle x0 hx0K) hx0
    have hmK : ∀ y ∈ D, y ∈ Metric.closedBall x0 1 → F k ≤ F y := by
      intro y hy hyK
      have h := hkle y hyK
      rw [hfF k hkD, hfF y hy] at h
      exact EReal.coe_le_coe_iff.mp h
    have hmx0 : F k ≤ F x0 := hmK x0 hx0D hx0K
    have key : ∀ y ∈ D, F k - (F x0 - F k) * ‖y - x0‖ ≤ F y := by
      intro y hy
      by_cases hr : ‖y - x0‖ ≤ 1
      · have hyK : y ∈ Metric.closedBall x0 1 := by
          rw [Metric.mem_closedBall, dist_eq_norm]; exact hr
        have h1 := hmK y hy hyK
        have h2 : 0 ≤ (F x0 - F k) * ‖y - x0‖ := mul_nonneg (by linarith) (norm_nonneg _)
        linarith
      · push_neg at hr
        have hrpos : 0 < ‖y - x0‖ := by linarith
        have hl0 : 0 ≤ 1 / ‖y - x0‖ := by positivity
        have hl1 : 0 ≤ 1 - 1 / ‖y - x0‖ := by
          rw [sub_nonneg, div_le_one hrpos]; linarith
        obtain ⟨hzD, hzF⟩ := hconvF y hy x0 hx0D (1 / ‖y - x0‖) (1 - 1 / ‖y - x0‖)
          hl0 hl1 (by ring)
        have hzK : (1 / ‖y - x0‖) • y + (1 - 1 / ‖y - x0‖) • x0 ∈ Metric.closedBall x0 1 := by
          rw [Metric.mem_closedBall, dist_eq_norm]
          have e : (1 / ‖y - x0‖) • y + (1 - 1 / ‖y - x0‖) • x0 - x0
              = (1 / ‖y - x0‖) • (y - x0) := by
            rw [smul_sub, sub_smul, one_smul]; abel
          rw [e, norm_smul, Real.norm_of_nonneg hl0, one_div, inv_mul_cancel₀ hrpos.ne']
        have h1 : F k ≤ (1 / ‖y - x0‖) * F y + (1 - 1 / ‖y - x0‖) * F x0 :=
          le_trans (hmK _ hzD hzK) hzF
        have h2 : ‖y - x0‖ * F k ≤ F y + (‖y - x0‖ - 1) * F x0 := by
          have h3 := mul_le_mul_of_nonneg_left h1 hrpos.le
          have e : ‖y - x0‖ * ((1 / ‖y - x0‖) * F y + (1 - 1 / ‖y - x0‖) * F x0)
              = F y + (‖y - x0‖ - 1) * F x0 := by
            field_simp
          linarith
        nlinarith
    refine ⟨F k - (F x0 - F k) * ‖x0‖, F x0 - F k, by linarith, ?_⟩
    intro y hy
    have h1 := key y hy
    have h2 : ‖y - x0‖ ≤ ‖y‖ + ‖x0‖ := norm_sub_le y x0
    have h3 : 0 ≤ F x0 - F k := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  have hprox : ∀ x : E, ∃ p ∈ D, ∀ y ∈ D, F p + inner ℝ (x - p) (y - p) ≤ F y := by
    intro x
    obtain ⟨a, b, hb, hab⟩ := hlin
    have hx0D : x0 ∈ D := hx0
    obtain ⟨K, hK⟩ : ∃ K : ℝ, K = F x0 + ‖x0 - x‖ ^ 2 / 2 - a + b * ‖x‖ := ⟨_, rfl⟩
    have hc : Continuous (fun y : E => ‖y - x‖ ^ 2 / 2) := by fun_prop
    obtain ⟨p, hpD, hp⟩ := hexmin (fun y : E => ‖y - x‖ ^ 2 / 2) hc x0 hx0D
      (‖x‖ + 2 * b + 2 + 2 * |K|) (by
        intro y hyD hyR
        show F x0 + ‖x0 - x‖ ^ 2 / 2 < F y + ‖y - x‖ ^ 2 / 2
        have h1 := hab y hyD
        have h2 : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := norm_sub_norm_le y x
        have hKa : 0 ≤ |K| := abs_nonneg K
        have hs : 0 < ‖y‖ - ‖x‖ := by linarith
        have hgap : 0 < ‖y‖ - ‖x‖ - 2 * b - 2 - 2 * |K| := by linarith
        have h3 : (‖y‖ - ‖x‖) ^ 2 ≤ ‖y - x‖ ^ 2 := pow_le_pow_left₀ hs.le h2 2
        have key := mul_pos hs hgap
        have hK1 : K ≤ |K| := le_abs_self K
        have hK2 := mul_nonneg hKa hs.le
        nlinarith)
    refine ⟨p, hpD, ?_⟩
    intro y hyD
    by_contra hcon
    push_neg at hcon
    have hδpos : 0 < F p + inner ℝ (x - p) (y - p) - F y := by linarith
    have hN0 : 0 ≤ ‖y - p‖ ^ 2 := by positivity
    obtain ⟨l, hl0, hl1, hl2⟩ : ∃ l : ℝ, 0 < l ∧ l ≤ 1 / 2 ∧
        l * (‖y - p‖ ^ 2 + 1) ≤ F p + inner ℝ (x - p) (y - p) - F y := by
      refine ⟨min (1 / 2 : ℝ) ((F p + inner ℝ (x - p) (y - p) - F y) / (‖y - p‖ ^ 2 + 1)),
        lt_min (by norm_num) (div_pos hδpos (by linarith)), min_le_left _ _, ?_⟩
      have h := min_le_right (1 / 2 : ℝ)
        ((F p + inner ℝ (x - p) (y - p) - F y) / (‖y - p‖ ^ 2 + 1))
      rwa [le_div_iff₀ (by linarith)] at h
    obtain ⟨hzD, hFz⟩ := hconvF y hyD p hpD l (1 - l) hl0.le (by linarith) (by ring)
    have hmin : F p + ‖p - x‖ ^ 2 / 2 ≤
        F (l • y + (1 - l) • p) + ‖l • y + (1 - l) • p - x‖ ^ 2 / 2 := hp _ hzD
    have hz : l • y + (1 - l) • p - x = (p - x) + l • (y - p) := by
      simp only [sub_smul, one_smul, smul_sub]; abel
    have hnorm : ‖(p - x) + l • (y - p)‖ ^ 2
        = ‖p - x‖ ^ 2 + 2 * l * inner ℝ (p - x) (y - p) + l ^ 2 * ‖y - p‖ ^ 2 := by
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    have hinner : inner ℝ (p - x) (y - p) = - inner ℝ (x - p) (y - p) := by
      rw [← inner_neg_left, neg_sub]
    rw [hz, hnorm, hinner] at hmin
    nlinarith [mul_le_mul_of_nonneg_left hl2 hl0.le, mul_pos hl0 hl0,
      mul_nonneg (mul_nonneg hl0.le hl0.le) hN0, hFz, hmin]
  have hdom_convex : Convex ℝ domConj := by
    intro t1 ht1 t2 ht2 a b ha hb hab
    obtain ⟨M1, hM1⟩ := (hdom_iff t1).mp ht1
    obtain ⟨M2, hM2⟩ := (hdom_iff t2).mp ht2
    refine (hdom_iff _).mpr ⟨a * M1 + b * M2, fun y hy => ?_⟩
    have e1 := mul_le_mul_of_nonneg_left (hM1 y hy) ha
    have e2 := mul_le_mul_of_nonneg_left (hM2 y hy) hb
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have : F y = a * F y + b * F y := by rw [← add_mul, hab, one_mul]
    nlinarith
  have hint : (interior domConj).Nonempty := by
    by_contra h
    -- every prox point gives an element of domConj
    have hmem : ∀ x : E, ∀ p ∈ D, (∀ y ∈ D, F p + inner ℝ (x - p) (y - p) ≤ F y) →
        x - p ∈ domConj := by
      intro x p hpD hp
      rw [hdom_iff]
      refine ⟨inner ℝ (x - p) p - F p, fun y hy => ?_⟩
      have h1 := hp y hy
      rw [inner_sub_right] at h1
      linarith
    obtain ⟨p0, hp0D, hp0⟩ := hprox 0
    have hne : domConj.Nonempty := ⟨_, hmem 0 p0 hp0D hp0⟩
    have haff : affineSpan ℝ domConj ≠ ⊤ := fun htop =>
      h (hdom_convex.interior_nonempty_iff_affineSpan_eq_top.mpr htop)
    have hvs : vectorSpan ℝ domConj ≠ ⊤ := by
      intro htop
      apply haff
      rw [← AffineSubspace.direction_eq_top_iff_of_nonempty
        (hne.mono (subset_affineSpan ℝ domConj)), direction_affineSpan]
      exact htop
    have horth : (vectorSpan ℝ domConj)ᗮ ≠ ⊥ := fun hbot =>
      hvs (Submodule.orthogonal_eq_bot_iff.mp hbot)
    obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot horth
    have hperp : ∀ t ∈ domConj, ∀ t' ∈ domConj, inner ℝ (t - t') d = 0 := by
      intro t ht t' ht'
      have hv : t - t' ∈ vectorSpan ℝ domConj := by
        have := vsub_mem_vectorSpan ℝ ht ht'
        rwa [vsub_eq_sub] at this
      exact Submodule.inner_right_of_mem_orthogonal hv hd
    obtain ⟨p, hpD, hp⟩ := hprox 0
    obtain ⟨p', hp'D, hp'⟩ := hprox d
    have hkey := hperp _ (hmem 0 p hpD hp) _ (hmem d p' hp'D hp')
    have e : ((0 : E) - p) - (d - p') = (p' - p) - d := by abel
    rw [e, inner_sub_left, real_inner_self_eq_norm_sq] at hkey
    -- hkey : inner (p' - p) d - ‖d‖^2 = 0
    have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd0
    have hpp : p ≠ p' := by
      intro heq
      rw [heq, sub_self, inner_zero_left] at hkey
      nlinarith
    have hmD := (hconvF p hpD p' hp'D (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)).1
    have hstrict := hstrictF p hpD p' hp'D hpp
    have h1 := hp _ hmD
    have h2 := hp' _ hmD
    have hm1 : ((1/2 : ℝ) • p + (1/2 : ℝ) • p') - p = (1/2 : ℝ) • (p' - p) := by module
    have hm2 : ((1/2 : ℝ) • p + (1/2 : ℝ) • p') - p' = (-(1/2) : ℝ) • (p' - p) := by module
    rw [hm1, real_inner_smul_right] at h1
    rw [hm2, real_inner_smul_right] at h2
    have e1 : inner ℝ ((0 : E) - p) (p' - p) - inner ℝ (d - p') (p' - p)
        = ‖p' - p‖ ^ 2 - inner ℝ (p' - p) d := by
      rw [← inner_sub_left, e, inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm]
    have hlt : ‖p' - p‖ ^ 2 < ‖d‖ ^ 2 := by nlinarith
    have hcs : inner ℝ (p' - p) d ≤ ‖p' - p‖ * ‖d‖ := real_inner_le_norm _ _
    have hle : ‖d‖ ≤ ‖p' - p‖ := by nlinarith
    nlinarith [norm_nonneg (p' - p)]
  set U := interior domConj with hU_def
  have hUopen : IsOpen U := isOpen_interior
  have hcoer : ∀ s ∈ U, ∃ M c : ℝ, 0 < c ∧ ∀ y ∈ D, inner ℝ (s) (y) - F y ≤ M - c * ‖y‖ := by
    intro s hs
    rw [hU_def, mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hs
    obtain ⟨ε, hε, hball⟩ := hs
    set b := stdOrthonormalBasis ℝ E with hb
    set δ : ℝ := ε / 2 with hδ
    have hδpos : 0 < δ := by positivity
    have hbn : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
    have hmemp : ∀ i, s + δ • b i ∈ domConj := by
      intro i
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hbn i, mul_one,
        Real.norm_eq_abs, abs_of_pos hδpos]
      linarith
    have hmemm : ∀ i, s - δ • b i ∈ domConj := by
      intro i
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, hbn i, mul_one,
        Real.norm_eq_abs, abs_of_pos hδpos]
      linarith
    have hs0 : s ∈ domConj := hball (Metric.mem_ball_self hε)
    obtain ⟨M0, hM0⟩ := (hdom_iff s).1 hs0
    choose Mp hMp using fun i => (hdom_iff _).1 (hmemp i)
    choose Mm hMm using fun i => (hdom_iff _).1 (hmemm i)
    obtain ⟨Bp, hBp⟩ := (Set.finite_range Mp).bddAbove
    obtain ⟨Bm, hBm⟩ := (Set.finite_range Mm).bddAbove
    set M : ℝ := max M0 (max Bp Bm) with hM
    have hM0le : M0 ≤ M := le_max_left _ _
    have hMple : ∀ i, Mp i ≤ M := fun i =>
      ((hBp (Set.mem_range_self i)).trans (le_max_left _ _)).trans (le_max_right _ _)
    have hMmle : ∀ i, Mm i ≤ M := fun i =>
      ((hBm (Set.mem_range_self i)).trans (le_max_right _ _)).trans (le_max_right _ _)
    set n : ℝ := (Module.finrank ℝ E : ℝ) with hn
    have hn0 : 0 ≤ n := Nat.cast_nonneg _
    have hn1 : 0 < n + 1 := by linarith
    refine ⟨M, δ / (n + 1), div_pos hδpos hn1, ?_⟩
    intro y hy
    have key : ∀ i, inner ℝ s y - F y + δ * |inner ℝ (b i) y| ≤ M := by
      intro i
      rcases le_or_gt 0 (inner ℝ (b i) y) with h | h
      · have h1 := hMp i y hy
        rw [inner_add_left, real_inner_smul_left] at h1
        rw [abs_of_nonneg h]
        linarith [hMple i]
      · have h1 := hMm i y hy
        rw [inner_sub_left, real_inner_smul_left] at h1
        rw [abs_of_neg h]
        linarith [hMmle i]
    have hsum : ∑ i, (inner ℝ s y - F y + δ * |inner ℝ (b i) y|) ≤ ∑ _i : Fin (Module.finrank ℝ E), M :=
      Finset.sum_le_sum (fun i _ => key i)
    have hsum_eq : ∑ i, (inner ℝ s y - F y + δ * |inner ℝ (b i) y|)
        = n * (inner ℝ s y - F y) + δ * ∑ i, |inner ℝ (b i) y| := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have hsumM : ∑ _i : Fin (Module.finrank ℝ E), M = n * M := by simp [hn]
    rw [hsum_eq, hsumM] at hsum
    have hnorm : ‖y‖ ≤ ∑ i, |inner ℝ (b i) y| := by
      calc ‖y‖ = ‖∑ i, inner ℝ (b i) y • b i‖ := by rw [b.sum_repr' y]
        _ ≤ ∑ i, ‖inner ℝ (b i) y • b i‖ := norm_sum_le _ _
        _ = ∑ i, |inner ℝ (b i) y| := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [norm_smul, hbn i, mul_one, Real.norm_eq_abs]
    have hδnorm : δ * ‖y‖ ≤ δ * ∑ i, |inner ℝ (b i) y| :=
      mul_le_mul_of_nonneg_left hnorm hδpos.le
    have hA := hM0 y hy
    have hfinal : (n + 1) * (inner ℝ s y - F y) + δ * ‖y‖ ≤ (n + 1) * M := by
      linarith
    have hrw : M - δ / (n + 1) * ‖y‖ = ((n + 1) * M - δ * ‖y‖) / (n + 1) := by
      field_simp
    rw [hrw, le_div_iff₀ hn1]
    linarith
  have hmax : ∀ s ∈ U, ∃ x ∈ D, ∀ y ∈ D, inner ℝ (s) (y) - F y ≤ inner ℝ (s) (x) - F x := by
    intro s hs
    obtain ⟨M, c, hc, hMc⟩ := hcoer s hs
    obtain ⟨p, hpD, hp⟩ := hexmin (fun y => - inner ℝ s y) (by fun_prop) x0 hx0
      ((M - (inner ℝ s x0 - F x0)) / c) (fun y hy hRy => by
        have h1 := hMc y hy
        have h2 : M - (inner ℝ s x0 - F x0) < c * ‖y‖ := by
          rw [div_lt_iff₀ hc] at hRy; linarith
        simp only; linarith)
    exact ⟨p, hpD, fun y hy => by have := hp y hy; simp only at this; linarith⟩
  have huniq : ∀ s x x', x ∈ D → x' ∈ D → (∀ y ∈ D, inner ℝ (s) (y) - F y ≤ inner ℝ (s) (x) - F x) →
      (∀ y ∈ D, inner ℝ (s) (y) - F y ≤ inner ℝ (s) (x') - F x') → x = x' := by
    intro s x x' hx hx' h1 h2
    by_contra hne
    have hm := hconvF x hx x' hx' (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)
    have hs := hstrictF x hx x' hx' hne
    have e1 := h1 _ hm.1
    have e2 := h1 x' hx'
    have e3 := h2 x hx
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right] at e1
    linarith
  choose! xm hxmD hxm using hmax
  have hcont : ∀ s ∈ U, ContinuousAt xm s := by
    intro s hs
    obtain ⟨M, c, hc, hMc⟩ := hcoer s hs
    have hx0D : xm s ∈ D := hxmD s hs
    have hbound : ∀ t ∈ U, ‖t - s‖ ≤ c / 2 →
        ‖xm t‖ ≤ 2 * (M + (‖s‖ + c / 2) * ‖xm s‖ + F (xm s)) / c := by
      intro t ht hts
      have hzD : xm t ∈ D := hxmD t ht
      have h1 := hxm t ht (xm s) hx0D
      have h2 := hMc (xm t) hzD
      have h3 : inner ℝ (t - s) (xm t) ≤ ‖t - s‖ * ‖xm t‖ := real_inner_le_norm _ _
      have h4 : inner ℝ t (xm t) = inner ℝ s (xm t) + inner ℝ (t - s) (xm t) := by
        rw [inner_sub_left]; ring
      have h5 : -(‖t‖ * ‖xm s‖) ≤ inner ℝ t (xm s) := by
        have := abs_real_inner_le_norm t (xm s)
        linarith [neg_abs_le (inner ℝ t (xm s))]
      have h6 : ‖t‖ ≤ ‖s‖ + c / 2 := by
        have := norm_sub_norm_le t s
        linarith
      have h7 : ‖t - s‖ * ‖xm t‖ ≤ c / 2 * ‖xm t‖ :=
        mul_le_mul_of_nonneg_right hts (norm_nonneg _)
      have h8 : ‖t‖ * ‖xm s‖ ≤ (‖s‖ + c / 2) * ‖xm s‖ :=
        mul_le_mul_of_nonneg_right h6 (norm_nonneg _)
      have h9 : c / 2 * ‖xm t‖ ≤ M + (‖s‖ + c / 2) * ‖xm s‖ + F (xm s) := by
        linarith
      rw [le_div_iff₀ hc]
      linarith
    show Filter.Tendsto xm (𝓝 s) (𝓝 (xm s))
    apply Filter.tendsto_of_subseq_tendsto
    intro ns hns
    have hU_ev : ∀ᶠ n in Filter.atTop, ns n ∈ U := hns.eventually (hUopen.mem_nhds hs)
    have hball_ev : ∀ᶠ n in Filter.atTop, ‖ns n - s‖ ≤ c / 2 := by
      have hcb : ∀ᶠ t in 𝓝 s, ‖t - s‖ ≤ c / 2 := by
        filter_upwards [Metric.closedBall_mem_nhds s (by linarith : (0:ℝ) < c / 2)] with t ht
        rwa [Metric.mem_closedBall, dist_eq_norm] at ht
      exact hns.eventually hcb
    have hfreq : ∃ᶠ n in Filter.atTop, xm (ns n) ∈
        Metric.closedBall (0 : E) (2 * (M + (‖s‖ + c / 2) * ‖xm s‖ + F (xm s)) / c) := by
      apply Filter.Eventually.frequently
      filter_upwards [hU_ev, hball_ev] with n h1 h2
      rw [Metric.mem_closedBall, _root_.dist_zero_right]
      exact hbound (ns n) h1 h2
    obtain ⟨a, -, phi, hphi, hlim⟩ := tendsto_subseq_of_frequently_bounded
      (x := fun n => xm (ns n)) Metric.isBounded_closedBall hfreq
    refine ⟨phi, ?_⟩
    have ht : Filter.Tendsto (fun n => ns (phi n)) Filter.atTop (𝓝 s) :=
      hns.comp hphi.tendsto_atTop
    have hlim' : Filter.Tendsto (fun n => xm (ns (phi n))) Filter.atTop (𝓝 a) := hlim
    have hUphi : ∀ᶠ n in Filter.atTop, ns (phi n) ∈ U := ht.eventually (hUopen.mem_nhds hs)
    have hr : Filter.Tendsto (fun n => inner ℝ (ns (phi n)) (xm (ns (phi n)))
        - inner ℝ (ns (phi n)) (xm s) + F (xm s)) Filter.atTop
        (𝓝 (inner ℝ s a - inner ℝ s (xm s) + F (xm s))) :=
      ((ht.inner hlim').sub (ht.inner tendsto_const_nhds)).add tendsto_const_nhds
    have hmem : (a, ((inner ℝ s a - inner ℝ s (xm s) + F (xm s) : ℝ) : EReal)) ∈
        {p : E × EReal | f p.1 ≤ p.2} := by
      refine hlsc.isClosed_epigraph.mem_of_tendsto
        (hlim'.prodMk_nhds (EReal.tendsto_coe.mpr hr)) ?_
      filter_upwards [hUphi] with n hn
      show f (xm (ns (phi n))) ≤ ((inner ℝ (ns (phi n)) (xm (ns (phi n)))
        - inner ℝ (ns (phi n)) (xm s) + F (xm s) : ℝ) : EReal)
      rw [hfF _ (hxmD _ hn), EReal.coe_le_coe_iff]
      have := hxm _ hn (xm s) hx0D
      linarith
    have hfa : f a ≤ ((inner ℝ s a - inner ℝ s (xm s) + F (xm s) : ℝ) : EReal) := hmem
    have haD : a ∈ D := lt_of_le_of_lt hfa (EReal.coe_lt_top _)
    have hFa : F a ≤ inner ℝ s a - inner ℝ s (xm s) + F (xm s) := by
      rw [hfF a haD, EReal.coe_le_coe_iff] at hfa
      exact hfa
    have hamax : ∀ y ∈ D, inner ℝ s y - F y ≤ inner ℝ s a - F a := by
      intro y hy
      have := hxm s hs y hy
      linarith
    have heq : a = xm s := huniq s a (xm s) haD hx0D hamax (hxm s hs)
    rw [← heq]
    exact hlim'
  have hval : ∀ s ∈ U, conjugate f s = ((inner ℝ (s) (xm s) - F (xm s) : ℝ) : EReal) := by
    intro s hs
    exact le_antisymm (hconj_le s _ (hxm s hs)) (hconj_ge s _ (hxmD s hs))
  have hderiv : ∀ s ∈ U, HasFDerivAt (fun s => (conjugate f s).toReal) (innerSL ℝ (xm s)) s := by
    intro s hs
    have hg : ∀ t ∈ U, (conjugate f t).toReal = inner ℝ t (xm t) - F (xm t) := by
      intro t ht
      rw [hval t ht, EReal.toReal_coe]
    have hkey : ∀ t ∈ U,
        |(conjugate f t).toReal - (conjugate f s).toReal - inner ℝ (xm s) (t - s)|
          ≤ ‖t - s‖ * ‖xm t - xm s‖ := by
      intro t ht
      rw [hg t ht, hg s hs]
      have h1 := hxm t ht (xm s) (hxmD s hs)
      have h2 := hxm s hs (xm t) (hxmD t ht)
      have h3 : inner ℝ (t - s) (xm t - xm s) ≤ ‖t - s‖ * ‖xm t - xm s‖ :=
        real_inner_le_norm _ _
      have e1 : inner ℝ (xm s) (t - s) = inner ℝ t (xm s) - inner ℝ s (xm s) := by
        rw [inner_sub_right, real_inner_comm (xm s) t, real_inner_comm (xm s) s]
      have e2 : inner ℝ (t - s) (xm t - xm s)
          = inner ℝ t (xm t) - inner ℝ t (xm s) - (inner ℝ s (xm t) - inner ℝ s (xm s)) := by
        rw [inner_sub_left, inner_sub_right, inner_sub_right]
      rw [abs_le]
      constructor <;> linarith
    apply HasFDerivAtFilter.of_isLittleO
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hU : ∀ᶠ t in 𝓝 s, t ∈ U := hUopen.mem_nhds hs
    have hball : ∀ᶠ t in 𝓝 s, xm t ∈ Metric.ball (xm s) c :=
      (hcont s hs).eventually_mem (Metric.ball_mem_nhds _ hc)
    filter_upwards [hU, hball] with t ht htb
    rw [Metric.mem_ball, dist_eq_norm] at htb
    simp only [innerSL_apply_apply, Real.norm_eq_abs]
    calc |(conjugate f t).toReal - (conjugate f s).toReal - inner ℝ (xm s) (t - s)|
        ≤ ‖t - s‖ * ‖xm t - xm s‖ := hkey t ht
      _ ≤ ‖t - s‖ * c := by gcongr
      _ = c * ‖t - s‖ := mul_comm _ _
  refine ⟨hint, fun s => (conjugate f s).toReal, ?_, ?_⟩
  · intro s hs
    show _ = ((conjugate f s).toReal : EReal)
    rw [hval s hs, EReal.toReal_coe]
  · intro s hs
    refine (contDiffAt_one_iff.mpr ⟨fun t => innerSL ℝ (xm t), U, hUopen.mem_nhds hs, ?_,
      fun t ht => hderiv t ht⟩).contDiffWithinAt
    intro t ht
    exact ((innerSL ℝ).continuous.continuousAt.comp (hcont t ht)).continuousWithinAt

end FCA_chap_E_4_1_1
