import ConvexStarLib.Defs

/-!
# `RW_chap_9_19`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_9_19` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_9_19`, so the main result is `RW_chap_9_19.RW_chap_9_19`.
-/

namespace RW_chap_9_19

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section aux_lemmas

-- ===== group C1 =====
/-- (L1) quadratic minorant gives a regular subgradient -/
lemma aux_isRegSub_of_quad (f : E → EReal) (p ζ : E) (k : ℝ) (W : Set E) (hW : W ∈ 𝓝 p)
    (hfin : ∀ y ∈ W, IsFiniteEReal (f y))
    (h : ∀ y ∈ W, (f p).toReal + inner ℝ ζ (y - p) - k * ‖y - p‖ ^ 2 ≤ (f y).toReal) :
    IsRegularSubgradientAt f p ζ := by
  have hp : p ∈ W := mem_of_mem_nhds hW
  obtain ⟨P, hP⟩ := hfin p hp
  refine ⟨by rw [hP]; exact EReal.bot_lt_coe P, by rw [hP]; exact EReal.coe_lt_top P,
    fun y => -(k * ‖y - p‖ ^ 2), ?_, W, hW, ?_⟩
  · rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hk : 0 < |k| + 1 := by positivity
    have hball : Metric.ball p (c / (|k| + 1)) ∈ 𝓝 p := Metric.ball_mem_nhds p (by positivity)
    filter_upwards [hball] with y hy
    rw [Metric.mem_ball, dist_eq_norm, lt_div_iff₀ hk] at hy
    have hn0 : 0 ≤ ‖y - p‖ := norm_nonneg _
    rw [norm_neg, norm_mul, norm_pow, norm_norm, Real.norm_eq_abs]
    have h1 : |k| * ‖y - p‖ ^ 2 ≤ (|k| + 1) * ‖y - p‖ * ‖y - p‖ := by
      nlinarith [abs_nonneg k]
    have h2 : (|k| + 1) * ‖y - p‖ * ‖y - p‖ ≤ c * ‖y - p‖ := by
      apply mul_le_mul_of_nonneg_right _ hn0
      linarith
    linarith
  · intro y hy
    obtain ⟨Y, hY⟩ := hfin y hy
    have := h y hy
    rw [hP, hY, EReal.toReal_coe, EReal.toReal_coe] at this
    rw [hP, hY, ← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith

/-- (L2) regular subgradient is a subgradient -/
lemma aux_mem_subdiff (f : E → EReal) (p ζ : E) (h : IsRegularSubgradientAt f p ζ) :
    ζ ∈ subdifferential f p := by
  exact ⟨h.1, h.2.1, fun _ => p, fun _ => ζ, tendsto_const_nhds, tendsto_const_nhds,
    tendsto_const_nhds, fun _ => h⟩

/-- (L3) bound of regular subgradient by an upper estimate -/
lemma aux_regSub_bound (f : E → EReal) (p ζ a : E) (c : ℝ) (hc : 0 ≤ c) (W : Set E)
    (hW : W ∈ 𝓝 p) (hfin : ∀ y ∈ W, IsFiniteEReal (f y))
    (h : IsRegularSubgradientAt f p ζ)
    (hup : ∀ y ∈ W, (f y).toReal ≤ (f p).toReal + inner ℝ a (y - p) + c * ‖y - p‖) :
    ‖ζ - a‖ ≤ c := by
  by_contra hcon
  push_neg at hcon
  have hdpos : 0 < ‖ζ - a‖ := lt_of_le_of_lt hc hcon
  have hε : 0 < (‖ζ - a‖ - c) / 2 := by linarith
  obtain ⟨_, _, r, hr, V, hV, hineq⟩ := h
  have hr' := (Asymptotics.isLittleO_iff.mp hr) hε
  have hmem : W ∩ V ∩ {y | ‖r y‖ ≤ (‖ζ - a‖ - c) / 2 * ‖‖y - p‖‖} ∈ 𝓝 p :=
    Filter.inter_mem (Filter.inter_mem hW hV) hr'
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hmem
  have ht : 0 < ρ / (2 * ‖ζ - a‖) := by positivity
  have hyp : (p + (ρ / (2 * ‖ζ - a‖)) • (ζ - a)) - p = (ρ / (2 * ‖ζ - a‖)) • (ζ - a) :=
    add_sub_cancel_left _ _
  have hnorm : ‖(p + (ρ / (2 * ‖ζ - a‖)) • (ζ - a)) - p‖ = ρ / (2 * ‖ζ - a‖) * ‖ζ - a‖ := by
    rw [hyp, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have htd : ρ / (2 * ‖ζ - a‖) * ‖ζ - a‖ = ρ / 2 := by
    field_simp
  have hyball : p + (ρ / (2 * ‖ζ - a‖)) • (ζ - a) ∈ Metric.ball p ρ := by
    rw [Metric.mem_ball, dist_eq_norm, hnorm, htd]; linarith
  obtain ⟨⟨hyW, hyV⟩, hyr⟩ := hball hyball
  obtain ⟨P, hP⟩ := hfin p (mem_of_mem_nhds hW)
  obtain ⟨Y, hY⟩ := hfin _ hyW
  have h1 := hineq _ hyV
  rw [hP, hY, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
  have h2 := hup _ hyW
  rw [hP, hY, EReal.toReal_coe, EReal.toReal_coe] at h2
  simp only [Set.mem_setOf_eq, norm_norm] at hyr
  have h3 : inner ℝ (ζ - a) ((p + (ρ / (2 * ‖ζ - a‖)) • (ζ - a)) - p)
      = ρ / (2 * ‖ζ - a‖) * ‖ζ - a‖ ^ 2 := by
    rw [hyp, inner_smul_right, real_inner_self_eq_norm_sq]
  have h4 := inner_sub_left (𝕜 := ℝ) ζ a ((p + (ρ / (2 * ‖ζ - a‖)) • (ζ - a)) - p)
  have h5 : -(r (p + (ρ / (2 * ‖ζ - a‖)) • (ζ - a))) ≤
      (‖ζ - a‖ - c) / 2 * (ρ / (2 * ‖ζ - a‖) * ‖ζ - a‖) := by
    rw [← hnorm]
    have := neg_abs_le (r (p + (ρ / (2 * ‖ζ - a‖)) • (ζ - a)))
    rw [Real.norm_eq_abs] at hyr
    linarith
  rw [hnorm] at h2
  have hkey : ρ / (2 * ‖ζ - a‖) * ‖ζ - a‖ ^ 2 ≤
      (c + (‖ζ - a‖ - c) / 2) * (ρ / (2 * ‖ζ - a‖) * ‖ζ - a‖) := by
    nlinarith
  have hpos : 0 < ρ / (2 * ‖ζ - a‖) * ‖ζ - a‖ * (‖ζ - a‖ - c - (‖ζ - a‖ - c) / 2) := by
    apply mul_pos (mul_pos ht hdpos)
    linarith
  nlinarith

lemma aux_bdd_of_locLip (f : E → EReal) (x : E) (h : IsLocallyLipschitzNearEReal f x) :
    IsLocallyBoundedAt (fun y => subdifferential f y) x := by
  obtain ⟨ρ, hρ, β, hβ0, hfin, hlip⟩ := h
  refine ⟨Metric.ball x ρ, Metric.ball_mem_nhds x hρ, β + 1, by linarith, ?_⟩
  intro y hy w hw
  have hw' : IsSubgradientAt f y w := hw
  obtain ⟨_, _, xs, vs, hxs, _, hvs, hreg⟩ := hw'
  have hev : ∀ᶠ i in Filter.atTop, xs i ∈ Metric.ball x ρ :=
    hxs (Metric.isOpen_ball.mem_nhds hy)
  have hbound : ∀ᶠ i in Filter.atTop, ‖vs i‖ ≤ β := by
    filter_upwards [hev] with i hi
    have key := aux_regSub_bound f (xs i) (vs i) 0 β hβ0 (Metric.ball x ρ)
      (Metric.isOpen_ball.mem_nhds hi)
      (fun z hz => ⟨(f z).toReal, (EReal.coe_toReal (hfin z hz).1 (hfin z hz).2).symm⟩)
      (hreg i) (by
        intro z hz
        have hl := hlip z (xs i) hz hi
        rw [Real.norm_eq_abs, smul_eq_mul, dist_eq_norm] at hl
        simp only [inner_zero_left, add_zero]
        have := (abs_le.mp hl).2
        linarith)
    simpa using key
  have hlim : Filter.Tendsto (fun i => ‖vs i‖) Filter.atTop (𝓝 ‖w‖) :=
    (continuous_norm.tendsto w).comp hvs
  have : ‖w‖ ≤ β := le_of_tendsto hlim hbound
  linarith


-- ===== group B =====
/-- (L4) lower semicontinuity of the real part from `LocalLscAt` -/
lemma aux_lsc_of_local (f : E → EReal) (O : Set E) (hO : IsOpen O)
    (hfin : ∀ x ∈ O, IsFiniteEReal (f x)) (p : E) (hp : p ∈ O) (h : LocalLscAt f p) :
    LowerSemicontinuousAt (fun y => (f y).toReal) p := by
  obtain ⟨-, -, ε, hε⟩ := h
  obtain ⟨r, hr⟩ := hfin p hp
  have hεpos : ε > 0 := by
    refine (hε (r + ε) ?_).1
    rw [hr]
    exact le_of_eq (by norm_cast)
  intro α hα
  simp only [hr, EReal.toReal_coe] at hα
  have hcl : IsClosed {x | x ∈ Metric.closedBall p ε ∧ f x ≤ α} := by
    refine (hε α ?_).2
    rw [hr]
    have h1 : ((r : ℝ) : EReal) + ((ε : ℝ) : EReal) = ((r + ε : ℝ) : EReal) := by norm_cast
    rw [h1]
    exact_mod_cast (by linarith)
  have hpS : p ∉ {x | x ∈ Metric.closedBall p ε ∧ f x ≤ α} := by
    rintro ⟨-, hle⟩
    rw [hr] at hle
    have : r ≤ α := by exact_mod_cast hle
    linarith
  have h1 : {x | x ∈ Metric.closedBall p ε ∧ f x ≤ α}ᶜ ∈ 𝓝 p := hcl.isOpen_compl.mem_nhds hpS
  have h2 : Metric.ball p ε ∈ 𝓝 p := Metric.ball_mem_nhds p hεpos
  have h3 : O ∈ 𝓝 p := hO.mem_nhds hp
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  obtain ⟨s, hs⟩ := hfin x hx3
  simp only [hs, EReal.toReal_coe]
  by_contra hcon
  push_neg at hcon
  apply hx1
  refine ⟨Metric.ball_subset_closedBall hx2, ?_⟩
  rw [hs]
  exact_mod_cast hcon

/-- (Dense) points with quadratic subgradients arbitrarily close to the center -/
lemma aux_exists_quad (G : E → ℝ) (c : E) (ρ : ℝ) (hρ : 0 < ρ)
    (hlsc : ∀ p ∈ Metric.closedBall c ρ, LowerSemicontinuousAt G p) (δ : ℝ) (hδ : 0 < δ) :
    ∃ p ∈ Metric.ball c ρ, dist p c < δ ∧ ∃ ζ : E, ∃ k : ℝ,
      ∀ y ∈ Metric.closedBall c ρ, G p + inner ℝ ζ (y - p) - k * ‖y - p‖ ^ 2 ≤ G y := by
  have hKc : IsCompact (Metric.closedBall c ρ) := isCompact_closedBall c ρ
  have hcK : c ∈ Metric.closedBall c ρ := Metric.mem_closedBall_self hρ.le
  have hKne : (Metric.closedBall c ρ).Nonempty := ⟨c, hcK⟩
  have hGlsc : LowerSemicontinuousOn G (Metric.closedBall c ρ) := fun y hy =>
    (hlsc y hy).lowerSemicontinuousWithinAt _
  obtain ⟨y₀, hy₀K, hy₀min⟩ := hGlsc.exists_isMinOn hKne hKc
  have hμ : 0 < min δ ρ := lt_min hδ hρ
  obtain ⟨k, hk, hkdef⟩ : ∃ k : ℝ, 0 < k ∧ k * (min δ ρ) ^ 2 = |G c - G y₀| + 1 :=
    ⟨(|G c - G y₀| + 1) / (min δ ρ) ^ 2, by positivity, by field_simp⟩
  have hHlsc : LowerSemicontinuousOn (fun y => G y + k * ‖y - c‖ ^ 2) (Metric.closedBall c ρ) := by
    intro y hy
    apply LowerSemicontinuousAt.lowerSemicontinuousWithinAt
    apply LowerSemicontinuousAt.add (hlsc y hy)
    exact (Continuous.continuousAt (by fun_prop)).lowerSemicontinuousAt
  obtain ⟨p, hpK, hpmin⟩ := hHlsc.exists_isMinOn hKne hKc
  have hHp : G p + k * ‖p - c‖ ^ 2 ≤ G c := by
    have := hpmin hcK
    simpa using this
  have hmp : G y₀ ≤ G p := hy₀min hpK
  have hpc : ‖p - c‖ < min δ ρ := by
    have h2 : k * ‖p - c‖ ^ 2 < k * (min δ ρ) ^ 2 := by
      rw [hkdef]
      have := le_abs_self (G c - G y₀)
      linarith
    have h3 : ‖p - c‖ ^ 2 < (min δ ρ) ^ 2 := lt_of_mul_lt_mul_left h2 hk.le
    nlinarith [norm_nonneg (p - c)]
  refine ⟨p, ?_, ?_, (-2 * k) • (p - c), k, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_lt_of_le hpc (min_le_right _ _)
  · rw [dist_eq_norm]
    exact lt_of_lt_of_le hpc (min_le_left _ _)
  · intro y hy
    have hHy : G p + k * ‖p - c‖ ^ 2 ≤ G y + k * ‖y - c‖ ^ 2 := by
      have := hpmin hy
      simpa using this
    have hyc : y - c = (y - p) + (p - c) := by abel
    have hn := norm_add_sq_real (y - p) (p - c)
    rw [← hyc] at hn
    rw [real_inner_smul_left, real_inner_comm]
    nlinarith

/-- limits of bounded regular subgradients are subgradients -/
lemma aux_limit_mem_subdiff (f : E → EReal) (x : E) (hx : IsFiniteEReal (f x))
    (hcont : Filter.Tendsto f (𝓝 x) (𝓝 (f x)))
    (p ζ : ℕ → E) (hp : Filter.Tendsto p Filter.atTop (𝓝 x))
    (hreg : ∀ n, IsRegularSubgradientAt f (p n) (ζ n)) (R : ℝ) (hR : ∀ n, ‖ζ n‖ ≤ R) :
    ∃ ζ' ∈ subdifferential f x, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Filter.Tendsto (ζ ∘ σ) Filter.atTop (𝓝 ζ') := by
  have hmem : ∀ n, ζ n ∈ Metric.closedBall (0 : E) R := fun n => by
    rw [mem_closedBall_zero_iff]
    exact hR n
  obtain ⟨ζ', -, σ, hσ, hlim⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_closedBall (x := (0 : E)) (r := R)) hmem
  obtain ⟨r, hr⟩ := hx
  have hpσ : Filter.Tendsto (p ∘ σ) Filter.atTop (𝓝 x) := hp.comp hσ.tendsto_atTop
  refine ⟨ζ', ?_, σ, hσ, hlim⟩
  refine ⟨by rw [hr]; exact EReal.bot_lt_coe r, by rw [hr]; exact EReal.coe_lt_top r,
    p ∘ σ, ζ ∘ σ, hpσ, ?_, hlim, fun i => hreg (σ i)⟩
  exact hcont.comp hpσ


-- ===== group A =====
/-- (Core) mean-value type estimate via penalized minimization -/
lemma aux_core (G : E → ℝ) (c : E) (ρ : ℝ) (hρ : 0 < ρ) (K₀ : ℝ)
    (hlsc : ∀ p ∈ Metric.closedBall c ρ, LowerSemicontinuousAt G p)
    (hsub : ∀ p ∈ Metric.ball c ρ, ∀ ζ : E, ∀ k : ℝ,
      (∀ y ∈ Metric.closedBall c ρ, G p + inner ℝ ζ (y - p) - k * ‖y - p‖ ^ 2 ≤ G y) →
        ‖ζ‖ ≤ K₀) :
    ∀ a ∈ Metric.ball c (ρ / 2), ∀ b ∈ Metric.ball c (ρ / 2), G b - G a ≤ K₀ * ‖b - a‖ := by
  intro a ha b hb
  by_contra hcon
  push_neg at hcon
  have haB : a ∈ Metric.closedBall c ρ := by
    rw [Metric.mem_closedBall]; rw [Metric.mem_ball] at ha; linarith
  have hbB : b ∈ Metric.closedBall c ρ := by
    rw [Metric.mem_closedBall]; rw [Metric.mem_ball] at hb; linarith
  obtain ⟨u, hu⟩ : ∃ u : E, u = b - a := ⟨_, rfl⟩
  rw [← hu] at hcon
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (K₀ * ‖u‖ + (G b - G a)) / 2 := ⟨_, rfl⟩
  have hr1 : K₀ * ‖u‖ < r := by rw [hr]; linarith
  have hr2 : r < G b - G a := by rw [hr]; linarith
  -- lower bound of G on the closed ball
  obtain ⟨p0, _hp0, hmin0⟩ := LowerSemicontinuousOn.exists_isMinOn (f := G)
    (Metric.nonempty_closedBall.mpr hρ.le) (isCompact_closedBall c ρ)
    (fun p hp => (hlsc p hp).lowerSemicontinuousWithinAt _)
  have hm : ∀ y ∈ Metric.closedBall c ρ, G p0 ≤ G y := fun y hy => isMinOn_iff.mp hmin0 y hy
  -- η from lower semicontinuity at b
  obtain ⟨η, hη, hηb⟩ := Metric.eventually_nhds_iff.mp
    (lowerSemicontinuousAt_iff.mp (hlsc b hbB) (G b - (G b - G a - r) / 2) (by linarith))
  -- choose the penalty parameter k
  have hC : 0 < G a - G p0 + |r| + 1 := by
    have := hm a haB
    have := abs_nonneg r
    linarith
  have hρ2 : 0 < (ρ / 2) ^ 2 := by positivity
  have hη2 : 0 < η ^ 2 := by positivity
  obtain ⟨k, hk1, hkA, hkB⟩ : ∃ k : ℝ, 1 ≤ k ∧ G a - G p0 + |r| + 1 < k * (ρ / 2) ^ 2 ∧
      G a - G p0 + |r| + 1 < k * η ^ 2 := by
    obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = G a - G p0 + |r| + 1 := ⟨_, rfl⟩
    rw [← hCdef] at hC ⊢
    refine ⟨C / (ρ / 2) ^ 2 + C / η ^ 2 + 1, ?_, ?_, ?_⟩
    · have : 0 ≤ C / (ρ / 2) ^ 2 := by positivity
      have : 0 ≤ C / η ^ 2 := by positivity
      linarith
    · have h1 : C / (ρ / 2) ^ 2 * (ρ / 2) ^ 2 = C := div_mul_cancel₀ C hρ2.ne'
      have : 0 ≤ C / η ^ 2 := by positivity
      nlinarith
    · have h1 : C / η ^ 2 * η ^ 2 = C := div_mul_cancel₀ C hη2.ne'
      have : 0 ≤ C / (ρ / 2) ^ 2 := by positivity
      nlinarith
  have hk0 : 0 < k := by linarith
  -- the penalized function
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : E × ℝ → ℝ, ∀ q : E × ℝ,
      Ψ q = G q.1 + (k * ‖a + q.2 • u - q.1‖ ^ 2 - q.2 * r) := ⟨_, fun q => rfl⟩
  have hSc : IsCompact (Metric.closedBall c ρ ×ˢ Set.Icc (0:ℝ) 1) :=
    (isCompact_closedBall c ρ).prod isCompact_Icc
  have hSne : (Metric.closedBall c ρ ×ˢ Set.Icc (0:ℝ) 1).Nonempty :=
    ⟨(a, 0), haB, by simp⟩
  have hΨlsc : LowerSemicontinuousOn Ψ (Metric.closedBall c ρ ×ˢ Set.Icc (0:ℝ) 1) := by
    have hΨeq : Ψ = fun q : E × ℝ => G q.1 + (k * ‖a + q.2 • u - q.1‖ ^ 2 - q.2 * r) :=
      funext hΨ
    rw [hΨeq]
    intro q hq
    apply LowerSemicontinuousAt.lowerSemicontinuousWithinAt
    apply LowerSemicontinuousAt.add
    · show LowerSemicontinuousAt (G ∘ Prod.fst) q
      exact (hlsc q.1 hq.1).comp continuous_fst.continuousAt
    · apply ContinuousAt.lowerSemicontinuousAt
      apply Continuous.continuousAt
      fun_prop
  obtain ⟨⟨p, t⟩, hpt, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hSne hSc hΨlsc
  have hpB : p ∈ Metric.closedBall c ρ := hpt.1
  have ht0 : 0 ≤ t := hpt.2.1
  have ht1 : t ≤ 1 := hpt.2.2
  have hmin' := isMinOn_iff.mp hmin
  obtain ⟨w, hw⟩ : ∃ w : E, w = a + t • u - p := ⟨_, rfl⟩
  have e2 : Ψ (p, t) = G p + (k * ‖w‖ ^ 2 - t * r) := by simp only [hΨ, hw]
  -- (A') comparison with (a, 0)
  have hA : G p + (k * ‖w‖ ^ 2 - t * r) ≤ G a := by
    have h1 := hmin' (a, 0) ⟨haB, by simp⟩
    have e1 : Ψ (a, 0) = G a := by rw [hΨ]; simp
    rw [e2, e1] at h1
    exact h1
  have htr : t * r ≤ |r| := by
    have h1 : t * r ≤ t * |r| := mul_le_mul_of_nonneg_left (le_abs_self r) ht0
    have h2 : t * |r| ≤ 1 * |r| := mul_le_mul_of_nonneg_right ht1 (abs_nonneg r)
    linarith
  have hkw : k * ‖w‖ ^ 2 < k * (ρ / 2) ^ 2 := by
    have := hm p hpB
    linarith
  have hw_lt : ‖w‖ < ρ / 2 := by
    have h2 : ‖w‖ ^ 2 < (ρ / 2) ^ 2 := lt_of_mul_lt_mul_left hkw hk0.le
    nlinarith [norm_nonneg w]
  have hq0 : a + t • u ∈ Metric.ball c (ρ / 2) := by
    have h1 := (convex_ball c (ρ / 2)) ha hb (sub_nonneg.mpr ht1) ht0 (by ring)
    have e : a + t • u = (1 - t) • a + t • b := by rw [hu]; module
    rw [e]; exact h1
  have hpball : p ∈ Metric.ball c ρ := by
    rw [Metric.mem_ball] at hq0 ⊢
    have h1 : dist p (a + t • u) = ‖w‖ := by rw [dist_eq_norm, hw, norm_sub_rev]
    have := dist_triangle p (a + t • u) c
    linarith
  -- (B') t < 1
  have ht_lt : t < 1 := by
    by_contra h
    have ht : t = 1 := le_antisymm ht1 (not_lt.mp h)
    have hwb : w = b - p := by rw [hw, ht, one_smul, hu]; abel
    rw [ht] at hA
    by_cases hpb : dist p b < η
    · have h1 := hηb hpb
      have hk0w : 0 ≤ k * ‖w‖ ^ 2 := by positivity
      linarith
    · push_neg at hpb
      have hwη : η ≤ ‖w‖ := by rw [hwb, ← dist_eq_norm, _root_.dist_comm]; exact hpb
      have h2 : k * η ^ 2 ≤ k * ‖w‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hη.le hwη 2) hk0.le
      have := hm p hpB
      have := le_abs_self r
      linarith
  -- (C) first-order condition in t
  have hCstep : r ≤ 2 * k * inner ℝ w u := by
    by_contra hneg
    push_neg at hneg
    have hδ0 : 0 < r - 2 * k * inner ℝ w u := by linarith
    have hden : 0 < 2 * (k * ‖u‖ ^ 2 + 1) := by positivity
    obtain ⟨s, hs⟩ : ∃ s : ℝ,
        s = min (1 - t) ((r - 2 * k * inner ℝ w u) / (2 * (k * ‖u‖ ^ 2 + 1))) := ⟨_, rfl⟩
    have hs0 : 0 < s := by rw [hs]; exact lt_min (by linarith) (div_pos hδ0 hden)
    have hs1 : s ≤ 1 - t := by rw [hs]; exact min_le_left _ _
    have hs2 : s ≤ (r - 2 * k * inner ℝ w u) / (2 * (k * ‖u‖ ^ 2 + 1)) := by
      rw [hs]; exact min_le_right _ _
    have h5 : s * (2 * (k * ‖u‖ ^ 2 + 1)) ≤ r - 2 * k * inner ℝ w u :=
      (le_div_iff₀ hden).mp hs2
    have h3 := hmin' (p, t + s) ⟨hpB, by show (0:ℝ) ≤ t + s; linarith,
      by show t + s ≤ 1; linarith⟩
    have e3 : Ψ (p, t + s) = G p + (k * ‖w + s • u‖ ^ 2 - (t + s) * r) := by
      rw [hΨ]
      dsimp only
      rw [show a + (t + s) • u - p = w + s • u by rw [hw, add_smul]; abel]
    have e4 : ‖w + s • u‖ ^ 2 = ‖w‖ ^ 2 + 2 * (s * inner ℝ w u) + s ^ 2 * ‖u‖ ^ 2 := by
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs]
    rw [e2, e3, e4] at h3
    have h6 : s * (s * (2 * (k * ‖u‖ ^ 2 + 1))) ≤ s * (r - 2 * k * inner ℝ w u) :=
      mul_le_mul_of_nonneg_left h5 hs0.le
    nlinarith [mul_pos hs0 hδ0, sq_nonneg s]
  -- (D) the quadratic minorant at p
  have hD : ∀ y ∈ Metric.closedBall c ρ,
      G p + inner ℝ ((2 * k) • w) (y - p) - k * ‖y - p‖ ^ 2 ≤ G y := by
    intro y hy
    have h3 := hmin' (y, t) ⟨hy, ht0, ht1⟩
    have e5 : Ψ (y, t) = G y + (k * ‖w - (y - p)‖ ^ 2 - t * r) := by
      rw [hΨ]
      dsimp only
      rw [show a + t • u - y = w - (y - p) by rw [hw]; abel]
    have e6 : ‖w - (y - p)‖ ^ 2 = ‖w‖ ^ 2 - 2 * inner ℝ w (y - p) + ‖y - p‖ ^ 2 :=
      norm_sub_sq_real w (y - p)
    rw [e2, e5, e6] at h3
    rw [real_inner_smul_left]
    nlinarith
  -- (E) contradiction with the subgradient bound
  have hζ := hsub p hpball ((2 * k) • w) k hD
  have h8 : inner ℝ ((2 * k) • w) u ≤ ‖(2 * k) • w‖ * ‖u‖ := real_inner_le_norm _ _
  rw [real_inner_smul_left] at h8
  have h9 : ‖(2 * k) • w‖ * ‖u‖ ≤ K₀ * ‖u‖ := mul_le_mul_of_nonneg_right hζ (norm_nonneg u)
  linarith


-- ===== group G =====
/-- (4) ⇒ strict differentiability, real form -/
lemma aux_S4_to_SD (f : E → EReal) (O : Set E) (hO : IsOpen O)
    (hfin : ∀ x ∈ O, IsFiniteEReal (f x))
    (hlsc : ∀ x ∈ O, LocalLscAt f x)
    (hbdd : ∀ x ∈ O, IsLocallyBoundedAt (fun y => subdifferential f y) x)
    (huniq : ∀ x ∈ O, (subdifferential f x).Nonempty → ∃! v, v ∈ subdifferential f x)
    (x : E) (hx : x ∈ O) :
    ∃ v : E, ∀ ε > 0, ∃ δ > 0, ∀ y ∈ Metric.ball x δ, ∀ z ∈ Metric.ball x δ,
      |(f y).toReal - (f z).toReal - inner ℝ v (y - z)| ≤ ε * ‖y - z‖ := by
  -- Step 1: a ball around x inside U ∩ O
  obtain ⟨U, hU, R, hRpos, hR⟩ := hbdd x hx
  have hUO : U ∩ O ∈ 𝓝 x := Filter.inter_mem hU (hO.mem_nhds hx)
  obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.mem_nhds_iff.mp hUO
  have hρ : 0 < ρ₁ / 2 := by positivity
  have hcb : Metric.closedBall x (ρ₁ / 2) ⊆ U ∩ O :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  -- Step 2: lower semicontinuity
  have hlscF : ∀ p ∈ Metric.closedBall x (ρ₁ / 2),
      LowerSemicontinuousAt (fun y => (f y).toReal) p := fun p hp =>
    aux_lsc_of_local f O hO hfin p (hcb hp).2 (hlsc p (hcb hp).2)
  -- Step 3: key fact
  have hQ : ∀ r, 0 < r → r ≤ ρ₁ / 2 → ∀ p ∈ Metric.ball x r, ∀ ζ : E, ∀ k : ℝ,
      (∀ y ∈ Metric.closedBall x r,
        (f p).toReal + inner ℝ ζ (y - p) - k * ‖y - p‖ ^ 2 ≤ (f y).toReal) →
      IsRegularSubgradientAt f p ζ := by
    intro r hr hrρ p hp ζ k h
    apply aux_isRegSub_of_quad f p ζ k (Metric.closedBall x r)
    · exact Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hp) Metric.ball_subset_closedBall
    · intro y hy
      exact hfin y (hcb (Metric.closedBall_subset_closedBall hrρ hy)).2
    · exact h
  have hRbound : ∀ p ∈ Metric.closedBall x (ρ₁ / 2), ∀ ζ,
      IsRegularSubgradientAt f p ζ → ‖ζ‖ ≤ R := by
    intro p hp ζ h
    exact hR p (hcb hp).1 ζ (aux_mem_subdiff f p ζ h)
  -- Step 4: Lipschitz and continuity
  have hLip : ∀ a ∈ Metric.ball x (ρ₁ / 2 / 2), ∀ b ∈ Metric.ball x (ρ₁ / 2 / 2),
      (f b).toReal - (f a).toReal ≤ R * ‖b - a‖ :=
    aux_core (fun y => (f y).toReal) x (ρ₁ / 2) hρ R hlscF
      (fun p hp ζ k h => hRbound p (Metric.ball_subset_closedBall hp) ζ
        (hQ (ρ₁ / 2) hρ le_rfl p hp ζ k h))
  have hFcont : ContinuousAt (fun y => (f y).toReal) x := by
    rw [Metric.continuousAt_iff]
    intro e he
    refine ⟨min (ρ₁ / 2 / 2) (e / (R + 1)), by positivity, fun y hy => ?_⟩
    have hy1 : dist y x < ρ₁ / 2 / 2 := lt_of_lt_of_le hy (min_le_left _ _)
    have hy2 : dist y x < e / (R + 1) := lt_of_lt_of_le hy (min_le_right _ _)
    have hyb : y ∈ Metric.ball x (ρ₁ / 2 / 2) := hy1
    have hxb : x ∈ Metric.ball x (ρ₁ / 2 / 2) := Metric.mem_ball_self (by positivity)
    have h1 := hLip x hxb y hyb
    have h2 := hLip y hyb x hxb
    rw [norm_sub_rev] at h2
    rw [← dist_eq_norm] at h1 h2
    rw [Real.dist_eq, abs_lt]
    have hR1 : R * dist y x < e := by
      have : R * dist y x ≤ R * (e / (R + 1)) :=
        mul_le_mul_of_nonneg_left hy2.le hRpos.le
      have h3 : R * (e / (R + 1)) < e := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith
      linarith
    constructor <;> linarith
  have hfeq : ∀ y ∈ O, (((f y).toReal : ℝ) : EReal) = f y := by
    intro y hy
    obtain ⟨r, hr⟩ := hfin y hy
    simp [hr]
  have hfcont : Filter.Tendsto f (𝓝 x) (𝓝 (f x)) := by
    have h1 : Filter.Tendsto (fun y => (((f y).toReal : ℝ) : EReal)) (𝓝 x)
        (𝓝 (((f x).toReal : ℝ) : EReal)) :=
      continuous_coe_real_ereal.continuousAt.tendsto.comp hFcont
    rw [hfeq x hx] at h1
    apply h1.congr'
    filter_upwards [hO.mem_nhds hx] with y hy
    exact hfeq y hy
  -- Step 5: nonemptiness of the subdifferential at x
  have hex : ∀ n : ℕ, ∃ p ∈ Metric.ball x (ρ₁ / 2), dist p x < 1 / ((n : ℝ) + 1) ∧
      ∃ ζ : E, ∃ k : ℝ, ∀ y ∈ Metric.closedBall x (ρ₁ / 2),
        (fun y => (f y).toReal) p + inner ℝ ζ (y - p) - k * ‖y - p‖ ^ 2 ≤
          (fun y => (f y).toReal) y :=
    fun n => aux_exists_quad (fun y => (f y).toReal) x (ρ₁ / 2) hρ hlscF _ (by positivity)
  choose p hp hpd ζ k hζ using hex
  have hpt : Filter.Tendsto p Filter.atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hpd n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hreg : ∀ n, IsRegularSubgradientAt f (p n) (ζ n) := fun n =>
    hQ (ρ₁ / 2) hρ le_rfl (p n) (hp n) (ζ n) (k n) (hζ n)
  have hζR : ∀ n, ‖ζ n‖ ≤ R := fun n =>
    hRbound (p n) (Metric.ball_subset_closedBall (hp n)) (ζ n) (hreg n)
  obtain ⟨ζ', hζ', -⟩ := aux_limit_mem_subdiff f x (hfin x hx) hfcont p ζ hpt hreg R hζR
  obtain ⟨v, hv, hvuniq⟩ := huniq x hx ⟨ζ', hζ'⟩
  refine ⟨v, ?_⟩
  -- Step 6: regular subgradients near x are close to v
  have hKL : ∀ η > 0, ∃ δ > 0, δ ≤ ρ₁ / 2 ∧ ∀ q ∈ Metric.ball x δ, ∀ ξ,
      IsRegularSubgradientAt f q ξ → ‖ξ - v‖ ≤ η := by
    intro η hη
    by_contra hcon
    push_neg at hcon
    have hex2 : ∀ n : ℕ, ∃ q ∈ Metric.ball x (min (ρ₁ / 2) (1 / ((n : ℝ) + 1))), ∃ ξ,
        IsRegularSubgradientAt f q ξ ∧ η < ‖ξ - v‖ := fun n =>
      hcon _ (lt_min hρ (by positivity)) (min_le_left _ _)
    choose q hq ξ hξreg hξη using hex2
    have hqρ : ∀ n, q n ∈ Metric.closedBall x (ρ₁ / 2) := fun n =>
      Metric.ball_subset_closedBall (Metric.ball_subset_ball (min_le_left _ _) (hq n))
    have hqt : Filter.Tendsto q Filter.atTop (𝓝 x) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun n => dist_nonneg)
        (fun n => (lt_of_lt_of_le (Metric.mem_ball.mp (hq n)) (min_le_right _ _)).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hξR : ∀ n, ‖ξ n‖ ≤ R := fun n => hRbound (q n) (hqρ n) (ξ n) (hξreg n)
    obtain ⟨ξ', hξ', σ, -, hξσ⟩ :=
      aux_limit_mem_subdiff f x (hfin x hx) hfcont q ξ hqt hξreg R hξR
    have hξv : ξ' = v := hvuniq ξ' hξ'
    have h1 : Filter.Tendsto (fun n => ‖(ξ ∘ σ) n - v‖) Filter.atTop (𝓝 ‖ξ' - v‖) :=
      (hξσ.sub_const v).norm
    have h2 : η ≤ ‖ξ' - v‖ := ge_of_tendsto' h1 (fun n => (hξη (σ n)).le)
    rw [hξv, sub_self, norm_zero] at h2
    linarith
  -- Step 7: strict differentiability estimate
  intro ε hε
  obtain ⟨δ, hδ, hδρ, hδKL⟩ := hKL ε hε
  have hlscG : ∀ p ∈ Metric.closedBall x δ,
      LowerSemicontinuousAt (fun y => (f y).toReal - inner ℝ v y) p := by
    intro p hp
    have h1 := hlscF p (Metric.closedBall_subset_closedBall hδρ hp)
    have h2 : ContinuousAt (fun y => inner ℝ v y) p :=
      (continuous_const.inner continuous_id).continuousAt
    intro t ht
    have hgap : 0 < (f p).toReal - inner ℝ v p - t := by linarith
    have hA := h1 ((f p).toReal - ((f p).toReal - inner ℝ v p - t) / 2) (by linarith)
    have hB : ∀ᶠ y in 𝓝 p, inner ℝ v y < inner ℝ v p + ((f p).toReal - inner ℝ v p - t) / 2 :=
      h2.eventually (gt_mem_nhds (by linarith))
    filter_upwards [hA, hB] with y hyA hyB
    linarith
  have hsubG : ∀ p ∈ Metric.ball x δ, ∀ ζ : E, ∀ k : ℝ,
      (∀ y ∈ Metric.closedBall x δ, ((f p).toReal - inner ℝ v p) + inner ℝ ζ (y - p) -
        k * ‖y - p‖ ^ 2 ≤ (f y).toReal - inner ℝ v y) → ‖ζ‖ ≤ ε := by
    intro p hp ζ k h
    have hreg : IsRegularSubgradientAt f p (ζ + v) := by
      apply hQ δ hδ hδρ p hp (ζ + v) k
      intro y hy
      have := h y hy
      rw [inner_add_left, inner_sub_right v y p]
      linarith
    have := hδKL p hp (ζ + v) hreg
    simpa using this
  have hcore : ∀ a ∈ Metric.ball x (δ / 2), ∀ b ∈ Metric.ball x (δ / 2),
      ((f b).toReal - inner ℝ v b) - ((f a).toReal - inner ℝ v a) ≤ ε * ‖b - a‖ :=
    aux_core (fun y => (f y).toReal - inner ℝ v y) x δ hδ ε hlscG hsubG
  refine ⟨δ / 2, by positivity, fun y hy z hz => ?_⟩
  have h1 := hcore z hz y hy
  have h2 := hcore y hy z hz
  rw [norm_sub_rev] at h2
  rw [inner_sub_right, abs_le]
  constructor <;> linarith


-- ===== group E =====
lemma aux_sd_of_strict (f : E → EReal) (O : Set E) (hO : IsOpen O)
    (hfin : ∀ x ∈ O, IsFiniteEReal (f x)) (x v : E) (hx : x ∈ O)
    (h : IsStrictlyDifferentiableAt f x v) :
    ∀ ε > 0, ∃ δ > 0, ∀ y ∈ Metric.ball x δ, ∀ z ∈ Metric.ball x δ,
      |(f y).toReal - (f z).toReal - inner ℝ v (y - z)| ≤ ε * ‖y - z‖ := by
  intro ε hε
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.mp hO x hx
  obtain ⟨_, htend⟩ := h
  have hnhds : Set.Ioo ((-ε : ℝ) : EReal) ((ε : ℝ) : EReal) ∈ 𝓝 (0 : EReal) := by
    apply Ioo_mem_nhds
    · exact_mod_cast (neg_neg_of_pos hε)
    · exact_mod_cast hε
  have hev := htend.eventually_mem hnhds
  rw [← nhds_prod_eq, Filter.eventually_inf_principal, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hd⟩ := hev
  refine ⟨min δ δ₀, lt_min hδ hδ₀, fun y hy z hz => ?_⟩
  have hy1 : y ∈ Metric.ball x δ := Metric.ball_subset_ball (min_le_left _ _) hy
  have hz1 : z ∈ Metric.ball x δ := Metric.ball_subset_ball (min_le_left _ _) hz
  have hyO : y ∈ O := hball (Metric.ball_subset_ball (min_le_right _ _) hy)
  have hzO : z ∈ O := hball (Metric.ball_subset_ball (min_le_right _ _) hz)
  by_cases hyz : y = z
  · subst hyz
    simp
  have hdist : dist (z, y) (x, x) < δ := by
    rw [Prod.dist_eq]
    exact max_lt hz1 hy1
  have hq := hd hdist hyz
  obtain ⟨a, ha⟩ := hfin y hyO
  obtain ⟨b, hb⟩ := hfin z hzO
  simp only at hq
  rw [ha, hb, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_div] at hq
  rw [ha, hb, EReal.toReal_coe, EReal.toReal_coe]
  obtain ⟨hq1, hq2⟩ := hq
  rw [EReal.coe_lt_coe_iff] at hq1 hq2
  have hpos : 0 < ‖y - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyz)
  have habs : |(a - b - inner ℝ v (y - z)) / ‖y - z‖| < ε := abs_lt.mpr ⟨hq1, hq2⟩
  rw [abs_div, abs_norm, div_lt_iff₀ hpos] at habs
  exact le_of_lt habs

lemma aux_strict_of_sd (f : E → EReal) (O : Set E) (hO : IsOpen O)
    (hfin : ∀ x ∈ O, IsFiniteEReal (f x)) (x v : E) (hx : x ∈ O)
    (h : ∀ ε > 0, ∃ δ > 0, ∀ y ∈ Metric.ball x δ, ∀ z ∈ Metric.ball x δ,
      |(f y).toReal - (f z).toReal - inner ℝ v (y - z)| ≤ ε * ‖y - z‖) :
    IsStrictlyDifferentiableAt f x v := by
  refine ⟨hfin x hx, ?_⟩
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.mp hO x hx
  let Q : E × E → ℝ := fun p =>
    ((f p.2).toReal - (f p.1).toReal - inner ℝ v (p.2 - p.1)) / ‖p.2 - p.1‖
  have hev : ∀ᶠ p in ((𝓝 x) ×ˢ (𝓝 x)) ⊓ Filter.principal {p : E × E | p.2 ≠ p.1},
      ((Q p : ℝ) : EReal) = (f p.2 - f p.1 - (((inner ℝ v (p.2 - p.1)) : ℝ) : EReal)) /
        ((‖p.2 - p.1‖ : ℝ) : EReal) := by
    have h1 : ∀ᶠ p in ((𝓝 x) ×ˢ (𝓝 x)) ⊓ Filter.principal {p : E × E | p.2 ≠ p.1},
        p ∈ Metric.ball x δ₀ ×ˢ Metric.ball x δ₀ := by
      apply Filter.mem_inf_of_left
      exact Filter.prod_mem_prod (Metric.ball_mem_nhds x hδ₀) (Metric.ball_mem_nhds x hδ₀)
    filter_upwards [h1] with p hp
    obtain ⟨a, ha⟩ := hfin p.2 (hball hp.2)
    obtain ⟨b, hb⟩ := hfin p.1 (hball hp.1)
    simp only [Q, ha, hb, EReal.toReal_coe]
    rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_div]
  apply Filter.Tendsto.congr' hev
  have hreal : Filter.Tendsto Q (((𝓝 x) ×ˢ (𝓝 x)) ⊓ Filter.principal {p : E × E | p.2 ≠ p.1})
      (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := h (ε / 2) (half_pos hε)
    have h2 : ∀ᶠ p in ((𝓝 x) ×ˢ (𝓝 x)) ⊓ Filter.principal {p : E × E | p.2 ≠ p.1},
        p ∈ (Metric.ball x δ ×ˢ Metric.ball x δ) ∩ {p : E × E | p.2 ≠ p.1} := by
      apply Filter.inter_mem_inf
      · exact Filter.prod_mem_prod (Metric.ball_mem_nhds x hδ) (Metric.ball_mem_nhds x hδ)
      · exact Filter.mem_principal_self _
    filter_upwards [h2] with p hp
    obtain ⟨⟨hp1, hp2⟩, hne⟩ := hp
    have hpos : 0 < ‖p.2 - p.1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hb := hd p.2 hp2 p.1 hp1
    rw [Real.dist_eq, sub_zero]
    simp only [Q]
    rw [abs_div, abs_norm, div_lt_iff₀ hpos]
    nlinarith
  have := (continuous_coe_real_ereal.tendsto 0).comp hreal
  simpa using this

lemma aux_sd_congr (F G : E → ℝ) (O : Set E) (hO : IsOpen O) (hFG : ∀ y ∈ O, F y = G y)
    (x v : E) (hx : x ∈ O)
    (h : ∀ ε > 0, ∃ δ > 0, ∀ y ∈ Metric.ball x δ, ∀ z ∈ Metric.ball x δ,
      |F y - F z - inner ℝ v (y - z)| ≤ ε * ‖y - z‖) :
    ∀ ε > 0, ∃ δ > 0, ∀ y ∈ Metric.ball x δ, ∀ z ∈ Metric.ball x δ,
      |G y - G z - inner ℝ v (y - z)| ≤ ε * ‖y - z‖ := by
  intro ε hε
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.mp hO x hx
  obtain ⟨δ, hδ, hd⟩ := h ε hε
  refine ⟨min δ δ₀, lt_min hδ hδ₀, fun y hy z hz => ?_⟩
  have hy1 : y ∈ Metric.ball x δ := Metric.ball_subset_ball (min_le_left _ _) hy
  have hz1 : z ∈ Metric.ball x δ := Metric.ball_subset_ball (min_le_left _ _) hz
  have hyO : y ∈ O := hball (Metric.ball_subset_ball (min_le_right _ _) hy)
  have hzO : z ∈ O := hball (Metric.ball_subset_ball (min_le_right _ _) hz)
  rw [← hFG y hyO, ← hFG z hzO]
  exact hd y hy1 z hz1


-- ===== group F =====
lemma aux_contDiffOn_of_sd (g : E → ℝ) (O : Set E) (hO : IsOpen O)
    (h : ∀ x ∈ O, ∃ v : E, ∀ ε > 0, ∃ δ > 0, ∀ y ∈ Metric.ball x δ, ∀ z ∈ Metric.ball x δ,
      |g y - g z - inner ℝ v (y - z)| ≤ ε * ‖y - z‖) :
    ContDiffOn ℝ 1 g O := by
  choose! V hV using h
  have hder : ∀ y ∈ O, HasFDerivAt g (innerSL ℝ (V y)) y := by
    intro y hy
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro c hc
    obtain ⟨δ, hδ, hδ'⟩ := hV y hy c hc
    rw [Metric.eventually_nhds_iff]
    refine ⟨δ, hδ, fun w hw => ?_⟩
    have hyw : y + w ∈ Metric.ball y δ := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      simpa [dist_eq_norm] using hw
    have := hδ' (y + w) hyw y (Metric.mem_ball_self hδ)
    rw [add_sub_cancel_left] at this
    rw [innerSL_apply_apply, Real.norm_eq_abs]
    exact this
  have hfd : ∀ y ∈ O, fderiv ℝ g y = innerSL ℝ (V y) := fun y hy => (hder y hy).fderiv
  have hcont : ContinuousOn (fderiv ℝ g) O := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hV x hx (ε / 2) (by positivity)
    obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO x hx
    refine ⟨min δ r, lt_min hδ hr, fun x' hx' => ?_⟩
    have hx'O : x' ∈ O := hrO (lt_of_lt_of_le hx' (min_le_right _ _))
    have hx'δ : x' ∈ Metric.ball x δ := lt_of_lt_of_le hx' (min_le_left _ _)
    rw [dist_eq_norm, hfd x' hx'O, hfd x hx]
    have hk : HasFDerivAt (fun y => g y - inner ℝ (V x) y)
        (innerSL ℝ (V x') - innerSL ℝ (V x)) x' :=
      (hder x' hx'O).sub ((innerSL ℝ (V x)).hasFDerivAt)
    have hle : ‖innerSL ℝ (V x') - innerSL ℝ (V x)‖ ≤ ε / 2 := by
      refine hk.le_of_lip' (by positivity) ?_
      have hn : Metric.ball x δ ∈ 𝓝 x' := Metric.isOpen_ball.mem_nhds hx'δ
      filter_upwards [hn] with y hy
      have h2 := hδ' y hy x' hx'δ
      rw [Real.norm_eq_abs]
      calc |g y - inner ℝ (V x) y - (g x' - inner ℝ (V x) x')|
          = |g y - g x' - inner ℝ (V x) (y - x')| := by rw [inner_sub_right]; ring_nf
        _ ≤ ε / 2 * ‖y - x'‖ := h2
    linarith
  have hca : ∀ x ∈ O, ContDiffAt ℝ 1 g x := by
    intro x hx
    rw [contDiffAt_one_iff]
    exact ⟨fderiv ℝ g, O, hO.mem_nhds hx, hcont, fun y hy => by rw [hfd y hy]; exact hder y hy⟩
  exact fun x hx => (hca x hx).contDiffWithinAt

lemma aux_sd_of_contDiffOn (g : E → ℝ) (O : Set E) (hO : IsOpen O)
    (hg : ContDiffOn ℝ 1 g O) (x : E) (hx : x ∈ O) :
    ∃ v : E, ∀ ε > 0, ∃ δ > 0, ∀ y ∈ Metric.ball x δ, ∀ z ∈ Metric.ball x δ,
      |g y - g z - inner ℝ v (y - z)| ≤ ε * ‖y - z‖ := by
  have hca : ContDiffAt ℝ 1 g x := hg.contDiffAt (hO.mem_nhds hx)
  have hs : HasStrictFDerivAt g (fderiv ℝ g x) x := hca.hasStrictFDerivAt (by norm_num)
  refine ⟨(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ g x), ?_⟩
  intro ε hε
  have hlo := hasStrictFDerivAt_iff_isLittleO.mp hs
  rw [Asymptotics.isLittleO_iff] at hlo
  have h1 := hlo hε
  rw [Metric.eventually_nhds_iff] at h1
  obtain ⟨δ, hδ, hδ'⟩ := h1
  refine ⟨δ, hδ, fun y hy z hz => ?_⟩
  have hyz : dist (y, z) (x, x) < δ := by
    rw [Prod.dist_eq]
    exact max_lt hy hz
  have h2 := hδ' hyz
  rw [InnerProductSpace.toDual_symm_apply]
  rw [Real.norm_eq_abs] at h2
  exact h2


-- ===== group C2 =====
lemma aux_C2_lip (f : E → EReal) (O : Set E) (hO : IsOpen O)
    (x v : E) (hx : x ∈ O)
    (h : ∀ ε > 0, ∃ δ > 0, ∀ y ∈ Metric.ball x δ, ∀ z ∈ Metric.ball x δ,
      |(f y).toReal - (f z).toReal - inner ℝ v (y - z)| ≤ ε * ‖y - z‖) :
    ∃ ρ > 0, Metric.ball x ρ ⊆ O ∧ ∀ y ∈ Metric.ball x ρ, ∀ z ∈ Metric.ball x ρ,
      |(f y).toReal - (f z).toReal| ≤ (‖v‖ + 1) * ‖y - z‖ := by
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.mp hO x hx
  obtain ⟨δ, hδ, hδh⟩ := h 1 one_pos
  refine ⟨min δ δ₀, lt_min hδ hδ₀, (Metric.ball_subset_ball (min_le_right _ _)).trans hball, ?_⟩
  intro y hy z hz
  have h1 := hδh y (Metric.ball_subset_ball (min_le_left _ _) hy) z
    (Metric.ball_subset_ball (min_le_left _ _) hz)
  have h2 := abs_real_inner_le_norm v (y - z)
  calc |(f y).toReal - (f z).toReal|
      = |((f y).toReal - (f z).toReal - inner ℝ v (y - z)) + inner ℝ v (y - z)| := by
        rw [sub_add_cancel]
    _ ≤ |(f y).toReal - (f z).toReal - inner ℝ v (y - z)| + |inner ℝ v (y - z)| :=
        abs_add_le _ _
    _ ≤ 1 * ‖y - z‖ + ‖v‖ * ‖y - z‖ := add_le_add h1 h2
    _ = (‖v‖ + 1) * ‖y - z‖ := by ring

lemma aux_locLip_of_sd (f : E → EReal) (O : Set E) (hO : IsOpen O)
    (hfin : ∀ x ∈ O, IsFiniteEReal (f x)) (x v : E) (hx : x ∈ O)
    (h : ∀ ε > 0, ∃ δ > 0, ∀ y ∈ Metric.ball x δ, ∀ z ∈ Metric.ball x δ,
      |(f y).toReal - (f z).toReal - inner ℝ v (y - z)| ≤ ε * ‖y - z‖) :
    IsLocallyLipschitzNearEReal f x := by
  obtain ⟨ρ, hρ, hsub, hlip⟩ := aux_C2_lip f O hO x v hx h
  refine ⟨ρ, hρ, ‖v‖ + 1, by positivity, ?_, ?_⟩
  · intro y hy
    obtain ⟨r, hr⟩ := hfin y (hsub hy)
    rw [hr]
    exact ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩
  · intro y z hy hz
    rw [Real.norm_eq_abs, smul_eq_mul, dist_eq_norm]
    exact hlip y hy z hz

lemma aux_localLsc_of_sd (f : E → EReal) (O : Set E) (hO : IsOpen O)
    (hfin : ∀ x ∈ O, IsFiniteEReal (f x)) (x v : E) (hx : x ∈ O)
    (h : ∀ ε > 0, ∃ δ > 0, ∀ y ∈ Metric.ball x δ, ∀ z ∈ Metric.ball x δ,
      |(f y).toReal - (f z).toReal - inner ℝ v (y - z)| ≤ ε * ‖y - z‖) :
    LocalLscAt f x := by
  obtain ⟨ρ, hρ, hsub, hlip⟩ := aux_C2_lip f O hO x v hx h
  obtain ⟨r, hr⟩ := hfin x hx
  have hcb : Metric.closedBall x (ρ / 2) ⊆ Metric.ball x ρ :=
    Metric.closedBall_subset_ball (by linarith)
  have hcont : ContinuousOn (fun y => (f y).toReal) (Metric.closedBall x (ρ / 2)) := by
    have hL : LipschitzOnWith (Real.toNNReal (‖v‖ + 1)) (fun y => (f y).toReal)
        (Metric.ball x ρ) := by
      apply LipschitzOnWith.of_dist_le'
      intro y hy z hz
      rw [Real.dist_eq, dist_eq_norm]
      exact hlip y hy z hz
    exact (hL.mono hcb).continuousOn
  refine ⟨by rw [hr]; exact EReal.bot_lt_coe r, by rw [hr]; exact EReal.coe_lt_top r,
    ρ / 2, fun α _ => ⟨by positivity, ?_⟩⟩
  have hset : {y | y ∈ Metric.closedBall x (ρ / 2) ∧ f y ≤ (α : EReal)} =
      Metric.closedBall x (ρ / 2) ∩ (fun y => (f y).toReal) ⁻¹' Set.Iic α := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
    constructor
    · rintro ⟨hy, hfy⟩
      obtain ⟨s, hs⟩ := hfin y (hsub (hcb hy))
      rw [hs] at hfy
      refine ⟨hy, ?_⟩
      rw [hs, EReal.toReal_coe]
      exact EReal.coe_le_coe_iff.mp hfy
    · rintro ⟨hy, hfy⟩
      obtain ⟨s, hs⟩ := hfin y (hsub (hcb hy))
      rw [hs, EReal.toReal_coe] at hfy
      refine ⟨hy, ?_⟩
      rw [hs]
      exact EReal.coe_le_coe_iff.mpr hfy
  rw [hset]
  exact hcont.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_Iic

lemma aux_unique_of_sd (f : E → EReal) (O : Set E) (hO : IsOpen O)
    (hfin : ∀ x ∈ O, IsFiniteEReal (f x)) (x v : E) (hx : x ∈ O)
    (h : ∀ ε > 0, ∃ δ > 0, ∀ y ∈ Metric.ball x δ, ∀ z ∈ Metric.ball x δ,
      |(f y).toReal - (f z).toReal - inner ℝ v (y - z)| ≤ ε * ‖y - z‖) :
    ∃! w, w ∈ subdifferential f x := by
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.mp hO x hx
  obtain ⟨a, ha⟩ := hfin x hx
  have hreg : IsRegularSubgradientAt f x v := by
    refine ⟨by rw [ha]; exact EReal.bot_lt_coe a, by rw [ha]; exact EReal.coe_lt_top a,
      fun y => (f y).toReal - (f x).toReal - inner ℝ v (y - x), ?_, O, hO.mem_nhds hx, ?_⟩
    · rw [Asymptotics.isLittleO_iff]
      intro c hc
      obtain ⟨δ, hδ, hδh⟩ := h c hc
      filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
      simp only [Real.norm_eq_abs, abs_norm]
      exact hδh y hy x (Metric.mem_ball_self hδ)
    · intro y hy
      obtain ⟨b, hb⟩ := hfin y hy
      simp only [ha, hb, EReal.toReal_coe]
      rw [← EReal.coe_add, EReal.coe_le_coe_iff]
      linarith
  refine ⟨v, aux_mem_subdiff f x v hreg, fun w hw => ?_⟩
  obtain ⟨_, _, xs, vs, hxs, _, hvs, hregs⟩ := hw
  have key : ∀ ε > 0, ‖w - v‖ ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδh⟩ := h ε hε
    have hδ' : 0 < min δ δ₀ := lt_min hδ hδ₀
    have hev : ∀ᶠ n in Filter.atTop, ‖vs n - v‖ ≤ ε := by
      filter_upwards [hxs (Metric.ball_mem_nhds x hδ')] with n hn
      have hn' : xs n ∈ Metric.ball x (min δ δ₀) := hn
      apply aux_regSub_bound f (xs n) (vs n) v ε hε.le (Metric.ball x (min δ δ₀))
        (Metric.isOpen_ball.mem_nhds hn')
      · intro y hy
        exact hfin y (hball (Metric.ball_subset_ball (min_le_right _ _) hy))
      · exact hregs n
      · intro y hy
        have h1 := hδh y (Metric.ball_subset_ball (min_le_left _ _) hy) (xs n)
          (Metric.ball_subset_ball (min_le_left _ _) hn')
        have h2 := (abs_le.mp h1).2
        linarith
    exact le_of_tendsto ((hvs.sub_const v).norm) hev
  by_contra hne
  have hpos : 0 < ‖w - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have := key (‖w - v‖ / 2) (by positivity)
  linarith


-- ===== group D1 =====
lemma aux_subderiv_of_sd (f : E → EReal) (O : Set E) (hO : IsOpen O)
    (hfin : ∀ x ∈ O, IsFiniteEReal (f x)) (x v : E) (hx : x ∈ O)
    (h : ∀ ε > 0, ∃ δ > 0, ∀ y ∈ Metric.ball x δ, ∀ z ∈ Metric.ball x δ,
      |(f y).toReal - (f z).toReal - inner ℝ v (y - z)| ≤ ε * ‖y - z‖) (w : E) :
    subderivative f x w = ((inner ℝ v w : ℝ) : EReal) := by
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.1 hO x hx
  have hfF : ∀ y ∈ O, f y = (((f y).toReal : ℝ) : EReal) := by
    intro y hy
    obtain ⟨r, hr⟩ := hfin y hy
    rw [hr, EReal.toReal_coe]
  have hw1 : (0:ℝ) < ‖w‖ + 1 := by positivity
  have hgeo : ∀ t : ℝ, ∀ d : E, ∀ δ : ℝ, 0 < t → t < δ / (‖w‖ + 1) → dist d w < 1 →
      x + t • d ∈ Metric.ball x δ := by
    intro t d δ ht htδ hd
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht]
    have hdn : ‖d‖ < ‖w‖ + 1 := by
      have := norm_sub_norm_le d w
      rw [dist_eq_norm] at hd
      linarith
    rw [lt_div_iff₀ hw1] at htδ
    calc t * ‖d‖ ≤ t * (‖w‖ + 1) := mul_le_mul_of_nonneg_left hdn.le ht.le
      _ < δ := htδ
  -- Step 1: eventual equality with a real-valued quotient
  have hev : (fun q : ℝ × E =>
      ((((f (x + q.1 • q.2)).toReal - (f x).toReal) / q.1 : ℝ) : EReal))
      =ᶠ[𝓝[>] (0:ℝ) ×ˢ 𝓝 w] (fun q : ℝ × E => differenceQuotient f x q.2 q.1) := by
    have h1 : ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Set.Ioo 0 (δ₀ / (‖w‖ + 1)) :=
      Ioo_mem_nhdsGT (by positivity)
    have h2 : ∀ᶠ d in 𝓝 w, d ∈ Metric.ball w 1 := Metric.ball_mem_nhds w one_pos
    filter_upwards [h1.prod_mk h2] with q hq
    obtain ⟨⟨ht0, htδ⟩, hd⟩ := hq
    have hyO : x + q.1 • q.2 ∈ O := hball (hgeo q.1 q.2 δ₀ ht0 htδ hd)
    simp only [differenceQuotient]
    rw [EReal.coe_div, EReal.coe_sub, ← hfF _ hyO, ← hfF _ hx]
  -- Step 2: real-valued limit
  have hreal : Filter.Tendsto
      (fun q : ℝ × E => ((f (x + q.1 • q.2)).toReal - (f x).toReal) / q.1)
      (𝓝[>] (0:ℝ) ×ˢ 𝓝 w) (𝓝 (inner ℝ v w)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε' : 0 < ε / (2 * (‖w‖ + 1)) := by positivity
    obtain ⟨δ, hδ, hδh⟩ := h _ hε'
    have hv1 : (0:ℝ) < ‖v‖ + 1 := by positivity
    have h1 : ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Set.Ioo 0 (δ / (‖w‖ + 1)) :=
      Ioo_mem_nhdsGT (by positivity)
    have h2 : ∀ᶠ d in 𝓝 w, d ∈ Metric.ball w (min 1 (ε / (2 * (‖v‖ + 1)))) :=
      Metric.ball_mem_nhds w (by positivity)
    filter_upwards [h1.prod_mk h2] with q hq
    obtain ⟨t, d⟩ := q
    obtain ⟨⟨ht0, htδ⟩, hd⟩ := hq
    simp only at ht0 htδ hd ⊢
    rw [Metric.mem_ball] at hd
    have ht0' : t ≠ 0 := ht0.ne'
    have hd1 : dist d w < 1 := lt_of_lt_of_le hd (min_le_left _ _)
    have hd2 : dist d w < ε / (2 * (‖v‖ + 1)) := lt_of_lt_of_le hd (min_le_right _ _)
    have hy : x + t • d ∈ Metric.ball x δ := hgeo t d δ ht0 htδ hd1
    have hxx : x ∈ Metric.ball x δ := Metric.mem_ball_self hδ
    have hest := hδh _ hy x hxx
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0,
      real_inner_smul_right] at hest
    have hdn : ‖d‖ < ‖w‖ + 1 := by
      have := norm_sub_norm_le d w
      rw [dist_eq_norm] at hd1
      linarith
    have e1 : |((f (x + t • d)).toReal - (f x).toReal) / t - inner ℝ v d| ≤
        ε / (2 * (‖w‖ + 1)) * ‖d‖ := by
      have hrw : ((f (x + t • d)).toReal - (f x).toReal) / t - inner ℝ v d =
          ((f (x + t • d)).toReal - (f x).toReal - t * inner ℝ v d) / t := by
        field_simp
      rw [hrw, abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
      exact hest.trans (le_of_eq (by ring))
    have e1' : ε / (2 * (‖w‖ + 1)) * ‖d‖ < ε / 2 := by
      calc ε / (2 * (‖w‖ + 1)) * ‖d‖ < ε / (2 * (‖w‖ + 1)) * (‖w‖ + 1) :=
            mul_lt_mul_of_pos_left hdn hε'
        _ = ε / 2 := by field_simp
    have e2 : |inner ℝ v d - inner ℝ v w| < ε / 2 := by
      rw [← inner_sub_right]
      calc |inner ℝ v (d - w)| ≤ ‖v‖ * ‖d - w‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖v‖ + 1) * ‖d - w‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
        _ < (‖v‖ + 1) * (ε / (2 * (‖v‖ + 1))) :=
            mul_lt_mul_of_pos_left (by rwa [dist_eq_norm] at hd2) hv1
        _ = ε / 2 := by field_simp
    rw [Real.dist_eq]
    calc |((f (x + t • d)).toReal - (f x).toReal) / t - inner ℝ v w|
        = |(((f (x + t • d)).toReal - (f x).toReal) / t - inner ℝ v d) +
            (inner ℝ v d - inner ℝ v w)| := by rw [sub_add_sub_cancel]
      _ ≤ |((f (x + t • d)).toReal - (f x).toReal) / t - inner ℝ v d| +
            |inner ℝ v d - inner ℝ v w| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := by linarith
      _ = ε := by ring
  have hT : Filter.Tendsto (fun q : ℝ × E => differenceQuotient f x q.2 q.1)
      (𝓝[>] (0:ℝ) ×ˢ 𝓝 w) (𝓝 ((inner ℝ v w : ℝ) : EReal)) :=
    (EReal.tendsto_coe.2 hreal).congr' hev
  exact hT.liminf_eq


-- ===== group D2 =====
lemma aux_D2_tendsto_of_bounds {α : Type*} (u : α → EReal) (l : Filter α) (L : ℝ)
    (hu : ∀ ε > 0, ∀ᶠ a in l, ((L - ε : ℝ) : EReal) ≤ u a ∧ u a ≤ ((L + ε : ℝ) : EReal)) :
    Filter.Tendsto u l (𝓝 (L : EReal)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨b, hab, hbL⟩ := EReal.lt_iff_exists_real_btwn.1 ha
    have hbL' : b < L := EReal.coe_lt_coe_iff.1 hbL
    filter_upwards [hu (L - b) (by linarith)] with y hy
    calc a < (b : EReal) := hab
      _ = ((L - (L - b) : ℝ) : EReal) := by congr 1; ring
      _ ≤ u y := hy.1
  · intro a ha
    obtain ⟨b, hLb, hba⟩ := EReal.lt_iff_exists_real_btwn.1 ha
    have hLb' : L < b := EReal.coe_lt_coe_iff.1 hLb
    filter_upwards [hu (b - L) (by linarith)] with y hy
    calc u y ≤ ((L + (b - L) : ℝ) : EReal) := hy.2
      _ = (b : EReal) := by congr 1; ring
      _ < a := hba

lemma aux_D2_inner (f : E → EReal) (O : Set E) (hO : IsOpen O)
    (hfin : ∀ x ∈ O, IsFiniteEReal (f x)) (x v : E) (hx : x ∈ O)
    (h : ∀ ε > 0, ∃ δ > 0, ∀ y ∈ Metric.ball x δ, ∀ z ∈ Metric.ball x δ,
      |(f y).toReal - (f z).toReal - inner ℝ v (y - z)| ≤ ε * ‖y - z‖) (w : E)
    (δ : ℝ) (hδ : 0 < δ) :
    Filter.Tendsto (fun p : E × ℝ => sInf ((delta f p.1 p.2) '' Metric.closedBall w δ))
      ((fApproach f x) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 ((inner ℝ v w - δ * ‖v‖ : ℝ) : EReal)) := by
  apply aux_D2_tendsto_of_bounds
  intro ε hε
  set M : ℝ := ‖w‖ + δ + 1 with hM
  have hMpos : 0 < M := by positivity
  obtain ⟨δ₁, hδ₁, hδ₁h⟩ := h (ε / M) (div_pos hε hMpos)
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hO x hx
  set ρ : ℝ := min δ₁ r with hρ
  have hρpos : 0 < ρ := lt_min hδ₁ hr
  have hball1 : Metric.ball x ρ ⊆ Metric.ball x δ₁ := Metric.ball_subset_ball (min_le_left _ _)
  have hball2 : Metric.ball x ρ ⊆ O := (Metric.ball_subset_ball (min_le_right _ _)).trans hrO
  have h1 : Metric.ball x (ρ / 2) ∈ fApproach f x :=
    Filter.mem_inf_of_left (Metric.ball_mem_nhds x (by positivity))
  have h2 : Set.Ioo (0 : ℝ) (ρ / (2 * M)) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by positivity)
  filter_upwards [Filter.prod_mem_prod h1 h2] with p hp
  rcases p with ⟨y, τ⟩
  simp only [Set.mem_prod] at hp
  obtain ⟨hp1, hp2⟩ := hp
  dsimp only at hp1 hp2 ⊢
  have hτ : 0 < τ := hp2.1
  have hτM : τ * M < ρ / 2 := by
    have := hp2.2
    rw [lt_div_iff₀ (by positivity)] at this
    linarith
  -- key estimate
  have key : ∀ w' ∈ Metric.closedBall w δ,
      delta f y τ w' = ((((f (y + τ • w')).toReal - (f y).toReal) / τ : ℝ) : EReal) ∧
      |((f (y + τ • w')).toReal - (f y).toReal) / τ - inner ℝ v w'| ≤ ε := by
    intro w' hw'
    have hw'n : ‖w'‖ ≤ ‖w‖ + δ := by
      have := Metric.mem_closedBall.1 hw'
      rw [dist_eq_norm] at this
      calc ‖w'‖ = ‖(w' - w) + w‖ := by rw [sub_add_cancel]
        _ ≤ ‖w' - w‖ + ‖w‖ := norm_add_le _ _
        _ ≤ δ + ‖w‖ := by linarith
        _ = ‖w‖ + δ := by ring
    have hy : y ∈ Metric.ball x ρ := Metric.ball_subset_ball (by linarith) hp1
    have hyw : y + τ • w' ∈ Metric.ball x ρ := by
      rw [Metric.mem_ball] at hp1 ⊢
      have hle : τ * ‖w'‖ ≤ τ * M := mul_le_mul_of_nonneg_left (by linarith) hτ.le
      calc dist (y + τ • w') x ≤ dist (y + τ • w') y + dist y x := dist_triangle _ _ _
        _ = ‖τ • w'‖ + dist y x := by rw [dist_eq_norm, add_sub_cancel_left]
        _ = τ * ‖w'‖ + dist y x := by rw [norm_smul, Real.norm_of_nonneg hτ.le]
        _ < ρ / 2 + ρ / 2 := by linarith
        _ = ρ := by ring
    obtain ⟨a, ha⟩ := hfin _ (hball2 hyw)
    obtain ⟨b, hb⟩ := hfin _ (hball2 hy)
    constructor
    · simp only [delta, differenceQuotient, ha, hb, EReal.toReal_coe]
      rfl
    · have := hδ₁h _ (hball1 hyw) _ (hball1 hy)
      rw [add_sub_cancel_left, inner_smul_right, norm_smul, Real.norm_of_nonneg hτ.le] at this
      have e1 : ((f (y + τ • w')).toReal - (f y).toReal) / τ - inner ℝ v w' =
          ((f (y + τ • w')).toReal - (f y).toReal - τ * inner ℝ v w') / τ := by
        field_simp
      rw [e1, abs_div, abs_of_pos hτ, div_le_iff₀ hτ]
      have hεM : ε / M * ‖w'‖ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hMpos]
        nlinarith
      calc _ ≤ ε / M * (τ * ‖w'‖) := this
        _ = (ε / M * ‖w'‖) * τ := by ring
        _ ≤ ε * τ := mul_le_mul_of_nonneg_right hεM hτ.le
  constructor
  · -- lower bound
    apply le_sInf
    rintro _ ⟨w', hw', rfl⟩
    obtain ⟨e, he⟩ := key w' hw'
    rw [e]
    apply EReal.coe_le_coe_iff.2
    have hin : inner ℝ v w - δ * ‖v‖ ≤ inner ℝ v w' := by
      have h3 : inner ℝ v w' = inner ℝ v w + inner ℝ v (w' - w) := by
        rw [inner_sub_right]; ring
      have h4 : |inner ℝ v (w' - w)| ≤ ‖v‖ * ‖w' - w‖ := abs_real_inner_le_norm _ _
      have h5 : ‖w' - w‖ ≤ δ := by
        have := Metric.mem_closedBall.1 hw'
        rwa [dist_eq_norm] at this
      have h6 : ‖v‖ * ‖w' - w‖ ≤ ‖v‖ * δ := mul_le_mul_of_nonneg_left h5 (norm_nonneg _)
      have := neg_abs_le (inner ℝ v (w' - w))
      linarith
    have := (abs_le.1 he).1
    linarith
  · -- upper bound
    set w₀ := w - (δ / ‖v‖) • v with hw₀
    have hw₀mem : w₀ ∈ Metric.closedBall w δ := by
      rw [Metric.mem_closedBall, dist_eq_norm, hw₀, sub_sub_cancel_left, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_div, abs_of_pos hδ, abs_norm]
      rcases eq_or_ne ‖v‖ 0 with h0 | h0
      · rw [h0]; simp; linarith
      · rw [div_mul_cancel₀ _ h0]
    have hw₀in : inner ℝ v w₀ = inner ℝ v w - δ * ‖v‖ := by
      rw [hw₀, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
      rcases eq_or_ne ‖v‖ 0 with h0 | h0
      · rw [h0]; simp
      · field_simp
    obtain ⟨e, he⟩ := key w₀ hw₀mem
    apply sInf_le_of_le (Set.mem_image_of_mem _ hw₀mem)
    rw [e]
    apply EReal.coe_le_coe_iff.2
    have := (abs_le.1 he).2
    linarith

lemma aux_regSubderiv_of_sd (f : E → EReal) (O : Set E) (hO : IsOpen O)
    (hfin : ∀ x ∈ O, IsFiniteEReal (f x)) (x v : E) (hx : x ∈ O)
    (h : ∀ ε > 0, ∃ δ > 0, ∀ y ∈ Metric.ball x δ, ∀ z ∈ Metric.ball x δ,
      |(f y).toReal - (f z).toReal - inner ℝ v (y - z)| ≤ ε * ‖y - z‖) (w : E) :
    regularSubderivative f x w = ((inner ℝ v w : ℝ) : EReal) := by
  have hne : (fApproach f x).NeBot := by
    have : pure x ≤ fApproach f x := by
      unfold fApproach
      refine le_inf (pure_le_nhds x) ?_
      rw [← Filter.map_le_iff_le_comap, Filter.map_pure]
      exact pure_le_nhds _
    exact Filter.neBot_of_le this
  have hinner : ∀ δ : ℝ, 0 < δ →
      Filter.limsup (fun p : E × ℝ => sInf ((delta f p.1 p.2) '' Metric.closedBall w δ))
        ((fApproach f x) ×ˢ (𝓝[>] (0 : ℝ))) = ((inner ℝ v w - δ * ‖v‖ : ℝ) : EReal) := by
    intro δ hδ
    exact (aux_D2_inner f O hO hfin x v hx h w δ hδ).limsup_eq
  unfold regularSubderivative
  apply Filter.Tendsto.limsup_eq
  have hlim : Filter.Tendsto (fun δ : ℝ => ((inner ℝ v w - δ * ‖v‖ : ℝ) : EReal)) (𝓝[>] (0:ℝ))
      (𝓝 ((inner ℝ v w : ℝ) : EReal)) := by
    have hc : Continuous (fun δ : ℝ => ((inner ℝ v w - δ * ‖v‖ : ℝ) : EReal)) :=
      continuous_coe_real_ereal.comp (continuous_const.sub (continuous_id.mul continuous_const))
    have := hc.tendsto 0
    simp only [zero_mul, sub_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (hinner δ hδ).symm


end aux_lemmas

theorem RW_chap_9_19
  (f : E → EReal)
  (O : Set E)
  (hO_open : IsOpen O)
  (hf_finite_on : ∀ x ∈ O, IsFiniteEReal (f x)) :
  List.TFAE [
  ∀ x ∈ O, IsStrictlyDifferentiable f x,
  ∃ (g : E → ℝ),
    (∀ x ∈ O, f x = (g x : EReal)) ∧
    ContDiffOn ℝ 1 g O,
  (∀ x ∈ O, IsLocallyLipschitzNearEReal f x) ∧
    (∀ x ∈ O, IsRegularAt f x) ∧
    (∀ x ∈ O, ∃! (v : E), v ∈ subdifferential f x),
  (∀ x ∈ O, LocalLscAt f x) ∧
    (∀ x ∈ O,
      IsLocallyBoundedAt (fun y => subdifferential f y) x) ∧
    (∀ x ∈ O,
      (subdifferential f x).Nonempty →
        ∃! (v : E), v ∈ subdifferential f x) ] := by
  -- (3) from strict differentiability (real form) at every point
  have hS3 : (∀ x ∈ O, ∃ v : E, ∀ ε > 0, ∃ δ > 0, ∀ y ∈ Metric.ball x δ,
      ∀ z ∈ Metric.ball x δ,
        |(f y).toReal - (f z).toReal - inner ℝ v (y - z)| ≤ ε * ‖y - z‖) →
      (∀ x ∈ O, IsLocallyLipschitzNearEReal f x) ∧
        (∀ x ∈ O, IsRegularAt f x) ∧
        (∀ x ∈ O, ∃! (v : E), v ∈ subdifferential f x) := by
    intro hsd
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · obtain ⟨v, hv⟩ := hsd x hx
      exact aux_locLip_of_sd f O hO_open hf_finite_on x v hx hv
    · obtain ⟨v, hv⟩ := hsd x hx
      obtain ⟨r, hr⟩ := hf_finite_on x hx
      refine ⟨⟨by rw [hr]; exact EReal.bot_lt_coe r, by rw [hr]; exact EReal.coe_lt_top r⟩,
        aux_localLsc_of_sd f O hO_open hf_finite_on x v hx hv, fun w => ?_⟩
      rw [aux_subderiv_of_sd f O hO_open hf_finite_on x v hx hv w,
        aux_regSubderiv_of_sd f O hO_open hf_finite_on x v hx hv w]
    · obtain ⟨v, hv⟩ := hsd x hx
      exact aux_unique_of_sd f O hO_open hf_finite_on x v hx hv
  tfae_have 1 → 2 := by
    intro h1
    refine ⟨fun y => (f y).toReal, fun x hx => ?_, ?_⟩
    · obtain ⟨r, hr⟩ := hf_finite_on x hx
      simp [hr]
    · apply aux_contDiffOn_of_sd _ O hO_open
      intro x hx
      obtain ⟨v, hv⟩ := h1 x hx
      exact ⟨v, aux_sd_of_strict f O hO_open hf_finite_on x v hx hv⟩
  tfae_have 2 → 3 := by
    rintro ⟨g, hfg, hg⟩
    apply hS3
    intro x hx
    obtain ⟨v, hv⟩ := aux_sd_of_contDiffOn g O hO_open hg x hx
    refine ⟨v, aux_sd_congr g (fun y => (f y).toReal) O hO_open ?_ x v hx hv⟩
    intro y hy
    simp [hfg y hy]
  tfae_have 3 → 4 := by
    rintro ⟨hlip, hreg, huniq⟩
    exact ⟨fun x hx => (hreg x hx).2.1, fun x hx => aux_bdd_of_locLip f x (hlip x hx),
      fun x hx _ => huniq x hx⟩
  tfae_have 4 → 1 := by
    rintro ⟨hlsc, hbdd, huniq⟩ x hx
    obtain ⟨v, hv⟩ := aux_S4_to_SD f O hO_open hf_finite_on hlsc hbdd huniq x hx
    exact ⟨v, aux_strict_of_sd f O hO_open hf_finite_on x v hx hv⟩
  tfae_finish

end RW_chap_9_19
