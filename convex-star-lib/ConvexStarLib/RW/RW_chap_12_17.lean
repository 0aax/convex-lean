import ConvexStarLib.Defs

/-!
# `RW_chap_12_17`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_12_17` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_12_17`, so the main result is `RW_chap_12_17.RW_chap_12_17`.
-/

namespace RW_chap_12_17

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace RW1217

open Filter

/-- (L1) regular subgradients are limiting subgradients. -/
lemma subdiff_of_regular {f : E → EReal} {x v : E} (h : IsRegularSubgradientAt f x v) :
    v ∈ subdifferential f x :=
  ⟨h.1, h.2.1, fun _ => x, fun _ => v, tendsto_const_nhds, tendsto_const_nhds,
    tendsto_const_nhds, fun _ => h⟩

lemma ereal_aux {a b : EReal} {c d : ℝ} (ha : ⊥ < a) (h : a + (c : EReal) ≤ b + (d : EReal)) :
    a + ((c - d : ℝ) : EReal) ≤ b := by
  induction a using EReal.rec with
  | bot => exact absurd ha (lt_irrefl _)
  | top =>
    induction b using EReal.rec with
    | bot => simp at h
    | top => exact le_top
    | coe b =>
      exfalso
      have : (⊤ : EReal) + (c : EReal) = ⊤ := EReal.top_add_coe c
      rw [this] at h
      have h2 : ((b : EReal) + (d : EReal)) = ((b + d : ℝ) : EReal) := by norm_cast
      rw [h2] at h
      exact absurd h (not_le.2 (EReal.coe_lt_top _))
  | coe a =>
    induction b using EReal.rec with
    | bot =>
      exfalso
      have h2 : ((a : EReal) + (c : EReal)) = ((a + c : ℝ) : EReal) := by norm_cast
      rw [h2, EReal.bot_add] at h
      exact absurd h (not_le.2 (EReal.bot_lt_coe _))
    | top => exact le_top
    | coe b =>
      have h2 : ((a : EReal) + (c : EReal)) = ((a + c : ℝ) : EReal) := by norm_cast
      have h3 : ((b : EReal) + (d : EReal)) = ((b + d : ℝ) : EReal) := by norm_cast
      rw [h2, h3, EReal.coe_le_coe_iff] at h
      have h4 : ((a : EReal) + ((c - d : ℝ) : EReal)) = ((a + (c - d) : ℝ) : EReal) := by norm_cast
      rw [h4, EReal.coe_le_coe_iff]
      linarith

lemma regular_of_localMin {f : E → EReal} {H : E → ℝ} {x₀ v : E}
    (hbot : ⊥ < f x₀) (htop : f x₀ < ⊤)
    (hH : (fun x => H x - H x₀ + inner ℝ v (x - x₀)) =o[𝓝 x₀] (fun x => ‖x - x₀‖))
    (hmin : ∀ᶠ x in 𝓝 x₀, f x₀ + ((H x₀ : ℝ) : EReal) ≤ f x + ((H x : ℝ) : EReal)) :
    IsRegularSubgradientAt f x₀ v := by
  refine ⟨hbot, htop, fun x => -(H x - H x₀ + inner ℝ v (x - x₀)), hH.neg_left, _, hmin, ?_⟩
  intro x hx
  have : inner ℝ v (x - x₀) + -(H x - H x₀ + inner ℝ v (x - x₀)) = H x₀ - H x := by ring
  rw [this]
  exact ereal_aux hbot hx

lemma isLittleO_of_hasFDerivAt {H : E → ℝ} {L : E →L[ℝ] ℝ} {p v : E} (hH : HasFDerivAt H L p)
    (hL : ∀ h, L h = - inner ℝ v h) :
    (fun x => H x - H p + inner ℝ v (x - p)) =o[𝓝 p] (fun x => ‖x - p‖) := by
  have h1 := hasFDerivAtFilter_iff_isLittleO.mp hH
  refine h1.norm_right.congr_left ?_
  intro x
  rw [hL]
  ring

lemma lsc_add_real {f : E → EReal} {H : E → ℝ} (hf : LowerSemicontinuous f) (hH : Continuous H) :
    LowerSemicontinuous (fun x => f x + ((H x : ℝ) : EReal)) := by
  refine hf.add' (continuous_coe_real_ereal.comp hH).lowerSemicontinuous ?_
  intro x
  exact EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))

lemma exists_min_interior {Φ : E → EReal} (hΦ : LowerSemicontinuous Φ) (c y : E) (R : ℝ)
    (hy : ‖y - c‖ ≤ R) (hbd : ∀ x, ‖x - c‖ = R → Φ y < Φ x) :
    ∃ p, ‖p - c‖ < R ∧ Φ p ≤ Φ y ∧ ∀ᶠ x in 𝓝 p, Φ p ≤ Φ x := by
  have hyb : y ∈ Metric.closedBall c R := by simpa [dist_eq_norm] using hy
  obtain ⟨p, hp, hmin⟩ := (hΦ.lowerSemicontinuousOn (Metric.closedBall c R)).exists_isMinOn
    ⟨y, hyb⟩ (isCompact_closedBall c R)
  have hpR : ‖p - c‖ ≤ R := by simpa [dist_eq_norm] using hp
  have hpy : Φ p ≤ Φ y := isMinOn_iff.mp hmin y hyb
  have hlt : ‖p - c‖ < R := by
    rcases hpR.lt_or_eq with h | h
    · exact h
    · exact absurd (hbd p h) (not_lt.2 hpy)
  refine ⟨p, hlt, hpy, ?_⟩
  have : Metric.ball c R ∈ 𝓝 p :=
    Metric.isOpen_ball.mem_nhds (by simpa [dist_eq_norm] using hlt)
  filter_upwards [this] with x hx
  exact isMinOn_iff.mp hmin x (Metric.ball_subset_closedBall hx)

/-- (L4) monotonicity of regular subgradients relative to `(xb, wb)` implies the global
subgradient inequality at `xb`. -/
lemma global_of_monotone_regular {f : E → EReal} (hlsc : LowerSemicontinuous f)
    (hbot : ∀ x, ⊥ < f x) {xb wb : E} (htop : f xb < ⊤)
    (hmon : ∀ x w, IsRegularSubgradientAt f x w → 0 ≤ inner ℝ (w - wb) (x - xb)) (y : E) :
    f xb + ((inner ℝ wb (y - xb) : ℝ) : EReal) ≤ f y := by
  by_contra hcon
  push_neg at hcon
  have hxb_ne_top : f xb ≠ ⊤ := htop.ne
  have hxb_ne_bot : f xb ≠ ⊥ := (hbot xb).ne'
  obtain ⟨F, hF⟩ : ∃ F : ℝ, (F : EReal) = f xb := ⟨_, EReal.coe_toReal hxb_ne_top hxb_ne_bot⟩
  have hy_lt_top : f y < ⊤ := by
    refine lt_trans hcon ?_
    rw [← hF, ← EReal.coe_add]
    exact EReal.coe_lt_top _
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, (Y : EReal) = f y :=
    ⟨_, EReal.coe_toReal hy_lt_top.ne (hbot y).ne'⟩
  have hlt : Y < F + inner ℝ wb (y - xb) := by
    rw [← hF, ← hY, ← EReal.coe_add] at hcon
    exact EReal.coe_lt_coe_iff.mp hcon
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = F + inner ℝ wb (y - xb) - Y := ⟨_, rfl⟩
  have hα : 0 < α := by rw [hαdef]; linarith
  have hyx : y ≠ xb := by
    intro h
    rw [h] at hY hlt
    have hFY : F = Y := by exact_mod_cast hF.trans hY.symm
    simp only [sub_self, inner_zero_right, add_zero] at hlt
    linarith
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = ‖y - xb‖ := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρdef]; exact norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
  -- the function g and its minimum on the closed ball
  have hglsc : LowerSemicontinuous (fun x => f x + (((-inner ℝ wb (x - xb)) : ℝ) : EReal)) :=
    lsc_add_real hlsc (by fun_prop)
  obtain ⟨q, hqmem, hqmin⟩ := (hglsc.lowerSemicontinuousOn (Metric.closedBall xb (2 * ρ))).exists_isMinOn
      ⟨xb, Metric.mem_closedBall_self (by linarith)⟩ (isCompact_closedBall xb (2 * ρ))
  have hgq_ne_bot : f q + (((-inner ℝ wb (q - xb)) : ℝ) : EReal) ≠ ⊥ := by
    rw [Ne, EReal.add_eq_bot_iff, not_or]
    exact ⟨(hbot q).ne', EReal.coe_ne_bot _⟩
  obtain ⟨m₀, hm₀def⟩ : ∃ m₀ : ℝ, m₀ = (f q + (((-inner ℝ wb (q - xb)) : ℝ) : EReal)).toReal :=
    ⟨_, rfl⟩
  have hm₀ : ∀ x ∈ Metric.closedBall xb (2 * ρ),
      (m₀ : EReal) ≤ f x + (((-inner ℝ wb (x - xb)) : ℝ) : EReal) := by
    intro x hx
    rw [hm₀def]
    exact (EReal.coe_toReal_le hgq_ne_bot).trans (isMinOn_iff.mp hqmin x hx)
  -- choice of the exponent
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (2 * (F - m₀) / α) (by norm_num : (1 : ℝ) < 4)
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = α / (2 * (ρ ^ 2) ^ (N + 1)) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; positivity
  set H : E → ℝ := fun x => -inner ℝ wb (x - xb) + c * (‖x - xb‖ ^ 2) ^ (N + 1) with hHdef
  have hHc : Continuous H := by
    show Continuous (fun x => -inner ℝ wb (x - xb) + c * (‖x - xb‖ ^ 2) ^ (N + 1))
    fun_prop
  have hcρ : c * (ρ ^ 2) ^ (N + 1) = α / 2 := by
    have hρ2 : (ρ ^ 2) ^ (N + 1) ≠ 0 := by positivity
    rw [hcdef]
    field_simp
  have hΦlsc : LowerSemicontinuous (fun x => f x + ((H x : ℝ) : EReal)) := lsc_add_real hlsc hHc
  have hΦy : f y + ((H y : ℝ) : EReal) = ((F - α / 2 : ℝ) : EReal) := by
    have h1 : H y = F - α / 2 - Y := by
      simp only [hHdef]
      rw [← hρdef, hcρ, hαdef]
      ring
    rw [h1, ← hY, ← EReal.coe_add]
    congr 1
    ring
  have hbd : ∀ x, ‖x - xb‖ = 2 * ρ → f y + ((H y : ℝ) : EReal) < f x + ((H x : ℝ) : EReal) := by
    intro x hx
    have hxmem : x ∈ Metric.closedBall xb (2 * ρ) := by
      rw [Metric.mem_closedBall, dist_eq_norm, hx]
    have h1 := hm₀ x hxmem
    have h4 : ((2 * ρ) ^ 2) ^ (N + 1) = 4 ^ (N + 1) * (ρ ^ 2) ^ (N + 1) := by
      rw [mul_pow, mul_pow]
      norm_num
    have hpen : c * (‖x - xb‖ ^ 2) ^ (N + 1) = α / 2 * 4 ^ (N + 1) := by
      rw [hx, h4, ← hcρ]
      ring
    have hΦx : f x + ((H x : ℝ) : EReal) =
        (f x + (((-inner ℝ wb (x - xb)) : ℝ) : EReal)) + ((α / 2 * 4 ^ (N + 1) : ℝ) : EReal) := by
      simp only [hHdef]
      rw [hpen, EReal.coe_add, add_assoc]
    rw [hΦx, hΦy]
    have hreal : F - α / 2 < m₀ + α / 2 * 4 ^ (N + 1) := by
      have h4' : (4:ℝ) ^ N ≤ 4 ^ (N + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ N)
      have h5 : 2 * (F - m₀) < 4 ^ N * α := (div_lt_iff₀ hα).mp hN
      nlinarith
    calc ((F - α / 2 : ℝ) : EReal) < ((m₀ + α / 2 * 4 ^ (N + 1) : ℝ) : EReal) :=
          EReal.coe_lt_coe_iff.mpr hreal
      _ = (m₀ : EReal) + ((α / 2 * 4 ^ (N + 1) : ℝ) : EReal) := EReal.coe_add _ _
      _ ≤ _ := add_le_add h1 le_rfl
  obtain ⟨p, hpR, hpy, hpmin⟩ := exists_min_interior hΦlsc xb y (2 * ρ)
    (by rw [← hρdef]; linarith) hbd
  have hpx : p ≠ xb := by
    intro h
    rw [h] at hpy
    have hHxb : H xb = 0 := by simp [hHdef]
    rw [hHxb, hΦy, ← hF, ← EReal.coe_add, EReal.coe_le_coe_iff] at hpy
    linarith
  have hptop : f p < ⊤ := by
    have h1 : f p + ((H p : ℝ) : EReal) < ⊤ := by
      refine lt_of_le_of_lt hpy ?_
      rw [hΦy]
      exact EReal.coe_lt_top _
    by_contra h2
    rw [not_lt, top_le_iff] at h2
    rw [h2, EReal.top_add_coe] at h1
    exact lt_irrefl _ h1
  -- derivative of H at p
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = 2 * c * (N + 1) * (‖p - xb‖ ^ 2) ^ N := ⟨_, rfl⟩
  have hderiv : ∃ L : E →L[ℝ] ℝ, HasFDerivAt H L p ∧
      ∀ h, L h = - inner ℝ (wb - s • (p - xb)) h := by
    have h1 : HasFDerivAt (fun x : E => x - xb) (ContinuousLinearMap.id ℝ E) p :=
      (hasFDerivAt_id p).sub_const xb
    have h2 : HasFDerivAt (fun x : E => -inner ℝ wb (x - xb))
        (-((innerSL ℝ wb).comp (ContinuousLinearMap.id ℝ E))) p :=
      (((innerSL ℝ wb).hasFDerivAt).comp p h1).neg
    have h3 := ((h1.norm_sq).pow (N + 1)).const_mul c
    refine ⟨_, h2.add h3, ?_⟩
    intro h
    simp [inner_sub_left, real_inner_smul_left, hsdef]
    ring
  obtain ⟨L, hL1, hL2⟩ := hderiv
  have hreg : IsRegularSubgradientAt f p (wb - s • (p - xb)) :=
    regular_of_localMin (hbot p) hptop (isLittleO_of_hasFDerivAt hL1 hL2) hpmin
  have hfin := hmon p _ hreg
  have hpn : 0 < ‖p - xb‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpx)
  have hs : 0 < s := by rw [hsdef]; positivity
  have hv : wb - s • (p - xb) - wb = -(s • (p - xb)) := by abel
  rw [hv, inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at hfin
  nlinarith [mul_pos hs (pow_pos hpn 2)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma C_sq_isLittleO (K : ℝ) (p : E) :
    (fun x : E => K * ‖x - p‖ ^ 2) =o[𝓝 p] (fun x => ‖x - p‖) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hpos : 0 < c / (|K| + 1) := by positivity
  filter_upwards [Metric.ball_mem_nhds p hpos] with x hx
  rw [Metric.mem_ball, dist_eq_norm] at hx
  simp only [norm_mul, Real.norm_eq_abs, norm_pow, abs_norm]
  have h1 : (|K| + 1) * ‖x - p‖ ≤ c := by
    rw [lt_div_iff₀ (by positivity)] at hx
    linarith
  have h0 : 0 ≤ ‖x - p‖ := norm_nonneg _
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1), sq_nonneg ‖x - p‖, abs_nonneg K]

omit [FiniteDimensional ℝ E] in
lemma C_quad_isLittleO (K : ℝ) (z p : E) :
    (fun x => K * ‖x - z‖ ^ 2 - K * ‖p - z‖ ^ 2 + inner ℝ ((2 * K) • (z - p)) (x - p))
      =o[𝓝 p] (fun x => ‖x - p‖) := by
  have h : ∀ x, K * ‖x - z‖ ^ 2 - K * ‖p - z‖ ^ 2 + inner ℝ ((2 * K) • (z - p)) (x - p)
      = K * ‖x - p‖ ^ 2 := by
    intro x
    have hx : x - z = (x - p) + (p - z) := by abel
    have hzp : z - p = -(p - z) := by abel
    rw [hx, norm_add_sq_real, hzp, inner_smul_left, inner_neg_left, real_inner_comm]
    simp only [conj_trivial]
    ring
  simp_rw [h]
  exact C_sq_isLittleO K p

/-- (L5) existence of a regular subgradient. -/
lemma exists_regular {f : E → EReal} (hlsc : LowerSemicontinuous f) (hbot : ∀ x, ⊥ < f x)
    {x₀ : E} (htop : f x₀ < ⊤) : ∃ x v, IsRegularSubgradientAt f x v := by
  set F : ℝ := (f x₀).toReal with hF
  have hfx₀ : f x₀ = ((F : ℝ) : EReal) := (EReal.coe_toReal htop.ne (hbot x₀).ne').symm
  have hlev : ((F - 1 : ℝ) : EReal) < f x₀ := by
    rw [hfx₀]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hlsc x₀ _ hlev)
  set R : ℝ := δ / 2 with hR
  set K : ℝ := 8 / δ ^ 2 with hK
  let H : E → ℝ := fun x => K * ‖x - x₀‖ ^ 2
  let Φ : E → EReal := fun x => f x + ((H x : ℝ) : EReal)
  have hHc : Continuous H := by fun_prop
  have hΦlsc : LowerSemicontinuous Φ := lsc_add_real hlsc hHc
  have hΦx₀ : Φ x₀ = ((F : ℝ) : EReal) := by
    simp only [Φ, H, sub_self, norm_zero]
    rw [hfx₀]
    norm_num
  have hbd : ∀ x, ‖x - x₀‖ = R → Φ x₀ < Φ x := by
    intro x hx
    have hlt : ((F - 1 : ℝ) : EReal) < f x := hball (by rw [dist_eq_norm, hx]; linarith)
    have hH : H x = 2 := by
      simp only [H, hx, hR, hK]
      field_simp
      ring
    show Φ x₀ < f x + ((H x : ℝ) : EReal)
    rw [hΦx₀, hH]
    calc ((F : ℝ) : EReal) < ((F - 1 : ℝ) : EReal) + ((2 : ℝ) : EReal) := by
          rw [← EReal.coe_add]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
      _ ≤ f x + ((2 : ℝ) : EReal) := add_le_add hlt.le le_rfl
  obtain ⟨p, -, hpΦ, hploc⟩ :=
    exists_min_interior hΦlsc x₀ x₀ R (by rw [sub_self, norm_zero]; positivity) hbd
  have hptop : f p < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    have h' : Φ p = ⊤ := by simp only [Φ, h]; exact EReal.top_add_coe _
    rw [h', hΦx₀] at hpΦ
    exact absurd hpΦ (not_le.mpr (EReal.coe_lt_top F))
  exact ⟨p, (2 * K) • (x₀ - p),
    regular_of_localMin (H := H) (hbot p) hptop (C_quad_isLittleO K x₀ p) hploc⟩

/-- (L6) proximal point. -/
lemma exists_prox {f : E → EReal} (hlsc : LowerSemicontinuous f) (hbot : ∀ x, ⊥ < f x)
    {x₀ : E} (htop : f x₀ < ⊤) (a : E) (b : ℝ)
    (hmin : ∀ x, ((inner ℝ a x + b : ℝ) : EReal) ≤ f x)
    (z : E) {k : ℝ} (hk : 0 < k) : ∃ p, IsRegularSubgradientAt f p (k • (z - p)) := by
  set F₀ : ℝ := (f x₀).toReal + (k / 2) * ‖x₀ - z‖ ^ 2 with hF₀
  set D : ℝ := F₀ - inner ℝ a z - b with hD
  set R : ℝ := max (‖x₀ - z‖ + 1) (max 1 (2 * (‖a‖ + |D| + 1) / k)) with hR
  have hR0 : ‖x₀ - z‖ + 1 ≤ R := le_max_left _ _
  have hR1 : 1 ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hR2 : 2 * (‖a‖ + |D| + 1) / k ≤ R := le_trans (le_max_right _ _) (le_max_right _ _)
  have hR2' : 2 * (‖a‖ + |D| + 1) ≤ R * k := (div_le_iff₀ hk).mp hR2
  have hR3 : |D| + 1 ≤ R * ((k / 2) * R - ‖a‖) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR1) (show 0 ≤ (k / 2) * R - ‖a‖ by
      nlinarith [abs_nonneg D])]
  let H : E → ℝ := fun x => (k / 2) * ‖x - z‖ ^ 2
  let Φ : E → EReal := fun x => f x + ((H x : ℝ) : EReal)
  have hHc : Continuous H := by fun_prop
  have hΦlsc : LowerSemicontinuous Φ := lsc_add_real hlsc hHc
  have hfx₀ : f x₀ = (((f x₀).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal htop.ne (hbot x₀).ne').symm
  have hΦx₀ : Φ x₀ = ((F₀ : ℝ) : EReal) := by
    show f x₀ + ((H x₀ : ℝ) : EReal) = _
    rw [hfx₀, ← EReal.coe_add]
  have hbd : ∀ x, ‖x - z‖ = R → Φ x₀ < Φ x := by
    intro x hx
    rw [hΦx₀]
    show ((F₀ : ℝ) : EReal) < f x + ((H x : ℝ) : EReal)
    by_cases hfx : f x = ⊤
    · rw [hfx, EReal.top_add_coe]
      exact EReal.coe_lt_top F₀
    · have hfx' : f x = (((f x).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal hfx (hbot x).ne').symm
      have hlow : inner ℝ a x + b ≤ (f x).toReal := by
        have := hmin x
        rw [hfx'] at this
        exact EReal.coe_le_coe_iff.mp this
      rw [hfx', ← EReal.coe_add, EReal.coe_lt_coe_iff]
      have hHx : H x = (k / 2) * R ^ 2 := by simp only [H, hx]
      rw [hHx]
      have h1 : inner ℝ a x = inner ℝ a z + inner ℝ a (x - z) := by
        rw [inner_sub_right]; ring
      have h2 : |inner ℝ a (x - z)| ≤ ‖a‖ * ‖x - z‖ := abs_real_inner_le_norm _ _
      rw [hx] at h2
      have h3 := neg_abs_le (inner ℝ a (x - z))
      have h4 := le_abs_self D
      nlinarith
  obtain ⟨p, -, hpΦ, hploc⟩ :=
    exists_min_interior hΦlsc z x₀ R (by linarith) hbd
  have hptop : f p < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    have h' : Φ p = ⊤ := by simp only [Φ, h]; exact EReal.top_add_coe _
    rw [h', hΦx₀] at hpΦ
    exact absurd hpΦ (not_le.mpr (EReal.coe_lt_top F₀))
  have hlo := C_quad_isLittleO (k / 2) z p
  rw [show 2 * (k / 2) = k by ring] at hlo
  exact ⟨p, regular_of_localMin (H := H) (hbot p) hptop hlo hploc⟩

/-- (L7a) convexity inequality from convex epigraph. -/
lemma convex_ineq {f : E → EReal} (hf : ConvexEReal f) {x y : E} (hx : f x < ⊤) (hy : f y < ⊤)
    (hxb : ⊥ < f x) (hyb : ⊥ < f y) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f ((1 - t) • x + t • y) ≤ (((1 - t) * (f x).toReal + t * (f y).toReal : ℝ) : EReal) := by
  have hpx : (x, (f x).toReal) ∈ epigraph f := by
    show f x ≤ (((f x).toReal : ℝ) : EReal)
    rw [EReal.coe_toReal hx.ne hxb.ne']
  have hpy : (y, (f y).toReal) ∈ epigraph f := by
    show f y ≤ (((f y).toReal : ℝ) : EReal)
    rw [EReal.coe_toReal hy.ne hyb.ne']
  have h := hf hpx hpy (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
  have h2 : f ((1 - t) • (x, (f x).toReal) + t • (y, (f y).toReal)).1 ≤
      ((((1 - t) • (x, (f x).toReal) + t • (y, (f y).toReal)).2 : ℝ) : EReal) := h
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h2
  exact h2

/-- (L7b) for convex `f`, regular subgradients are global subgradients. -/
lemma global_of_regular_convex {f : E → EReal} (hf : ConvexEReal f) (hbot : ∀ x, ⊥ < f x)
    {xb v : E} (h : IsRegularSubgradientAt f xb v) (y : E) :
    f xb + ((inner ℝ v (y - xb) : ℝ) : EReal) ≤ f y := by
  obtain ⟨hb, ht, r, hr, V, hV, hineq⟩ := h
  by_cases hyt : f y = ⊤
  · rw [hyt]; exact le_top
  have hyt' : f y < ⊤ := lt_top_iff_ne_top.mpr hyt
  obtain ⟨Fx, hFx⟩ : ∃ a : ℝ, f xb = (a : EReal) :=
    ⟨(f xb).toReal, (EReal.coe_toReal ht.ne hb.ne').symm⟩
  obtain ⟨Fy, hFy⟩ : ∃ a : ℝ, f y = (a : EReal) :=
    ⟨(f y).toReal, (EReal.coe_toReal hyt (hbot y).ne').symm⟩
  -- key estimate: for every `ε > 0`, `⟪v, y - xb⟫ ≤ Fy - Fx + ε * ‖y - xb‖`
  have key : ∀ ε > 0, inner ℝ v (y - xb) ≤ Fy - Fx + ε * ‖y - xb‖ := by
    intro ε hε
    have h1 := (Asymptotics.isLittleO_iff.mp hr) hε
    have h2 : ∀ᶠ x in 𝓝 xb, ‖r x‖ ≤ ε * ‖‖x - xb‖‖ ∧ x ∈ V := h1.and hV
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp h2
    obtain ⟨t, ht0, ht1, htd⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ t * ‖y - xb‖ < δ := by
      refine ⟨min 1 (δ / (2 * (‖y - xb‖ + 1))), lt_min one_pos (by positivity),
        min_le_left _ _, ?_⟩
      have hm : min 1 (δ / (2 * (‖y - xb‖ + 1))) ≤ δ / (2 * (‖y - xb‖ + 1)) := min_le_right _ _
      calc min 1 (δ / (2 * (‖y - xb‖ + 1))) * ‖y - xb‖
          ≤ δ / (2 * (‖y - xb‖ + 1)) * ‖y - xb‖ := by gcongr
        _ < δ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg (y - xb)]
    have hxt : ((1 - t) • xb + t • y) - xb = t • (y - xb) := by
      simp only [smul_sub, sub_smul, one_smul]; abel
    have hdist : dist ((1 - t) • xb + t • y) xb < δ := by
      rw [dist_eq_norm, hxt, norm_smul, Real.norm_of_nonneg ht0.le]; exact htd
    obtain ⟨hrx, hxV⟩ := hball hdist
    have hlow := hineq _ hxV
    have hup := convex_ineq hf ht hyt' hb (hbot y) ht0.le ht1
    rw [hFx, hFy, EReal.toReal_coe, EReal.toReal_coe] at hup
    have hcomb := hlow.trans hup
    rw [hFx, ← EReal.coe_add, EReal.coe_le_coe_iff, hxt, inner_smul_right] at hcomb
    rw [Real.norm_eq_abs, norm_norm, hxt, norm_smul, Real.norm_of_nonneg ht0.le] at hrx
    have hr' := neg_abs_le (r ((1 - t) • xb + t • y))
    have h3 : t * inner ℝ v (y - xb) ≤ t * (Fy - Fx + ε * ‖y - xb‖) := by
      nlinarith
    exact le_of_mul_le_mul_left h3 ht0
  have hle : inner ℝ v (y - xb) ≤ Fy - Fx := by
    apply _root_.le_of_forall_pos_le_add
    intro ε hε
    have h4 := key (ε / (‖y - xb‖ + 1)) (by positivity)
    have h5 : ε / (‖y - xb‖ + 1) * ‖y - xb‖ ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg (y - xb)]
    linarith
  rw [hFx, hFy, ← EReal.coe_add, EReal.coe_le_coe_iff]
  linarith

/-- (L7c) for convex `f`, limiting subgradients are global subgradients. -/
lemma global_of_subdiff_convex {f : E → EReal} (hf : ConvexEReal f) (hbot : ∀ x, ⊥ < f x)
    {xb v : E} (h : v ∈ subdifferential f xb) (y : E) :
    f xb + ((inner ℝ v (y - xb) : ℝ) : EReal) ≤ f y := by
  obtain ⟨hb, ht, xs, vs, hx, hfx, hv, hreg⟩ := h
  by_cases hyt : f y = ⊤
  · rw [hyt]; exact le_top
  obtain ⟨Fx, hFx⟩ : ∃ a : ℝ, f xb = (a : EReal) :=
    ⟨(f xb).toReal, (EReal.coe_toReal ht.ne hb.ne').symm⟩
  obtain ⟨Fy, hFy⟩ : ∃ a : ℝ, f y = (a : EReal) :=
    ⟨(f y).toReal, (EReal.coe_toReal hyt (hbot y).ne').symm⟩
  have hn : ∀ n, f (xs n) ≤ ((Fy - inner ℝ (vs n) (y - xs n) : ℝ) : EReal) := by
    intro n
    have h1 := global_of_regular_convex hf hbot (hreg n) y
    obtain ⟨c, hc⟩ : ∃ c : ℝ, f (xs n) = (c : EReal) :=
      ⟨(f (xs n)).toReal, (EReal.coe_toReal (hreg n).2.1.ne (hreg n).1.ne').symm⟩
    rw [hc, hFy, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
    rw [hc, EReal.coe_le_coe_iff]
    linarith
  have hlim : Tendsto (fun n => ((Fy - inner ℝ (vs n) (y - xs n) : ℝ) : EReal)) atTop
      (𝓝 ((Fy - inner ℝ v (y - xb) : ℝ) : EReal)) := by
    apply EReal.tendsto_coe.mpr
    exact tendsto_const_nhds.sub (hv.inner (tendsto_const_nhds.sub hx))
  have hle := le_of_tendsto_of_tendsto' hfx hlim hn
  rw [hFx, EReal.coe_le_coe_iff] at hle
  rw [hFx, hFy, ← EReal.coe_add, EReal.coe_le_coe_iff]
  linarith

lemma regular_of_global {f : E → EReal} {xb v : E} (hb : ⊥ < f xb) (ht : f xb < ⊤)
    (h : ∀ y, f xb + ((inner ℝ v (y - xb) : ℝ) : EReal) ≤ f y) :
    IsRegularSubgradientAt f xb v := by
  refine ⟨hb, ht, fun _ => 0, Asymptotics.isLittleO_zero _ _, Set.univ, Filter.univ_mem, ?_⟩
  intro x _
  simpa using h x

omit [FiniteDimensional ℝ E] in
/-- Finiteness of `f` at points with a limiting subgradient. -/
lemma E_fin {f : E → EReal} {x v : E} (h : v ∈ subdifferential f x) :
    ∃ F : ℝ, f x = (F : EReal) :=
  ⟨(f x).toReal, (EReal.coe_toReal h.2.1.ne h.1.ne').symm⟩

omit [FiniteDimensional ℝ E] in
/-- Real form of a subgradient inequality between finite values. -/
lemma E_glob {f : E → EReal} {x y v : E} {Fx Fy : ℝ} (hx : f x = Fx) (hy : f y = Fy)
    (h : f x + ((inner ℝ v (y - x) : ℝ) : EReal) ≤ f y) : Fx + inner ℝ v (y - x) ≤ Fy := by
  rw [hx, hy] at h
  exact_mod_cast h

/-- (L9) Part 1. -/
lemma part1 (f : E → EReal) (hf_proper : IsProper f) (hc : ConvexEReal f) :
    IsMonotone (subdifferential f) := by
  intro x₀ x₁ v₀ v₁ h₀ h₁
  obtain ⟨F₀, hF₀⟩ := E_fin h₀
  obtain ⟨F₁, hF₁⟩ := E_fin h₁
  have r₀ := E_glob hF₀ hF₁ (global_of_subdiff_convex hc hf_proper.1 h₀ x₁)
  have r₁ := E_glob hF₁ hF₀ (global_of_subdiff_convex hc hf_proper.1 h₁ x₀)
  have e1 : inner ℝ (v₁ - v₀) (x₁ - x₀) = inner ℝ v₁ (x₁ - x₀) - inner ℝ v₀ (x₁ - x₀) :=
    inner_sub_left _ _ _
  have e2 : inner ℝ v₁ (x₀ - x₁) = - inner ℝ v₁ (x₁ - x₀) := by
    rw [← inner_neg_right, neg_sub]
  linarith

/-- (L10) Part 2b. -/
lemma part2b (f : E → EReal) (hf_proper : IsProper f) (hlsc : LowerSemicontinuous f)
    (hc : ConvexEReal f) : IsMaximalMonotone (subdifferential f) := by
  refine ⟨part1 f hf_proper hc, ?_⟩
  intro xh vh hnot
  obtain ⟨x₀, hx₀⟩ := hf_proper.2
  obtain ⟨x₁, v₁, hreg⟩ := exists_regular hlsc hf_proper.1 hx₀
  obtain ⟨F₁, hF₁⟩ := E_fin (subdiff_of_regular hreg)
  have hmin : ∀ y, ((inner ℝ v₁ y + (F₁ - inner ℝ v₁ x₁) : ℝ) : EReal) ≤ f y := by
    intro y
    have h := global_of_regular_convex hc hf_proper.1 hreg y
    have e : inner ℝ v₁ y + (F₁ - inner ℝ v₁ x₁) = F₁ + inner ℝ v₁ (y - x₁) := by
      rw [inner_sub_right]; ring
    rw [e, EReal.coe_add, ← hF₁]
    exact h
  obtain ⟨p, hp⟩ := exists_prox hlsc hf_proper.1 hx₀ v₁ (F₁ - inner ℝ v₁ x₁) hmin (xh + vh)
    one_pos
  rw [one_smul] at hp
  have hsub := subdiff_of_regular hp
  refine ⟨p, xh + vh - p, hsub, ?_⟩
  by_cases hpx : p = xh
  · exfalso
    apply hnot
    subst hpx
    simpa using hsub
  · have e : vh - (xh + vh - p) = -(xh - p) := by abel
    rw [e, inner_neg_left, real_inner_self_eq_norm_sq]
    have h1 : 0 < ‖xh - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hpx))
    have h2 := pow_pos h1 2
    linarith

/-- (L11) Part 2c. -/
lemma part2c (f : E → EReal) (hf_proper : IsProper f) (hc : ConvexEReal f) :
    AlmostStrictConvexEReal f ↔ IsStrictMonotone (subdifferential f) := by
  constructor
  · intro hasc x₀ x₁ v₀ v₁ hne h₀ h₁
    by_contra hcon
    push_neg at hcon
    obtain ⟨F₀, hF₀⟩ := E_fin h₀
    obtain ⟨F₁, hF₁⟩ := E_fin h₁
    have g₀ := global_of_subdiff_convex hc hf_proper.1 h₀
    have r₀ := E_glob hF₀ hF₁ (g₀ x₁)
    have r₁ := E_glob hF₁ hF₀ (global_of_subdiff_convex hc hf_proper.1 h₁ x₀)
    have heq : F₁ - F₀ = inner ℝ v₀ (x₁ - x₀) := by
      have e1 : inner ℝ (v₁ - v₀) (x₁ - x₀) = inner ℝ v₁ (x₁ - x₀) - inner ℝ v₀ (x₁ - x₀) :=
        inner_sub_left _ _ _
      have e2 : inner ℝ v₁ (x₀ - x₁) = - inner ℝ v₁ (x₁ - x₀) := by
        rw [← inner_neg_right, neg_sub]
      linarith
    have hseg : segment ℝ x₀ x₁ ⊆ {x | (subdifferential f x).Nonempty} := by
      intro z hz
      obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
      obtain rfl : a = 1 - b := by linarith
      have hzle := convex_ineq hc h₀.2.1 h₁.2.1 h₀.1 h₁.1 hb (by linarith)
      rw [hF₀, hF₁, EReal.toReal_coe, EReal.toReal_coe] at hzle
      refine ⟨v₀, subdiff_of_regular (regular_of_global (hf_proper.1 _)
        (lt_of_le_of_lt hzle (EReal.coe_lt_top _)) ?_)⟩
      intro y
      calc f ((1 - b) • x₀ + b • x₁) + ((inner ℝ v₀ (y - ((1 - b) • x₀ + b • x₁)) : ℝ) : EReal)
          ≤ (((1 - b) * F₀ + b * F₁ : ℝ) : EReal)
            + ((inner ℝ v₀ (y - ((1 - b) • x₀ + b • x₁)) : ℝ) : EReal) :=
            add_le_add hzle le_rfl
        _ = (F₀ : EReal) + ((inner ℝ v₀ (y - x₀) : ℝ) : EReal) := by
            rw [← EReal.coe_add, ← EReal.coe_add]
            congr 1
            have hd : y - ((1 - b) • x₀ + b • x₁) = (y - x₀) - b • (x₁ - x₀) := by
              module
            rw [hd, inner_sub_right, inner_smul_right]
            linear_combination b * heq
        _ = f x₀ + ((inner ℝ v₀ (y - x₀) : ℝ) : EReal) := by rw [hF₀]
        _ ≤ f y := g₀ y
    have key := hasc (segment ℝ x₀ x₁) hseg (convex_segment x₀ x₁) x₀ x₁
      (left_mem_segment ℝ x₀ x₁) (right_mem_segment ℝ x₀ x₁) hne (1 / 2)
      ⟨by norm_num, by norm_num⟩
    have hge := g₀ ((1 / 2 : ℝ) • x₀ + (1 - 1 / 2 : ℝ) • x₁)
    have hd : (1 / 2 : ℝ) • x₀ + (1 - 1 / 2 : ℝ) • x₁ - x₀ = (1 / 2 : ℝ) • (x₁ - x₀) := by
      module
    rw [hd, inner_smul_right] at hge
    have hlt := lt_of_le_of_lt hge key
    rw [hF₀, hF₁] at hlt
    have hlt' : F₀ + 1 / 2 * inner ℝ v₀ (x₁ - x₀) < 1 / 2 * F₀ + (1 - 1 / 2) * F₁ := by
      exact_mod_cast hlt
    linarith
  · intro hsm C hC hconv x y hx hy hxy t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hz : t • x + (1 - t) • y ∈ C := hconv hx hy (le_of_lt ht0) (by linarith) (by ring)
    obtain ⟨w, hw⟩ := hC hz
    obtain ⟨vx, hvx⟩ := hC hx
    obtain ⟨vy, hvy⟩ := hC hy
    obtain ⟨Fx, hFx⟩ := E_fin hvx
    obtain ⟨Fy, hFy⟩ := E_fin hvy
    obtain ⟨Fz, hFz⟩ := E_fin hw
    have gz := global_of_subdiff_convex hc hf_proper.1 hw
    have gx := E_glob hFz hFx (gz x)
    have gy := E_glob hFz hFy (gz y)
    by_contra hcon
    rw [not_lt, hFx, hFy, hFz] at hcon
    have hcon' : t * Fx + (1 - t) * Fy ≤ Fz := by exact_mod_cast hcon
    have hxz : x - (t • x + (1 - t) • y) = (1 - t) • (x - y) := by module
    have hyz : y - (t • x + (1 - t) • y) = (-t) • (x - y) := by module
    rw [hxz, inner_smul_right] at gx
    rw [hyz, inner_smul_right] at gy
    have hA : Fx - Fz - (1 - t) * inner ℝ w (x - y) ≤ 0 := by
      by_contra hA
      push_neg at hA
      have h1 := mul_pos ht0 hA
      have h2 : 0 ≤ (1 - t) * (Fy - Fz + t * inner ℝ w (x - y)) :=
        mul_nonneg (by linarith) (by linarith)
      have h3 : t * (Fx - Fz - (1 - t) * inner ℝ w (x - y))
          + (1 - t) * (Fy - Fz + t * inner ℝ w (x - y)) = t * Fx + (1 - t) * Fy - Fz := by ring
      linarith
    have heqx : Fx = Fz + (1 - t) * inner ℝ w (x - y) := by linarith
    have hwx : w ∈ subdifferential f x := by
      apply subdiff_of_regular
      apply regular_of_global (hf_proper.1 x) (by rw [hFx]; exact EReal.coe_lt_top _)
      intro u
      have h := gz u
      rw [hFz] at h
      rw [hFx]
      convert h using 1
      rw [← EReal.coe_add, ← EReal.coe_add]
      congr 1
      have hu : u - x = (u - (t • x + (1 - t) • y)) - (x - (t • x + (1 - t) • y)) := by abel
      rw [hu, inner_sub_right, hxz, inner_smul_right, heqx]
      ring
    have hne : x ≠ t • x + (1 - t) • y := by
      intro h
      have h0 : x - (t • x + (1 - t) • y) = 0 := sub_eq_zero.mpr h
      rw [hxz] at h0
      rcases smul_eq_zero.mp h0 with h1 | h2
      · linarith
      · exact hxy (sub_eq_zero.mp h2)
    have := hsm x _ w w hne hwx hw
    simp at this

/-- (L12) Part 2a, hard direction. -/
lemma part2a (f : E → EReal) (hf_proper : IsProper f) (hlsc : LowerSemicontinuous f)
    (hm : IsMonotone (subdifferential f)) : ConvexEReal f := by
  have hbot := hf_proper.1
  -- Step 1: regular subgradients are global subgradients
  have hglob : ∀ x v, IsRegularSubgradientAt f x v → ∀ y,
      f x + ((inner ℝ v (y - x) : ℝ) : EReal) ≤ f y := by
    intro x v h y
    exact global_of_monotone_regular hlsc hbot h.2.1
      (fun x' w h' => hm x x' v w (subdiff_of_regular h) (subdiff_of_regular h')) y
  -- Step 2: affine minorant
  obtain ⟨x₀, hx0⟩ := hf_proper.2
  have hx0' : f x₀ < ⊤ := hx0
  obtain ⟨x₁, v₁, h₁⟩ := exists_regular hlsc hbot hx0'
  have hmin : ∀ y, ((inner ℝ v₁ y + ((f x₁).toReal - inner ℝ v₁ x₁) : ℝ) : EReal) ≤ f y := by
    intro y
    have h := hglob x₁ v₁ h₁ y
    rw [← EReal.coe_toReal h₁.2.1.ne h₁.1.ne', ← EReal.coe_add, inner_sub_right] at h
    convert h using 2
    ring
  set a := v₁ with ha
  set b := (f x₁).toReal - inner ℝ v₁ x₁ with hb
  -- Step 3: main inequality
  have hmain : ∀ x y t, f x < ⊤ → f y < ⊤ → 0 ≤ t → t ≤ 1 →
      f ((1 - t) • x + t • y) ≤ (((1 - t) * (f x).toReal + t * (f y).toReal : ℝ) : EReal) := by
    intro x y t hx hy ht0 ht1
    set z := (1 - t) • x + t • y with hz
    set Rv := (1 - t) * (f x).toReal + t * (f y).toReal with hRv
    by_contra hcon
    push_neg at hcon
    obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff.mp (hlsc z (Rv : EReal) hcon)
    obtain ⟨C, hC⟩ : ∃ C : ℝ, C = Rv - inner ℝ a z - b := ⟨_, rfl⟩
    obtain ⟨k, hk⟩ : ∃ k : ℝ, k = (|C| + 1) / δ ^ 2 + ‖a‖ / δ + 1 := ⟨_, rfl⟩
    have hkpos : 0 < k := by rw [hk]; positivity
    obtain ⟨p, hp⟩ := exists_prox hlsc hbot hx0' a b hmin z hkpos
    have hpb := hp.1
    have hpt := hp.2.1
    set P := (f p).toReal with hP
    have hfp : f p = (P : EReal) := (EReal.coe_toReal hpt.ne hpb.ne').symm
    have hfx : f x = ((f x).toReal : EReal) := (EReal.coe_toReal hx.ne (hbot x).ne').symm
    have hfy : f y = ((f y).toReal : EReal) := (EReal.coe_toReal hy.ne (hbot y).ne').symm
    have h1 := hglob p _ hp x
    have h2 := hglob p _ hp y
    rw [hfp, hfx, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
    rw [hfp, hfy, ← EReal.coe_add, EReal.coe_le_coe_iff] at h2
    have e : (1 - t) * inner ℝ (k • (z - p)) (x - p) + t * inner ℝ (k • (z - p)) (y - p)
        = k * ‖p - z‖ ^ 2 := by
      rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right]
      have hzp : (1 - t) • (x - p) + t • (y - p) = z - p := by
        rw [hz]; simp only [smul_sub, sub_smul, one_smul]; abel
      rw [hzp, real_inner_smul_left, real_inner_self_eq_norm_sq, norm_sub_rev]
    have hkey : P + k * ‖p - z‖ ^ 2 ≤ Rv := by
      rw [hRv, ← e]
      nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr ht1),
        mul_le_mul_of_nonneg_left h2 ht0]
    have haff := hmin p
    rw [hfp, EReal.coe_le_coe_iff] at haff
    have hA : inner ℝ a z - ‖a‖ * ‖p - z‖ ≤ inner ℝ a p := by
      have h3 := abs_real_inner_le_norm a (p - z)
      rw [inner_sub_right] at h3
      have h4 := neg_abs_le (inner ℝ a p - inner ℝ a z)
      linarith
    by_cases hs : ‖p - z‖ < δ
    · have hlt : (Rv : EReal) < f p := hδball (show dist p z < δ by rwa [dist_eq_norm])
      rw [hfp, EReal.coe_lt_coe_iff] at hlt
      nlinarith [mul_nonneg hkpos.le (sq_nonneg ‖p - z‖)]
    · push_neg at hs
      have hkδ : k * δ - ‖a‖ = (|C| + 1) / δ + δ := by
        rw [hk]; field_simp; ring
      have hkδpos : 0 < k * δ - ‖a‖ := by rw [hkδ]; positivity
      have hkδ2 : δ * (k * δ - ‖a‖) = |C| + 1 + δ ^ 2 := by
        rw [hkδ]; field_simp
      have hs0 : 0 ≤ ‖p - z‖ := norm_nonneg _
      have hprod : 0 ≤ (‖p - z‖ - δ) * (k * (‖p - z‖ + δ) - ‖a‖) := by
        apply mul_nonneg (by linarith)
        nlinarith [mul_nonneg hkpos.le hs0]
      nlinarith [le_abs_self C, hprod, hkδ2, sq_nonneg δ]
  -- Step 4: convexity of the epigraph
  intro p hp q hq α β hα hβ hαβ
  simp only [epigraph, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at hp hq ⊢
  have hpt : f p.1 < ⊤ := lt_of_le_of_lt hp (EReal.coe_lt_top _)
  have hqt : f q.1 < ⊤ := lt_of_le_of_lt hq (EReal.coe_lt_top _)
  have hp' : (f p.1).toReal ≤ p.2 := by
    rw [← EReal.coe_toReal hpt.ne (hbot _).ne', EReal.coe_le_coe_iff] at hp
    exact hp
  have hq' : (f q.1).toReal ≤ q.2 := by
    rw [← EReal.coe_toReal hqt.ne (hbot _).ne', EReal.coe_le_coe_iff] at hq
    exact hq
  have hα' : α = 1 - β := by linarith
  have h := hmain p.1 q.1 β hpt hqt hβ (by linarith)
  rw [← hα'] at h
  refine h.trans ?_
  rw [EReal.coe_le_coe_iff]
  nlinarith [mul_le_mul_of_nonneg_left hp' hα, mul_le_mul_of_nonneg_left hq' hβ]

end RW1217

theorem RW_chap_12_17
  (f : E → EReal)
  (hf_proper : IsProper f) :
  (ConvexEReal f → IsMonotone (subdifferential f)) ∧
  (LowerSemicontinuous f →
    (ConvexEReal f ↔ IsMonotone (subdifferential f)) ∧
    (ConvexEReal f → IsMaximalMonotone (subdifferential f)) ∧
    (ConvexEReal f →
      (AlmostStrictConvexEReal f ↔
        IsStrictMonotone (subdifferential f)))) := by
  refine ⟨RW1217.part1 f hf_proper, fun hlsc => ⟨⟨RW1217.part1 f hf_proper,
    RW1217.part2a f hf_proper hlsc⟩, RW1217.part2b f hf_proper hlsc,
    RW1217.part2c f hf_proper⟩⟩

end RW_chap_12_17
