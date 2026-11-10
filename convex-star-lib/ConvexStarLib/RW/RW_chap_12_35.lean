import ConvexStarLib.Defs

/-!
# `RW_chap_12_35`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_12_35` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_12_35`, so the main result is `RW_chap_12_35.RW_chap_12_35`.
-/

namespace RW_chap_12_35

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## Auxiliary material for the proof of `RW_chap_12_35` -/

namespace Att

open Filter

/-- proper, lower semicontinuous, convex -/
structure PLC (f : E → EReal) : Prop where
  proper : IsProper f
  lsc : LowerSemicontinuous f
  convex : ConvexEReal f

/-- convex subgradient -/
def CSub (f : E → EReal) (x v : E) : Prop :=
  f x ≠ ⊤ ∧ ∀ w, f x + ((inner ℝ v (w - x) : ℝ) : EReal) ≤ f w

open Classical in
/-- the proximal point (when it is unique) -/
noncomputable def proxPt (f : E → EReal) (lam : ℝ) (x : E) : E :=
  if h : ∃ p, proximalMapping f lam x = {p} then h.choose else 0

/-- real-valued Moreau envelope -/
noncomputable def envR (f : E → EReal) (lam : ℝ) (x : E) : ℝ :=
  (f (proxPt f lam x)).toReal + (2 * lam)⁻¹ * ‖proxPt f lam x - x‖ ^ 2

variable {f : E → EReal}

/-! ### Basic convexity -/

lemma cvx_ineq (hf : ConvexEReal f) {x y : E} {a b : ℝ} (hx : f x ≤ a) (hy : f y ≤ b)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f ((1 - t) • x + t • y) ≤ (((1 - t) * a + t * b : ℝ) : EReal) := by
  have hxe : (x, a) ∈ epigraph f := hx
  have hye : (y, b) ∈ epigraph f := hy
  have h := hf hxe hye (by linarith : (0 : ℝ) ≤ 1 - t) ht0 (by ring)
  simp only [epigraph, Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at h
  exact h

lemma linear_lower_bound (hf : ConvexEReal f) {w : E} {α M : ℝ} (hw : f w ≤ α)
    (hM : ∀ y ∈ Metric.closedBall w 1, ((-M : ℝ) : EReal) ≤ f y) :
    ∀ y, ((-M - (M + α) * ‖y - w‖ : ℝ) : EReal) ≤ f y := by
  have hMα : -M ≤ α := by
    have h1 := hM w (Metric.mem_closedBall_self zero_le_one)
    exact EReal.coe_le_coe_iff.mp (h1.trans hw)
  intro y
  by_cases hy : ‖y - w‖ ≤ 1
  · have h1 := hM y (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hy)
    refine le_trans ?_ h1
    rw [EReal.coe_le_coe_iff]
    have : 0 ≤ (M + α) * ‖y - w‖ := mul_nonneg (by linarith) (norm_nonneg _)
    linarith
  · push_neg at hy
    set d := ‖y - w‖ with hd
    have dpos : 0 < d := by linarith
    set t := d⁻¹ with ht
    have htd : t * d = 1 := inv_mul_cancel₀ dpos.ne'
    have ht0 : 0 ≤ t := inv_nonneg.mpr dpos.le
    have ht1 : t ≤ 1 := inv_le_one_of_one_le₀ hy.le
    -- key claim: every real upper bound of `f y` is above the target value
    have claim : ∀ b : ℝ, f y ≤ b → -M - (M + α) * d ≤ b := by
      intro b hb
      have hu := cvx_ineq hf hw hb ht0 ht1
      have hmem : (1 - t) • w + t • y ∈ Metric.closedBall w 1 := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have e : (1 - t) • w + t • y - w = t • (y - w) := by
          rw [smul_sub, sub_smul, one_smul]; abel
        rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, ← hd, htd]
      have h2 := (hM _ hmem).trans hu
      have key : -M ≤ (1 - t) * α + t * b := EReal.coe_le_coe_iff.mp h2
      have h3 : -M * d ≤ ((1 - t) * α + t * b) * d := mul_le_mul_of_nonneg_right key dpos.le
      have e2 : ((1 - t) * α + t * b) * d = α * d - α + b := by
        linear_combination (b - α) * htd
      have e3 : (M + α) * d = M * d + α * d := by ring
      rw [e2] at h3
      linarith
    by_cases htop : f y = ⊤
    · rw [htop]; exact le_top
    by_cases hbot : f y = ⊥
    · exfalso
      have := claim (-M - (M + α) * d - 1) (by rw [hbot]; exact bot_le)
      linarith
    rw [← EReal.coe_toReal htop hbot, EReal.coe_le_coe_iff]
    exact claim _ (EReal.coe_toReal htop hbot).ge

lemma lsc_bdd_below_closedBall (hf : IsProper f) (hlsc : LowerSemicontinuous f) (w : E) (r : ℝ) :
    ∃ M : ℝ, ∀ y ∈ Metric.closedBall w r, ((-M : ℝ) : EReal) ≤ f y := by
  rcases (Metric.closedBall w r).eq_empty_or_nonempty with h | h
  · refine ⟨0, fun y hy => ?_⟩
    rw [h] at hy
    exact absurd hy (Set.notMem_empty y)
  · obtain ⟨y0, -, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn h (isCompact_closedBall w r)
      (hlsc.lowerSemicontinuousOn _)
    rw [isMinOn_iff] at hmin
    by_cases htop : f y0 = ⊤
    · refine ⟨0, fun y hy => ?_⟩
      have h1 := hmin y hy
      rw [htop, top_le_iff] at h1
      rw [h1]
      exact le_top
    · have hbot : f y0 ≠ ⊥ := (hf.1 y0).ne'
      refine ⟨-(f y0).toReal, fun y hy => ?_⟩
      rw [neg_neg, EReal.coe_toReal htop hbot]
      exact hmin y hy

lemma PLC.linear_lb (hf : PLC f) (x : E) :
    ∃ A B : ℝ, 0 ≤ B ∧ ∀ y, ((-A - B * ‖y - x‖ : ℝ) : EReal) ≤ f y := by
  obtain ⟨w, hw⟩ := hf.proper.2
  have hw' : f w < ⊤ := hw
  have hwtop : f w ≠ ⊤ := ne_of_lt hw'
  have hwbot : f w ≠ ⊥ := (hf.proper.1 w).ne'
  have hwα : f w ≤ (((f w).toReal : ℝ) : EReal) := (EReal.coe_toReal hwtop hwbot).ge
  obtain ⟨M, hM⟩ := lsc_bdd_below_closedBall hf.proper hf.lsc w 1
  have hMα : 0 ≤ M + (f w).toReal := by
    have h1 := hM w (Metric.mem_closedBall_self zero_le_one)
    have h3 : -M ≤ (f w).toReal := EReal.coe_le_coe_iff.mp (h1.trans hwα)
    linarith
  have hlin := linear_lower_bound hf.convex hwα hM
  refine ⟨M + (M + (f w).toReal) * ‖x - w‖, M + (f w).toReal, hMα, fun y => ?_⟩
  refine le_trans ?_ (hlin y)
  rw [EReal.coe_le_coe_iff]
  have htri : ‖y - w‖ ≤ ‖y - x‖ + ‖x - w‖ := norm_sub_le_norm_sub_add_norm_sub y x w
  have h4 := mul_le_mul_of_nonneg_left htri hMα
  rw [mul_add] at h4
  linarith

/-! ### Subgradients and proximal points -/

lemma A3_coe_mul_sq (c t : ℝ) :
    ((c : ℝ) : EReal) * ((t : ℝ) : EReal) ^ 2 = ((c * t ^ 2 : ℝ) : EReal) := by
  rw [EReal.coe_mul, EReal.coe_pow]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma A3_ereal_eq (hf : IsProper f) {w : E} (hw : f w ≠ ⊤) :
    f w = (((f w).toReal : ℝ) : EReal) :=
  (EReal.coe_toReal hw (hf.1 w).ne').symm

lemma mem_prox_iff (hf : PLC f) {lam : ℝ} (hlam : 0 < lam) {x p : E} :
    p ∈ proximalMapping f lam x ↔ CSub f p (lam⁻¹ • (x - p)) := by
  have hc : 0 < (2 * lam)⁻¹ := by positivity
  have h2c : 2 * (2 * lam)⁻¹ = lam⁻¹ := by field_simp
  constructor
  · rintro ⟨hp_top, hp⟩
    refine ⟨hp_top.ne, fun w => ?_⟩
    by_cases hw : f w = ⊤
    · rw [hw]; exact le_top
    have hpa := A3_ereal_eq hf.proper hp_top.ne
    have hwb := A3_ereal_eq hf.proper hw
    set a := (f p).toReal with ha_def
    set b := (f w).toReal with hb_def
    set c := (2 * lam)⁻¹ with hc_def
    set B := inner ℝ (p - x) (w - p) with hB_def
    set K := c * ‖w - p‖ ^ 2 with hK_def
    have hK : 0 ≤ K := by positivity
    -- key real inequality for each t ∈ (0,1]
    have key : ∀ t : ℝ, 0 < t → t ≤ 1 → t * (a - lam⁻¹ * B - b) ≤ t ^ 2 * K := by
      intro t ht0 ht1
      have h1 := cvx_ineq hf.convex (le_of_eq hpa) (le_of_eq hwb) ht0.le ht1
      have h2 := hp ((1 - t) • p + t • w)
      have hz : (1 - t) • p + t • w - x = (p - x) + t • (w - p) := by
        simp only [sub_smul, one_smul, smul_sub]; abel
      have hnorm : ‖(1 - t) • p + t • w - x‖ ^ 2
          = ‖p - x‖ ^ 2 + 2 * t * B + t ^ 2 * ‖w - p‖ ^ 2 := by
        rw [hz, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos ht0]
        ring
      rw [hpa, A3_coe_mul_sq, A3_coe_mul_sq, hnorm] at h2
      have h3 : ((a + c * ‖p - x‖ ^ 2 : ℝ) : EReal) ≤
          (((1 - t) * a + t * b + c * (‖p - x‖ ^ 2 + 2 * t * B + t ^ 2 * ‖w - p‖ ^ 2) : ℝ) :
            EReal) := by
        calc ((a + c * ‖p - x‖ ^ 2 : ℝ) : EReal)
            = (a : EReal) + ((c * ‖p - x‖ ^ 2 : ℝ) : EReal) := by rw [EReal.coe_add]
          _ ≤ f ((1 - t) • p + t • w)
                + ((c * (‖p - x‖ ^ 2 + 2 * t * B + t ^ 2 * ‖w - p‖ ^ 2) : ℝ) : EReal) := h2
          _ ≤ (((1 - t) * a + t * b : ℝ) : EReal)
                + ((c * (‖p - x‖ ^ 2 + 2 * t * B + t ^ 2 * ‖w - p‖ ^ 2) : ℝ) : EReal) := by
              gcongr
          _ = _ := by rw [← EReal.coe_add]
      have h4 := EReal.coe_le_coe_iff.mp h3
      rw [← h2c]
      nlinarith
    -- conclude
    have hinner : inner ℝ (lam⁻¹ • (x - p)) (w - p) = - lam⁻¹ * B := by
      rw [real_inner_smul_left, hB_def, ← neg_sub p x, inner_neg_left]; ring
    rw [hpa, hwb, hinner, ← EReal.coe_add, EReal.coe_le_coe_iff]
    by_contra hcon
    push_neg at hcon
    set d := a - lam⁻¹ * B - b with hd_def
    have hd : 0 < d := by rw [hd_def]; linarith
    have hden : 0 < d + K + 1 := by linarith
    set t := d / (d + K + 1) with ht_def
    have ht0 : 0 < t := div_pos hd hden
    have ht1 : t ≤ 1 := by rw [ht_def, div_le_one hden]; linarith
    have htk : t * (d + K + 1) = d := div_mul_cancel₀ d hden.ne'
    have h5 := key t ht0 ht1
    have h6 : d ≤ t * K := by
      have h7 : t * d ≤ t * (t * K) := by nlinarith
      exact le_of_mul_le_mul_left h7 ht0
    have h8 : t * K < d := by nlinarith
    linarith
  · rintro ⟨hp_top, hp⟩
    refine ⟨lt_top_iff_ne_top.mpr hp_top, fun z => ?_⟩
    have hpa := A3_ereal_eq hf.proper hp_top
    rw [A3_coe_mul_sq, A3_coe_mul_sq]
    by_cases hz : f z = ⊤
    · rw [hz, EReal.top_add_coe]; exact le_top
    have hzb := A3_ereal_eq hf.proper hz
    have h1 := hp z
    rw [hpa, hzb, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
    rw [hpa, hzb, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
    set a := (f p).toReal with ha_def
    set b := (f z).toReal with hb_def
    set c := (2 * lam)⁻¹ with hc_def
    have hinner : inner ℝ (lam⁻¹ • (x - p)) (z - p) = - lam⁻¹ * inner ℝ (z - p) (p - x) := by
      rw [real_inner_smul_left, ← neg_sub p x, inner_neg_left, real_inner_comm]; ring
    have hnorm : ‖z - x‖ ^ 2 = ‖z - p‖ ^ 2 + 2 * inner ℝ (z - p) (p - x) + ‖p - x‖ ^ 2 := by
      have : z - x = (z - p) + (p - x) := by abel
      rw [this, norm_add_sq_real]
    rw [hinner, ← h2c] at h1
    rw [hnorm]
    have : 0 ≤ c * ‖z - p‖ ^ 2 := by positivity
    nlinarith

lemma A3_reg_csub (hf : PLC f) {y u : E} (h : IsRegularSubgradientAt f y u) : CSub f y u := by
  obtain ⟨hbot, htop, r, hr, V, hV, hineq⟩ := h
  refine ⟨htop.ne, fun w => ?_⟩
  by_cases hw : f w = ⊤
  · rw [hw]; exact le_top
  have hya := A3_ereal_eq hf.proper htop.ne
  have hwb := A3_ereal_eq hf.proper hw
  set a := (f y).toReal with ha_def
  set b := (f w).toReal with hb_def
  set B := inner ℝ u (w - y) with hB_def
  set N := ‖w - y‖ with hN_def
  have hN : 0 ≤ N := norm_nonneg _
  -- for every ε > 0 : a + B ≤ b + ε * N
  have key : ∀ ε : ℝ, 0 < ε → a + B ≤ b + ε * N := by
    intro ε hε
    have hev : ∀ᶠ z in 𝓝 y, z ∈ V ∧ ‖r z‖ ≤ ε * ‖‖z - y‖‖ :=
      Filter.inter_mem hV (hr.def hε)
    obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff.mp hev
    have hden : 0 < δ + N + 1 := by linarith
    set t := δ / (δ + N + 1) with ht_def
    have ht0 : 0 < t := div_pos hδ hden
    have ht1 : t ≤ 1 := by rw [ht_def, div_le_one hden]; linarith
    have htk : t * (δ + N + 1) = δ := div_mul_cancel₀ δ hden.ne'
    have htN : t * N < δ := by nlinarith
    set z := y + t • (w - y) with hz_def
    have hzy : z - y = t • (w - y) := by rw [hz_def]; abel
    have hznorm : ‖z - y‖ = t * N := by
      rw [hzy, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    have hdist : dist z y < δ := by rw [dist_eq_norm, hznorm]; exact htN
    obtain ⟨hzV, hrz⟩ := hδball hdist
    rw [norm_norm, hznorm, Real.norm_eq_abs] at hrz
    have hrz' : -(ε * (t * N)) ≤ r z := by
      have := neg_abs_le (r z); linarith
    have h1 := hineq z hzV
    have hz2 : z = (1 - t) • y + t • w := by
      rw [hz_def]; simp only [sub_smul, one_smul, smul_sub]; abel
    have h2 := cvx_ineq hf.convex (le_of_eq hya) (le_of_eq hwb) ht0.le ht1
    rw [← hz2] at h2
    have h3 := h1.trans h2
    rw [hya, ← EReal.coe_add, EReal.coe_le_coe_iff, hzy, real_inner_smul_right] at h3
    -- h3 : a + (t * B + r z) ≤ (1 - t) * a + t * b
    have h4 : t * (a + B) ≤ t * (b + ε * N) := by nlinarith
    exact le_of_mul_le_mul_left h4 ht0
  rw [hya, hwb, ← EReal.coe_add, EReal.coe_le_coe_iff]
  by_contra hcon
  push_neg at hcon
  set d := a + B - b with hd_def
  have hd : 0 < d := by rw [hd_def]; linarith
  have hden : 0 < N + 1 := by linarith
  set ε := d / (N + 1) with hε_def
  have hε : 0 < ε := div_pos hd hden
  have hεk : ε * (N + 1) = d := div_mul_cancel₀ d hden.ne'
  have h5 := key ε hε
  nlinarith

lemma mem_subdiff_iff (hf : PLC f) {x v : E} :
    v ∈ subdifferential f x ↔ CSub f x v := by
  constructor
  · rintro ⟨hbot, htop, xs, vs, hxs, hfxs, hvs, hreg⟩
    have hcs : ∀ i, CSub f (xs i) (vs i) := fun i => A3_reg_csub hf (hreg i)
    refine ⟨htop.ne, fun w => ?_⟩
    by_cases hw : f w = ⊤
    · rw [hw]; exact le_top
    have hxa := A3_ereal_eq hf.proper htop.ne
    have hwb := A3_ereal_eq hf.proper hw
    have hlim1 : Tendsto (fun n => (f (xs n)).toReal) atTop (𝓝 (f x).toReal) :=
      (EReal.tendsto_toReal htop.ne hbot.ne').comp hfxs
    have hlim2 : Tendsto (fun n => inner ℝ (vs n) (w - xs n)) atTop
        (𝓝 (inner ℝ v (w - x))) :=
      hvs.inner (tendsto_const_nhds.sub hxs)
    have hlim := hlim1.add hlim2
    have hle : ∀ n, (f (xs n)).toReal + inner ℝ (vs n) (w - xs n) ≤ (f w).toReal := by
      intro n
      have h1 := (hcs n).2 w
      have hxn := A3_ereal_eq hf.proper (hcs n).1
      rw [hxn, hwb, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
      exact h1
    have h2 := le_of_tendsto' hlim hle
    rw [hxa, hwb, ← EReal.coe_add, EReal.coe_le_coe_iff]
    exact h2
  · rintro ⟨hx_top, hx⟩
    have hbot := hf.proper.1 x
    have htop : f x < ⊤ := lt_top_iff_ne_top.mpr hx_top
    refine ⟨hbot, htop, fun _ => x, fun _ => v, tendsto_const_nhds, tendsto_const_nhds,
      tendsto_const_nhds, fun _ => ?_⟩
    refine ⟨hbot, htop, fun _ => 0, Asymptotics.isLittleO_zero _ _, Set.univ, Filter.univ_mem,
      fun z _ => ?_⟩
    simpa using hx z

lemma CSub.monotone (hf : IsProper f) {p q u v : E} (hu : CSub f p u) (hv : CSub f q v) :
    0 ≤ inner ℝ (u - v) (p - q) := by
  obtain ⟨hp, hu'⟩ := hu
  obtain ⟨hq, hv'⟩ := hv
  have hpb : f p ≠ ⊥ := (hf.1 p).ne'
  have hqb : f q ≠ ⊥ := (hf.1 q).ne'
  have h1 := hu' q
  have h2 := hv' p
  rw [← EReal.coe_toReal hp hpb, ← EReal.coe_toReal hq hqb, ← EReal.coe_add,
    EReal.coe_le_coe_iff] at h1 h2
  simp only [inner_sub_left, inner_sub_right] at h1 h2 ⊢
  linarith

lemma A2_coe_quad (a t : ℝ) :
    ((a : ℝ) : EReal) * ((t : ℝ) : EReal) ^ 2 = ((a * t ^ 2 : ℝ) : EReal) := by
  rw [EReal.coe_mul, EReal.coe_pow]

lemma A2_quad_large_t {K : ℝ} (hK : 0 < K) (A B C : ℝ) (hB : 0 ≤ B) :
    ∃ R > 0, ∀ t, R ≤ t → C < -A - B * t + K * t ^ 2 := by
  have hM : 0 ≤ (B + |A| + |C| + 1) / K := by positivity
  refine ⟨1 + (B + |A| + |C| + 1) / K, by positivity, fun t ht => ?_⟩
  have h1 : 1 ≤ t := by linarith
  have h2 : B + |A| + |C| + 1 ≤ K * t := by
    have h3 : (B + |A| + |C| + 1) / K ≤ t := by linarith
    rw [div_le_iff₀ hK] at h3
    linarith
  have hA := le_abs_self A
  have hC := le_abs_self C
  have hm1 : t * (B + |A| + |C| + 1) ≤ t * (K * t) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have hm2 : 1 * (|A| + |C| + 1) ≤ t * (|A| + |C| + 1) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  nlinarith

lemma prox_exists_unique (hf : PLC f) {lam : ℝ} (hlam : 0 < lam) (x : E) :
    ∃ p, proximalMapping f lam x = {p} := by
  have hk : 0 < (2 * lam)⁻¹ := by positivity
  -- the objective function
  let h : E → EReal := fun w => f w + (((2 * lam)⁻¹ * ‖w - x‖ ^ 2 : ℝ) : EReal)
  have hh : ∀ w, h w = f w + (((2 * lam)⁻¹ * ‖w - x‖ ^ 2 : ℝ) : EReal) := fun w => rfl
  have hcont : Continuous (fun w : E => (((2 * lam)⁻¹ * ‖w - x‖ ^ 2 : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp (by fun_prop)
  have hlsc : LowerSemicontinuous h := by
    refine LowerSemicontinuous.add' hf.lsc hcont.lowerSemicontinuous ?_
    intro w
    apply EReal.continuousAt_add
    · right; exact EReal.coe_ne_bot _
    · left; exact (hf.proper.1 w).ne'
  obtain ⟨w0, hw0⟩ := hf.proper.2
  have hw0' : f w0 < ⊤ := hw0
  have hw0bot : ⊥ < f w0 := hf.proper.1 w0
  obtain ⟨A, B, hB, hlb⟩ := hf.linear_lb x
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, c0 = (f w0).toReal + (2 * lam)⁻¹ * ‖w0 - x‖ ^ 2 := ⟨_, rfl⟩
  have hhw0 : h w0 = (c0 : EReal) := by
    rw [hh, hc0, EReal.coe_add, EReal.coe_toReal hw0'.ne hw0bot.ne']
  obtain ⟨R, hR, hRt⟩ := A2_quad_large_t hk A B c0 hB
  have hout : ∀ z, max R ‖w0 - x‖ < ‖z - x‖ → (c0 : EReal) < h z := by
    intro z hz
    have ht : R ≤ ‖z - x‖ := le_trans (le_max_left _ _) hz.le
    calc (c0 : EReal) < ((-A - B * ‖z - x‖ + (2 * lam)⁻¹ * ‖z - x‖ ^ 2 : ℝ) : EReal) :=
          EReal.coe_lt_coe_iff.mpr (hRt _ ht)
      _ = ((-A - B * ‖z - x‖ : ℝ) : EReal) + (((2 * lam)⁻¹ * ‖z - x‖ ^ 2 : ℝ) : EReal) :=
          EReal.coe_add _ _
      _ ≤ f z + (((2 * lam)⁻¹ * ‖z - x‖ ^ 2 : ℝ) : EReal) := add_le_add (hlb z) le_rfl
      _ = h z := (hh z).symm
  have hw0mem : w0 ∈ Metric.closedBall x (max R ‖w0 - x‖) := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact le_max_right _ _
  obtain ⟨p, -, hpmin⟩ := (hlsc.lowerSemicontinuousOn _).exists_isMinOn ⟨w0, hw0mem⟩
    (isCompact_closedBall x (max R ‖w0 - x‖))
  have hpmin' := isMinOn_iff.mp hpmin
  have hpc0 : h p ≤ (c0 : EReal) := by
    have := hpmin' w0 hw0mem
    rwa [hhw0] at this
  have hglob : ∀ z, h p ≤ h z := by
    intro z
    by_cases hz : z ∈ Metric.closedBall x (max R ‖w0 - x‖)
    · exact hpmin' z hz
    · rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hz
      exact hpc0.trans (hout z hz).le
  have hfp : f p < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [hh, htop, EReal.top_add_coe] at hpc0
    exact absurd hpc0 (not_le.mpr (EReal.coe_lt_top c0))
  have hpprox : p ∈ proximalMapping f lam x := by
    unfold proximalMapping
    rw [Set.mem_setOf_eq]
    refine ⟨hfp, fun z => ?_⟩
    rw [A2_coe_quad, A2_coe_quad]
    exact hglob z
  refine ⟨p, Set.eq_singleton_iff_unique_mem.mpr ⟨hpprox, fun q hq => ?_⟩⟩
  have hp' := (mem_prox_iff hf hlam).mp hpprox
  have hq' := (mem_prox_iff hf hlam).mp hq
  have hmono := CSub.monotone hf.proper hp' hq'
  have e1 : lam⁻¹ • (x - p) - lam⁻¹ • (x - q) = lam⁻¹ • (q - p) := by
    rw [← smul_sub]; congr 1; abel
  have e2 : inner ℝ (q - p) (p - q) = -‖p - q‖ ^ 2 := by
    rw [← neg_sub p q, inner_neg_left, real_inner_self_eq_norm_sq]
  rw [e1, real_inner_smul_left, e2] at hmono
  have hlaminv : 0 < lam⁻¹ := inv_pos.mpr hlam
  have hsq : ‖p - q‖ ^ 2 ≤ 0 := by nlinarith
  have hn : ‖p - q‖ = 0 := by nlinarith [norm_nonneg (p - q)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

lemma proximalMapping_eq (hf : PLC f) {lam : ℝ} (hlam : 0 < lam) (x : E) :
    proximalMapping f lam x = {proxPt f lam x} := by
  have h := prox_exists_unique hf hlam x
  unfold proxPt
  rw [dif_pos h]
  exact h.choose_spec

lemma proxPt_mem (hf : PLC f) {lam : ℝ} (hlam : 0 < lam) (x : E) :
    proxPt f lam x ∈ proximalMapping f lam x := by
  rw [proximalMapping_eq hf hlam x]; rfl

lemma proxPt_eq_of_mem (hf : PLC f) {lam : ℝ} (hlam : 0 < lam) {x p : E}
    (hp : p ∈ proximalMapping f lam x) : proxPt f lam x = p := by
  rw [proximalMapping_eq hf hlam x] at hp
  exact hp.symm

lemma A4_prox_firm (hf : PLC f) {lam : ℝ} (hlam : 0 < lam) (x y : E) :
    ‖proxPt f lam x - proxPt f lam y‖ ^ 2 ≤
      inner ℝ (x - y) (proxPt f lam x - proxPt f lam y) := by
  have hp := (mem_prox_iff hf hlam).mp (proxPt_mem hf hlam x)
  have hq := (mem_prox_iff hf hlam).mp (proxPt_mem hf hlam y)
  have hm := CSub.monotone hf.proper hp hq
  rw [← smul_sub, real_inner_smul_left] at hm
  have hm' : 0 ≤ inner ℝ (x - proxPt f lam x - (y - proxPt f lam y))
      (proxPt f lam x - proxPt f lam y) :=
    (mul_nonneg_iff_of_pos_left (inv_pos.mpr hlam)).mp hm
  have e : x - proxPt f lam x - (y - proxPt f lam y)
      = (x - y) - (proxPt f lam x - proxPt f lam y) := by abel
  rw [e, inner_sub_left, real_inner_self_eq_norm_sq] at hm'
  linarith

lemma prox_nonexp (hf : PLC f) {lam : ℝ} (hlam : 0 < lam) (x y : E) :
    ‖proxPt f lam x - proxPt f lam y‖ ≤ ‖x - y‖ := by
  have h1 := A4_prox_firm hf hlam x y
  have h2 := real_inner_le_norm (x - y) (proxPt f lam x - proxPt f lam y)
  have h3 := norm_nonneg (proxPt f lam x - proxPt f lam y)
  have h4 := norm_nonneg (x - y)
  nlinarith

lemma f_proxPt_coe (hf : PLC f) {lam : ℝ} (hlam : 0 < lam) (x : E) :
    f (proxPt f lam x) = (((f (proxPt f lam x)).toReal : ℝ) : EReal) := by
  have h := proxPt_mem hf hlam x
  have h1 : f (proxPt f lam x) < ⊤ := h.1
  exact (EReal.coe_toReal (ne_of_lt h1) (hf.proper.1 _).ne').symm

lemma A4_envR_le (hf : PLC f) {lam : ℝ} (hlam : 0 < lam) (x w : E) :
    (envR f lam x : EReal) ≤ f w + (((2 * lam)⁻¹ * ‖w - x‖ ^ 2 : ℝ) : EReal) := by
  have h := (proxPt_mem hf hlam x).2 w
  rw [f_proxPt_coe hf hlam x] at h
  unfold envR
  rw [EReal.coe_add, EReal.coe_mul, EReal.coe_pow, EReal.coe_mul, EReal.coe_pow]
  exact h

lemma moreau_eq (hf : PLC f) {lam : ℝ} (hlam : 0 < lam) (x : E) :
    moreauEnvelope f lam x = (envR f lam x : EReal) := by
  unfold moreauEnvelope
  apply le_antisymm
  · apply sInf_le
    refine ⟨proxPt f lam x, ?_⟩
    unfold envR
    rw [EReal.coe_add, EReal.coe_mul, EReal.coe_pow, ← f_proxPt_coe hf hlam x]
  · apply le_sInf
    rintro v ⟨w, rfl⟩
    have h := A4_envR_le hf hlam x w
    rwa [EReal.coe_mul, EReal.coe_pow] at h

lemma envR_le (hf : PLC f) {lam : ℝ} (hlam : 0 < lam) (x w : E) :
    (envR f lam x : EReal) ≤ f w + (((2 * lam)⁻¹ * ‖w - x‖ ^ 2 : ℝ) : EReal) :=
  A4_envR_le hf hlam x w

lemma A4_alg {lam : ℝ} (hlam : 0 < lam) (a b p q : E) (fp fq : ℝ)
    (h : fp + inner ℝ (lam⁻¹ • (a - p)) (q - p) ≤ fq) :
    fp + (2 * lam)⁻¹ * ‖p - a‖ ^ 2 + inner ℝ (lam⁻¹ • (a - p)) (b - a)
      ≤ fq + (2 * lam)⁻¹ * ‖q - b‖ ^ 2 := by
  have e1 : q - p = (q - b) + (b - a) + (a - p) := by abel
  rw [e1, inner_add_right, inner_add_right] at h
  simp only [real_inner_smul_left, real_inner_self_eq_norm_sq] at h
  rw [real_inner_smul_left, norm_sub_rev p a, mul_inv]
  have key : 0 ≤ ‖(a - p) + (q - b)‖ ^ 2 := sq_nonneg _
  rw [norm_add_sq_real] at key
  have hl : 0 < lam⁻¹ := inv_pos.mpr hlam
  have key2 := mul_nonneg hl.le key
  nlinarith

lemma A4_env_lower (hf : PLC f) {lam : ℝ} (hlam : 0 < lam) (a b : E) :
    envR f lam a + inner ℝ (lam⁻¹ • (a - proxPt f lam a)) (b - a) ≤ envR f lam b := by
  have hcs : CSub f (proxPt f lam a) (lam⁻¹ • (a - proxPt f lam a)) :=
    (mem_prox_iff hf hlam).mp (proxPt_mem hf hlam a)
  have h1 := hcs.2 (proxPt f lam b)
  rw [f_proxPt_coe hf hlam a, f_proxPt_coe hf hlam b, ← EReal.coe_add,
    EReal.coe_le_coe_iff] at h1
  unfold envR
  exact A4_alg hlam a b _ _ _ _ h1

lemma env_two_point (hf : PLC f) {lam : ℝ} (hlam : 0 < lam) (a b : E) :
    0 ≤ envR f lam b - envR f lam a - inner ℝ (lam⁻¹ • (a - proxPt f lam a)) (b - a) ∧
    envR f lam b - envR f lam a - inner ℝ (lam⁻¹ • (a - proxPt f lam a)) (b - a)
      ≤ 2 / lam * ‖b - a‖ ^ 2 := by
  have hab := A4_env_lower hf hlam a b
  have hba := A4_env_lower hf hlam b a
  refine ⟨by linarith, ?_⟩
  have hfirm := A4_prox_firm hf hlam b a
  have i1 : inner ℝ (lam⁻¹ • (b - proxPt f lam b)) (a - b)
      = -(lam⁻¹ * inner ℝ (b - proxPt f lam b) (b - a)) := by
    rw [real_inner_smul_left, ← neg_sub b a, inner_neg_right, mul_neg]
  have i2 : inner ℝ (lam⁻¹ • (a - proxPt f lam a)) (b - a)
      = lam⁻¹ * inner ℝ (a - proxPt f lam a) (b - a) := real_inner_smul_left _ _ _
  have i3 : inner ℝ (b - proxPt f lam b) (b - a)
      = inner ℝ (a - proxPt f lam a) (b - a) + ‖b - a‖ ^ 2
        - inner ℝ (b - a) (proxPt f lam b - proxPt f lam a) := by
    have : b - proxPt f lam b
        = (a - proxPt f lam a) + (b - a) - (proxPt f lam b - proxPt f lam a) := by abel
    rw [this, inner_sub_left, inner_add_left, real_inner_self_eq_norm_sq,
      real_inner_comm (b - a) (proxPt f lam b - proxPt f lam a)]
  rw [i1, i3] at hba
  rw [i2, div_eq_mul_inv]
  have hl : 0 < lam⁻¹ := inv_pos.mpr hlam
  have hJ : 0 ≤ inner ℝ (b - a) (proxPt f lam b - proxPt f lam a) :=
    le_trans (sq_nonneg _) hfirm
  have k1 := mul_nonneg hl.le hJ
  have k2 := mul_nonneg hl.le (sq_nonneg ‖b - a‖)
  nlinarith

lemma A2_quad_large_K {δ : ℝ} (hδ : 0 < δ) (A B C : ℝ) (hB : 0 ≤ B) :
    ∃ K > 0, ∀ t, δ ≤ t → C < -A - B * t + K * t ^ 2 := by
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (|A| + |C| + 1) / δ := ⟨_, rfl⟩
  have hD0 : 0 < D := by rw [hD]; positivity
  have hDδ : D * δ = |A| + |C| + 1 := by rw [hD]; field_simp
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = (B + D) / δ := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hKdef]; positivity
  have hKδ : K * δ = B + D := by rw [hKdef]; field_simp
  refine ⟨K, hK0, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := le_trans hδ.le ht
  have h1 : K * t * δ ≤ K * t * t := mul_le_mul_of_nonneg_left ht (mul_nonneg hK0.le ht0)
  have h2 : D * δ ≤ D * t := mul_le_mul_of_nonneg_left ht hD0.le
  have h3 : K * δ * t = (B + D) * t := by rw [hKδ]
  have hA := le_abs_self A
  have hC := le_abs_self C
  nlinarith

lemma small_mu_bound (hf : PLC f) (x : E) (b : ℝ) (hb : (b : EReal) < f x) :
    ∃ μ > 0, ∀ y, (b : EReal) < f y + ((μ⁻¹ * ‖y - x‖ ^ 2 : ℝ) : EReal) := by
  have hev : ∀ᶠ y in 𝓝 x, (b : EReal) < f y := hf.lsc x b hb
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨A, B, hB, hlb⟩ := hf.linear_lb x
  obtain ⟨K, hK, hKt⟩ := A2_quad_large_K hδ A B b hB
  refine ⟨K⁻¹, inv_pos.mpr hK, fun y => ?_⟩
  rw [inv_inv]
  by_cases hy : dist y x < δ
  · have h1 := hball hy
    have h2 : (0 : EReal) ≤ ((K * ‖y - x‖ ^ 2 : ℝ) : EReal) :=
      EReal.coe_nonneg.mpr (mul_nonneg hK.le (sq_nonneg _))
    exact lt_of_lt_of_le h1 (le_add_of_nonneg_right h2)
  · rw [not_lt, dist_eq_norm] at hy
    calc (b : EReal) < ((-A - B * ‖y - x‖ + K * ‖y - x‖ ^ 2 : ℝ) : EReal) :=
          EReal.coe_lt_coe_iff.mpr (hKt _ hy)
      _ = ((-A - B * ‖y - x‖ : ℝ) : EReal) + ((K * ‖y - x‖ ^ 2 : ℝ) : EReal) :=
          EReal.coe_add _ _
      _ ≤ f y + ((K * ‖y - x‖ ^ 2 : ℝ) : EReal) := add_le_add (hlb y) le_rfl

lemma prox_close (hf : PLC f) (x : E) (hx : f x ≠ ⊤) (ε : ℝ) (hε : 0 < ε) :
    ∃ μ > 0, ‖proxPt f μ x - x‖ < ε := by
  have hxbot : f x ≠ ⊥ := (hf.proper.1 x).ne'
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (f x).toReal := ⟨_, rfl⟩
  have hfx : f x = (c : EReal) := by rw [hc, EReal.coe_toReal hx hxbot]
  obtain ⟨A, B, hB, hlb⟩ := hf.linear_lb x
  obtain ⟨K, hK, hKt⟩ := A2_quad_large_K hε A B c hB
  have hμ : 0 < (2 * K)⁻¹ := by positivity
  have h2μ : (2 * (2 * K)⁻¹)⁻¹ = K := by
    have := hK.ne'
    field_simp
  refine ⟨(2 * K)⁻¹, hμ, ?_⟩
  by_contra hcon
  rw [not_lt] at hcon
  have henv := envR_le hf hμ x x
  have hzero : (((2 * (2 * K)⁻¹)⁻¹ * ‖x - x‖ ^ 2 : ℝ) : EReal) = 0 := by simp
  rw [hzero, add_zero, hfx, EReal.coe_le_coe_iff] at henv
  unfold envR at henv
  rw [h2μ] at henv
  have hfp := hlb (proxPt f (2 * K)⁻¹ x)
  rw [f_proxPt_coe hf hμ x, EReal.coe_le_coe_iff] at hfp
  have := hKt _ hcon
  linarith

/-! ### An abstract integration lemma -/

lemma A5_telescope (e1 : E → ℝ) (g1 : E → E) (L : ℝ)
    (h : ∀ a b, 0 ≤ e1 b - e1 a - inner ℝ (g1 a) (b - a) ∧
      e1 b - e1 a - inner ℝ (g1 a) (b - a) ≤ L * ‖b - a‖ ^ 2)
    (y : ℕ → E) (Δ : E) (hstep : ∀ k, y (k + 1) - y k = Δ) (m : ℕ) :
    0 ≤ (e1 (y m) - e1 (y 0)) - ∑ k ∈ Finset.range m, inner ℝ (g1 (y k)) Δ ∧
    (e1 (y m) - e1 (y 0)) - ∑ k ∈ Finset.range m, inner ℝ (g1 (y k)) Δ
      ≤ m * (L * ‖Δ‖ ^ 2) := by
  have hdiff : (e1 (y m) - e1 (y 0)) - ∑ k ∈ Finset.range m, inner ℝ (g1 (y k)) Δ
      = ∑ k ∈ Finset.range m,
          (e1 (y (k + 1)) - e1 (y k) - inner ℝ (g1 (y k)) (y (k + 1) - y k)) := by
    rw [← Finset.sum_range_sub (fun k => e1 (y k)) m, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [hstep]
  rw [hdiff]
  constructor
  · exact Finset.sum_nonneg (fun k _ => (h (y k) (y (k + 1))).1)
  · calc ∑ k ∈ Finset.range m,
          (e1 (y (k + 1)) - e1 (y k) - inner ℝ (g1 (y k)) (y (k + 1) - y k))
        ≤ ∑ k ∈ Finset.range m, L * ‖Δ‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro k _
          have := (h (y k) (y (k + 1))).2
          rw [hstep] at this ⊢
          exact this
      _ = m * (L * ‖Δ‖ ^ 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma riemann_conv (e : ℕ → E → ℝ) (e0 : E → ℝ) (g : ℕ → E → E) (g0 : E → E) (L : ℝ)
    (h1 : ∀ n a b, 0 ≤ e n b - e n a - inner ℝ (g n a) (b - a) ∧
      e n b - e n a - inner ℝ (g n a) (b - a) ≤ L * ‖b - a‖ ^ 2)
    (h0 : ∀ a b, 0 ≤ e0 b - e0 a - inner ℝ (g0 a) (b - a) ∧
      e0 b - e0 a - inner ℝ (g0 a) (b - a) ≤ L * ‖b - a‖ ^ 2)
    (hg : ∀ a, Tendsto (fun n => g n a) atTop (𝓝 (g0 a)))
    (xt : E) (xs : ℕ → E) (hxs : Tendsto xs atTop (𝓝 xt))
    (he : Tendsto (fun n => e n (xs n)) atTop (𝓝 (e0 xt))) :
    ∀ y, Tendsto (fun n => e n y) atTop (𝓝 (e0 y)) := by
  -- Step A: convergence at `xt`
  have hA : Tendsto (fun n => e n xt) atTop (𝓝 (e0 xt)) := by
    have hd : Tendsto (fun n => xs n - xt) atTop (𝓝 0) := by
      have := hxs.sub_const xt
      rwa [sub_self] at this
    have hin : Tendsto (fun n => inner ℝ (g n xt) (xs n - xt)) atTop (𝓝 0) := by
      have := Filter.Tendsto.inner (𝕜 := ℝ) (hg xt) hd
      rwa [inner_zero_right] at this
    have hsq : Tendsto (fun n => L * ‖xs n - xt‖ ^ 2) atTop (𝓝 0) := by
      have := (hd.norm.pow 2).const_mul L
      simpa using this
    have hr : Tendsto (fun n => e n (xs n) - e n xt - inner ℝ (g n xt) (xs n - xt))
        atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsq
        (fun n => (h1 n xt (xs n)).1) (fun n => (h1 n xt (xs n)).2)
    have := (he.sub hin).sub hr
    rw [sub_zero, sub_zero] at this
    refine this.congr ?_
    intro n
    ring
  -- Step B
  intro y
  rw [Metric.tendsto_atTop]
  intro ε hε
  set D := y - xt with hD
  set C := L * ‖D‖ ^ 2 with hC
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * |C| / ε)
  have hmpos : (0 : ℝ) < m := lt_of_le_of_lt (div_nonneg (by positivity) hε.le) hm
  have hm0 : (m : ℝ) ≠ 0 := hmpos.ne'
  have hCm : C / m < ε / 2 := by
    rw [div_lt_iff₀ hmpos]
    rw [div_lt_iff₀ hε] at hm
    nlinarith [le_abs_self C]
  let yk : ℕ → E := fun k => xt + ((k : ℝ) / m) • D
  let Δ : E := (1 / (m : ℝ)) • D
  have hstep : ∀ k, yk (k + 1) - yk k = Δ := by
    intro k
    simp only [yk, Δ]
    rw [add_sub_add_left_eq_sub, ← sub_smul]
    congr 1
    push_cast
    ring
  have hy0 : yk 0 = xt := by simp [yk]
  have hym : yk m = y := by
    simp only [yk]
    rw [div_self hm0, one_smul, hD]
    abel
  have hbound : (m : ℝ) * (L * ‖Δ‖ ^ 2) = C / m := by
    simp only [Δ, hC]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hmpos)]
    field_simp
  have hS : Tendsto (fun n => e n xt + ∑ k ∈ Finset.range m, inner ℝ (g n (yk k)) Δ) atTop
      (𝓝 (e0 xt + ∑ k ∈ Finset.range m, inner ℝ (g0 (yk k)) Δ)) := by
    apply hA.add
    apply tendsto_finset_sum
    intro k _
    exact Filter.Tendsto.inner (𝕜 := ℝ) (hg (yk k)) tendsto_const_nhds
  rw [Metric.tendsto_atTop] at hS
  obtain ⟨N, hN⟩ := hS (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hNn := hN n hn
  rw [Real.dist_eq, abs_sub_lt_iff] at hNn ⊢
  obtain ⟨hN1, hN2⟩ := hNn
  have T1 := A5_telescope (e n) (g n) L (h1 n) yk Δ hstep m
  have T0 := A5_telescope e0 g0 L h0 yk Δ hstep m
  rw [hy0, hym, hbound] at T1 T0
  obtain ⟨T1a, T1b⟩ := T1
  obtain ⟨T0a, T0b⟩ := T0
  constructor <;> linarith

/-! ### Set limits -/

lemma mem_setLiminf_of_seq {X : Type*} [TopologicalSpace X] (A : ℕ → Set X) {u : X} (s : ℕ → X)
    (hs : ∀ᶠ n in atTop, s n ∈ A n) (hsu : Tendsto s atTop (𝓝 u)) : u ∈ setLiminf A := by
  intro V hV
  filter_upwards [hs, hsu hV] with n hn hn'
  exact ⟨s n, hn, hn'⟩

lemma mem_setLimsup_of_seq {X : Type*} [TopologicalSpace X] (A : ℕ → Set X) {u : X}
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) (s : ℕ → X)
    (hs : ∀ᶠ k in atTop, s k ∈ A (ns k)) (hsu : Tendsto s atTop (𝓝 u)) : u ∈ setLimsup A := by
  intro V hV
  have h : ∀ᶠ k in atTop, ∃ v ∈ A (ns k), v ∈ V := by
    filter_upwards [hs, hsu hV] with k hk hk'
    exact ⟨s k, hk, hk'⟩
  exact hns.frequently (p := fun n => ∃ v ∈ A n, v ∈ V) h.frequently

lemma setLiminf_seq {X : Type*} [MetricSpace X] (A : ℕ → Set X) (hne : ∀ n, (A n).Nonempty)
    {u : X} (hu : u ∈ setLiminf A) :
    ∃ s : ℕ → X, (∀ n, s n ∈ A n) ∧ Tendsto s atTop (𝓝 u) := by
  have hd : Tendsto (fun n => Metric.infDist u (A n)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have h1 : ∀ᶠ n in atTop, ∃ v ∈ A n, v ∈ Metric.ball u ε :=
      hu (Metric.ball u ε) (Metric.ball_mem_nhds u hε)
    rw [eventually_atTop] at h1
    obtain ⟨N, hN⟩ := h1
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨v, hvA, hvV⟩ := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg]
    rw [Metric.mem_ball, _root_.dist_comm] at hvV
    calc Metric.infDist u (A n) ≤ dist u v := Metric.infDist_le_dist_of_mem hvA
      _ < ε := hvV
  have hex : ∀ n : ℕ, ∃ v ∈ A n, dist u v < Metric.infDist u (A n) + 1 / ((n:ℝ) + 1) := by
    intro n
    rw [← Metric.infDist_lt_iff (hne n)]
    have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
    linarith
  choose s hsA hsd using hex
  refine ⟨s, hsA, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  have h1 : Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun n : ℕ => Metric.infDist u (A n) + 1 / ((n:ℝ) + 1)) atTop (𝓝 0) := by
    simpa using hd.add h1
  apply squeeze_zero (fun n => dist_nonneg) _ h2
  intro n
  rw [_root_.dist_comm]
  exact (hsd n).le

lemma setLimsup_seq {X : Type*} [MetricSpace X] (A : ℕ → Set X) {u : X}
    (hu : u ∈ setLimsup A) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ s : ℕ → X, (∀ k, s k ∈ A (ns k)) ∧ Tendsto s atTop (𝓝 u) := by
  have hfr : ∀ k : ℕ, ∃ᶠ n in atTop, ∃ v ∈ A n, dist v u < 1 / ((k:ℝ) + 1) := by
    intro k
    exact hu (Metric.ball u (1 / ((k:ℝ) + 1))) (Metric.ball_mem_nhds u (by positivity))
  obtain ⟨ns, hns, hP⟩ := extraction_forall_of_frequently hfr
  choose s hsA hsd using hP
  refine ⟨ns, hns, s, hsA, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun n => dist_nonneg) (fun n => (hsd n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

lemma setLiminf_subset_setLimsup {X : Type*} [TopologicalSpace X] (A : ℕ → Set X) :
    setLiminf A ⊆ setLimsup A := by
  intro u hu V hV
  exact (hu V hV).frequently

lemma isClosed_setLiminf {X : Type*} [TopologicalSpace X] (A : ℕ → Set X) :
    IsClosed (setLiminf A) := by
  apply isClosed_of_closure_subset
  intro u hu V hV
  obtain ⟨W, hWV, hWo, huW⟩ := mem_nhds_iff.mp hV
  obtain ⟨u', hu'W, hu'⟩ := mem_closure_iff.mp hu W hWo huW
  have h1 : ∀ᶠ n in atTop, ∃ v ∈ A n, v ∈ W := hu' W (hWo.mem_nhds hu'W)
  filter_upwards [h1] with n hn
  obtain ⟨v, hvA, hvW⟩ := hn
  exact ⟨v, hvA, hWV hvW⟩

lemma singleton_conv_iff {X : Type*} [TopologicalSpace X] [T2Space X] (a : ℕ → X) (b : X) :
    (setLimsup (fun n => ({a n} : Set X)) = {b} ∧ setLiminf (fun n => ({a n} : Set X)) = {b}) ↔
      Tendsto a atTop (𝓝 b) := by
  constructor
  · rintro ⟨-, h2⟩
    have hb : b ∈ setLiminf (fun n => ({a n} : Set X)) := by rw [h2]; rfl
    intro V hV
    have h3 : ∀ᶠ n in atTop, ∃ v ∈ ({a n} : Set X), v ∈ V := hb V hV
    have h4 : ∀ᶠ n in atTop, a n ∈ V := by
      filter_upwards [h3] with n hn
      obtain ⟨v, hv, hvV⟩ := hn
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact hvV
    exact h4
  · intro ha
    have hsup : setLimsup (fun n => ({a n} : Set X)) ⊆ {b} := by
      intro u hu
      by_contra hne
      rw [Set.mem_singleton_iff] at hne
      obtain ⟨U, V, hU, hV, huU, hbV, hUV⟩ := t2_separation hne
      have h1 : ∃ᶠ n in atTop, ∃ v ∈ ({a n} : Set X), v ∈ U := hu U (hU.mem_nhds huU)
      have h2 : ∀ᶠ n in atTop, a n ∈ V := ha (hV.mem_nhds hbV)
      obtain ⟨n, ⟨v, hv, hvU⟩, hn⟩ := (h1.and_eventually h2).exists
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact Set.disjoint_left.mp hUV hvU hn
    have hb : b ∈ setLiminf (fun n => ({a n} : Set X)) :=
      mem_setLiminf_of_seq _ a (Eventually.of_forall (fun n => rfl)) ha
    refine ⟨Set.Subset.antisymm hsup ?_,
      Set.Subset.antisymm ((setLiminf_subset_setLimsup _).trans hsup) ?_⟩
    · rw [Set.singleton_subset_iff]; exact setLiminf_subset_setLimsup _ hb
    · rw [Set.singleton_subset_iff]; exact hb

lemma EpiConverges.comp {fs : ℕ → E → EReal} (h : EpiConverges fs f) (ns : ℕ → ℕ)
    (hns : Tendsto ns atTop atTop) : EpiConverges (fun k => fs (ns k)) f := by
  obtain ⟨h1, h2⟩ := h
  have hA : setLiminf (fun n => epigraph (fs n)) ⊆ setLiminf (fun k => epigraph (fs (ns k))) := by
    intro u hu V hV
    have h3 : ∀ᶠ n in atTop, ∃ v ∈ epigraph (fs n), v ∈ V := hu V hV
    exact hns.eventually h3
  have hB : setLimsup (fun k => epigraph (fs (ns k))) ⊆ setLimsup (fun n => epigraph (fs n)) := by
    intro u hu V hV
    have h3 : ∃ᶠ k in atTop, ∃ v ∈ epigraph (fs (ns k)), v ∈ V := hu V hV
    exact hns.frequently (p := fun n => ∃ v ∈ epigraph (fs n), v ∈ V) h3
  have hC := setLiminf_subset_setLimsup (fun k => epigraph (fs (ns k)))
  have h1' : setLimsup (fun n => epigraph (fs n)) = epigraph f := h1
  have h2' : setLiminf (fun n => epigraph (fs n)) = epigraph f := h2
  constructor
  · show setLimsup (fun k => epigraph (fs (ns k))) = epigraph f
    apply Set.Subset.antisymm
    · rw [← h1']; exact hB
    · rw [← h2']; exact hA.trans hC
  · show setLiminf (fun k => epigraph (fs (ns k))) = epigraph f
    apply Set.Subset.antisymm
    · rw [← h1']; exact hC.trans hB
    · rw [← h2']; exact hA

lemma epi_const (hf : LowerSemicontinuous f) : EpiConverges (fun _ => f) f := by
  have hcl : IsClosed (epigraph f) := by
    have h : IsClosed {p : E × EReal | f p.1 ≤ p.2} := hf.isClosed_epigraph
    have hc : Continuous (fun p : E × ℝ => (p.1, ((p.2 : ℝ) : EReal))) :=
      continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
    exact h.preimage hc
  have hsup : setLimsup (fun _ : ℕ => epigraph f) = epigraph f := by
    apply Set.Subset.antisymm
    · intro u hu
      rw [← hcl.closure_eq, mem_closure_iff_nhds]
      intro V hV
      have h1 : ∃ᶠ _ in atTop, ∃ v ∈ epigraph f, v ∈ V := hu V hV
      rw [frequently_const] at h1
      obtain ⟨v, hv, hvV⟩ := h1
      exact ⟨v, hvV, hv⟩
    · intro u hu V hV
      show ∃ᶠ _ in atTop, ∃ v ∈ epigraph f, v ∈ V
      rw [frequently_const]
      exact ⟨u, hu, mem_of_mem_nhds hV⟩
  have hinf : setLiminf (fun _ : ℕ => epigraph f) = epigraph f := by
    apply Set.Subset.antisymm
    · intro u hu
      rw [← hcl.closure_eq, mem_closure_iff_nhds]
      intro V hV
      have h1 : ∀ᶠ _ in atTop, ∃ v ∈ epigraph f, v ∈ V := hu V hV
      rw [eventually_const] at h1
      obtain ⟨v, hv, hvV⟩ := h1
      exact ⟨v, hvV, hv⟩
    · intro u hu V hV
      exact Eventually.of_forall (fun _ => ⟨u, hu, mem_of_mem_nhds hV⟩)
  exact ⟨hsup, hinf⟩

/-! ### Epi-convergence implies convergence of proximal points and envelopes -/

lemma epi_unif_lb {fs : ℕ → E → EReal} (hf : ∀ y, ⊥ < f y) (h : epiLiminfSet fs ⊆ epigraph f)
    {K : Set E} (hK : IsCompact K) :
    ∃ M : ℝ, ∀ᶠ n in atTop, ∀ y ∈ K, ((-M : ℝ) : EReal) ≤ fs n y := by
  refine hK.induction_on
    (p := fun S => ∃ M : ℝ, ∀ᶠ n in atTop, ∀ y ∈ S, ((-M : ℝ) : EReal) ≤ fs n y) ?_ ?_ ?_ ?_
  · exact ⟨0, Filter.Eventually.of_forall (fun n y hy => absurd hy (Set.notMem_empty y))⟩
  · intro s t hst ⟨M, hM⟩
    exact ⟨M, hM.mono (fun n hn y hy => hn y (hst hy))⟩
  · intro s t ⟨M1, hM1⟩ ⟨M2, hM2⟩
    refine ⟨max M1 M2, (hM1.and hM2).mono (fun n hn y hy => ?_)⟩
    rcases hy with hy | hy
    · exact le_trans (EReal.coe_le_coe_iff.2 (by linarith [le_max_left M1 M2])) (hn.1 y hy)
    · exact le_trans (EReal.coe_le_coe_iff.2 (by linarith [le_max_right M1 M2])) (hn.2 y hy)
  · intro y0 _
    by_contra hcon
    push_neg at hcon
    have key : ∀ M : ℝ, ((y0, -M) : E × ℝ) ∈ epiLiminfSet fs := by
      intro M V hV
      rcases mem_nhds_prod_iff.1 hV with ⟨t, ht, u, hu, htu⟩
      have hfr := hcon t (mem_nhdsWithin_of_mem_nhds ht) M
      refine hfr.mono (fun n hn => ?_)
      rcases hn with ⟨y, hyt, hy⟩
      exact ⟨(y, -M), le_of_lt hy, htu ⟨hyt, mem_of_mem_nhds hu⟩⟩
    obtain ⟨x, _, hx2⟩ := EReal.lt_iff_exists_real_btwn.1 (hf y0)
    have hmem := h (key (-x))
    have h3 : f y0 ≤ ((-(-x) : ℝ) : EReal) := hmem
    rw [neg_neg] at h3
    exact absurd (lt_of_le_of_lt h3 hx2) (lt_irrefl _)

lemma A7_epi_nonempty {g : E → EReal} (hg : IsProper g) : (epigraph g).Nonempty := by
  obtain ⟨w, hw⟩ := hg.2
  exact ⟨(w, (g w).toReal), EReal.le_coe_toReal (ne_of_lt hw)⟩

lemma A7_recovery {fs : ℕ → E → EReal} (hfs : ∀ n, IsProper (fs n))
    (h : epigraph f ⊆ epiLimsupSet fs) {p : E} {a : ℝ} (hp : f p ≤ (a : EReal)) :
    ∃ ws : ℕ → E, ∃ αs : ℕ → ℝ, (∀ n, fs n (ws n) ≤ ((αs n : ℝ) : EReal)) ∧
      Tendsto ws atTop (𝓝 p) ∧ Tendsto αs atTop (𝓝 a) := by
  have hmem : ((p, a) : E × ℝ) ∈ setLiminf (fun n => epigraph (fs n)) := h hp
  obtain ⟨s, hs, hlim⟩ :=
    setLiminf_seq (fun n => epigraph (fs n)) (fun n => A7_epi_nonempty (hfs n)) hmem
  exact ⟨fun n => (s n).1, fun n => (s n).2, fun n => hs n, hlim.fst_nhds, hlim.snd_nhds⟩

lemma A7_quad_tendsto {lams : ℕ → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hlt : Tendsto lams atTop (𝓝 lam))
    {α : ℕ → ℝ} {a : ℝ} (hα : Tendsto α atTop (𝓝 a)) {ws zs : ℕ → E} {w z : E}
    (hws : Tendsto ws atTop (𝓝 w)) (hzs : Tendsto zs atTop (𝓝 z)) :
    Tendsto (fun n => α n + (2 * lams n)⁻¹ * ‖ws n - zs n‖ ^ 2) atTop
      (𝓝 (a + (2 * lam)⁻¹ * ‖w - z‖ ^ 2)) := by
  have h2 : (2 * lam) ≠ 0 := by positivity
  exact hα.add (((hlt.const_mul 2).inv₀ h2).mul ((hws.sub hzs).norm.pow 2))

lemma A7_env_upper {g : E → EReal} (hg : PLC g) {mu : ℝ} (hmu : 0 < mu) (x w : E) {α : ℝ}
    (hw : g w ≤ (α : EReal)) :
    envR g mu x ≤ α + (2 * mu)⁻¹ * ‖w - x‖ ^ 2 := by
  have h1 := envR_le hg hmu x w
  have h2 : g w + (((2 * mu)⁻¹ * ‖w - x‖ ^ 2 : ℝ) : EReal) ≤
      ((α : ℝ) : EReal) + (((2 * mu)⁻¹ * ‖w - x‖ ^ 2 : ℝ) : EReal) :=
    add_le_add hw le_rfl
  rw [← EReal.coe_add] at h2
  exact EReal.coe_le_coe_iff.1 (h1.trans h2)

lemma A7_lin_lb {fs : ℕ → E → EReal} (hfs : ∀ n, PLC (fs n)) (hf : PLC f)
    (hepi : EpiConverges fs f) (p : E) (hp : f p ≠ ⊤) :
    ∃ A B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, ∀ y, ((-A - B * ‖y - p‖ : ℝ) : EReal) ≤ fs n y := by
  obtain ⟨ws, αs, hwα, hws, hαs⟩ :=
    A7_recovery (fun n => (hfs n).proper) hepi.2.symm.subset (EReal.le_coe_toReal hp)
  obtain ⟨M, hM⟩ := epi_unif_lb hf.proper.1 hepi.1.subset (isCompact_closedBall p 2)
  refine ⟨M + max (M + ((f p).toReal + 1)) 0, max (M + ((f p).toReal + 1)) 0,
    le_max_right _ _, ?_⟩
  have hw1 : ∀ᶠ n in atTop, dist (ws n) p < 1 := Metric.tendsto_nhds.1 hws 1 one_pos
  have hα1 : ∀ᶠ n in atTop, αs n < (f p).toReal + 1 :=
    hαs.eventually (eventually_lt_nhds (lt_add_one _))
  filter_upwards [hM, hw1, hα1] with n hMn hwn hαn
  have hball : ∀ y ∈ Metric.closedBall (ws n) 1, ((-M : ℝ) : EReal) ≤ fs n y := by
    intro y hy
    apply hMn y
    rw [Metric.mem_closedBall] at hy ⊢
    linarith [dist_triangle y (ws n) p]
  have hll := linear_lower_bound (hfs n).convex (hwα n) hball
  intro y
  refine le_trans ?_ (hll y)
  apply EReal.coe_le_coe_iff.2
  have h0 : 0 ≤ M + αs n := by
    have h1 := (hball (ws n) (Metric.mem_closedBall_self zero_le_one)).trans (hwα n)
    have h2 := EReal.coe_le_coe_iff.1 h1
    linarith
  have htri : ‖y - ws n‖ ≤ ‖y - p‖ + 1 := by
    have h1 : ‖y - ws n‖ ≤ ‖y - p‖ + ‖p - ws n‖ := norm_sub_le_norm_sub_add_norm_sub y p (ws n)
    have h2 : ‖p - ws n‖ = dist (ws n) p := by rw [dist_eq_norm, norm_sub_rev]
    linarith
  have hB : M + αs n ≤ max (M + ((f p).toReal + 1)) 0 :=
    le_trans (by linarith) (le_max_left _ _)
  have hB0 : 0 ≤ max (M + ((f p).toReal + 1)) 0 := le_max_right _ _
  have k1 := mul_le_mul_of_nonneg_left htri h0
  have k2 := mul_le_mul_of_nonneg_right hB (by positivity : (0:ℝ) ≤ ‖y - p‖ + 1)
  nlinarith

lemma A7_quad_bound {d t s a A B C k0 k : ℝ} (hk0 : 0 < k0) (hk : k0 ≤ k) (hB : 0 ≤ B)
    (hdt : d ≤ t + s) (ha : -A - B * d ≤ a) (hC : a + k * t ^ 2 ≤ C) :
    d ≤ 1 + (|C + A + B * s| + B) / k0 + s := by
  have h1 : k0 * t ^ 2 ≤ C + A + B * s + B * t := by
    have e1 : k0 * t ^ 2 ≤ k * t ^ 2 := mul_le_mul_of_nonneg_right hk (by positivity)
    have e2 : B * d ≤ B * (t + s) := mul_le_mul_of_nonneg_left hdt hB
    nlinarith
  have hfrac : 0 ≤ (|C + A + B * s| + B) / k0 := by positivity
  have h2 : t ≤ 1 + (|C + A + B * s| + B) / k0 := by
    rcases le_or_gt t 1 with h | h
    · linarith
    · have h3 : k0 * t ^ 2 ≤ (|C + A + B * s| + B) * t := by
        have := le_abs_self (C + A + B * s)
        have : |C + A + B * s| ≤ |C + A + B * s| * t := by
          nlinarith [abs_nonneg (C + A + B * s)]
        nlinarith
      have h4 : k0 * t ≤ |C + A + B * s| + B := by
        have ht0 : 0 < t := by linarith
        nlinarith
      have h5 : t ≤ (|C + A + B * s| + B) / k0 := by
        rw [le_div_iff₀ hk0]; linarith
      linarith
  linarith

lemma A7_bdd {lams : ℕ → ℝ} {lam : ℝ} (hlam : 0 < lam) (hlams : ∀ n, 0 < lams n)
    (hlt : Tendsto lams atTop (𝓝 lam)) {zs : ℕ → E} {z : E} (hz : Tendsto zs atTop (𝓝 z))
    (P : ℕ → E) (a : ℕ → ℝ) (p : E) {A B C : ℝ} (hB : 0 ≤ B)
    (hlow : ∀ᶠ n in atTop, -A - B * ‖P n - p‖ ≤ a n)
    (hup : ∀ᶠ n in atTop, a n + (2 * lams n)⁻¹ * ‖P n - zs n‖ ^ 2 ≤ C) :
    ∃ R : ℝ, ∀ᶠ n in atTop, ‖P n - p‖ ≤ R ∧ |a n| ≤ R := by
  set s := 1 + ‖z - p‖ with hs
  set R0 := 1 + (|C + A + B * s| + B) / (4 * lam)⁻¹ + s with hR0
  refine ⟨max R0 (|C| + |A| + B * |R0|), ?_⟩
  have hl2 : ∀ᶠ n in atTop, lams n < 2 * lam :=
    hlt.eventually (eventually_lt_nhds (by linarith))
  have hz1 : ∀ᶠ n in atTop, dist (zs n) z < 1 := Metric.tendsto_nhds.1 hz 1 one_pos
  filter_upwards [hlow, hup, hl2, hz1] with n hlown hupn hl2n hz1n
  have hk0 : 0 < (4 * lam)⁻¹ := by positivity
  have hk : (4 * lam)⁻¹ ≤ (2 * lams n)⁻¹ :=
    inv_anti₀ (by linarith [hlams n]) (by linarith)
  have hdt : ‖P n - p‖ ≤ ‖P n - zs n‖ + s := by
    have h1 : ‖P n - p‖ ≤ ‖P n - zs n‖ + ‖zs n - p‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h2 : ‖zs n - p‖ ≤ ‖zs n - z‖ + ‖z - p‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h3 : ‖zs n - z‖ = dist (zs n) z := (dist_eq_norm _ _).symm
    linarith
  have hd := A7_quad_bound hk0 hk hB hdt hlown hupn
  have hkt : 0 ≤ (2 * lams n)⁻¹ * ‖P n - zs n‖ ^ 2 := by
    have := hlams n; positivity
  refine ⟨le_trans hd (le_max_left _ _), ?_⟩
  rw [abs_le]
  constructor
  · have e1 : B * ‖P n - p‖ ≤ B * |R0| :=
      mul_le_mul_of_nonneg_left (hd.trans (le_abs_self _)) hB
    have := le_abs_self A
    have := abs_nonneg C
    have := le_max_right R0 (|C| + |A| + B * |R0|)
    linarith
  · have := le_abs_self C
    have := abs_nonneg A
    have : 0 ≤ B * |R0| := mul_nonneg hB (abs_nonneg _)
    have := le_max_right R0 (|C| + |A| + B * |R0|)
    linarith

lemma A7_subseq {fs : ℕ → E → EReal} (hf : PLC f) (hepi1 : epiLiminfSet fs ⊆ epigraph f)
    {lams : ℕ → ℝ} {lam : ℝ} (hlam : 0 < lam) (hlt : Tendsto lams atTop (𝓝 lam))
    {zs : ℕ → E} {z : E} (hz : Tendsto zs atTop (𝓝 z))
    (P : ℕ → E) (a : ℕ → ℝ) (hPa : ∀ n, fs n (P n) ≤ ((a n : ℝ) : EReal))
    (β : ℕ → ℝ) (hβ : ∀ n, a n + (2 * lams n)⁻¹ * ‖P n - zs n‖ ^ 2 ≤ β n)
    (hβlim : Tendsto β atTop (𝓝 (envR f lam z)))
    {S : Set (E × ℝ)} (hS : Bornology.IsBounded S) (hPS : ∀ᶠ n in atTop, (P n, a n) ∈ S)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
    ∃ ms : ℕ → ℕ, Tendsto (fun k => (P (ns (ms k)),
      a (ns (ms k)) + (2 * lams (ns (ms k)))⁻¹ * ‖P (ns (ms k)) - zs (ns (ms k))‖ ^ 2))
      atTop (𝓝 (proxPt f lam z, envR f lam z)) := by
  have hfreq : ∃ᶠ k in atTop, (fun k => (P (ns k), a (ns k))) k ∈ S :=
    (hns.eventually hPS).frequently
  obtain ⟨q, _, ms, hms, hlim⟩ := tendsto_subseq_of_frequently_bounded hS hfreq
  obtain ⟨p', a'⟩ := q
  have hN : Tendsto (fun k => ns (ms k)) atTop atTop := hns.comp hms.tendsto_atTop
  have hlim' : Tendsto (fun k => (P (ns (ms k)), a (ns (ms k)))) atTop (𝓝 (p', a')) := hlim
  have hP' : Tendsto (fun k => P (ns (ms k))) atTop (𝓝 p') := hlim'.fst_nhds
  have ha' : Tendsto (fun k => a (ns (ms k))) atTop (𝓝 a') := hlim'.snd_nhds
  have hmem : ((p', a') : E × ℝ) ∈ epiLiminfSet fs :=
    mem_setLimsup_of_seq (fun n => epigraph (fs n)) (fun k => ns (ms k)) hN
      (fun k => (P (ns (ms k)), a (ns (ms k))))
      (Eventually.of_forall (fun k => hPa (ns (ms k)))) hlim'
  have hfp' : f p' ≤ ((a' : ℝ) : EReal) := hepi1 hmem
  have hel := A7_quad_tendsto hlam (hlt.comp hN) ha' hP' (hz.comp hN)
  have hle : a' + (2 * lam)⁻¹ * ‖p' - z‖ ^ 2 ≤ envR f lam z :=
    le_of_tendsto_of_tendsto' hel (hβlim.comp hN) (fun k => hβ (ns (ms k)))
  have hprox : p' ∈ proximalMapping f lam z := by
    refine ⟨lt_of_le_of_lt hfp' (EReal.coe_lt_top a'), fun w => ?_⟩
    have h1 := envR_le hf hlam z w
    have e1 : (((2 * lam)⁻¹ : ℝ) : EReal) * ((‖p' - z‖ : ℝ) : EReal) ^ 2 =
        (((2 * lam)⁻¹ * ‖p' - z‖ ^ 2 : ℝ) : EReal) := by norm_cast
    have e2 : (((2 * lam)⁻¹ : ℝ) : EReal) * ((‖w - z‖ : ℝ) : EReal) ^ 2 =
        (((2 * lam)⁻¹ * ‖w - z‖ ^ 2 : ℝ) : EReal) := by norm_cast
    show f p' + (((2 * lam)⁻¹ : ℝ) : EReal) * ((‖p' - z‖ : ℝ) : EReal) ^ 2 ≤
      f w + (((2 * lam)⁻¹ : ℝ) : EReal) * ((‖w - z‖ : ℝ) : EReal) ^ 2
    rw [e1, e2]
    calc f p' + (((2 * lam)⁻¹ * ‖p' - z‖ ^ 2 : ℝ) : EReal)
        ≤ ((a' : ℝ) : EReal) + (((2 * lam)⁻¹ * ‖p' - z‖ ^ 2 : ℝ) : EReal) :=
          add_le_add hfp' le_rfl
      _ = ((a' + (2 * lam)⁻¹ * ‖p' - z‖ ^ 2 : ℝ) : EReal) := (EReal.coe_add _ _).symm
      _ ≤ ((envR f lam z : ℝ) : EReal) := EReal.coe_le_coe_iff.2 hle
      _ ≤ _ := h1
  have hpp : proxPt f lam z = p' := proxPt_eq_of_mem hf hlam hprox
  have hfp := f_proxPt_coe hf hlam z
  rw [hpp] at hfp
  have hfa : (f p').toReal ≤ a' := by
    rw [hfp] at hfp'
    exact EReal.coe_le_coe_iff.1 hfp'
  have ha_eq : a' + (2 * lam)⁻¹ * ‖p' - z‖ ^ 2 = envR f lam z := by
    apply le_antisymm hle
    have : envR f lam z = (f p').toReal + (2 * lam)⁻¹ * ‖p' - z‖ ^ 2 := by
      unfold envR; rw [hpp]
    linarith
  refine ⟨ms, ?_⟩
  rw [hpp, ← ha_eq]
  exact hP'.prodMk_nhds hel

lemma epi_prox_conv {fs : ℕ → E → EReal} (hfs : ∀ n, PLC (fs n)) (hf : PLC f)
    (hepi : EpiConverges fs f) {lams : ℕ → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hlams : ∀ n, 0 < lams n) (hlt : Tendsto lams atTop (𝓝 lam)) {zs : ℕ → E} {z : E}
    (hz : Tendsto zs atTop (𝓝 z)) :
    Tendsto (fun n => proxPt (fs n) (lams n) (zs n)) atTop (𝓝 (proxPt f lam z)) ∧
    Tendsto (fun n => envR (fs n) (lams n) (zs n)) atTop (𝓝 (envR f lam z)) := by
  set P : ℕ → E := fun n => proxPt (fs n) (lams n) (zs n) with hPdef
  set a : ℕ → ℝ := fun n => (fs n (P n)).toReal with hadef
  have hPa : ∀ n, fs n (P n) ≤ ((a n : ℝ) : EReal) :=
    fun n => le_of_eq (f_proxPt_coe (hfs n) (hlams n) (zs n))
  have hfp := f_proxPt_coe hf hlam z
  obtain ⟨ws, αs, hwα, hws, hαs⟩ :=
    A7_recovery (fun n => (hfs n).proper) hepi.2.symm.subset (le_of_eq hfp)
  have hβ : ∀ n, a n + (2 * lams n)⁻¹ * ‖P n - zs n‖ ^ 2 ≤
      αs n + (2 * lams n)⁻¹ * ‖ws n - zs n‖ ^ 2 :=
    fun n => A7_env_upper (hfs n) (hlams n) (zs n) (ws n) (hwα n)
  have hβlim : Tendsto (fun n => αs n + (2 * lams n)⁻¹ * ‖ws n - zs n‖ ^ 2) atTop
      (𝓝 (envR f lam z)) := A7_quad_tendsto hlam hlt hαs hws hz
  have hpt : f (proxPt f lam z) ≠ ⊤ := by rw [hfp]; exact EReal.coe_ne_top _
  obtain ⟨A, B, hB, hAB⟩ := A7_lin_lb hfs hf hepi (proxPt f lam z) hpt
  have hlow : ∀ᶠ n in atTop, -A - B * ‖P n - proxPt f lam z‖ ≤ a n :=
    hAB.mono (fun n hn => EReal.coe_le_coe_iff.1 ((hn (P n)).trans (hPa n)))
  have hup : ∀ᶠ n in atTop, a n + (2 * lams n)⁻¹ * ‖P n - zs n‖ ^ 2 ≤ envR f lam z + 1 :=
    (hβlim.eventually (eventually_le_nhds (lt_add_one _))).mono
      (fun n hn => (hβ n).trans hn)
  obtain ⟨R, hR⟩ := A7_bdd hlam hlams hlt hz P a (proxPt f lam z) hB hlow hup
  have hS : Bornology.IsBounded
      (Metric.closedBall (proxPt f lam z) R ×ˢ Metric.closedBall (0:ℝ) R) :=
    Metric.isBounded_closedBall.prod Metric.isBounded_closedBall
  have hPS : ∀ᶠ n in atTop,
      (P n, a n) ∈ Metric.closedBall (proxPt f lam z) R ×ˢ Metric.closedBall (0:ℝ) R :=
    hR.mono (fun n hn => ⟨by rw [Metric.mem_closedBall, dist_eq_norm]; exact hn.1,
      by rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hn.2⟩)
  have hmain : Tendsto (fun n => (P n, a n + (2 * lams n)⁻¹ * ‖P n - zs n‖ ^ 2)) atTop
      (𝓝 (proxPt f lam z, envR f lam z)) :=
    tendsto_of_subseq_tendsto (fun ns hns =>
      A7_subseq hf hepi.1.subset hlam hlt hz P a hPa _ hβ hβlim hS hPS ns hns)
  exact ⟨hmain.fst_nhds, hmain.snd_nhds⟩

lemma A8_unif {Y : Type*} [PseudoMetricSpace Y] (F : ℕ → E → Y) (G : E → Y)
    (hF : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ zs : ℕ → E, ∀ z : E, Tendsto zs atTop (𝓝 z) →
      Tendsto (fun j => F (ψ j) (zs j)) atTop (𝓝 (G z)))
    (hG : ∀ zs : ℕ → E, ∀ z : E, Tendsto zs atTop (𝓝 z) →
      Tendsto (fun j => G (zs j)) atTop (𝓝 (G z)))
    (R ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x : E, ‖x‖ ≤ R → dist (F n x) (G x) < ε := by
  by_contra hcon
  push_neg at hcon
  have hfreq : ∃ᶠ n in atTop, ∃ x : E, ‖x‖ ≤ R ∧ ε ≤ dist (F n x) (G x) := by
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨n, hn, x, hx1, hx2⟩ := hcon N
    exact ⟨n, hn, x, hx1, hx2⟩
  obtain ⟨ns, hns, hP⟩ := Filter.extraction_of_frequently_atTop hfreq
  choose xs hxsR hxsd using hP
  have hbdd : ∀ k, xs k ∈ Metric.closedBall (0 : E) R := by
    intro k
    rw [Metric.mem_closedBall, _root_.dist_zero_right]
    exact hxsR k
  obtain ⟨xbar, -, ms, hms, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hbdd
  have h1 := hF (ns ∘ ms) (hns.comp hms) (xs ∘ ms) xbar hlim
  have h2 := hG (xs ∘ ms) xbar hlim
  have h3 := h1.dist h2
  rw [_root_.dist_self] at h3
  have h4 : ∀ j, ε ≤ dist (F ((ns ∘ ms) j) ((xs ∘ ms) j)) (G ((xs ∘ ms) j)) :=
    fun j => hxsd (ms j)
  have h5 := ge_of_tendsto' h3 h4
  linarith

lemma final_part {fs : ℕ → E → EReal} (hfs : ∀ n, PLC (fs n)) (hf : PLC f)
    (hepi : EpiConverges fs f) {lams : ℕ → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hlams : ∀ n, 0 < lams n) (hlt : Tendsto lams atTop (𝓝 lam)) :
    UniformlyConvergesOnBounded (fun n => proximalMapping (fs n) (lams n))
      (proximalMapping f lam) ∧
    UniformlyConvergesOnBoundedEReal (fun n => moreauEnvelope (fs n) (lams n))
      (moreauEnvelope f lam) := by
  have hPconv : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ zs : ℕ → E, ∀ z : E, Tendsto zs atTop (𝓝 z) →
      Tendsto (fun j => proxPt (fs (ψ j)) (lams (ψ j)) (zs j)) atTop (𝓝 (proxPt f lam z)) ∧
      Tendsto (fun j => envR (fs (ψ j)) (lams (ψ j)) (zs j)) atTop (𝓝 (envR f lam z)) := by
    intro ψ hψ zs z hz
    have hψt : Tendsto ψ atTop atTop := hψ.tendsto_atTop
    exact epi_prox_conv (fs := fun j => fs (ψ j)) (fun j => hfs (ψ j)) hf (EpiConverges.comp hepi ψ hψt)
      hlam (fun j => hlams (ψ j)) (hlt.comp hψt) hz
  have hGconv : ∀ zs : ℕ → E, ∀ z : E, Tendsto zs atTop (𝓝 z) →
      Tendsto (fun j => proxPt f lam (zs j)) atTop (𝓝 (proxPt f lam z)) ∧
      Tendsto (fun j => envR f lam (zs j)) atTop (𝓝 (envR f lam z)) := by
    intro zs z hz
    exact epi_prox_conv (fs := fun _ => f) (fun _ => hf) hf (epi_const hf.lsc) hlam
      (fun _ => hlam) tendsto_const_nhds hz
  have U1 := A8_unif (fun n x => proxPt (fs n) (lams n) x) (fun x => proxPt f lam x)
    (fun ψ hψ zs z hz => (hPconv ψ hψ zs z hz).1) (fun zs z hz => (hGconv zs z hz).1)
  have U2 := A8_unif (fun n x => envR (fs n) (lams n) x) (fun x => envR f lam x)
    (fun ψ hψ zs z hz => (hPconv ψ hψ zs z hz).2) (fun zs z hz => (hGconv zs z hz).2)
  refine ⟨fun R _hR => ?_, fun R _hR => ?_⟩
  · intro ε hε ρ _hρ
    obtain ⟨N, hN⟩ := U1 R ε hε
    refine ⟨N, fun n hn x hx => ?_⟩
    have hx' : ‖x‖ ≤ R := hx
    have hd : dist (proxPt (fs n) (lams n) x) (proxPt f lam x) < ε := hN n hn x hx'
    constructor
    · rintro y ⟨hy, -⟩
      have hy' : proxPt (fs n) (lams n) x = y := proxPt_eq_of_mem (hfs n) (hlams n) hy
      subst hy'
      exact ⟨proxPt f lam x, proxPt_mem hf hlam x, hd⟩
    · rintro y ⟨hy, -⟩
      have hy' : proxPt f lam x = y := proxPt_eq_of_mem hf hlam hy
      subst hy'
      refine ⟨proxPt (fs n) (lams n) x, proxPt_mem (hfs n) (hlams n) x, ?_⟩
      rw [_root_.dist_comm]
      exact hd
  · intro ε hε
    obtain ⟨N, hN⟩ := U2 R ε hε
    refine ⟨N, fun n hn x hx => ?_⟩
    have hd : dist (envR (fs n) (lams n) x) (envR f lam x) < ε := hN n hn x hx
    rw [Real.dist_eq] at hd
    have h1 := abs_sub_lt_iff.mp hd
    show moreauEnvelope f lam x - (ε : EReal) ≤ moreauEnvelope (fs n) (lams n) x ∧
      moreauEnvelope (fs n) (lams n) x ≤ moreauEnvelope f lam x + (ε : EReal)
    rw [moreau_eq (hfs n) (hlams n) x, moreau_eq hf hlam x]
    constructor
    · rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
      linarith
    · rw [← EReal.coe_add, EReal.coe_le_coe_iff]
      linarith

/-! ### Converse directions -/

lemma A9_toReal_tendsto {fs : ℕ → E → EReal} {lam : ℝ}
    (hP : ∀ x, Tendsto (fun n => proxPt (fs n) lam x) atTop (𝓝 (proxPt f lam x)))
    (he : ∀ x, Tendsto (fun n => envR (fs n) lam x) atTop (𝓝 (envR f lam x)))
    (z : E) :
    Tendsto (fun n => (fs n (proxPt (fs n) lam z)).toReal) atTop
      (𝓝 ((f (proxPt f lam z)).toReal)) := by
  have h1 : (fun n => (fs n (proxPt (fs n) lam z)).toReal) =
      fun n => envR (fs n) lam z - (2 * lam)⁻¹ * ‖proxPt (fs n) lam z - z‖ ^ 2 := by
    funext n; unfold envR; ring
  have h2 : (f (proxPt f lam z)).toReal =
      envR f lam z - (2 * lam)⁻¹ * ‖proxPt f lam z - z‖ ^ 2 := by
    unfold envR; ring
  rw [h1, h2]
  exact (he z).sub ((((hP z).sub_const z).norm.pow 2).const_mul _)

lemma A9_prox_shift (hf : PLC f) {lam : ℝ} (hlam : 0 < lam) {p v : E} (hcs : CSub f p v) :
    proxPt f lam (p + lam • v) = p := by
  apply proxPt_eq_of_mem hf hlam
  rw [mem_prox_iff hf hlam]
  have : lam⁻¹ • (p + lam • v - p) = v := by
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
  rw [this]; exact hcs

lemma A9_limsup_sub {fs : ℕ → E → EReal} (hfs : ∀ n, PLC (fs n)) (hf : PLC f) {lam : ℝ}
    (hlam : 0 < lam)
    (hP : ∀ x, Tendsto (fun n => proxPt (fs n) lam x) atTop (𝓝 (proxPt f lam x)))
    (he : ∀ x, Tendsto (fun n => envR (fs n) lam x) atTop (𝓝 (envR f lam x))) :
    setLimsup (fun n => epigraph (fs n)) ⊆ epigraph f := by
  rintro ⟨x, a⟩ hu
  obtain ⟨ns, hns, s, hsA, hsu⟩ := setLimsup_seq _ hu
  have hns_t : Tendsto ns atTop atTop := hns.tendsto_atTop
  have hs1 : Tendsto (fun k => (s k).1) atTop (𝓝 x) :=
    ((continuous_fst.tendsto (x, a)).comp hsu)
  have hs2 : Tendsto (fun k => (s k).2) atTop (𝓝 a) :=
    ((continuous_snd.tendsto (x, a)).comp hsu)
  -- key claim
  have key : ∀ p' v', CSub f p' v' → (f p').toReal + inner ℝ v' (x - p') ≤ a := by
    intro p' v' hcs
    set z := p' + lam • v' with hz
    have hPz : proxPt f lam z = p' := A9_prox_shift hf hlam hcs
    have hv' : v' = lam⁻¹ • (z - p') := by
      rw [hz, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
    have hineq : ∀ k, (fs (ns k) (proxPt (fs (ns k)) lam z)).toReal
        + inner ℝ (lam⁻¹ • (z - proxPt (fs (ns k)) lam z)) ((s k).1 - proxPt (fs (ns k)) lam z)
        ≤ (s k).2 := by
      intro k
      have hcsn : CSub (fs (ns k)) (proxPt (fs (ns k)) lam z)
          (lam⁻¹ • (z - proxPt (fs (ns k)) lam z)) :=
        (mem_prox_iff (hfs (ns k)) hlam).1 (proxPt_mem (hfs (ns k)) hlam z)
      have h1 := hcsn.2 (s k).1
      have h2 : fs (ns k) (s k).1 ≤ ((s k).2 : EReal) := hsA k
      have h3 := f_proxPt_coe (hfs (ns k)) hlam z
      rw [h3] at h1
      have h4 := h1.trans h2
      exact_mod_cast h4
    have hA := (A9_toReal_tendsto hP he z).comp hns_t
    have hB := (hP z).comp hns_t
    rw [hPz] at hA hB
    have hv : Tendsto (fun k => lam⁻¹ • (z - proxPt (fs (ns k)) lam z)) atTop (𝓝 v') := by
      rw [hv']
      exact (tendsto_const_nhds.sub hB).const_smul lam⁻¹
    have hL : Tendsto (fun k => (fs (ns k) (proxPt (fs (ns k)) lam z)).toReal
        + inner ℝ (lam⁻¹ • (z - proxPt (fs (ns k)) lam z)) ((s k).1 - proxPt (fs (ns k)) lam z))
        atTop (𝓝 ((f p').toReal + inner ℝ v' (x - p'))) :=
      hA.add (hv.inner (hs1.sub hB))
    exact le_of_tendsto_of_tendsto' hL hs2 hineq
  -- conclude
  show f x ≤ (a : EReal)
  by_contra hcon
  push_neg at hcon
  obtain ⟨μ, hμ, hb⟩ := small_mu_bound hf x a hcon
  have hcs : CSub f (proxPt f μ x) (μ⁻¹ • (x - proxPt f μ x)) :=
    (mem_prox_iff hf hμ).1 (proxPt_mem hf hμ x)
  have hk := key _ _ hcs
  have hb' := hb (proxPt f μ x)
  rw [f_proxPt_coe hf hμ x] at hb'
  have hin : inner ℝ (μ⁻¹ • (x - proxPt f μ x)) (x - proxPt f μ x)
      = μ⁻¹ * ‖proxPt f μ x - x‖ ^ 2 := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, norm_sub_rev]
  rw [hin] at hk
  have hb'' : a < (f (proxPt f μ x)).toReal + μ⁻¹ * ‖proxPt f μ x - x‖ ^ 2 := by
    exact_mod_cast hb'
  linarith

lemma A9_step1 {fs : ℕ → E → EReal} (hfs : ∀ n, PLC (fs n)) (hf : PLC f) {lam : ℝ}
    (hlam : 0 < lam)
    (hP : ∀ x, Tendsto (fun n => proxPt (fs n) lam x) atTop (𝓝 (proxPt f lam x)))
    (he : ∀ x, Tendsto (fun n => envR (fs n) lam x) atTop (𝓝 (envR f lam x)))
    {x v : E} {a : ℝ} (hcs : CSub f x v) (hxa : f x ≤ (a : EReal)) :
    (x, a) ∈ setLiminf (fun n => epigraph (fs n)) := by
  set z := x + lam • v with hz
  have hPz : proxPt f lam z = x := A9_prox_shift hf hlam hcs
  have hfx : f x = (((f x).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal hcs.1 (hf.proper.1 x).ne').symm
  have hle : (f x).toReal ≤ a := by
    rw [hfx] at hxa
    exact_mod_cast hxa
  apply mem_setLiminf_of_seq _
    (fun n => (proxPt (fs n) lam z, (fs n (proxPt (fs n) lam z)).toReal + (a - (f x).toReal)))
  · apply Filter.Eventually.of_forall
    intro n
    show fs n (proxPt (fs n) lam z)
      ≤ (((fs n (proxPt (fs n) lam z)).toReal + (a - (f x).toReal) : ℝ) : EReal)
    calc fs n (proxPt (fs n) lam z) = (((fs n (proxPt (fs n) lam z)).toReal : ℝ) : EReal) :=
          f_proxPt_coe (hfs n) hlam z
      _ ≤ (((fs n (proxPt (fs n) lam z)).toReal + (a - (f x).toReal) : ℝ) : EReal) := by
          rw [EReal.coe_le_coe_iff]; linarith
  · have hA := A9_toReal_tendsto hP he z
    have hB := hP z
    rw [hPz] at hA hB
    have hA' : Tendsto (fun n => (fs n (proxPt (fs n) lam z)).toReal + (a - (f x).toReal))
        atTop (𝓝 a) := by
      have := hA.add_const (a - (f x).toReal)
      rwa [add_sub_cancel] at this
    exact hB.prodMk_nhds hA'

lemma A9_liminf_sup {fs : ℕ → E → EReal} (hfs : ∀ n, PLC (fs n)) (hf : PLC f) {lam : ℝ}
    (hlam : 0 < lam)
    (hP : ∀ x, Tendsto (fun n => proxPt (fs n) lam x) atTop (𝓝 (proxPt f lam x)))
    (he : ∀ x, Tendsto (fun n => envR (fs n) lam x) atTop (𝓝 (envR f lam x))) :
    epigraph f ⊆ setLiminf (fun n => epigraph (fs n)) := by
  rintro ⟨x, a⟩ hu
  have hxa : f x ≤ (a : EReal) := hu
  have hfin : f x ≠ ⊤ := by
    intro h
    rw [h] at hxa
    exact absurd hxa (by simp)
  have hchoice : ∀ k : ℕ, ∃ μ > 0, ‖proxPt f μ x - x‖ < 1 / ((k : ℝ) + 1) := fun k =>
    prox_close hf x hfin _ (by positivity)
  choose μs hμs hclose using hchoice
  have hmem : ∀ k, (proxPt f (μs k) x, a) ∈ setLiminf (fun n => epigraph (fs n)) := by
    intro k
    apply A9_step1 hfs hf hlam hP he ((mem_prox_iff hf (hμs k)).1 (proxPt_mem hf (hμs k) x))
    have h1 := envR_le hf (hμs k) x x
    have h0 : ((2 * μs k)⁻¹ * ‖x - x‖ ^ 2 : ℝ) = 0 := by simp
    rw [h0, EReal.coe_zero, add_zero] at h1
    have h2 : ((envR f (μs k) x : ℝ) : EReal) ≤ (a : EReal) := h1.trans hxa
    rw [EReal.coe_le_coe_iff] at h2
    have h3 : (f (proxPt f (μs k) x)).toReal ≤ envR f (μs k) x := by
      unfold envR
      have : 0 ≤ (2 * μs k)⁻¹ * ‖proxPt f (μs k) x - x‖ ^ 2 := by
        have := hμs k
        positivity
      linarith
    rw [f_proxPt_coe hf (hμs k) x]
    exact_mod_cast h3.trans h2
  have hconv : Tendsto (fun k => proxPt f (μs k) x) atTop (𝓝 x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun k => norm_nonneg _) (fun k => (hclose k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  exact (isClosed_setLiminf _).mem_of_tendsto (hconv.prodMk_nhds tendsto_const_nhds)
    (Filter.Eventually.of_forall hmem)

lemma c_to_a {fs : ℕ → E → EReal} (hfs : ∀ n, PLC (fs n)) (hf : PLC f) {lam : ℝ}
    (hlam : 0 < lam)
    (hP : ∀ x, Tendsto (fun n => proxPt (fs n) lam x) atTop (𝓝 (proxPt f lam x)))
    (he : ∀ x, Tendsto (fun n => envR (fs n) lam x) atTop (𝓝 (envR f lam x))) :
    EpiConverges fs f := by
  have hI := A9_limsup_sub hfs hf hlam hP he
  have hII := A9_liminf_sup hfs hf hlam hP he
  have h3 := setLiminf_subset_setLimsup (fun n => epigraph (fs n))
  refine ⟨?_, ?_⟩
  · unfold epiLiminfSet
    exact Set.Subset.antisymm hI (hII.trans h3)
  · unfold epiLimsupSet
    exact Set.Subset.antisymm (h3.trans hI) hII

lemma A10_graph_iff {g : E → EReal} (hg : PLC g) {lam : ℝ} (hlam : 0 < lam) (x v : E) :
    (x, v) ∈ graph (subdifferential g) ↔ proxPt g lam (x + lam • v) = x := by
  show v ∈ subdifferential g x ↔ _
  rw [mem_subdiff_iff hg]
  have key : lam⁻¹ • ((x + lam • v) - x) = v := by
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
  constructor
  · intro hx
    apply proxPt_eq_of_mem hg hlam
    rw [mem_prox_iff hg hlam, key]
    exact hx
  · intro hx
    have hm := proxPt_mem hg hlam (x + lam • v)
    rw [hx, mem_prox_iff hg hlam, key] at hm
    exact hm

lemma A10_graph_mem {g : E → EReal} (hg : PLC g) {lam : ℝ} (hlam : 0 < lam) (z : E) :
    (proxPt g lam z, lam⁻¹ • (z - proxPt g lam z)) ∈ graph (subdifferential g) := by
  show lam⁻¹ • (z - proxPt g lam z) ∈ subdifferential g (proxPt g lam z)
  rw [mem_subdiff_iff hg]
  exact (mem_prox_iff hg hlam).mp (proxPt_mem hg hlam z)

lemma gc_to_pc {fs : ℕ → E → EReal} (hfs : ∀ n, PLC (fs n)) (hf : PLC f) {lam : ℝ}
    (hlam : 0 < lam)
    (h : graph (subdifferential f) ⊆ graphSetLiminf (fun n => subdifferential (fs n))) :
    ∀ z, Tendsto (fun n => proxPt (fs n) lam z) atTop (𝓝 (proxPt f lam z)) := by
  intro z
  set p := proxPt f lam z with hp
  set v := lam⁻¹ • (z - p) with hv
  have hmem : (p, v) ∈ graph (subdifferential f) := A10_graph_mem hf hlam z
  have hlim : (p, v) ∈ setLiminf (fun n => graph (subdifferential (fs n))) := h hmem
  have hne : ∀ n, (graph (subdifferential (fs n))).Nonempty := fun n =>
    ⟨_, A10_graph_mem (hfs n) hlam 0⟩
  obtain ⟨s, hs, hst⟩ := setLiminf_seq (fun n => graph (subdifferential (fs n))) hne hlim
  have hz : p + lam • v = z := by
    rw [hv, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul, add_sub_cancel]
  have h1 : Tendsto (fun n => (s n).1) atTop (𝓝 p) := (continuous_fst.tendsto _).comp hst
  have h2 : Tendsto (fun n => (s n).2) atTop (𝓝 v) := (continuous_snd.tendsto _).comp hst
  have hzs_t : Tendsto (fun n => (s n).1 + lam • (s n).2) atTop (𝓝 z) := by
    rw [← hz]
    exact h1.add (h2.const_smul lam)
  have hq : ∀ n, proxPt (fs n) lam ((s n).1 + lam • (s n).2) = (s n).1 := fun n =>
    (A10_graph_iff (hfs n) hlam (s n).1 (s n).2).mp (hs n)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ n, ‖proxPt (fs n) lam z - p‖
      ≤ ‖z - ((s n).1 + lam • (s n).2)‖ + ‖(s n).1 - p‖ := by
    intro n
    calc ‖proxPt (fs n) lam z - p‖
        = ‖(proxPt (fs n) lam z - proxPt (fs n) lam ((s n).1 + lam • (s n).2))
            + ((s n).1 - p)‖ := by
          rw [hq n]; congr 1; abel
      _ ≤ ‖proxPt (fs n) lam z - proxPt (fs n) lam ((s n).1 + lam • (s n).2)‖
            + ‖(s n).1 - p‖ := norm_add_le _ _
      _ ≤ ‖z - ((s n).1 + lam • (s n).2)‖ + ‖(s n).1 - p‖ := by
          gcongr
          exact prox_nonexp (hfs n) hlam z _
  apply squeeze_zero (fun n => norm_nonneg _) hb
  have h3 : Tendsto (fun n => ‖z - ((s n).1 + lam • (s n).2)‖) atTop (𝓝 0) := by
    have := tendsto_iff_norm_sub_tendsto_zero.mp hzs_t
    simpa only [norm_sub_rev] using this
  have h4 := tendsto_iff_norm_sub_tendsto_zero.mp h1
  simpa using h3.add h4

lemma pc_to_gc {fs : ℕ → E → EReal} (hfs : ∀ n, PLC (fs n)) (hf : PLC f) {lam : ℝ}
    (hlam : 0 < lam)
    (hP : ∀ z, Tendsto (fun n => proxPt (fs n) lam z) atTop (𝓝 (proxPt f lam z))) :
    GraphicallyConverges (fun n => subdifferential (fs n)) (subdifferential f) := by
  have hsub1 : graph (subdifferential f) ⊆
      setLiminf (fun n => graph (subdifferential (fs n))) := by
    rintro ⟨x, v⟩ hxv
    have hPx := (A10_graph_iff hf hlam x v).mp hxv
    set z := x + lam • v with hz
    have hv : lam⁻¹ • (z - x) = v := by
      rw [hz, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
    apply mem_setLiminf_of_seq _
      (fun n => (proxPt (fs n) lam z, lam⁻¹ • (z - proxPt (fs n) lam z)))
    · exact Filter.Eventually.of_forall (fun n => A10_graph_mem (hfs n) hlam z)
    · have h1 := hP z
      rw [hPx] at h1
      have h2 : Tendsto (fun n => lam⁻¹ • (z - proxPt (fs n) lam z)) atTop
          (𝓝 (lam⁻¹ • (z - x))) :=
        (tendsto_const_nhds.sub h1).const_smul lam⁻¹
      rw [hv] at h2
      exact h1.prodMk_nhds h2
  have hsub2 : setLimsup (fun n => graph (subdifferential (fs n))) ⊆
      graph (subdifferential f) := by
    rintro ⟨x, v⟩ hxv
    obtain ⟨ns, hns, s, hs, hst⟩ :=
      setLimsup_seq (fun n => graph (subdifferential (fs n))) hxv
    rw [A10_graph_iff hf hlam x v]
    set z := x + lam • v with hz
    have h1 : Tendsto (fun k => (s k).1) atTop (𝓝 x) := (continuous_fst.tendsto _).comp hst
    have h2 : Tendsto (fun k => (s k).2) atTop (𝓝 v) := (continuous_snd.tendsto _).comp hst
    have hzs_t : Tendsto (fun k => (s k).1 + lam • (s k).2) atTop (𝓝 z) :=
      h1.add (h2.const_smul lam)
    have hq : ∀ k, proxPt (fs (ns k)) lam ((s k).1 + lam • (s k).2) = (s k).1 := fun k =>
      (A10_graph_iff (hfs (ns k)) hlam (s k).1 (s k).2).mp (hs k)
    have hPz : Tendsto (fun k => proxPt (fs (ns k)) lam z) atTop (𝓝 (proxPt f lam z)) :=
      (hP z).comp hns.tendsto_atTop
    have h3 : Tendsto (fun k => (s k).1) atTop (𝓝 (proxPt f lam z)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hb : ∀ k, ‖(s k).1 - proxPt f lam z‖
          ≤ ‖((s k).1 + lam • (s k).2) - z‖
            + ‖proxPt (fs (ns k)) lam z - proxPt f lam z‖ := by
        intro k
        calc ‖(s k).1 - proxPt f lam z‖
            = ‖(proxPt (fs (ns k)) lam ((s k).1 + lam • (s k).2) - proxPt (fs (ns k)) lam z)
                + (proxPt (fs (ns k)) lam z - proxPt f lam z)‖ := by
              rw [hq k]; congr 1; abel
          _ ≤ ‖proxPt (fs (ns k)) lam ((s k).1 + lam • (s k).2) - proxPt (fs (ns k)) lam z‖
                + ‖proxPt (fs (ns k)) lam z - proxPt f lam z‖ := norm_add_le _ _
          _ ≤ ‖((s k).1 + lam • (s k).2) - z‖
                + ‖proxPt (fs (ns k)) lam z - proxPt f lam z‖ := by
              gcongr
              exact prox_nonexp (hfs (ns k)) hlam _ z
      apply squeeze_zero (fun k => norm_nonneg _) hb
      have := (tendsto_iff_norm_sub_tendsto_zero.mp hzs_t).add
        (tendsto_iff_norm_sub_tendsto_zero.mp hPz)
      simpa using this
    exact (tendsto_nhds_unique h1 h3).symm
  have hls : setLiminf (fun n => graph (subdifferential (fs n))) ⊆
      setLimsup (fun n => graph (subdifferential (fs n))) := setLiminf_subset_setLimsup _
  refine ⟨?_, ?_⟩
  · show setLimsup (fun n => graph (subdifferential (fs n))) = graph (subdifferential f)
    exact Set.Subset.antisymm hsub2 (hsub1.trans hls)
  · show setLiminf (fun n => graph (subdifferential (fs n))) = graph (subdifferential f)
    exact Set.Subset.antisymm (hls.trans hsub2) hsub1

end Att

namespace Att

open Filter

variable {f : E → EReal}

lemma pmc_iff {fs : ℕ → E → EReal} (hfs : ∀ n, PLC (fs n)) (hf : PLC f) {lam : ℝ}
    (hlam : 0 < lam) :
    PointwiseMapConverges (fun n => proximalMapping (fs n) lam) (proximalMapping f lam) ↔
      ∀ x, Tendsto (fun n => proxPt (fs n) lam x) atTop (𝓝 (proxPt f lam x)) := by
  have hE : ∀ n x, proximalMapping (fs n) lam x = {proxPt (fs n) lam x} :=
    fun n x => proximalMapping_eq (hfs n) hlam x
  have hE0 : ∀ x, proximalMapping f lam x = {proxPt f lam x} :=
    fun x => proximalMapping_eq hf hlam x
  have hE0' : proximalMapping f lam = fun x => {proxPt f lam x} := funext hE0
  unfold PointwiseMapConverges pLimsup pLiminf
  rw [hE0']
  simp only [hE]
  constructor
  · rintro ⟨h1, h2⟩ x
    exact (singleton_conv_iff _ _).1 ⟨congrFun h1 x, congrFun h2 x⟩
  · intro h
    exact ⟨funext fun x => ((singleton_conv_iff _ _).2 (h x)).1,
      funext fun x => ((singleton_conv_iff _ _).2 (h x)).2⟩

lemma prox_moving {fs : ℕ → E → EReal} (hfs : ∀ n, PLC (fs n)) {lam : ℝ}
    (hlam : 0 < lam) {P0 : E → E}
    (hP : ∀ x, Tendsto (fun n => proxPt (fs n) lam x) atTop (𝓝 (P0 x)))
    {xs : ℕ → E} {x : E} (hxs : Tendsto xs atTop (𝓝 x)) :
    Tendsto (fun n => proxPt (fs n) lam (xs n)) atTop (𝓝 (P0 x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 := tendsto_iff_norm_sub_tendsto_zero.1 (hP x)
  have h2 := tendsto_iff_norm_sub_tendsto_zero.1 hxs
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using h2.add h1)
  calc ‖proxPt (fs n) lam (xs n) - P0 x‖
      = ‖(proxPt (fs n) lam (xs n) - proxPt (fs n) lam x) + (proxPt (fs n) lam x - P0 x)‖ := by
        congr 1; abel
    _ ≤ ‖proxPt (fs n) lam (xs n) - proxPt (fs n) lam x‖ + ‖proxPt (fs n) lam x - P0 x‖ :=
        norm_add_le _ _
    _ ≤ ‖xs n - x‖ + ‖proxPt (fs n) lam x - P0 x‖ := by
        gcongr; exact prox_nonexp (hfs n) hlam _ _

lemma f_proxPt_eq (hf : PLC f) {lam : ℝ} (hlam : 0 < lam) (x : E) :
    f (proxPt f lam x) =
      ((envR f lam x - (2 * lam)⁻¹ * ‖proxPt f lam x - x‖ ^ 2 : ℝ) : EReal) := by
  rw [f_proxPt_coe hf hlam x]
  congr 1
  simp [envR]

end Att

theorem RW_chap_12_35
  (fseq : ℕ → E → EReal)
  (f : E → EReal)
  (lam : ℝ)
  (h_lam : 0 < lam)
  (hfseq_proper : ∀ n, IsProper (f := fseq n))
  (hf_proper : IsProper (f := f))
  (hfseq_lsc : ∀ n, LowerSemicontinuous (f := fseq n))
  (hf_lsc : LowerSemicontinuous (f := f))
  (hfseq_convex : ∀ n, ConvexEReal (f := fseq n))
  (hf_convex : ConvexEReal (f := f)) :
  List.TFAE [
    EpiConverges fseq f,
    GraphicallyConverges
      (fun n => subdifferential (f := fseq n))
      (subdifferential (f := f)) ∧
    ∃ (xbar : E), ∃ (vbar : E),
      ∃ (xseq : ℕ → E), ∃ (vseq : ℕ → E),
        Filter.Tendsto xseq Filter.atTop (𝓝 xbar) ∧
        Filter.Tendsto vseq Filter.atTop (𝓝 vbar) ∧
        (∀ n, vseq n ∈ subdifferential (f := fseq n) (xseq n)) ∧
        vbar ∈ subdifferential (f := f) xbar ∧
        Filter.Tendsto (fun n => fseq n (xseq n)) Filter.atTop (𝓝 (f xbar)),
    PointwiseMapConverges
      (fun n => proximalMapping (f := fseq n) lam)
      (proximalMapping (f := f) lam) ∧
    ∃ (xtilde : E), ∃ (xseq : ℕ → E),
      Filter.Tendsto xseq Filter.atTop (𝓝 xtilde) ∧
      Filter.Tendsto
        (fun n => moreauEnvelope (f := fseq n) lam (xseq n))
        Filter.atTop
        (𝓝 (moreauEnvelope (f := f) lam xtilde))] ∧
  (EpiConverges fseq f →
    ∀ (lamseq : ℕ → ℝ),
      Filter.Tendsto lamseq Filter.atTop (𝓝 lam) →
      (∀ n, 0 < lamseq n) →
        UniformlyConvergesOnBounded
          (fun n => proximalMapping (f := fseq n) (lamseq n))
          (proximalMapping (f := f) lam) ∧
        UniformlyConvergesOnBoundedEReal
          (fun n => moreauEnvelope (f := fseq n) (lamseq n))
          (moreauEnvelope (f := f) lam)) := by
  have hF : ∀ n, Att.PLC (fseq n) := fun n => ⟨hfseq_proper n, hfseq_lsc n, hfseq_convex n⟩
  have hF0 : Att.PLC f := ⟨hf_proper, hf_lsc, hf_convex⟩
  have hM : ∀ n x, moreauEnvelope (fseq n) lam x = (Att.envR (fseq n) lam x : EReal) :=
    fun n x => Att.moreau_eq (hF n) h_lam x
  have hM0 : ∀ x, moreauEnvelope f lam x = (Att.envR f lam x : EReal) :=
    fun x => Att.moreau_eq hF0 h_lam x
  refine ⟨?_, fun h lamseq hl hpos => Att.final_part hF hF0 h h_lam hpos hl⟩
  tfae_have 1 → 3 := by
    intro h
    have key : ∀ x : E,
        Filter.Tendsto (fun n => Att.proxPt (fseq n) lam x) Filter.atTop
          (𝓝 (Att.proxPt f lam x)) ∧
        Filter.Tendsto (fun n => Att.envR (fseq n) lam x) Filter.atTop
          (𝓝 (Att.envR f lam x)) := fun x =>
      Att.epi_prox_conv (lams := fun _ => lam) (zs := fun _ => x) hF hF0 h h_lam
        (fun _ => h_lam) tendsto_const_nhds tendsto_const_nhds
    refine ⟨(Att.pmc_iff hF hF0 h_lam).2 fun x => (key x).1, 0, fun _ => 0,
      tendsto_const_nhds, ?_⟩
    simp only [hM, hM0]
    exact EReal.tendsto_coe.2 (key 0).2
  tfae_have 3 → 2 := by
    rintro ⟨hpc, xt, xs, hxs, henv⟩
    have hP := (Att.pmc_iff hF hF0 h_lam).1 hpc
    refine ⟨Att.pc_to_gc hF hF0 h_lam hP, ?_⟩
    have henvR : Filter.Tendsto (fun n => Att.envR (fseq n) lam (xs n)) Filter.atTop
        (𝓝 (Att.envR f lam xt)) := by
      simp only [hM, hM0] at henv
      exact EReal.tendsto_coe.1 henv
    have hp : Filter.Tendsto (fun n => Att.proxPt (fseq n) lam (xs n)) Filter.atTop
        (𝓝 (Att.proxPt f lam xt)) := Att.prox_moving hF h_lam hP hxs
    refine ⟨Att.proxPt f lam xt, lam⁻¹ • (xt - Att.proxPt f lam xt),
      fun n => Att.proxPt (fseq n) lam (xs n),
      fun n => lam⁻¹ • (xs n - Att.proxPt (fseq n) lam (xs n)), hp,
      (hxs.sub hp).const_smul lam⁻¹, fun n => ?_, ?_, ?_⟩
    · exact (Att.mem_subdiff_iff (hF n)).2
        ((Att.mem_prox_iff (hF n) h_lam).1 (Att.proxPt_mem (hF n) h_lam (xs n)))
    · exact (Att.mem_subdiff_iff hF0).2
        ((Att.mem_prox_iff hF0 h_lam).1 (Att.proxPt_mem hF0 h_lam xt))
    · simp only [Att.f_proxPt_eq (hF _) h_lam, Att.f_proxPt_eq hF0 h_lam]
      apply EReal.tendsto_coe.2
      exact henvR.sub (((hp.sub hxs).norm.pow 2).const_mul _)
  tfae_have 2 → 3 := by
    rintro ⟨hgc, xb, vb, xs, vs, hxs, hvs, hsub, hvb, hfx⟩
    have hP := Att.gc_to_pc hF hF0 h_lam (hgc.2 ▸ subset_rfl)
    refine ⟨(Att.pmc_iff hF hF0 h_lam).2 hP, xb + lam • vb, fun n => xs n + lam • vs n,
      hxs.add (hvs.const_smul lam), ?_⟩
    have hsmul : ∀ a b : E, lam⁻¹ • (a + lam • b - a) = b := by
      intro a b
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ h_lam.ne', one_smul]
    have hpx : ∀ n, Att.proxPt (fseq n) lam (xs n + lam • vs n) = xs n := by
      intro n
      apply Att.proxPt_eq_of_mem (hF n) h_lam
      rw [Att.mem_prox_iff (hF n) h_lam, hsmul]
      exact (Att.mem_subdiff_iff (hF n)).1 (hsub n)
    have hpx0 : Att.proxPt f lam (xb + lam • vb) = xb := by
      apply Att.proxPt_eq_of_mem hF0 h_lam
      rw [Att.mem_prox_iff hF0 h_lam, hsmul]
      exact (Att.mem_subdiff_iff hF0).1 hvb
    simp only [hM, hM0]
    apply EReal.tendsto_coe.2
    simp only [Att.envR, hpx, hpx0]
    apply Filter.Tendsto.add
    · exact (EReal.tendsto_toReal hvb.2.1.ne hvb.1.ne').comp hfx
    · exact ((hxs.sub (hxs.add (hvs.const_smul lam))).norm.pow 2).const_mul _
  tfae_have 3 → 1 := by
    rintro ⟨hpc, xt, xs, hxs, henv⟩
    have hP := (Att.pmc_iff hF hF0 h_lam).1 hpc
    have henvR : Filter.Tendsto (fun n => Att.envR (fseq n) lam (xs n)) Filter.atTop
        (𝓝 (Att.envR f lam xt)) := by
      simp only [hM, hM0] at henv
      exact EReal.tendsto_coe.1 henv
    have hall := Att.riemann_conv (fun n => Att.envR (fseq n) lam) (Att.envR f lam)
      (fun n a => lam⁻¹ • (a - Att.proxPt (fseq n) lam a))
      (fun a => lam⁻¹ • (a - Att.proxPt f lam a)) (2 / lam)
      (fun n a b => Att.env_two_point (hF n) h_lam a b)
      (fun a b => Att.env_two_point hF0 h_lam a b)
      (fun a => (tendsto_const_nhds.sub (hP a)).const_smul lam⁻¹) xt xs hxs henvR
    exact Att.c_to_a hF hF0 h_lam hP hall
  tfae_finish

end RW_chap_12_35
