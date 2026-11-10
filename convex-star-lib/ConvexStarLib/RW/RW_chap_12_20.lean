import ConvexStarLib.Defs

/-!
# `RW_chap_12_20`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_12_20` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_12_20`, so the main result is `RW_chap_12_20.RW_chap_12_20`.
-/

namespace RW_chap_12_20

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Auxiliary lemmas for `RW_chap_12_20` -/

/-- Nearest points exist for nonempty closed sets in finite dimension. -/
lemma rw1220_proj_exists (C : Set E) (hne : C.Nonempty) (hcl : IsClosed C) (x : E) :
    ∃ w, w ∈ projectionMapping C x := by
  obtain ⟨y, hy, hyd⟩ := hcl.exists_infDist_eq_dist hne x
  refine ⟨y, hy, fun z hz => ?_⟩
  have h1 := Metric.infDist_le_dist_of_mem (x := x) hz
  rw [hyd, dist_eq_norm, dist_eq_norm] at h1
  rw [norm_sub_rev y x, norm_sub_rev z x]
  exact h1

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma rw1220_infDist_eq {C : Set E} {x w : E} (hw : w ∈ projectionMapping C x) :
    Metric.infDist x C = ‖w - x‖ := by
  apply le_antisymm
  · rw [norm_sub_rev, ← dist_eq_norm]
    exact Metric.infDist_le_dist_of_mem hw.1
  · rw [Metric.le_infDist ⟨w, hw.1⟩]
    intro y hy
    rw [dist_eq_norm, norm_sub_rev x y]
    exact hw.2 y hy

omit [FiniteDimensional ℝ E] in
lemma rw1220_proj_monotone (C : Set E) : IsMonotone (projectionMapping C) := by
  intro x₀ x₁ v₀ v₁ h₀ h₁
  have a := h₀.2 v₁ h₁.1
  have b := h₁.2 v₀ h₀.1
  have a2 : ‖v₀ - x₀‖ ^ 2 ≤ ‖v₁ - x₀‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) a 2
  have b2 : ‖v₁ - x₁‖ ^ 2 ≤ ‖v₀ - x₁‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) b 2
  rw [norm_sub_sq_real, norm_sub_sq_real] at a2 b2
  have e : inner ℝ (v₁ - v₀) (x₁ - x₀)
      = inner ℝ v₁ x₁ - inner ℝ v₁ x₀ - inner ℝ v₀ x₁ + inner ℝ v₀ x₀ := by
    simp only [inner_sub_left, inner_sub_right]; ring
  rw [e]
  linarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma rw1220_sq_littleO (w : E) (t : ℝ) :
    (fun y : E => t * ‖y - w‖ ^ 2) =o[𝓝 w] (fun y => ‖y - w‖) := by
  have h : (fun y : E => ‖y - w‖ ^ 2) =o[𝓝 w] (fun y => ‖y - w‖) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    filter_upwards [Metric.ball_mem_nhds w hc] with y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (norm_nonneg _), sq]
    exact mul_le_mul_of_nonneg_right hy.le (norm_nonneg _)
  exact h.const_mul_left t

omit [FiniteDimensional ℝ E] in
/-- Proximal normals are regular normals. -/
lemma rw1220_proxnormal {C : Set E} {x w : E} (hw : w ∈ projectionMapping C x) {t : ℝ}
    (ht : 0 ≤ t) : IsRegularNormalAt C w (t • (x - w)) := by
  refine ⟨hw.1, fun y => t * ‖y - w‖ ^ 2, rw1220_sq_littleO w t, Set.univ, Filter.univ_mem,
    fun y _ hy => ?_⟩
  have h1 := hw.2 y hy
  have h2 : ‖w - x‖ ^ 2 ≤ ‖y - x‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have e : ‖y - x‖ ^ 2 = ‖y - w‖ ^ 2 - 2 * inner ℝ (y - w) (x - w) + ‖x - w‖ ^ 2 := by
    rw [← norm_sub_sq_real]; congr 1; abel_nf
  rw [e, norm_sub_rev w x] at h2
  show inner ℝ (t • (x - w)) (y - w) ≤ t * ‖y - w‖ ^ 2
  rw [real_inner_smul_left, real_inner_comm]
  have h3 : inner ℝ (y - w) (x - w) ≤ ‖y - w‖ ^ 2 := by nlinarith [sq_nonneg ‖y - w‖]
  exact mul_le_mul_of_nonneg_left h3 ht

omit [FiniteDimensional ℝ E] in
lemma rw1220_reg_to_normal {C : Set E} {x v : E} (h : IsRegularNormalAt C x v) :
    v ∈ normalCone C x :=
  ⟨fun _ => x, fun _ => v, tendsto_const_nhds, tendsto_const_nhds, fun _ => h⟩

omit [FiniteDimensional ℝ E] in
/-- For convex sets, regular normals are normals in the sense of convex analysis. -/
lemma rw1220_regnormal_convex {C : Set E} (hconv : Convex ℝ C) {xb v : E}
    (hv : IsRegularNormalAt C xb v) : ∀ z ∈ C, inner ℝ v (z - xb) ≤ 0 := by
  obtain ⟨hxb, r, hr, V, hV, hVr⟩ := hv
  intro z hz
  by_contra hpos
  push_neg at hpos
  set s := inner ℝ v (z - xb) with hs
  set η := s / (2 * (‖z - xb‖ + 1)) with hη
  have hη0 : 0 < η := by positivity
  have h2 : ∀ᶠ x in 𝓝 xb, x ∈ V ∧ ‖r x‖ ≤ η * ‖‖x - xb‖‖ :=
    (Filter.eventually_mem_set.2 hV).and (hr.def hη0)
  have htend : Filter.Tendsto (fun t : ℝ => xb + t • (z - xb)) (𝓝[>] 0) (𝓝 xb) := by
    have : Filter.Tendsto (fun t : ℝ => xb + t • (z - xb)) (𝓝 0)
        (𝓝 (xb + (0 : ℝ) • (z - xb))) :=
      tendsto_const_nhds.add (Filter.tendsto_id.smul tendsto_const_nhds)
    rw [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h3 := htend.eventually h2
  have h4 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  obtain ⟨t, ⟨hxV, hrx⟩, ht0, ht1⟩ := (h3.and h4).exists
  have hxC : xb + t • (z - xb) ∈ C := hconv.add_smul_sub_mem hxb hz ⟨ht0.le, ht1.le⟩
  have h5 := hVr _ hxV hxC
  simp only [add_sub_cancel_left] at h5 hrx
  rw [real_inner_smul_right] at h5
  rw [norm_norm, norm_smul, Real.norm_of_nonneg ht0.le] at hrx
  have h6 : r (xb + t • (z - xb)) ≤ ‖r (xb + t • (z - xb))‖ := Real.le_norm_self _
  have h7 : t * s ≤ η * (t * ‖z - xb‖) := by linarith
  have h8 : s ≤ η * ‖z - xb‖ := by
    have : t * s ≤ t * (η * ‖z - xb‖) := by linarith
    exact le_of_mul_le_mul_left this ht0
  have h9 : η * ‖z - xb‖ < s := by
    rw [hη, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg (z - xb)]
  linarith

omit [FiniteDimensional ℝ E] in
lemma rw1220_normal_convex {C : Set E} (hconv : Convex ℝ C) (hcl : IsClosed C) {xb v : E}
    (hv : v ∈ normalCone C xb) : xb ∈ C ∧ ∀ z ∈ C, inner ℝ v (z - xb) ≤ 0 := by
  obtain ⟨x, vs, hx, hvs, hreg⟩ := hv
  refine ⟨hcl.mem_of_tendsto hx (Filter.Eventually.of_forall fun n => (hreg n).1), fun z hz => ?_⟩
  have h : ∀ n, inner ℝ (vs n) (z - x n) ≤ 0 :=
    fun n => rw1220_regnormal_convex hconv (hreg n) z hz
  have ht : Filter.Tendsto (fun n => inner ℝ (vs n) (z - x n)) Filter.atTop
      (𝓝 (inner ℝ v (z - xb))) :=
    hvs.inner (tendsto_const_nhds.sub hx)
  exact le_of_tendsto' ht h

omit [FiniteDimensional ℝ E] in
/-- Variational inequality for projections onto convex sets. -/
lemma rw1220_VI {C : Set E} (hconv : Convex ℝ C) {x w : E} (hw : w ∈ projectionMapping C x) :
    ∀ z ∈ C, inner ℝ (x - w) (z - w) ≤ 0 := by
  have := rw1220_regnormal_convex hconv (rw1220_proxnormal hw zero_le_one)
  simpa only [one_smul] using this

omit [FiniteDimensional ℝ E] in
lemma rw1220_uniq_of_mid {C : Set E} {z w₀ w₁ : E} (h₀ : w₀ ∈ projectionMapping C z)
    (h₁ : w₁ ∈ projectionMapping C z) (hmid : (1 / 2 : ℝ) • w₀ + (1 / 2 : ℝ) • w₁ ∈ C) :
    w₀ = w₁ := by
  have a := h₀.2 w₁ h₁.1
  have b := h₁.2 w₀ h₀.1
  have c := h₀.2 _ hmid
  have hpar := parallelogram_law_with_norm ℝ (w₀ - z) (w₁ - z)
  have e1 : (w₀ - z) + (w₁ - z) = (2 : ℝ) • ((1 / 2 : ℝ) • w₀ + (1 / 2 : ℝ) • w₁ - z) := by
    module
  have e2 : (w₀ - z) - (w₁ - z) = w₀ - w₁ := by abel
  rw [e1, e2, norm_smul] at hpar
  have hD : ‖w₀ - z‖ * ‖w₀ - z‖ ≤
      ‖(1 / 2 : ℝ) • w₀ + (1 / 2 : ℝ) • w₁ - z‖ * ‖(1 / 2 : ℝ) • w₀ + (1 / 2 : ℝ) • w₁ - z‖ :=
    mul_self_le_mul_self (norm_nonneg _) c
  have hab : ‖w₀ - z‖ = ‖w₁ - z‖ := le_antisymm a b
  rw [← hab] at hpar
  norm_num at hpar
  have : ‖w₀ - w₁‖ * ‖w₀ - w₁‖ ≤ 0 := by nlinarith
  have : ‖w₀ - w₁‖ = 0 := by nlinarith [norm_nonneg (w₀ - w₁)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- Key step of the Chebyshev-set argument: at a minimizer `y₀` of
`F y = (1+ε)/2 ‖y‖² - ⟪m, y⟫ - d_C(y)²/2`, the (unique) nearest point is `m - ε y₀`. -/
lemma rw1220_cheb_key (C : Set E) (hne : C.Nonempty) (hcl : IsClosed C) (m : E) {ε : ℝ}
    (y₀ p : E) (hp : p ∈ projectionMapping C y₀)
    (huniq : ∀ q, q ∈ projectionMapping C y₀ → q = p)
    (hy₀ : ∀ y, (1 + ε) / 2 * ‖y₀‖ ^ 2 - inner ℝ m y₀ - (Metric.infDist y₀ C) ^ 2 / 2 ≤
      (1 + ε) / 2 * ‖y‖ ^ 2 - inner ℝ m y - (Metric.infDist y C) ^ 2 / 2) :
    p = m - ε • y₀ := by
  set u := m - ε • y₀ - p with hu
  suffices hu0 : ‖u‖ ^ 2 ≤ 0 by
    have h1 : ‖u‖ = 0 := by nlinarith [norm_nonneg u]
    have h2 : u = 0 := norm_eq_zero.1 h1
    rw [hu, sub_eq_zero] at h2
    exact h2.symm
  set t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with ht
  have ht0 : ∀ n, 0 < t n := fun n => by positivity
  have ht1 : ∀ n, t n ≤ 1 := fun n => by
    rw [ht]; dsimp only
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have htlim : Filter.Tendsto t Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set z : ℕ → E := fun n => y₀ + t n • u with hz
  choose c hc using fun n => rw1220_proj_exists C hne hcl (z n)
  -- first-order inequality from minimality of `y₀`
  have hineq : ∀ n, ‖u‖ ^ 2 ≤ inner ℝ (c n - p) u + ε / 2 * t n * ‖u‖ ^ 2 := by
    intro n
    have h1 := hy₀ (z n)
    have hD1 : Metric.infDist (z n) C = ‖c n - z n‖ := rw1220_infDist_eq (hc n)
    have hD0 : Metric.infDist y₀ C ≤ ‖y₀ - c n‖ := by
      rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem (hc n).1
    have hD0' : (Metric.infDist y₀ C) ^ 2 ≤ ‖y₀ - c n‖ ^ 2 :=
      pow_le_pow_left₀ Metric.infDist_nonneg hD0 2
    rw [hD1] at h1
    have e1 : ‖z n‖ ^ 2 = ‖y₀‖ ^ 2 + 2 * t n * inner ℝ y₀ u + (t n) ^ 2 * ‖u‖ ^ 2 := by
      rw [hz]; dsimp only
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_of_nonneg (ht0 n).le]
      ring
    have e2 : inner ℝ m (z n) = inner ℝ m y₀ + t n * inner ℝ m u := by
      rw [hz]; dsimp only
      rw [inner_add_right, real_inner_smul_right]
    have e3 : ‖c n - z n‖ ^ 2
        = ‖c n - y₀‖ ^ 2 - 2 * t n * inner ℝ (c n - y₀) u + (t n) ^ 2 * ‖u‖ ^ 2 := by
      have : c n - z n = (c n - y₀) - t n • u := by rw [hz]; dsimp only; abel
      rw [this, norm_sub_sq_real, real_inner_smul_right, norm_smul,
        Real.norm_of_nonneg (ht0 n).le]
      ring
    have e4 : ‖y₀ - c n‖ = ‖c n - y₀‖ := norm_sub_rev _ _
    have e5 : inner ℝ (c n - p) u = inner ℝ (c n - y₀) u + inner ℝ y₀ u - inner ℝ p u := by
      rw [inner_sub_left, inner_sub_left]; ring
    have e6 : ‖u‖ ^ 2 = inner ℝ m u - ε * inner ℝ y₀ u - inner ℝ p u := by
      rw [← real_inner_self_eq_norm_sq]
      conv_lhs => arg 2; rw [hu]
      rw [inner_sub_left, inner_sub_left, real_inner_smul_left]
    rw [e1, e2, e3] at h1
    rw [e4] at hD0'
    have eq : t n * (inner ℝ (c n - p) u - ‖u‖ ^ 2 + ε / 2 * t n * ‖u‖ ^ 2)
        = t n * (inner ℝ (c n - y₀) u + (1 + ε) * inner ℝ y₀ u - inner ℝ m u)
          + ε / 2 * (t n) ^ 2 * ‖u‖ ^ 2 := by
      linear_combination (t n) * e5 - (t n) * e6
    have key : 0 ≤ t n * (inner ℝ (c n - p) u - ‖u‖ ^ 2 + ε / 2 * t n * ‖u‖ ^ 2) := by
      rw [eq]; linarith
    have := (mul_nonneg_iff_of_pos_left (ht0 n)).1 key
    linarith
  -- boundedness of the nearest points
  have hbound : ∀ n, c n ∈ Metric.closedBall y₀ (‖p - y₀‖ + 2 * ‖u‖) := by
    intro n
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h1 := (hc n).2 p hp.1
    have h2 : ‖z n - y₀‖ ≤ ‖u‖ := by
      rw [hz]; dsimp only
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (ht0 n).le]
      exact mul_le_of_le_one_left (norm_nonneg _) (ht1 n)
    have h3 : ‖p - z n‖ ≤ ‖p - y₀‖ + ‖y₀ - z n‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h4 : ‖c n - y₀‖ ≤ ‖c n - z n‖ + ‖z n - y₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    rw [norm_sub_rev y₀] at h3
    linarith
  obtain ⟨q, -, g, hg, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hbound
  have hzlim : Filter.Tendsto (z ∘ g) Filter.atTop (𝓝 y₀) := by
    have h1 : Filter.Tendsto z Filter.atTop (𝓝 y₀) := by
      have : Filter.Tendsto (fun n => y₀ + t n • u) Filter.atTop (𝓝 (y₀ + (0 : ℝ) • u)) :=
        tendsto_const_nhds.add (htlim.smul_const u)
      rwa [zero_smul, add_zero] at this
    exact h1.comp hg.tendsto_atTop
  have hqC : q ∈ C := hcl.mem_of_tendsto hlim (Filter.Eventually.of_forall fun n => (hc (g n)).1)
  have hqP : q ∈ projectionMapping C y₀ := by
    refine ⟨hqC, fun w hw => ?_⟩
    have h1 : Filter.Tendsto (fun n => ‖c (g n) - z (g n)‖) Filter.atTop (𝓝 ‖q - y₀‖) :=
      (hlim.sub hzlim).norm
    have h2 : Filter.Tendsto (fun n => ‖w - z (g n)‖) Filter.atTop (𝓝 ‖w - y₀‖) :=
      (tendsto_const_nhds.sub hzlim).norm
    exact le_of_tendsto_of_tendsto' h1 h2 (fun n => (hc (g n)).2 w hw)
  have hqp : q = p := huniq q hqP
  have htg : Filter.Tendsto (t ∘ g) Filter.atTop (𝓝 0) := htlim.comp hg.tendsto_atTop
  have hR : Filter.Tendsto (fun n => inner ℝ (c (g n) - p) u + ε / 2 * t (g n) * ‖u‖ ^ 2)
      Filter.atTop (𝓝 (inner ℝ (q - p) u + ε / 2 * 0 * ‖u‖ ^ 2)) :=
    ((hlim.sub tendsto_const_nhds).inner tendsto_const_nhds).add
      ((htg.const_mul (ε / 2)).mul_const _)
  rw [hqp, sub_self, inner_zero_left, mul_zero, zero_mul, add_zero] at hR
  exact ge_of_tendsto' hR (fun n => hineq (g n))

/-- In finite dimension, Chebyshev sets are convex. -/
lemma rw1220_cheb_convex (C : Set E) (hne : C.Nonempty) (hcl : IsClosed C)
    (hsv : IsSingleValued (projectionMapping C)) : Convex ℝ C := by
  intro c₀ hc₀ c₁ hc₁ a b ha hb hab
  set m := a • c₀ + b • c₁ with hm
  rw [← hcl.closure_eq, Metric.mem_closure_iff]
  intro δ hδ
  set K := (a * ‖c₀‖ ^ 2 + b * ‖c₁‖ ^ 2) / 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set ε := δ ^ 2 / (2 * K + 1) with hε
  have hε0 : 0 < ε := by positivity
  set F : E → ℝ := fun y => (1 + ε) / 2 * ‖y‖ ^ 2 - inner ℝ m y - (Metric.infDist y C) ^ 2 / 2
    with hF
  have hlow : ∀ y, ε / 2 * ‖y‖ ^ 2 - K ≤ F y := by
    intro y
    have d0 : Metric.infDist y C ≤ ‖y - c₀‖ := by
      rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hc₀
    have d1 : Metric.infDist y C ≤ ‖y - c₁‖ := by
      rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hc₁
    have dn : 0 ≤ Metric.infDist y C := Metric.infDist_nonneg
    have s0 : (Metric.infDist y C) ^ 2 ≤ ‖y - c₀‖ ^ 2 := pow_le_pow_left₀ dn d0 2
    have s1 : (Metric.infDist y C) ^ 2 ≤ ‖y - c₁‖ ^ 2 := pow_le_pow_left₀ dn d1 2
    have e0 := norm_sub_sq_real y c₀
    have e1 := norm_sub_sq_real y c₁
    have em : inner ℝ m y = a * inner ℝ y c₀ + b * inner ℝ y c₁ := by
      rw [hm, inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_comm c₀ y,
        real_inner_comm c₁ y]
    have hcomb : (Metric.infDist y C) ^ 2 ≤ a * ‖y - c₀‖ ^ 2 + b * ‖y - c₁‖ ^ 2 := by
      have h0 := mul_le_mul_of_nonneg_left s0 ha
      have h1 := mul_le_mul_of_nonneg_left s1 hb
      have : (Metric.infDist y C) ^ 2 = a * (Metric.infDist y C) ^ 2 + b * (Metric.infDist y C) ^ 2 := by
        rw [← add_mul, hab, one_mul]
      linarith
    show ε / 2 * ‖y‖ ^ 2 - K ≤ (1 + ε) / 2 * ‖y‖ ^ 2 - inner ℝ m y - (Metric.infDist y C) ^ 2 / 2
    rw [em]
    rw [e0, e1] at hcomb
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith
  have hcont : Continuous F :=
    ((continuous_const.mul (continuous_norm.pow 2)).sub (continuous_const.inner continuous_id)).sub
      (((Metric.continuous_infDist_pt C).pow 2).div_const 2)
  have hF0 : F 0 ≤ 0 := by
    show (1 + ε) / 2 * ‖(0 : E)‖ ^ 2 - inner ℝ m 0 - (Metric.infDist 0 C) ^ 2 / 2 ≤ 0
    rw [norm_zero, inner_zero_right]
    nlinarith [sq_nonneg (Metric.infDist (0 : E) C)]
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, ∀ y, F y₀ ≤ F y := by
    refine hcont.exists_forall_le' 0 ?_
    filter_upwards [(tendsto_norm_cocompact_atTop (E := E)).eventually_ge_atTop
      (Real.sqrt (2 * K / ε))] with y hy
    have h1 : 2 * K / ε ≤ ‖y‖ ^ 2 := by
      calc 2 * K / ε = (Real.sqrt (2 * K / ε)) ^ 2 := (Real.sq_sqrt (by positivity)).symm
        _ ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hy 2
    have h2 : K ≤ ε / 2 * ‖y‖ ^ 2 := by
      rw [div_le_iff₀ hε0] at h1; linarith
    linarith [hlow y]
  obtain ⟨p, hp, huniq⟩ := hsv y₀
  have hkey : p = m - ε • y₀ := rw1220_cheb_key C hne hcl m y₀ p hp huniq hy₀
  refine ⟨p, hp.1, ?_⟩
  rw [dist_eq_norm, hkey, _root_.sub_sub_cancel, norm_smul, Real.norm_of_nonneg hε0.le]
  have h1 := hlow y₀
  have h2 : F y₀ ≤ 0 := le_trans (hy₀ 0) hF0
  have h3 : ε * ‖y₀‖ ^ 2 ≤ 2 * K := by linarith
  have h4 : (ε * ‖y₀‖) ^ 2 < δ ^ 2 := by
    calc (ε * ‖y₀‖) ^ 2 = ε * (ε * ‖y₀‖ ^ 2) := by ring
      _ ≤ ε * (2 * K) := by gcongr
      _ < δ ^ 2 := by
        rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [sq_pos_of_pos hδ]
  exact lt_of_pow_lt_pow_left₀ 2 hδ.le h4

theorem RW_chap_12_20
  (C : Set E)
  (hC_nonempty : Set.Nonempty C)
  (hC_closed : IsClosed C) :
  IsMonotone (projectionMapping C) ∧
  List.TFAE [
    Convex ℝ C,
    IsSingleValued (projectionMapping C),
    IsNonexpansive (projectionMapping C),
    IsMaximalMonotone (projectionMapping C),
    ∃ rho : ℝ, IsMonotone (addMap (normalCone C) (smulMap rho idMap))
  ] := by
  refine ⟨rw1220_proj_monotone C, ?_⟩
  tfae_have 1 → 3 := by
    intro hconv z₀ z₁ w₀ w₁ h₀ h₁
    have v₀ := rw1220_VI hconv h₀ w₁ h₁.1
    have v₁ := rw1220_VI hconv h₁ w₀ h₀.1
    have e : inner ℝ (z₁ - z₀) (w₁ - w₀) - ‖w₁ - w₀‖ ^ 2
        = -(inner ℝ (z₀ - w₀) (w₁ - w₀)) - inner ℝ (z₁ - w₁) (w₀ - w₁) := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right]
      ring
    have key : ‖w₁ - w₀‖ ^ 2 ≤ inner ℝ (z₁ - z₀) (w₁ - w₀) := by linarith
    have cs := real_inner_le_norm (z₁ - z₀) (w₁ - w₀)
    rcases eq_or_lt_of_le (norm_nonneg (w₁ - w₀)) with h | h
    · rw [← h]; exact norm_nonneg _
    · nlinarith
  tfae_have 3 → 4 := by
    intro hne
    refine ⟨rw1220_proj_monotone C, fun xh vh hnot => ?_⟩
    obtain ⟨p, hp⟩ := rw1220_proj_exists C hC_nonempty hC_closed xh
    set d := vh - p with hd
    have hd0 : d ≠ 0 := by
      intro h
      apply hnot
      rw [hd, sub_eq_zero] at h
      rw [h]; exact hp
    set xt := xh + (1 / 2 : ℝ) • d with hxt
    obtain ⟨vt, hvt⟩ := rw1220_proj_exists C hC_nonempty hC_closed xt
    refine ⟨xt, vt, hvt, ?_⟩
    have hn := hne xh xt p vt hp hvt
    have e1 : xt - xh = (1 / 2 : ℝ) • d := by rw [hxt]; abel
    rw [e1, norm_smul, Real.norm_of_nonneg (by norm_num)] at hn
    have e2 : xh - xt = -((1 / 2 : ℝ) • d) := by rw [hxt]; abel
    have e3 : vh - vt = d - (vt - p) := by rw [hd]; abel
    rw [e2, e3, inner_neg_right, inner_sub_left, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    have cs := real_inner_le_norm (vt - p) d
    have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hd0
    nlinarith [norm_nonneg (vt - p)]
  tfae_have 4 → 2 := by
    rintro ⟨hmono, hmax⟩ z
    obtain ⟨w, hw⟩ := rw1220_proj_exists C hC_nonempty hC_closed z
    refine ⟨w, hw, fun w' hw' => ?_⟩
    have hmid : (1 / 2 : ℝ) • w' + (1 / 2 : ℝ) • w ∈ projectionMapping C z := by
      by_contra hnot
      obtain ⟨xt, vt, hvt, hlt⟩ := hmax z _ hnot
      have m1 := hmono xt z vt w' hvt hw'
      have m2 := hmono xt z vt w hvt hw
      have e : (1 / 2 : ℝ) • w' + (1 / 2 : ℝ) • w - vt
          = (1 / 2 : ℝ) • (w' - vt) + (1 / 2 : ℝ) • (w - vt) := by module
      rw [e, inner_add_left, real_inner_smul_left, real_inner_smul_left] at hlt
      linarith
    exact rw1220_uniq_of_mid hw' hw hmid.1
  tfae_have 2 → 1 := rw1220_cheb_convex C hC_nonempty hC_closed
  tfae_have 1 → 5 := by
    intro hconv
    refine ⟨0, ?_⟩
    intro x₀ x₁ v₀ v₁ h₀ h₁
    obtain ⟨u₀, hu₀, s₀, hs₀, rfl⟩ := h₀
    obtain ⟨u₁, hu₁, s₁, hs₁, rfl⟩ := h₁
    obtain ⟨y₀, -, rfl⟩ := hs₀
    obtain ⟨y₁, -, rfl⟩ := hs₁
    simp only [zero_smul, add_zero]
    obtain ⟨hx₀, n₀⟩ := rw1220_normal_convex hconv hC_closed hu₀
    obtain ⟨hx₁, n₁⟩ := rw1220_normal_convex hconv hC_closed hu₁
    have a := n₀ x₁ hx₁
    have b := n₁ x₀ hx₀
    have e : inner ℝ (u₁ - u₀) (x₁ - x₀) = -(inner ℝ u₁ (x₀ - x₁)) - inner ℝ u₀ (x₁ - x₀) := by
      rw [inner_sub_left, ← inner_neg_right, neg_sub]
    linarith
  tfae_have 5 → 1 := by
    rintro ⟨ρ, hmono⟩
    have key : ∀ x w, w ∈ projectionMapping C x → ∀ z ∈ C, inner ℝ (x - w) (z - w) ≤ 0 := by
      intro x w hw z hz
      have h : ∀ t : ℝ, 0 ≤ t → 0 ≤ t * inner ℝ (x - w) (w - z) + ρ * ‖w - z‖ ^ 2 := by
        intro t ht
        have hv₁ : t • (x - w) + ρ • w ∈ addMap (normalCone C) (smulMap ρ idMap) w :=
          ⟨t • (x - w), rw1220_reg_to_normal (rw1220_proxnormal hw ht), ρ • w, ⟨w, rfl, rfl⟩, rfl⟩
        have hzP : z ∈ projectionMapping C z := ⟨hz, fun y _ => by simp⟩
        have hv₀ : (0 : E) + ρ • z ∈ addMap (normalCone C) (smulMap ρ idMap) z := by
          refine ⟨0, ?_, ρ • z, ⟨z, rfl, rfl⟩, rfl⟩
          have := rw1220_reg_to_normal (rw1220_proxnormal hzP le_rfl)
          simpa using this
        have hm := hmono z w _ _ hv₀ hv₁
        have e : (t • (x - w) + ρ • w) - ((0 : E) + ρ • z) = t • (x - w) + ρ • (w - z) := by
          module
        rw [e, inner_add_left, real_inner_smul_left, real_inner_smul_left,
          real_inner_self_eq_norm_sq] at hm
        exact hm
      by_contra hcon
      push_neg at hcon
      have e : inner ℝ (x - w) (w - z) = -inner ℝ (x - w) (z - w) := by
        rw [← inner_neg_right, neg_sub]
      set A := inner ℝ (x - w) (z - w) with hA
      set B := ρ * ‖w - z‖ ^ 2 with hB
      have h1 := h ((|B| + 1) / A) (by positivity)
      rw [e] at h1
      have h2 : (|B| + 1) / A * -A = -(|B| + 1) := by field_simp
      linarith [le_abs_self B]
    intro c₀ hc₀ c₁ hc₁ a b ha hb hab
    obtain ⟨w, hw⟩ := rw1220_proj_exists C hC_nonempty hC_closed (a • c₀ + b • c₁)
    have k₀ := key _ w hw c₀ hc₀
    have k₁ := key _ w hw c₁ hc₁
    set m := a • c₀ + b • c₁ with hm
    have e1 : m - w = a • (c₀ - w) + b • (c₁ - w) := by
      have : a • (c₀ - w) + b • (c₁ - w) = m - (a + b) • w := by rw [hm]; module
      rw [this, hab, one_smul]
    have e2 : ‖m - w‖ ^ 2 = a * inner ℝ (m - w) (c₀ - w) + b * inner ℝ (m - w) (c₁ - w) := by
      rw [← real_inner_self_eq_norm_sq]
      conv_lhs => arg 3; rw [e1]
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have h0 : ‖m - w‖ ^ 2 ≤ 0 := by nlinarith
    have h1 : ‖m - w‖ = 0 := by nlinarith [norm_nonneg (m - w)]
    have h2 : m = w := sub_eq_zero.1 (norm_eq_zero.1 h1)
    rw [h2]; exact hw.1
  tfae_finish

end RW_chap_12_20
