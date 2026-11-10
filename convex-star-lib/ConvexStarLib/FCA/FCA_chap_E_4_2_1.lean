import ConvexStarLib.Defs

/-!
# `FCA_chap_E_4_2_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_4_2_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_4_2_1`, so the main result is `FCA_chap_E_4_2_1.FCA_chap_E_4_2_1`.
-/

namespace FCA_chap_E_4_2_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open Filter Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_E_4_2_1
  (f : E → ℝ)
  (c : ℝ)
  (hc : c > 0)
  (hf_strong : StrongConvexOn Set.univ c f) :
  (∀ s, conjugate (liftRealtoEReal f) s < ⊤) ∧
  (∃ (g : E → ℝ),
  (∀ s, (conjugate (liftRealtoEReal f) s) = (g s : EReal)) ∧
  (Differentiable ℝ g) ∧
  (∀ s₁ s₂, ‖gradient g s₁ - gradient g s₂‖ ≤ (1 / c) * ‖s₁ - s₂‖)) := by
  -- strong convexity inequality
  have hsc : ∀ x y : E, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) ≤ a * f x + b * f y - a * b * (c / 2 * ‖x - y‖ ^ 2) := by
    intro x y a b ha hb hab
    have := hf_strong.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    simpa only [smul_eq_mul] using this
  -- continuity
  have hconv : ConvexOn ℝ Set.univ f := hf_strong.convexOn (fun r => by positivity)
  have hcont : Continuous f := hconv.locallyLipschitz.continuous
  -- coercivity
  obtain ⟨K, hK0, hK⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : E, c / 2 * ‖x‖ ^ 2 - K * ‖x‖ - K ≤ f x := by
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn
      hcont.continuousOn
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by simp))
    have hMl : ∀ x : E, ‖x‖ ≤ 1 → -M ≤ f x := by
      intro x hx
      have := hM x (by simpa using hx)
      rw [Real.norm_eq_abs, abs_le] at this
      exact this.1
    have hMu : f 0 ≤ M := by
      have := hM 0 (by simp)
      rw [Real.norm_eq_abs, abs_le] at this
      exact this.2
    refine ⟨2 * M + c / 2, by positivity, fun x => ?_⟩
    by_cases hx : ‖x‖ ≤ 1
    · have h1 := hMl x hx
      nlinarith [mul_nonneg (mul_nonneg hc.le (norm_nonneg x)) (sub_nonneg.2 hx),
        mul_nonneg hM0 (norm_nonneg x)]
    · push_neg at hx
      set r := ‖x‖ with hr
      have hr0 : 0 < r := by linarith
      set t := 1 / r with ht
      have htr : t * r = 1 := by rw [ht]; field_simp
      have ht0 : 0 ≤ t := by positivity
      have ht1 : t ≤ 1 := by rw [ht, div_le_one hr0]; linarith
      have h1 := hsc x 0 t (1 - t) ht0 (by linarith) (by ring)
      simp only [smul_zero, add_zero, sub_zero] at h1
      have hu : ‖t • x‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, ← hr, htr]
      have hfu : -M ≤ f (t • x) := hMl _ hu
      have h2 : r * f (t • x) ≤ r * (t * f x + (1 - t) * f 0 - t * (1 - t) * (c / 2 * r ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 hr0.le
      have h3 : r * (t * f x + (1 - t) * f 0 - t * (1 - t) * (c / 2 * r ^ 2)) =
          f x + (r - 1) * f 0 - c / 2 * (r ^ 2 - r) := by
        linear_combination (f x - f 0 - c / 2 * ((1 - t) * r ^ 2 - r)) * htr
      have h4 : r * (-M) ≤ r * f (t • x) := mul_le_mul_of_nonneg_left hfu hr0.le
      have h5 : (r - 1) * f 0 ≤ (r - 1) * M := mul_le_mul_of_nonneg_left hMu (by linarith)
      nlinarith
  -- maximizer
  have hmax : ∀ s : E, ∃ x : E, ∀ y : E, inner ℝ s y - f y ≤ inner ℝ s x - f x := by
    intro s
    have hφc : Continuous (fun y => inner ℝ s y - f y) :=
      (continuous_const.inner continuous_id).sub hcont
    refine hφc.exists_forall_ge' 0 ?_
    set B := ‖s‖ + K with hB
    set A := B + |K + f 0| with hA
    have hA0 : 0 ≤ A := by positivity
    filter_upwards [tendsto_norm_cocompact_atTop.eventually
      (eventually_ge_atTop (2 * A / c + 1))] with y hy
    simp only [inner_zero_right, zero_sub]
    have h1 := hK y
    have h2 : inner ℝ s y ≤ ‖s‖ * ‖y‖ := real_inner_le_norm s y
    have h3 : K + f 0 ≤ |K + f 0| := le_abs_self _
    have hr1 : 1 ≤ ‖y‖ := by
      have : 0 ≤ 2 * A / c := by positivity
      linarith
    have hr2 : A ≤ c / 2 * ‖y‖ := by
      have : 2 * A / c * c = 2 * A := by field_simp
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hr2 (norm_nonneg y),
      mul_le_mul_of_nonneg_left hr1 (abs_nonneg (K + f 0))]
  choose xs hxs using hmax
  -- quadratic growth
  have hqg : ∀ s y : E,
      inner ℝ s y - f y + c / 2 * ‖y - xs s‖ ^ 2 ≤ inner ℝ s (xs s) - f (xs s) := by
    intro s y
    set x₀ := xs s with hx₀
    set d2 := ‖y - x₀‖ ^ 2 with hd2
    have hd2nn : 0 ≤ d2 := by positivity
    have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
        inner ℝ s y - f y + (1 - t) * (c / 2 * d2) ≤ inner ℝ s x₀ - f x₀ := by
      intro t ht0 ht1
      have h1 := hsc y x₀ t (1 - t) ht0.le (by linarith) (by ring)
      have h2 := hxs s (t • y + (1 - t) • x₀)
      have h3 : inner ℝ s (t • y + (1 - t) • x₀) = t * inner ℝ s y + (1 - t) * inner ℝ s x₀ := by
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      rw [h3] at h2
      have h4 : t * (inner ℝ s y - f y + (1 - t) * (c / 2 * d2) - (inner ℝ s x₀ - f x₀)) ≤ 0 := by
        nlinarith
      by_contra hcon
      push_neg at hcon
      nlinarith
    apply _root_.le_of_forall_pos_le_add
    intro ε hε
    have hden : 0 < ε + c / 2 * d2 := by positivity
    set t := ε / (ε + c / 2 * d2) with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hden]; nlinarith
    have htd : t * (c / 2 * d2) ≤ ε := by
      rw [ht, div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith
    have := key t ht0 ht1
    nlinarith
  -- Lipschitz
  have hlip : ∀ s₁ s₂ : E, ‖xs s₁ - xs s₂‖ ≤ (1 / c) * ‖s₁ - s₂‖ := by
    intro s₁ s₂
    have h1 := hqg s₁ (xs s₂)
    have h2 := hqg s₂ (xs s₁)
    have h3 : ‖xs s₂ - xs s₁‖ = ‖xs s₁ - xs s₂‖ := norm_sub_rev _ _
    rw [h3] at h1
    have h4 : inner ℝ (s₁ - s₂) (xs s₁ - xs s₂) = inner ℝ s₁ (xs s₁) - inner ℝ s₁ (xs s₂)
        - inner ℝ s₂ (xs s₁) + inner ℝ s₂ (xs s₂) := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right]; ring
    have h5 : inner ℝ (s₁ - s₂) (xs s₁ - xs s₂) ≤ ‖s₁ - s₂‖ * ‖xs s₁ - xs s₂‖ :=
      real_inner_le_norm _ _
    have h6 : c * ‖xs s₁ - xs s₂‖ ^ 2 ≤ ‖s₁ - s₂‖ * ‖xs s₁ - xs s₂‖ := by
      linarith
    rcases eq_or_lt_of_le (norm_nonneg (xs s₁ - xs s₂)) with h | h
    · rw [← h]; positivity
    · rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc]
      nlinarith
  -- the conjugate
  set g : E → ℝ := fun s => inner ℝ s (xs s) - f (xs s) with hg_def
  have hconj : ∀ s, conjugate (liftRealtoEReal f) s = (g s : EReal) := by
    intro s
    unfold conjugate liftRealtoEReal
    apply IsGreatest.csSup_eq
    constructor
    · refine ⟨xs s, Set.mem_univ _, ?_⟩
      simp only [g, EReal.coe_sub]
    · rintro _ ⟨y, -, rfl⟩
      simp only [g]
      rw [← EReal.coe_sub]
      exact EReal.coe_le_coe_iff.mpr (hxs s y)
  -- gradient
  have hgrad : ∀ s, HasGradientAt g (xs s) s := by
    intro s
    rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero]
    have hb : ∀ h, |g (s + h) - g s - inner ℝ (xs s) h| ≤ (1 / c) * ‖h‖ ^ 2 := by
      intro h
      have e1 := hxs (s + h) (xs s)
      have e2 := hxs s (xs (s + h))
      have e3 := real_inner_le_norm h (xs (s + h) - xs s)
      have e4 := hlip (s + h) s
      rw [add_sub_cancel_left] at e4
      have e5 : inner ℝ (s + h) (xs s) = inner ℝ s (xs s) + inner ℝ (xs s) h := by
        rw [inner_add_left, real_inner_comm h]
      have e6 : inner ℝ (s + h) (xs (s + h)) = inner ℝ s (xs (s + h)) + inner ℝ h (xs (s + h)) := by
        rw [inner_add_left]
      have e7 : inner ℝ h (xs (s + h) - xs s) = inner ℝ h (xs (s + h)) - inner ℝ (xs s) h := by
        rw [inner_sub_right, real_inner_comm h (xs s)]
      have e8 : ‖h‖ * ‖xs (s + h) - xs s‖ ≤ ‖h‖ * ((1 / c) * ‖h‖) :=
        mul_le_mul_of_nonneg_left e4 (norm_nonneg h)
      rw [abs_le]
      simp only [g]
      constructor
      · nlinarith
      · nlinarith
    refine Asymptotics.IsBigO.trans_isLittleO ?_
      (Asymptotics.isLittleO_norm_pow_id (n := 2) one_lt_two)
    refine Asymptotics.IsBigO.of_bound (1 / c) ?_
    filter_upwards with h
    rw [InnerProductSpace.toDual_apply_apply]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖h‖ ^ 2)]
    exact hb h
  refine ⟨fun s => by rw [hconj s]; exact EReal.coe_lt_top _, g, hconj,
    fun s => (hgrad s).differentiableAt, ?_⟩
  intro s₁ s₂
  rw [(hgrad s₁).gradient, (hgrad s₂).gradient]
  exact hlip s₁ s₂

end FCA_chap_E_4_2_1
