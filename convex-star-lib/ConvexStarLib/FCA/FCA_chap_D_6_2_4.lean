import ConvexStarLib.Defs

/-!
# `FCA_chap_D_6_2_4`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_6_2_4` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_6_2_4`, so the main result is `FCA_chap_D_6_2_4.FCA_chap_D_6_2_4`.
-/

namespace FCA_chap_D_6_2_4

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_D_6_2_4
    (f : E → ℝ)
    (x : E)
    (hf_convex : ConvexOn ℝ Set.univ f) :
    let subdiff_neighborhood := fun (ε : ℝ) =>
      {v | ∃ w d, ‖d‖ ≤ ε ∧
        w ∈ directionalSubdifferential (liftRealtoEReal f) x ∧ v = w + d}
    ∀ ε > 0, ∃ δ > 0, ∀ y,
      y ∈ Metric.ball x δ →
        directionalSubdifferential (liftRealtoEReal f) y ⊆ subdiff_neighborhood ε := by
  intro subdiff_neighborhood ε hε
  -- continuity
  have hcont : Continuous f := hf_convex.locallyLipschitz.continuous
  -- the difference quotient is the coercion of the real difference quotient
  have hDQ : ∀ y d t, differenceQuotient (liftRealtoEReal f) y d t
      = (((f (y + t • d) - f y) / t : ℝ) : EReal) := by
    intro y d t
    simp only [differenceQuotient, liftRealtoEReal, EReal.coe_div, EReal.coe_sub]
  -- monotonicity of the real difference quotient
  have hmono : ∀ y d, MonotoneOn (fun t : ℝ => (f (y + t • d) - f y) / t) (Set.Ioi 0) := by
    intro y d
    have hline : ConvexOn ℝ Set.univ (fun t : ℝ => f (y + t • d)) := by
      refine ⟨convex_univ, fun a _ b _ α β hα hβ hαβ => ?_⟩
      have h := hf_convex.2 (Set.mem_univ (y + a • d)) (Set.mem_univ (y + b • d)) hα hβ hαβ
      have heq : y + (α • a + β • b) • d = α • (y + a • d) + β • (y + b • d) := by
        obtain rfl : β = 1 - α := by linarith
        simp only [smul_eq_mul]
        module
      simp only
      rw [heq]
      exact h
    intro s hs t ht hst
    have := hline.secant_mono (a := 0) (Set.mem_univ 0) (Set.mem_univ s) (Set.mem_univ t)
      (ne_of_gt hs) (ne_of_gt ht) hst
    simpa using this
  -- the difference quotient converges to the directional derivative
  have htends : ∀ y d, Filter.Tendsto (fun t => differenceQuotient (liftRealtoEReal f) y d t)
      (𝓝[>] 0) (𝓝 (directionalDeriv (liftRealtoEReal f) y d)) := by
    intro y d
    apply tendsto_nhds_limUnder
    refine ⟨_, MonotoneOn.tendsto_nhdsGT ?_ (OrderBot.bddBelow _)⟩
    intro s hs t ht hst
    simp only [hDQ]
    exact EReal.coe_le_coe_iff.2 (hmono y d hs ht hst)
  -- subgradient inequality from the directional subdifferential
  have hsub : ∀ y s, s ∈ directionalSubdifferential (liftRealtoEReal f) y →
      ∀ z, f y + inner ℝ s (z - y) ≤ f z := by
    intro y s hs z
    have h1 : ((inner ℝ s (z - y) : ℝ) : EReal)
        ≤ directionalDeriv (liftRealtoEReal f) y (z - y) := hs (z - y)
    have h2 : directionalDeriv (liftRealtoEReal f) y (z - y) ≤ ((f z - f y : ℝ) : EReal) := by
      apply le_of_tendsto (htends y (z - y))
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
      rw [hDQ, EReal.coe_le_coe_iff]
      have := hmono y (z - y) ht.1 (show (1:ℝ) ∈ Set.Ioi 0 by norm_num) ht.2.le
      simp only at this
      convert this using 1
      simp
    have := EReal.coe_le_coe_iff.1 (h1.trans h2)
    linarith
  -- converse: subgradient inequality gives membership in the directional subdifferential
  have hsub' : ∀ s, (∀ z, f x + inner ℝ s (z - x) ≤ f z) →
      s ∈ directionalSubdifferential (liftRealtoEReal f) x := by
    intro s hs d
    show ((inner ℝ s d : ℝ) : EReal) ≤ directionalDeriv (liftRealtoEReal f) x d
    apply ge_of_tendsto (htends x d)
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hDQ, EReal.coe_le_coe_iff]
    have ht' : (0:ℝ) < t := ht
    have := hs (x + t • d)
    rw [le_div_iff₀ ht']
    simp only [add_sub_cancel_left, inner_smul_right] at this
    linarith
  -- local boundedness of subgradients
  obtain ⟨K, hK⟩ : ∃ K, ∀ z ∈ Metric.closedBall x 2, ‖f z‖ ≤ K :=
    (isCompact_closedBall x 2).exists_bound_of_continuousOn hcont.continuousOn
  have hbound : ∀ y ∈ Metric.ball x 1, ∀ s, s ∈ directionalSubdifferential (liftRealtoEReal f) y →
      ‖s‖ ≤ 2 * K := by
    intro y hy s hs
    have hy2 : y ∈ Metric.closedBall x 2 := by
      rw [Metric.mem_closedBall]
      rw [Metric.mem_ball] at hy
      linarith
    have hKy := hK y hy2
    rcases eq_or_ne s 0 with rfl | hs0
    · simp only [norm_zero]
      linarith [norm_nonneg (f y)]
    have hnorm : 0 < ‖s‖ := norm_pos_iff.2 hs0
    have hz : y + (1 / ‖s‖) • s ∈ Metric.closedBall x 2 := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      calc ‖y + (1 / ‖s‖) • s - x‖ = ‖(y - x) + (1 / ‖s‖) • s‖ := by congr 1; abel
        _ ≤ ‖y - x‖ + ‖(1 / ‖s‖) • s‖ := norm_add_le _ _
        _ ≤ 1 + 1 := by
          gcongr
          · rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hy).le
          · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
            field_simp
            rfl
        _ = 2 := by norm_num
    have h1 := hsub y s hs (y + (1 / ‖s‖) • s)
    simp only [add_sub_cancel_left, inner_smul_right, real_inner_self_eq_norm_sq] at h1
    have h2 := hK _ hz
    have h3 : 1 / ‖s‖ * ‖s‖ ^ 2 = ‖s‖ := by field_simp
    rw [h3] at h1
    rw [Real.norm_eq_abs] at h2 hKy
    have h2' := (abs_le.1 h2).2
    have hKy' := (abs_le.1 hKy).1
    linarith
  -- main argument by contradiction
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ n : ℕ, ∃ y ∈ Metric.ball x (1 / ((n : ℝ) + 1)),
      ∃ s ∈ directionalSubdifferential (liftRealtoEReal f) y, s ∉ subdiff_neighborhood ε := by
    intro n
    obtain ⟨y, hy, hny⟩ := hcon (1 / ((n : ℝ) + 1)) (by positivity)
    rw [Set.not_subset] at hny
    obtain ⟨s, hs, hnotin⟩ := hny
    exact ⟨y, hy, s, hs, hnotin⟩
  choose y hy s hs hnotin using hseq
  have hy_lim : Filter.Tendsto y Filter.atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => (Metric.mem_ball.1 (hy n)).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hs_bdd : ∀ n, s n ∈ Metric.closedBall (0 : E) (2 * K) := by
    intro n
    rw [mem_closedBall_zero_iff]
    apply hbound (y n) _ (s n) (hs n)
    have := hy n
    rw [Metric.mem_ball] at this ⊢
    calc dist (y n) x < 1 / ((n : ℝ) + 1) := this
      _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  obtain ⟨a, -, ns, hns_mono, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hs_bdd
  have ha : a ∈ directionalSubdifferential (liftRealtoEReal f) x := by
    apply hsub'
    intro z
    have hyns : Filter.Tendsto (y ∘ ns) Filter.atTop (𝓝 x) := hy_lim.comp hns_mono.tendsto_atTop
    have hT : Filter.Tendsto (fun n => f (y (ns n)) + inner ℝ (s (ns n)) (z - y (ns n)))
        Filter.atTop (𝓝 (f x + inner ℝ a (z - x))) := by
      apply Filter.Tendsto.add
      · exact (hcont.tendsto x).comp hyns
      · apply Filter.Tendsto.inner hlim
        exact tendsto_const_nhds.sub hyns
    exact le_of_tendsto' hT (fun n => hsub (y (ns n)) (s (ns n)) (hs (ns n)) z)
  have hev : ∀ᶠ n in Filter.atTop, dist (s (ns n)) a < ε := (Metric.tendsto_nhds.1 hlim) ε hε
  obtain ⟨N, hN⟩ := hev.exists
  apply hnotin (ns N)
  refine ⟨a, s (ns N) - a, ?_, ha, ?_⟩
  · rw [← dist_eq_norm]; exact hN.le
  · abel

end FCA_chap_D_6_2_4
