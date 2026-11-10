import ConvexStarLib.Defs

/-!
# `FCA_chap_D_2_1_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_2_1_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_2_1_1`, so the main result is `FCA_chap_D_2_1_1.FCA_chap_D_2_1_1`.
-/

namespace FCA_chap_D_2_1_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_D_2_1_1 (f : E → ℝ) (x : E) (hf_convex : ConvexOn ℝ Set.univ f) :
  let f'_ereal := fun (d : E) => directionalDeriv (liftRealtoEReal f) x d
  let f'_real := fun (d : E) => realDirectionalDeriv f x d
  (∀ x, IsFiniteEReal (f'_ereal x)) ∧
  (∀ x, (f'_ereal x) = (f'_real x : EReal)) ∧
  (∀ (ε : ℝ), (ε > 0) → ∃ δ > 0,
  ∀ (h : E), ‖h‖ ≤ δ →
  abs (f (x + h) - f x - realDirectionalDeriv f x h) ≤ ε • ‖h‖) := by
  intro f'_ereal f'_real
  -- difference quotient
  set q : ℝ → E → ℝ := fun t d => (f (x + t • d) - f x) / t with hq
  -- 1D convexity
  have hφ : ∀ d : E, ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • d)) := by
    intro d
    refine ⟨convex_univ, fun a _ b _ μ ν hμ hν hμν => ?_⟩
    have := hf_convex.2 (Set.mem_univ (x + a • d)) (Set.mem_univ (x + b • d)) hμ hν hμν
    convert this using 2
    obtain rfl : ν = 1 - μ := by linarith
    simp only [smul_eq_mul]
    module
  -- secant monotonicity
  have hmono : ∀ d : E, ∀ s t : ℝ, s ≠ 0 → t ≠ 0 → s ≤ t → q s d ≤ q t d := by
    intro d s t hs ht hst
    have := (hφ d).secant_mono (a := 0) (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _) hs ht hst
    simpa [q] using this
  -- lower bound
  have hlow : ∀ d : E, ∀ t : ℝ, 0 < t → f x - f (x - d) ≤ q t d := by
    intro d t ht
    have := hmono d (-1) t (by norm_num) ht.ne' (by linarith)
    simp only [q] at this
    convert this using 1
    simp only [neg_smul, one_smul, ← sub_eq_add_neg]
    ring
  have hbdd : ∀ d : E, BddBelow ((fun t => q t d) '' Set.Ioi 0) := by
    intro d
    refine ⟨f x - f (x - d), ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hlow d t ht
  -- limit
  set L : E → ℝ := fun d => sInf ((fun t => q t d) '' Set.Ioi 0) with hL
  have htend : ∀ d : E, Filter.Tendsto (fun t => q t d) (𝓝[>] 0) (𝓝 (L d)) := by
    intro d
    apply MonotoneOn.tendsto_nhdsGT
    · intro s hs t ht hst
      exact hmono d s t (ne_of_gt hs) (ne_of_gt ht) hst
    · exact hbdd d
  have hLle : ∀ d : E, ∀ t : ℝ, 0 < t → L d ≤ q t d := by
    intro d t ht
    exact csInf_le (hbdd d) ⟨t, ht, rfl⟩
  -- identify directional derivative
  have hdir : ∀ d : E, directionalDeriv (liftRealtoEReal f) x d = (L d : EReal) := by
    intro d
    unfold directionalDeriv
    have : (fun t => differenceQuotient (liftRealtoEReal f) x d t) =
        fun t => ((q t d : ℝ) : EReal) := by
      funext t
      rfl
    rw [this]
    exact (EReal.tendsto_coe.2 (htend d)).limUnder_eq
  have hreal : ∀ d : E, realDirectionalDeriv f x d = L d := by
    intro d
    unfold realDirectionalDeriv
    rw [hdir d]
    exact EReal.toReal_coe _
  refine ⟨fun d => ⟨L d, hdir d⟩, fun d => ?_, ?_⟩
  · show directionalDeriv (liftRealtoEReal f) x d = ((realDirectionalDeriv f x d : ℝ) : EReal)
    rw [hreal d, hdir d]
  · intro ε hε
    simp only [hreal]
    -- positive homogeneity
    have hhom : ∀ d : E, ∀ c : ℝ, 0 < c → L (c • d) = c * L d := by
      intro d c hc
      have hct : Filter.Tendsto (fun t : ℝ => c * t) (𝓝[>] 0) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have : Filter.Tendsto (fun t : ℝ => c * t) (𝓝 0) (𝓝 (c * 0)) :=
            tendsto_const_nhds.mul Filter.tendsto_id
          rw [mul_zero] at this
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with t ht
          exact mul_pos hc ht
      have h1 : Filter.Tendsto (fun t => c * q (c * t) d) (𝓝[>] 0) (𝓝 (c * L d)) :=
        ((htend d).comp hct).const_mul c
      have h2 : Filter.Tendsto (fun t => c * q (c * t) d) (𝓝[>] 0) (𝓝 (L (c • d))) := by
        refine (htend (c • d)).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht' : t ≠ 0 := ne_of_gt ht
        have hc' : c ≠ 0 := ne_of_gt hc
        simp only [q, smul_smul, mul_comm t c]
        field_simp
      exact tendsto_nhds_unique h2 h1
    have hL0 : L 0 = 0 := by
      have := hhom 0 2 two_pos
      rw [smul_zero] at this
      linarith
    -- local Lipschitz
    obtain ⟨K, U, hU, hKU⟩ := hf_convex.locallyLipschitz x
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
    have hK0 : (0:ℝ) ≤ K := K.coe_nonneg
    have hqlip : ∀ t : ℝ, 0 < t → t < r → ∀ a b : E, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
        q t a ≤ q t b + K * ‖a - b‖ := by
      intro t ht htr a b ha hb
      have hball : ∀ e : E, ‖e‖ ≤ 1 → x + t • e ∈ U := by
        intro e he
        apply hrU
        rw [Metric.mem_ball, dist_eq_norm]
        simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        nlinarith [norm_nonneg e]
      have h1 := hKU.dist_le_mul _ (hball a ha) _ (hball b hb)
      have h1' : dist (x + t • a) (x + t • b) = t * ‖a - b‖ := by
        rw [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
          Real.norm_of_nonneg ht.le]
      rw [h1', Real.dist_eq] at h1
      have h2 : f (x + t • a) - f (x + t • b) ≤ K * (t * ‖a - b‖) := (le_abs_self _).trans h1
      have h3 : (f (x + t • a) - f (x + t • b)) / t ≤ K * ‖a - b‖ := by
        rw [div_le_iff₀ ht]
        linarith
      have h4 : q t a = q t b + (f (x + t • a) - f (x + t • b)) / t := by
        simp only [q]
        ring
      linarith
    have hLlip : ∀ a b : E, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → L a ≤ L b + K * ‖a - b‖ := by
      intro a b ha hb
      have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), q t a ≤ q t b + K * ‖a - b‖ := by
        filter_upwards [Ioo_mem_nhdsGT hr] with t ht
        exact hqlip t ht.1 ht.2 a b ha hb
      exact le_of_tendsto_of_tendsto (htend a) ((htend b).add_const _) hev
    -- finite cover of the unit ball
    set η : ℝ := ε / (3 * (K + 1)) with hη
    have hηpos : 0 < η := by positivity
    have hηeq : η * (3 * ((K:ℝ) + 1)) = ε := by
      rw [hη]
      field_simp
    have hKη : (K:ℝ) * η ≤ ε / 3 := by nlinarith
    obtain ⟨T, hTS, hTfin, hcover⟩ :=
      finite_cover_balls_of_compact (isCompact_closedBall (0:E) 1) hηpos
    have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), t < r ∧ ∀ y ∈ T, q t y < L y + ε / 3 := by
      refine Filter.Eventually.and ?_ ?_
      · filter_upwards [Ioo_mem_nhdsGT hr] with t ht
        exact ht.2
      · rw [hTfin.eventually_all]
        intro y _
        exact (htend y).eventually_lt_const (by linarith)
    obtain ⟨δ₀, hδ₀, hδ₀prop⟩ := (nhdsGT_basis (0:ℝ)).eventually_iff.1 hev
    refine ⟨δ₀ / 2, by positivity, fun h hh => ?_⟩
    rcases eq_or_ne h 0 with rfl | hne
    · simp [hL0]
    · set t := ‖h‖ with ht_def
      have htpos : 0 < t := norm_pos_iff.2 hne
      have htδ : t < δ₀ := by linarith
      obtain ⟨htr, hT⟩ := hδ₀prop ⟨htpos, htδ⟩
      set d := t⁻¹ • h with hd
      have hdn : ‖d‖ = 1 := by
        rw [hd, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ htpos.ne']
      have hhd : h = t • d := by
        rw [hd, smul_smul, mul_inv_cancel₀ htpos.ne', one_smul]
      have hdS : d ∈ Metric.closedBall (0:E) 1 := by
        rw [mem_closedBall_zero_iff, hdn]
      obtain ⟨y, hyT, hdy⟩ : ∃ y ∈ T, d ∈ Metric.ball y η := by
        have := hcover hdS
        simpa only [Set.mem_iUnion, exists_prop] using this
      have hyS : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.1 (hTS hyT)
      have hdy' : ‖d - y‖ < η := by rwa [Metric.mem_ball, dist_eq_norm] at hdy
      have hyd' : ‖y - d‖ < η := by rwa [norm_sub_rev]
      have e1 : q t d ≤ q t y + K * ‖d - y‖ := hqlip t htpos htr d y hdn.le hyS
      have e2 : q t y < L y + ε / 3 := hT y hyT
      have e3 : L y ≤ L d + K * ‖y - d‖ := hLlip y d hyS hdn.le
      have e4 : L d ≤ q t d := hLle d t htpos
      have hKd1 : (K:ℝ) * ‖d - y‖ ≤ K * η := mul_le_mul_of_nonneg_left hdy'.le hK0
      have hKd2 : (K:ℝ) * ‖y - d‖ ≤ K * η := mul_le_mul_of_nonneg_left hyd'.le hK0
      have hmain : |q t d - L d| ≤ ε := by
        rw [abs_le]
        constructor <;> linarith
      have hfx : f (x + h) - f x = t * q t d := by
        simp only [q]
        rw [← hhd]
        field_simp
      have hLh : L h = t * L d := by
        rw [hhd]
        exact hhom d t htpos
      rw [hLh, hfx, ← mul_sub, abs_mul, abs_of_pos htpos, smul_eq_mul, mul_comm ε t]
      exact mul_le_mul_of_nonneg_left hmain htpos.le

end FCA_chap_D_2_1_1
