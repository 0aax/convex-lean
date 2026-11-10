import ConvexStarLib.Defs

/-!
# `FCA_chap_B_ex_21`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_ex_21` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_ex_21`, so the main result is `FCA_chap_B_ex_21.FCA_chap_B_ex_21`.
-/

namespace FCA_chap_B_ex_21

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_B_ex_21
  (C : Set E)
  (hC_nonempty : Set.Nonempty C)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C)
  (x₀ : E)
  (hx₀ : x₀ ∈ C) :
  let d_C : E → EReal := fun x => Metric.infDist x C
  ∀ d : E,
    asymptoticFun d_C d = (Metric.infDist d (asymptoticConeAt C x₀) : EReal) := by
  intro d_C d
  set K := asymptoticConeAt C x₀ with hK
  have hK0 : (0 : E) ∈ K := by
    intro t ht; simpa using hx₀
  have hK_closed : IsClosed K := by
    have : K = ⋂ t ∈ Set.Ioi (0:ℝ), (fun v => x₀ + t • v) ⁻¹' C := by
      ext v; simp [K, asymptoticConeAt]
    rw [this]
    exact isClosed_biInter fun t _ => hC_closed.preimage (by fun_prop)
  have key1 : (d, Metric.infDist d K) ∈ horizonCone (epigraph d_C) := by
    obtain ⟨c, hcK, hc⟩ := hK_closed.exists_infDist_eq_dist ⟨0, hK0⟩ d
    set δ := Metric.infDist d K
    refine ⟨fun i : ℕ => (((i:ℝ) + 1) • d, ((i:ℝ)+1) * δ + ‖x₀‖), fun i => 1 / ((i:ℝ) + 1), ?_, ?_, ?_⟩
    · intro i
      show d_C _ ≤ _
      simp only [d_C]
      rw [EReal.coe_le_coe_iff]
      have hi : (0:ℝ) < (i:ℝ) + 1 := by positivity
      have hmem : x₀ + ((i:ℝ)+1) • c ∈ C := hcK _ hi
      calc Metric.infDist (((i:ℝ) + 1) • d) C ≤ dist (((i:ℝ) + 1) • d) (x₀ + ((i:ℝ)+1) • c) :=
            Metric.infDist_le_dist_of_mem hmem
        _ = ‖((i:ℝ)+1) • (d - c) - x₀‖ := by rw [dist_eq_norm, smul_sub]; congr 1; abel
        _ ≤ ‖((i:ℝ)+1) • (d - c)‖ + ‖x₀‖ := norm_sub_le _ _
        _ = ((i:ℝ)+1) * δ + ‖x₀‖ := by
            rw [norm_smul, hc, dist_eq_norm, Real.norm_of_nonneg hi.le]
    · apply tendsto_nhdsWithin_iff.mpr
      exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Filter.Eventually.of_forall fun i => by
        simp only [Set.mem_Ioi]; positivity⟩
    · have : (fun i : ℕ => (1 / ((i:ℝ) + 1)) • (((i:ℝ) + 1) • d, ((i:ℝ)+1) * δ + ‖x₀‖)) =
          fun i : ℕ => (d, δ + ‖x₀‖ * (1 / ((i:ℝ)+1))) := by
        funext i
        have hi : (i:ℝ) + 1 ≠ 0 := by positivity
        ext
        · simp only [Prod.smul_fst, smul_smul]
          rw [one_div_mul_cancel hi, one_smul]
        · simp only [Prod.smul_snd, smul_eq_mul]
          field_simp
      rw [this]
      apply Filter.Tendsto.prodMk_nhds tendsto_const_nhds
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ‖x₀‖
      simpa using this.const_add δ
  have key2 : ∀ r : ℝ, (d, r) ∈ horizonCone (epigraph d_C) → Metric.infDist d K ≤ r := by
    rintro r ⟨p, l, hp, hl, hconv⟩
    have hl_pos : ∀ᶠ i in Filter.atTop, 0 < l i := hl.eventually self_mem_nhdsWithin
    have hl0 : Filter.Tendsto l Filter.atTop (𝓝 0) := hl.mono_right nhdsWithin_le_nhds
    have hx : Filter.Tendsto (fun i => l i • (p i).1) Filter.atTop (𝓝 d) :=
      (continuous_fst.tendsto _).comp hconv
    have hr : Filter.Tendsto (fun i => l i * (p i).2) Filter.atTop (𝓝 r) :=
      (continuous_snd.tendsto _).comp hconv
    have hp' : ∀ i, Metric.infDist (p i).1 C ≤ (p i).2 := fun i => EReal.coe_le_coe_iff.mp (hp i)
    have : ∀ i, ∃ c ∈ C, Metric.infDist (p i).1 C = dist (p i).1 c := fun i =>
      hC_closed.exists_infDist_eq_dist hC_nonempty _
    choose c hcC hc using this
    set y : ℕ → E := fun i => l i • c i with hy
    have hy_close : ∀ᶠ i in Filter.atTop, ‖l i • (p i).1 - y i‖ ≤ l i * (p i).2 := by
      filter_upwards [hl_pos] with i hi
      simp only [y]
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg hi.le, ← dist_eq_norm, ← hc i]
      exact mul_le_mul_of_nonneg_left (hp' i) hi.le
    have hbdd : ∀ᶠ i in Filter.atTop, y i ∈ Metric.closedBall (0:E) (‖d‖ + r + 2) := by
      have h1 := hx.norm.eventually (gt_mem_nhds (lt_add_one ‖d‖))
      have h2 := hr.eventually (gt_mem_nhds (lt_add_one r))
      filter_upwards [h1, h2, hy_close] with i h1 h2 h3
      rw [mem_closedBall_zero_iff]
      calc ‖y i‖ = ‖l i • (p i).1 - (l i • (p i).1 - y i)‖ := by congr 1; abel
        _ ≤ ‖l i • (p i).1‖ + ‖l i • (p i).1 - y i‖ := norm_sub_le _ _
        _ ≤ ‖d‖ + r + 2 := by linarith
    obtain ⟨c₀, -, ns, hns, hnsc⟩ :=
      tendsto_subseq_of_frequently_bounded Metric.isBounded_closedBall hbdd.frequently
    have hc₀K : c₀ ∈ K := by
      intro t ht
      have hlns : Filter.Tendsto (l ∘ ns) Filter.atTop (𝓝 0) := hl0.comp hns.tendsto_atTop
      have hconv' : Filter.Tendsto (fun k => (1 - t * l (ns k)) • x₀ + t • y (ns k)) Filter.atTop
          (𝓝 (x₀ + t • c₀)) := by
        have h1 : Filter.Tendsto (fun k => (1 - t * l (ns k))) Filter.atTop (𝓝 1) := by
          have := hlns.const_mul t
          simpa using (tendsto_const_nhds (x := (1:ℝ))).sub this
        have h2 := h1.smul_const x₀
        rw [one_smul] at h2
        exact h2.add (hnsc.const_smul t)
      apply hC_closed.mem_of_tendsto hconv'
      have hev1 : ∀ᶠ k in Filter.atTop, 0 < l (ns k) := hns.tendsto_atTop.eventually hl_pos
      have hev2 : ∀ᶠ k in Filter.atTop, t * l (ns k) < 1 :=
        (hlns.const_mul t).eventually (gt_mem_nhds (by simp))
      filter_upwards [hev1, hev2] with k hk1 hk2
      have : (1 - t * l (ns k)) • x₀ + t • y (ns k) = (1 - t * l (ns k)) • x₀ + (t * l (ns k)) • c (ns k) := by
        simp only [y, smul_smul]
      rw [this]
      exact hC_convex hx₀ (hcC _) (by linarith) (by positivity) (by ring)
    have hdist : dist d c₀ ≤ r := by
      rw [dist_eq_norm]
      have hA : Filter.Tendsto (fun k => ‖l (ns k) • (p (ns k)).1 - y (ns k)‖) Filter.atTop (𝓝 ‖d - c₀‖) :=
        ((hx.comp hns.tendsto_atTop).sub hnsc).norm
      have hB : Filter.Tendsto (fun k => l (ns k) * (p (ns k)).2) Filter.atTop (𝓝 r) :=
        hr.comp hns.tendsto_atTop
      exact le_of_tendsto_of_tendsto hA hB (hns.tendsto_atTop.eventually hy_close)
    calc Metric.infDist d K ≤ dist d c₀ := Metric.infDist_le_dist_of_mem hc₀K
      _ ≤ r := hdist
  unfold asymptoticFun funFromSet
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨_, key1, rfl⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact EReal.coe_le_coe_iff.mpr (key2 r hr)

end FCA_chap_B_ex_21
