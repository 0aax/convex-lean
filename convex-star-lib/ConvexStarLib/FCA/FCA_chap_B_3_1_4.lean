import ConvexStarLib.Defs

/-!
# `FCA_chap_B_3_1_4`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_3_1_4` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_3_1_4`, so the main result is `FCA_chap_B_3_1_4.FCA_chap_B_3_1_4`.
-/

namespace FCA_chap_B_3_1_4

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_B_3_1_4
  (fk : ℕ → E → ℝ)
  (f : E → ℝ)
  (hfk_convex : ∀ k, InConvRn (liftRealtoEReal (fk k)))
  (hfk_pointwise : ∀ x, Filter.Tendsto (fun k ↦ fk k x) Filter.atTop (𝓝 (f x))) :
  InConvRn (liftRealtoEReal f) ∧
  ∀ (S : Set E), IsCompact S → TendstoUniformlyOn fk f Filter.atTop S := by
  have hepi : ∀ g : E → ℝ, epigraph (liftRealtoEReal g) =
      {p : E × ℝ | p.1 ∈ (Set.univ : Set E) ∧ g p.1 ≤ p.2} := by
    intro g
    ext p
    simp [epigraph, liftRealtoEReal]
  have hconv : ∀ k, ConvexOn ℝ Set.univ (fk k) := by
    intro k
    rw [convexOn_iff_convex_epigraph, ← hepi]
    exact (hfk_convex k).2.2
  have hfconv : ConvexOn ℝ Set.univ f := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have h1 := hfk_pointwise (a • x + b • y)
    have h2 : Filter.Tendsto (fun k => a • fk k x + b • fk k y) Filter.atTop
        (𝓝 (a • f x + b • f y)) :=
      ((hfk_pointwise x).const_smul a).add ((hfk_pointwise y).const_smul b)
    exact le_of_tendsto_of_tendsto' h1 h2 (fun k => (hconv k).2 trivial trivial ha hb hab)
  refine ⟨⟨fun x => EReal.bot_lt_coe _, ⟨0, EReal.coe_lt_top _⟩, ?_⟩, ?_⟩
  · unfold ConvexEReal
    rw [hepi]
    exact hfconv.convex_epigraph
  · intro S hS
    -- local uniform bound
    have hbound : ∀ x₀ : E, ∃ r > 0, ∃ M, ∀ k, ∀ x, dist x x₀ < r → |fk k x| ≤ M := by
      intro x₀
      obtain ⟨b, hb, -⟩ := exists_mem_interior_convexHull_affineBasis
        (Filter.univ_mem (f := 𝓝 x₀))
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x₀ hb
      have hvert : ∃ B, ∀ k, ∀ i, fk k (b i) ≤ B := by
        have : ∀ i, ∃ B, ∀ k, fk k (b i) ≤ B := by
          intro i
          obtain ⟨B, hB⟩ := (hfk_pointwise (b i)).bddAbove_range
          exact ⟨B, fun k => hB ⟨k, rfl⟩⟩
        choose B hB using this
        exact ⟨Finset.univ.sup' Finset.univ_nonempty B,
          fun k i => (hB i k).trans (Finset.le_sup' B (Finset.mem_univ i))⟩
      obtain ⟨B, hB⟩ := hvert
      have hup : ∀ k, ∀ x, dist x x₀ < r → fk k x ≤ B := by
        intro k x hx
        have hxmem : x ∈ convexHull ℝ (Set.range b) :=
          interior_subset (hball (Metric.mem_ball.2 hx))
        obtain ⟨y, ⟨i, rfl⟩, hy⟩ :=
          (hconv k).exists_ge_of_mem_convexHull (Set.subset_univ _) hxmem
        exact hy.trans (hB k i)
      obtain ⟨C, hC⟩ : ∃ C, ∀ k, |fk k x₀| ≤ C := by
        obtain ⟨C, hC⟩ := (hfk_pointwise x₀).abs.bddAbove_range
        exact ⟨C, fun k => hC ⟨k, rfl⟩⟩
      refine ⟨r, hr, max B (2 * C + B), fun k x hx => ?_⟩
      rw [abs_le]
      constructor
      · have hx' : dist ((2:ℝ) • x₀ - x) x₀ < r := by
          rw [dist_eq_norm] at hx ⊢
          have : (2:ℝ) • x₀ - x - x₀ = -(x - x₀) := by
            rw [two_smul]; abel
          rw [this, norm_neg]
          exact hx
        have hmid : fk k x₀ ≤ (1/2 : ℝ) • fk k x + (1/2 : ℝ) • fk k ((2:ℝ) • x₀ - x) := by
          have := (hconv k).2 (Set.mem_univ x) (Set.mem_univ ((2:ℝ) • x₀ - x))
            (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
          convert this using 2
          rw [smul_sub, smul_smul]
          norm_num
        have h1 := hup k _ hx'
        have h2 := (abs_le.1 (hC k)).1
        simp only [smul_eq_mul] at hmid
        have : -(2 * C + B) ≤ fk k x := by linarith
        exact le_trans (neg_le_neg (le_max_right _ _)) this
      · exact (hup k x hx).trans (le_max_left _ _)
    -- equicontinuity
    have heq : Equicontinuous fk := by
      intro x₀
      obtain ⟨r, hr, M, hM⟩ := hbound x₀
      have hlip : ∀ k, LipschitzOnWith (2 * M / (r/2)).toNNReal (fk k)
          (Metric.ball x₀ (r - r/2)) :=
        fun k => ((hconv k).subset (Set.subset_univ _) (convex_ball _ _)).lipschitzOnWith_of_abs_le
          (half_pos hr) (hM k)
      refine Metric.equicontinuousAt_of_continuity_modulus
        (fun x => ((2 * M / (r/2)).toNNReal : ℝ) * dist x₀ x) ?_ fk ?_
      · have hc : Continuous (fun x => ((2 * M / (r/2)).toNNReal : ℝ) * dist x₀ x) :=
          continuous_const.mul (continuous_const.dist continuous_id)
        simpa using hc.tendsto x₀
      · filter_upwards [Metric.ball_mem_nhds x₀ (by linarith : (0:ℝ) < r - r/2)] with x hx i
        exact (hlip i).dist_le_mul x₀ (Metric.mem_ball_self (by linarith)) x hx
    -- Ascoli
    have key := (EquicontinuousOn.tendsto_uniformOnFun_iff_pi' (𝔖 := {S})
      (by simpa using hS) (fun K _ => heq.equicontinuousOn K) Filter.atTop f).2
      (tendsto_pi_nhds.2 fun x => hfk_pointwise x)
    exact UniformOnFun.tendsto_iff_tendstoUniformlyOn.1 key S (Set.mem_singleton S)

end FCA_chap_B_3_1_4
