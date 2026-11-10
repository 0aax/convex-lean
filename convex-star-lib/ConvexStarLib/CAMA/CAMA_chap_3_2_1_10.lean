import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_2_1_10`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_2_1_10` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_2_1_10`, so the main result is `CAMA_chap_3_2_1_10.CAMA_chap_3_2_1_10`.
-/

namespace CAMA_chap_3_2_1_10

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_2_1_10
  (C₁ : Set E)
  (C₂ : Set E)
  (hC₁ : Convex ℝ C₁)
  (hC₂ : Convex ℝ C₂)
  (hC : Set.Nonempty (intrinsicInterior ℝ C₁ ∩ intrinsicInterior ℝ C₂)) :
  (intrinsicInterior ℝ (C₁ ∩ C₂) = intrinsicInterior ℝ C₁ ∩ intrinsicInterior ℝ C₂) ∧
  (closure (C₁ ∩ C₂) = closure C₁ ∩ closure C₂) := by
  -- Metric characterization of the intrinsic (relative) interior.
  have mem_iff : ∀ {C : Set E} {x : E}, x ∈ intrinsicInterior ℝ C ↔
      x ∈ C ∧ ∃ ε > 0, ∀ y ∈ affineSpan ℝ C, dist y x < ε → y ∈ C := by
    intro C x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨intrinsicInterior_subset ⟨y, hy, rfl⟩, ?_⟩
      rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hy
      obtain ⟨ε, hε, hball⟩ := hy
      refine ⟨ε, hε, fun z hz hzd => ?_⟩
      exact hball (show (⟨z, hz⟩ : affineSpan ℝ C) ∈ Metric.ball y ε from hzd)
    · rintro ⟨hx, ε, hε, h⟩
      refine ⟨⟨x, subset_affineSpan ℝ C hx⟩, ?_, rfl⟩
      rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
      exact ⟨ε, hε, fun z hz => h z z.2 hz⟩
  -- Rockafellar, Theorem 6.1: if `x ∈ ri C` and `y ∈ cl C`, then `(1 - t) x + t y ∈ ri C`
  -- for `0 ≤ t < 1`.
  have key : ∀ {C : Set E}, Convex ℝ C → ∀ {x y : E}, x ∈ intrinsicInterior ℝ C →
      y ∈ closure C → ∀ {t : ℝ}, 0 ≤ t → t < 1 →
      (1 - t) • x + t • y ∈ intrinsicInterior ℝ C := by
    intro C hC x y hx hy t ht0 ht1
    rw [mem_iff] at hx ⊢
    obtain ⟨hxC, ε, hε, hball⟩ := hx
    set A := affineSpan ℝ C with hA
    have hAclosed : IsClosed (A : Set E) := A.closed_of_finiteDimensional
    have hyA : y ∈ A := closure_minimal (subset_affineSpan ℝ C) hAclosed hy
    have hxA : x ∈ A := subset_affineSpan ℝ C hxC
    have h1t : 0 < 1 - t := by linarith
    have hzA : (1 - t) • x + t • y ∈ A := by
      have := A.smul_vsub_vadd_mem t hyA hxA hxA
      convert this using 1
      rw [vsub_eq_sub, vadd_eq_add]
      module
    have hmain : ∀ w ∈ A, dist w ((1 - t) • x + t • y) < (1 - t) * ε / 2 → w ∈ C := by
      intro w hwA hwz
      obtain ⟨y', hy'C, hyy'⟩ : ∃ y' ∈ C, dist y y' < (1 - t) * ε / 2 / (t + 1) := by
        rw [Metric.mem_closure_iff] at hy
        exact hy _ (by positivity)
      have hy'A : y' ∈ A := subset_affineSpan ℝ C hy'C
      set x' := (1 - t)⁻¹ • (w - y') + y' with hx'
      have h1 : (1 - t) • x' = (w - y') + (1 - t) • y' := by
        simp only [x', smul_add, smul_smul, mul_inv_cancel₀ h1t.ne', one_smul]
      have hw : w = (1 - t) • x' + t • y' := by
        rw [h1]; module
      have h2 : (1 - t) • (x' - x) = (w - ((1 - t) • x + t • y)) + t • (y - y') := by
        rw [smul_sub, h1]; module
      have hx'A : x' ∈ A := by
        have := A.smul_vsub_vadd_mem (1 - t)⁻¹ hwA hy'A hy'A
        convert this using 1
      have hx'x : dist x' x < ε := by
        rw [dist_eq_norm]
        have h3 : (1 - t) * ‖x' - x‖ = ‖(w - ((1 - t) • x + t • y)) + t • (y - y')‖ := by
          rw [← h2, norm_smul, Real.norm_of_nonneg h1t.le]
        have h4 : ‖(w - ((1 - t) • x + t • y)) + t • (y - y')‖ ≤
            ‖w - ((1 - t) • x + t • y)‖ + t * ‖y - y'‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_of_nonneg ht0]
        rw [← dist_eq_norm, ← dist_eq_norm] at h4
        have h5 : t * dist y y' ≤ (1 - t) * ε / 2 := by
          have : dist y y' * (t + 1) < (1 - t) * ε / 2 := by
            rwa [lt_div_iff₀ (by linarith)] at hyy'
          nlinarith [dist_nonneg (x := y) (y := y')]
        by_contra hcon
        push_neg at hcon
        nlinarith
      have hx'C := hball x' hx'A hx'x
      rw [hw]
      exact hC hx'C hy'C h1t.le ht0 (by ring)
    exact ⟨hmain _ hzA (by simp; positivity), (1 - t) * ε / 2, by positivity, hmain⟩
  obtain ⟨x, hx1, hx2⟩ := hC
  have hxC : x ∈ C₁ ∩ C₂ := ⟨intrinsicInterior_subset hx1, intrinsicInterior_subset hx2⟩
  constructor
  · ext z
    constructor
    · intro hz
      obtain ⟨hzC, ε, hε, hball⟩ := mem_iff.1 hz
      set A := affineSpan ℝ (C₁ ∩ C₂) with hA
      -- Extend the segment from `x` through `z` slightly beyond `z`.
      set δ := ε / (2 * (‖z - x‖ + 1)) with hδ
      have hδpos : 0 < δ := by positivity
      set y := z + δ • (z - x) with hy
      have hyA : y ∈ A := by
        have := A.smul_vsub_vadd_mem δ (subset_affineSpan ℝ _ hzC) (subset_affineSpan ℝ _ hxC)
          (subset_affineSpan ℝ _ hzC)
        convert this using 1
        rw [vsub_eq_sub, vadd_eq_add, add_comm]
      have hyz : dist y z < ε := by
        rw [dist_eq_norm, hy, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδpos.le, hδ]
        have hpos : 0 < ‖z - x‖ + 1 := by positivity
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg (z - x)]
      have hyC := hball y hyA hyz
      set t := (1 + δ)⁻¹ with ht
      have ht0 : 0 ≤ t := by positivity
      have ht1 : t < 1 := inv_lt_one_of_one_lt₀ (by linarith)
      have hzeq : (1 - t) • x + t • y = z := by
        have h : t * (1 + δ) = 1 := inv_mul_cancel₀ (by positivity)
        calc (1 - t) • x + t • y = (1 - t * (1 + δ)) • x + (t * (1 + δ)) • z := by
              rw [hy]; module
          _ = z := by rw [h]; simp
      rw [← hzeq]
      exact ⟨key hC₁ hx1 (subset_closure hyC.1) ht0 ht1,
        key hC₂ hx2 (subset_closure hyC.2) ht0 ht1⟩
    · rintro ⟨hz1, hz2⟩
      rw [mem_iff] at hz1 hz2 ⊢
      obtain ⟨hzC1, ε₁, hε₁, h1⟩ := hz1
      obtain ⟨hzC2, ε₂, hε₂, h2⟩ := hz2
      refine ⟨⟨hzC1, hzC2⟩, min ε₁ ε₂, lt_min hε₁ hε₂, fun w hw hwz => ⟨?_, ?_⟩⟩
      · exact h1 w (affineSpan_mono ℝ Set.inter_subset_left hw)
          (lt_of_lt_of_le hwz (min_le_left _ _))
      · exact h2 w (affineSpan_mono ℝ Set.inter_subset_right hw)
          (lt_of_lt_of_le hwz (min_le_right _ _))
  · apply Set.Subset.antisymm (closure_inter_subset_inter_closure _ _)
    rintro y ⟨hy1, hy2⟩
    have hmem : ∀ t : ℝ, 0 ≤ t → t < 1 → (1 - t) • x + t • y ∈ C₁ ∩ C₂ := fun t ht0 ht1 =>
      ⟨intrinsicInterior_subset (key hC₁ hx1 hy1 ht0 ht1),
        intrinsicInterior_subset (key hC₂ hx2 hy2 ht0 ht1)⟩
    have hcont : Continuous (fun t : ℝ => (1 - t) • x + t • y) := by fun_prop
    have htend : Filter.Tendsto (fun t : ℝ => (1 - t) • x + t • y) (𝓝[<] 1) (𝓝 y) := by
      have h := hcont.tendsto 1
      simp only [sub_self, zero_smul, one_smul, zero_add] at h
      exact h.mono_left nhdsWithin_le_nhds
    apply mem_closure_of_tendsto htend
    have hev : ∀ᶠ t in 𝓝[<] (1:ℝ), t ∈ Set.Ioo 0 1 := Ioo_mem_nhdsLT (by norm_num)
    filter_upwards [hev] with t ht
    exact hmem t ht.1.le ht.2

end CAMA_chap_3_2_1_10
