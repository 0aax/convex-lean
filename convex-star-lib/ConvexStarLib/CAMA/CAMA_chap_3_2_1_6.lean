import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_2_1_6`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_2_1_6` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_2_1_6`, so the main result is `CAMA_chap_3_2_1_6.CAMA_chap_3_2_1_6`.
-/

namespace CAMA_chap_3_2_1_6

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem CAMA_chap_3_2_1_6
  (x₁ : E)
  (x₂ : E)
  (C : Set E)
  (hC_nonempty : Set.Nonempty C)
  (hC_convex : Convex ℝ C)
  (hx₁ : x₁ ∈ closure C)
  (hx₂ : x₂ ∈ (intrinsicInterior ℝ C)) :
  {v : E | ∃ (α : ℝ), (0 ≤ α) ∧ (α < 1) ∧
                                  (v = α • x₁ + (1-α) • x₂)} ⊆ intrinsicInterior ℝ C := by
  -- Metric characterization of the intrinsic interior: a point of the affine span such that
  -- some ball around it, intersected with the affine span, lies in `C`.
  have key : ∀ x : E, x ∈ intrinsicInterior ℝ C ↔
      x ∈ affineSpan ℝ C ∧ ∃ ε > 0, ∀ y ∈ affineSpan ℝ C, dist y x < ε → y ∈ C := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      rw [mem_interior_iff_mem_nhds, mem_nhds_induced] at hy
      obtain ⟨u, hu, hsub⟩ := hy
      obtain ⟨ε, εpos, hball⟩ := Metric.mem_nhds_iff.1 hu
      refine ⟨ε, εpos, fun z hz hdist => ?_⟩
      exact hsub (show (⟨z, hz⟩ : affineSpan ℝ C) ∈ Subtype.val ⁻¹' u from hball hdist)
    · rintro ⟨hx, ε, εpos, hball⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      rw [mem_interior_iff_mem_nhds, mem_nhds_induced]
      refine ⟨Metric.ball x ε, Metric.ball_mem_nhds x εpos, ?_⟩
      rintro ⟨z, hz⟩ hz'
      exact hball z hz hz'
  rintro v ⟨α, hα0, hα1, rfl⟩
  obtain ⟨hx₂A, ε, εpos, hε⟩ := (key x₂).1 hx₂
  have hCA : C ⊆ affineSpan ℝ C := subset_affineSpan ℝ C
  have hx₁A : x₁ ∈ affineSpan ℝ C :=
    closure_minimal hCA (affineSpan ℝ C).closed_of_finiteDimensional hx₁
  have h1α : 0 < 1 - α := by linarith
  -- pick `c ∈ C` close to `x₁`
  obtain ⟨c, hcC, hc⟩ := Metric.mem_closure_iff.1 hx₁ ((1 - α) * ε / 2) (by positivity)
  refine (key _).2 ⟨?_, (1 - α) * ε / 2, by positivity, fun z hzA hz => ?_⟩
  · have := AffineMap.lineMap_mem (Q := affineSpan ℝ C) α hx₂A hx₁A
    rw [AffineMap.lineMap_apply_module] at this
    convert this using 1
    abel
  · -- write `z = α • c + (1 - α) • w` with `w` in the affine span, close to `x₂`
    set w : E := AffineMap.lineMap c z (1 - α)⁻¹ with hw
    have hwA : w ∈ affineSpan ℝ C := AffineMap.lineMap_mem _ (hCA hcC) hzA
    have hw2 : (1 - α) • w = z - α • c := by
      rw [hw, AffineMap.lineMap_apply_module, smul_add, smul_smul, smul_smul,
        mul_inv_cancel₀ h1α.ne', one_smul, mul_sub, mul_one, mul_inv_cancel₀ h1α.ne']
      rw [sub_smul, one_smul, sub_smul, one_smul]
      abel
    have h3 : (1 - α) • (w - x₂) = (z - (α • x₁ + (1 - α) • x₂)) + α • (x₁ - c) := by
      rw [smul_sub, hw2, smul_sub]
      abel
    have hwC : w ∈ C := by
      apply hε w hwA
      have h5 : ‖z - (α • x₁ + (1 - α) • x₂)‖ < (1 - α) * ε / 2 := by rwa [← dist_eq_norm]
      have h6 : ‖x₁ - c‖ < (1 - α) * ε / 2 := by rwa [← dist_eq_norm]
      have h7 : α * ‖x₁ - c‖ ≤ 1 * ((1 - α) * ε / 2) :=
        mul_le_mul hα1.le h6.le (norm_nonneg _) zero_le_one
      have h4 : (1 - α) * ‖w - x₂‖ < (1 - α) * ε := by
        have hn : ‖(1 - α) • (w - x₂)‖ = (1 - α) * ‖w - x₂‖ := by
          rw [norm_smul, Real.norm_of_nonneg h1α.le]
        rw [← hn, h3]
        calc ‖(z - (α • x₁ + (1 - α) • x₂)) + α • (x₁ - c)‖
            ≤ ‖z - (α • x₁ + (1 - α) • x₂)‖ + ‖α • (x₁ - c)‖ := norm_add_le _ _
          _ = ‖z - (α • x₁ + (1 - α) • x₂)‖ + α * ‖x₁ - c‖ := by
              rw [norm_smul, Real.norm_of_nonneg hα0]
          _ < (1 - α) * ε := by linarith
      rw [dist_eq_norm]
      nlinarith
    have hmem : α • c + (1 - α) • w ∈ C := hC_convex hcC hwC hα0 h1α.le (by ring)
    rwa [hw2, add_sub_cancel] at hmem

end CAMA_chap_3_2_1_6
