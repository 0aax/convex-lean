import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_5_1_2`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_5_1_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_5_1_2`, so the main result is `CAMA_chap_3_5_1_2.CAMA_chap_3_5_1_2`.
-/

namespace CAMA_chap_3_5_1_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_5_1_2
  (d : E)
  (S : Set E)
  (x : E) :
  (d ∈ posTangentConeAt S x) ↔
  ∃ (dk : ℕ → E), ∃ (tk : ℕ → ℝ),
  (Filter.Tendsto dk Filter.atTop (𝓝 d)) ∧
  (Filter.Tendsto tk Filter.atTop (𝓝 0)) ∧
  (∀ i, tk i > 0) ∧
  (∀ k, x + (tk k) • (dk k) ∈ S) := by
  rw [mem_tangentConeAt_iff_exists_seq]
  constructor
  · rintro ⟨c, δ, hδ, hS, hcδ⟩
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hS
    -- `r n = √(‖δ n‖ + 1/(n+1))` is positive, tends to `0`, and `‖δ n‖ ≤ r n * r n`.
    set r : ℕ → ℝ := fun n => Real.sqrt (‖δ n‖ + 1 / ((n : ℝ) + 1)) with hr_def
    have hr_pos : ∀ n, 0 < r n := by
      intro n
      apply Real.sqrt_pos.mpr
      have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      have := norm_nonneg (δ n)
      linarith
    have hr_tend : Filter.Tendsto r Filter.atTop (𝓝 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => ‖δ n‖ + 1 / ((n : ℝ) + 1)) Filter.atTop
          (𝓝 (‖(0:E)‖ + 0)) :=
        hδ.norm.add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [norm_zero, add_zero] at h1
      have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
      rw [Real.sqrt_zero] at h2
      exact h2
    have hsq : ∀ n, ‖δ n‖ ≤ r n * r n := by
      intro n
      rw [hr_def, Real.mul_self_sqrt (by positivity)]
      have : (0:ℝ) ≤ 1 / ((n:ℝ) + 1) := by positivity
      linarith
    -- `a n = c n + (r n)⁻¹` is positive, at least `(r n)⁻¹`, and `a n • δ n → d`.
    set a : ℕ → ℝ := fun n => (c n : ℝ) + (r n)⁻¹ with ha_def
    have ha_ge : ∀ n, (r n)⁻¹ ≤ a n := by
      intro n
      have := (c n).coe_nonneg
      simp only [ha_def]
      linarith
    have ha_pos : ∀ n, 0 < a n := fun n => lt_of_lt_of_le (inv_pos.mpr (hr_pos n)) (ha_ge n)
    refine ⟨fun k => a (k + N) • δ (k + N), fun k => (a (k + N))⁻¹, ?_, ?_, ?_, ?_⟩
    · -- `dk → d`
      rw [Filter.tendsto_add_atTop_iff_nat (f := fun n => a n • δ n) N]
      have h2 : Filter.Tendsto (fun n => (r n)⁻¹ • δ n) Filter.atTop (𝓝 0) := by
        apply squeeze_zero_norm (a := r)
        · intro n
          rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hr_pos n),
            inv_mul_le_iff₀ (hr_pos n)]
          exact hsq n
        · exact hr_tend
      have h3 : Filter.Tendsto (fun n => (c n : ℝ) • δ n + (r n)⁻¹ • δ n) Filter.atTop
          (𝓝 (d + 0)) := by
        have := hcδ
        simp only [NNReal.smul_def] at this
        exact this.add h2
      rw [add_zero] at h3
      refine h3.congr ?_
      intro n
      simp only [ha_def, add_smul]
    · -- `tk → 0`
      rw [Filter.tendsto_add_atTop_iff_nat (f := fun n => (a n)⁻¹) N]
      apply squeeze_zero (g := r)
      · intro n
        exact (inv_pos.mpr (ha_pos n)).le
      · intro n
        calc (a n)⁻¹ ≤ ((r n)⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr (hr_pos n)) (ha_ge n)
          _ = r n := inv_inv _
      · exact hr_tend
    · intro i
      exact inv_pos.mpr (ha_pos (i + N))
    · intro k
      simp only
      rw [inv_smul_smul₀ (ha_pos (k + N)).ne']
      exact hN (k + N) (by omega)
  · rintro ⟨dk, tk, hdk, htk, hpos, hS⟩
    refine ⟨fun n => ⟨(tk n)⁻¹, (inv_pos.mpr (hpos n)).le⟩, fun n => tk n • dk n, ?_, ?_, ?_⟩
    · have := htk.smul hdk
      rwa [zero_smul] at this
    · exact Filter.Eventually.of_forall hS
    · refine hdk.congr ?_
      intro n
      rw [NNReal.smul_def]
      simp only [NNReal.coe_mk]
      rw [inv_smul_smul₀ (hpos n).ne']

end CAMA_chap_3_5_1_2
