import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_5_2_1`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_5_2_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_5_2_1`, so the main result is `CAMA_chap_3_5_2_1.CAMA_chap_3_5_2_1`.
-/

namespace CAMA_chap_3_5_2_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem CAMA_chap_3_5_2_1
  (C : Set E)
  (x : E)
  (hx_inC : x ∈ C)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C) :
  posTangentConeAt C x = closure (genCone (translateSet C x)) := by
  -- `D` is the cone of feasible directions of `C` at `x`
  set D : Set E := {v | ∃ ε : ℝ, 0 < ε ∧ x + ε • v ∈ C} with hD_def
  -- every feasible direction is a tangent direction
  have hD_sub : D ⊆ posTangentConeAt C x := by
    rintro v ⟨ε, hε, hv⟩
    apply mem_posTangentConeAt_of_frequently_mem
    apply Filter.Eventually.frequently
    filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    have h1 : x + (t / ε) • (ε • v) ∈ C :=
      hC_convex.add_smul_mem hx_inC hv ⟨div_nonneg ht.1.le hε.le, (div_le_one hε).2 ht.2.le⟩
    rwa [smul_smul, div_mul_cancel₀ t hε.ne'] at h1
  -- `D` is closed under addition
  have hD_add : ∀ v w, v ∈ D → w ∈ D → v + w ∈ D := by
    rintro v w ⟨ε₁, hε₁, hv⟩ ⟨ε₂, hε₂, hw⟩
    have hne : ε₁ + ε₂ ≠ 0 := by positivity
    refine ⟨ε₁ * ε₂ / (ε₁ + ε₂), by positivity, ?_⟩
    have h := hC_convex hv hw (show 0 ≤ ε₂ / (ε₁ + ε₂) by positivity)
      (show 0 ≤ ε₁ / (ε₁ + ε₂) by positivity)
      (show ε₂ / (ε₁ + ε₂) + ε₁ / (ε₁ + ε₂) = 1 by
        rw [← add_div, div_eq_one_iff_eq hne]; ring)
    have key : x + (ε₁ * ε₂ / (ε₁ + ε₂)) • (v + w)
        = (ε₂ / (ε₁ + ε₂)) • (x + ε₁ • v) + (ε₁ / (ε₁ + ε₂)) • (x + ε₂ • w) := by
      match_scalars <;> field_simp; ring
    rw [key]
    exact h
  -- `D` is closed under multiplication by nonnegative scalars
  have hD_smul : ∀ (a : ℝ) v, 0 ≤ a → v ∈ D → a • v ∈ D := by
    rintro a v ha ⟨ε, hε, hv⟩
    refine ⟨ε / (a + 1), by positivity, ?_⟩
    have h1 : x + (a / (a + 1)) • (ε • v) ∈ C :=
      hC_convex.add_smul_mem hx_inC hv ⟨by positivity, (div_le_one (by positivity)).2 (by linarith)⟩
    have key : (ε / (a + 1)) • (a • v) = (a / (a + 1)) • (ε • v) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [key]
    exact h1
  have hD_zero : (0 : E) ∈ D := ⟨1, one_pos, by simpa using hx_inC⟩
  have hT_sub : translateSet C x ⊆ D := by
    rintro v ⟨c, hc, rfl⟩
    exact ⟨1, one_pos, by simpa using hc⟩
  have hG_sub : genCone (translateSet C x) ⊆ D := by
    rintro v ⟨k, α, y, hα, hy, rfl⟩
    induction k with
    | zero => simpa using hD_zero
    | succ k ih =>
      rw [Finset.sum_range_succ]
      apply hD_add
      · apply ih
        · intro i hi
          exact hα i (Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 hi)))
        · intro i hi
          exact hy i (Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 hi)))
      · exact hD_smul _ _ (hα k (Finset.mem_range.2 (Nat.lt_succ_self k)))
          (hT_sub (hy k (Finset.mem_range.2 (Nat.lt_succ_self k))))
  have hclosed : IsClosed (posTangentConeAt C x) := by
    show IsClosed (tangentConeAt ℝ≥0 C x)
    rw [tangentConeAt_def]
    exact isClosed_setOf_clusterPt
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hy
    apply mem_closure_of_tendsto hcd
    filter_upwards [hds] with n hn
    refine ⟨1, fun _ => (c n : ℝ), fun _ => d n, ?_, ?_, ?_⟩
    · intro i _
      exact (c n).coe_nonneg
    · intro i _
      exact ⟨x + d n, hn, by abel⟩
    · simp [NNReal.smul_def]
  · exact closure_minimal (hG_sub.trans hD_sub) hclosed

end CAMA_chap_3_5_2_1
