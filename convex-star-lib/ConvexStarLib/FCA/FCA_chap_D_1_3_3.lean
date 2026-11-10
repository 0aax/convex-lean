import ConvexStarLib.Defs

/-!
# `FCA_chap_D_1_3_3`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_1_3_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_1_3_3`, so the main result is `FCA_chap_D_1_3_3.FCA_chap_D_1_3_3`.
-/

namespace FCA_chap_D_1_3_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_D_1_3_3
  (g : E → ℝ)
  (hg_convex : ConvexOn ℝ Set.univ g)
  (hg_neg : ∃ (x₀ : E), g x₀ < 0):
  (closure {z | g z < 0} = {z | g z ≤ 0}) ∧
  ({z | g z < 0} = interior {z | g z ≤ 0}) ∧
  (frontier {z | g z ≤ 0} = {z | g z = 0}) := by
  obtain ⟨x₀, hx₀⟩ := hg_neg
  have hcont : Continuous g := hg_convex.locallyLipschitz.continuous
  have hclosed : IsClosed {z | g z ≤ 0} := isClosed_le hcont continuous_const
  have hopen : IsOpen {z | g z < 0} := isOpen_lt hcont continuous_const
  have h1 : closure {z | g z < 0} = {z | g z ≤ 0} := by
    apply Set.Subset.antisymm
    · exact closure_minimal (fun z (hz : g z < 0) => show g z ≤ 0 from hz.le) hclosed
    · intro z hz
      have hz' : g z ≤ 0 := hz
      have hseg : openSegment ℝ z x₀ ⊆ {z | g z < 0} := by
        rintro y ⟨a, b, ha, hb, hab, rfl⟩
        have hc := hg_convex.2 (Set.mem_univ z) (Set.mem_univ x₀) ha.le hb.le hab
        simp only [smul_eq_mul] at hc
        show g (a • z + b • x₀) < 0
        have h3 := mul_nonpos_of_nonneg_of_nonpos ha.le hz'
        have h4 := mul_neg_of_pos_of_neg hb hx₀
        linarith
      exact closure_mono hseg (segment_subset_closure_openSegment (left_mem_segment ℝ z x₀))
  have h2 : {z | g z < 0} = interior {z | g z ≤ 0} := by
    apply Set.Subset.antisymm
    · exact interior_maximal (fun z (hz : g z < 0) => show g z ≤ 0 from hz.le) hopen
    · intro z hz
      have hnhds : {z | g z ≤ 0} ∈ 𝓝 z := mem_interior_iff_mem_nhds.mp hz
      have htend : Filter.Tendsto (fun s : ℝ => z + s • (z - x₀)) (𝓝[>] 0) (𝓝 z) := by
        have h5 : Filter.Tendsto (fun s : ℝ => z + s • (z - x₀)) (𝓝 0)
            (𝓝 (z + (0:ℝ) • (z - x₀))) :=
          (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
        rw [zero_smul, add_zero] at h5
        exact h5.mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ s in 𝓝[>] (0:ℝ), g (z + s • (z - x₀)) ≤ 0 ∧ 0 < s :=
        (htend.eventually hnhds).and self_mem_nhdsWithin
      obtain ⟨s, hs, hspos⟩ := hev.exists
      set a : ℝ := (1 + s)⁻¹ with ha_def
      have ha_pos : 0 < a := inv_pos.mpr (by linarith)
      have ha1 : a * (1 + s) = 1 := inv_mul_cancel₀ (by linarith)
      have hsum : a + a * s = 1 := by linarith [ha1]
      have hconv := hg_convex.2 (Set.mem_univ (z + s • (z - x₀))) (Set.mem_univ x₀)
        ha_pos.le (mul_pos ha_pos hspos).le hsum
      have heq : a • (z + s • (z - x₀)) + (a * s) • x₀ = z := by
        calc a • (z + s • (z - x₀)) + (a * s) • x₀ = (a * (1 + s)) • z := by module
          _ = z := by rw [ha1, one_smul]
      rw [heq] at hconv
      simp only [smul_eq_mul] at hconv
      show g z < 0
      have h3 := mul_nonpos_of_nonneg_of_nonpos ha_pos.le hs
      have h4 := mul_neg_of_pos_of_neg (mul_pos ha_pos hspos) hx₀
      linarith
  refine ⟨h1, h2, ?_⟩
  rw [frontier, hclosed.closure_eq, ← h2]
  ext z
  simp only [Set.mem_diff, Set.mem_setOf_eq, not_lt]
  constructor
  · rintro ⟨h6, h7⟩
    exact le_antisymm h6 h7
  · intro h
    exact ⟨h.le, h.ge⟩

end FCA_chap_D_1_3_3
