import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_5_2_5`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_5_2_5` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_5_2_5`, so the main result is `CAMA_chap_3_5_2_5.CAMA_chap_3_5_2_5`.
-/

namespace CAMA_chap_3_5_2_5

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem CAMA_chap_3_5_2_5
  (C : Set E)
  (x : E)
  (hx_inC : x ∈ C)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C) :
  posTangentConeAt C x = polarCone (convexNormalCone x C) := by
  ext y
  constructor
  · intro hy s hs
    obtain ⟨c, d, -, hdC, hcd⟩ := mem_tangentConeAt_iff_exists_seq.mp hy
    have h1 : Filter.Tendsto (fun n => inner ℝ s (c n • d n)) Filter.atTop
        (𝓝 (inner ℝ s y)) :=
      Filter.Tendsto.inner tendsto_const_nhds hcd
    rw [real_inner_comm]
    refine le_of_tendsto h1 ?_
    filter_upwards [hdC] with n hn
    have := hs (x + d n) hn
    rw [add_sub_cancel_left] at this
    rw [NNReal.smul_def, inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos (c n).2 this
  · intro hy
    set D : Set E := (fun v => x + v) ⁻¹' C with hD_def
    have hD : Convex ℝ D := hC_convex.translate_preimage_right x
    set K : ConvexCone ℝ E := hD.toCone D with hK_def
    have hT_closed : IsClosed (posTangentConeAt C x) := by
      show IsClosed (tangentConeAt ℝ≥0 C x)
      rw [tangentConeAt_eq_biInter_closure]
      exact isClosed_biInter fun U _ => isClosed_closure
    have hK_sub : (K : Set E) ⊆ posTangentConeAt C x := by
      intro v hv
      obtain ⟨c, hc, hcv⟩ := hD.mem_toCone'.mp hv
      apply mem_posTangentConeAt_of_frequently_mem
      apply Filter.Eventually.frequently
      filter_upwards [Ioc_mem_nhdsGT hc] with t ht
      have h1 : x + t • v = (1 - t / c) • x + (t / c) • (x + c • v) := by
        rw [smul_add, smul_smul, div_mul_cancel₀ t hc.ne', sub_smul, one_smul]; abel
      rw [h1]
      exact hC_convex hx_inC hcv (by linarith [div_le_one_of_le₀ ht.2 hc.le])
        (div_nonneg ht.1.le hc.le) (by ring)
    have hKc_sub : closure (K : Set E) ⊆ posTangentConeAt C x :=
      closure_minimal hK_sub hT_closed
    refine hKc_sub ?_
    by_contra hyK
    obtain ⟨f, u, hfu, hu⟩ :=
      geometric_hahn_banach_closed_point (K.convex.closure) isClosed_closure hyK
    have h0 : (0 : E) ∈ K := hD.mem_toCone'.mpr ⟨1, one_pos, by simp [D, hx_inC]⟩
    have hu0 : 0 < u := by simpa using hfu 0 (subset_closure h0)
    have hfC : ∀ z ∈ C, f (z - x) ≤ 0 := by
      intro z hz
      by_contra hpos
      push_neg at hpos
      have hmem : (u / f (z - x)) • (z - x) ∈ K := by
        apply K.smul_mem (div_pos hu0 hpos)
        exact hD.mem_toCone'.mpr ⟨1, one_pos, by simp [D, hz]⟩
      have := hfu _ (subset_closure hmem)
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ u hpos.ne'] at this
      exact lt_irrefl _ this
    set s := (InnerProductSpace.toDual ℝ E).symm f
    have hs : s ∈ convexNormalCone x C := by
      intro z hz
      rw [InnerProductSpace.toDual_symm_apply]
      exact hfC z hz
    have := hy s hs
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply] at this
    linarith

end CAMA_chap_3_5_2_5
