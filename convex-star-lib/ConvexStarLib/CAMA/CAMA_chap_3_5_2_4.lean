import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_5_2_4`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_5_2_4` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_5_2_4`, so the main result is `CAMA_chap_3_5_2_4.CAMA_chap_3_5_2_4`.
-/

namespace CAMA_chap_3_5_2_4

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem CAMA_chap_3_5_2_4
  (C : Set E)
  (x : E)
  (hX_inC : x ∈ C)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C) :
  convexNormalCone x C = polarCone (posTangentConeAt C x) := by
  ext s
  constructor
  · intro hs v hv
    obtain ⟨α, l, hl, c, d, _hd0, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hv
    have h1 : Filter.Tendsto (fun n => inner ℝ s (c n • d n)) l (𝓝 (inner ℝ s v)) :=
      Filter.Tendsto.inner tendsto_const_nhds hcd
    refine le_of_tendsto h1 ?_
    filter_upwards [hds] with n hn
    have h2 := hs (x + d n) hn
    rw [add_sub_cancel_left] at h2
    rw [NNReal.smul_def, real_inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos (c n).coe_nonneg h2
  · intro hs y hy
    exact hs (y - x)
      (sub_mem_posTangentConeAt_of_segment_subset (hC_convex.segment_subset hX_inC hy))

end CAMA_chap_3_5_2_4
