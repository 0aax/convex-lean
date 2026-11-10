import ConvexStarLib.Defs

/-!
# `FCA_chap_B_1_2_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_1_2_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_1_2_2`, so the main result is `FCA_chap_B_1_2_2.FCA_chap_B_1_2_2`.
-/

namespace FCA_chap_B_1_2_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_B_1_2_2
  (f : E → EReal)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  List.TFAE [
    LowerSemicontinuousOn f Set.univ,
    IsClosed (epigraph f),
    ∀ (r : ℝ), IsClosed (sublevelSet r f)
  ] := by
  tfae_have 1 → 2 := by
    intro h
    rw [lowerSemicontinuousOn_univ_iff] at h
    have hc : IsClosed {p : E × EReal | f p.1 ≤ p.2} := h.isClosed_epigraph
    have hcont : Continuous (fun p : E × ℝ => (p.1, (p.2 : EReal))) :=
      continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
    exact hc.preimage hcont
  tfae_have 2 → 3 := by
    intro h r
    have hcont : Continuous (fun x : E => (x, r)) := continuous_id.prodMk continuous_const
    exact h.preimage hcont
  tfae_have 3 → 1 := by
    intro h
    rw [lowerSemicontinuousOn_univ_iff, lowerSemicontinuous_iff_isClosed_preimage]
    intro y
    induction y with
    | bot =>
      convert isClosed_empty
      ext x
      simp only [Set.mem_preimage, Set.mem_Iic, le_bot_iff, Set.mem_empty_iff_false, iff_false]
      exact (f_ne_bot x).ne'
    | coe r => exact h r
    | top =>
      convert isClosed_univ
      ext x
      simp
  tfae_finish

end FCA_chap_B_1_2_2
