import ConvexStarLib.Defs

/-!
# `FCA_chap_B_4_2_3`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_4_2_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_4_2_3`, so the main result is `FCA_chap_B_4_2_3.FCA_chap_B_4_2_3`.
-/

namespace FCA_chap_B_4_2_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_B_4_2_3
  {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EReal)
  (hf_convex : InConvRn f)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  let f_real := fun x ↦ (f x).toReal
  let non_diff_points :=
    {x | x ∈ interior (effDom f) ∧ ¬DifferentiableAt ℝ f_real x}
  (∀ x ∈ effDom f, f x = (f_real x : EReal)) ∧ volume non_diff_points = 0 := by
  intro f_real non_diff_points
  have hfin : ∀ x ∈ effDom f, f x = ((f x).toReal : EReal) := by
    intro x hx
    exact (EReal.coe_toReal (ne_of_lt hx) (ne_of_gt (f_ne_bot x))).symm
  refine ⟨hfin, ?_⟩
  -- convexity of f_real on effDom f
  have hconv : ConvexOn ℝ (effDom f) f_real := by
    obtain ⟨-, -, hepi⟩ := hf_convex
    have key : ∀ x ∈ effDom f, ∀ y ∈ effDom f, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
        f (a • x + b • y) ≤ ((a * f_real x + b * f_real y : ℝ) : EReal) := by
      intro x hx y hy a b ha hb hab
      have hx' : (x, f_real x) ∈ epigraph f := by
        show f x ≤ ((f x).toReal : EReal)
        rw [← hfin x hx]
      have hy' : (y, f_real y) ∈ epigraph f := by
        show f y ≤ ((f y).toReal : EReal)
        rw [← hfin y hy]
      have := hepi hx' hy' ha hb hab
      simpa [epigraph] using this
    refine ⟨?_, ?_⟩
    · intro x hx y hy a b ha hb hab
      have := key x hx y hy a b ha hb hab
      show f (a • x + b • y) < ⊤
      exact lt_of_le_of_lt this (EReal.coe_lt_top _)
    · intro x hx y hy a b ha hb hab
      have := key x hx y hy a b ha hb hab
      show (f (a • x + b • y)).toReal ≤ a • f_real x + b • f_real y
      have hne : f (a • x + b • y) ≠ ⊥ := ne_of_gt (f_ne_bot _)
      rw [smul_eq_mul, smul_eq_mul]
      exact (EReal.toReal_le_toReal this hne (EReal.coe_ne_top _)).trans_eq (EReal.toReal_coe _)
  have hlip := hconv.locallyLipschitzOn_interior
  apply MeasureTheory.measure_null_of_locally_null
  intro x hx
  obtain ⟨K, t, ht, hKt⟩ := hlip hx.1
  rw [isOpen_interior.nhdsWithin_eq hx.1] at ht
  obtain ⟨V, hVt, hVo, hxV⟩ := mem_nhds_iff.1 ht
  refine ⟨non_diff_points ∩ V, inter_mem_nhdsWithin _ (hVo.mem_nhds hxV), ?_⟩
  have hae := (hKt.mono hVt).ae_differentiableWithinAt_of_mem (μ := volume)
  rw [MeasureTheory.ae_iff] at hae
  apply measure_mono_null _ hae
  intro y hy
  simp only [Set.mem_setOf_eq, Classical.not_imp]
  refine ⟨hy.2, fun hd => hy.1.2 ?_⟩
  exact hd.differentiableAt (hVo.mem_nhds hy.2)

end FCA_chap_B_4_2_3
