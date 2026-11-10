import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_4_2_4`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_4_2_4` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_4_2_4`, so the main result is `CAMA_chap_3_4_2_4.CAMA_chap_3_4_2_4`.
-/

namespace CAMA_chap_3_4_2_4

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem CAMA_chap_3_4_2_4
  (C : Set E)
  (hC₀ : Convex ℝ C)
  (hC₁ : Set.Nonempty C)
  (hC₂ : C ⊂ Set.univ) :
  closure C = ⋂ v ∈ (halfspacesContaining C), hyperplaneHalfspace v.1 v.2 := by
  apply Set.Subset.antisymm
  · apply Set.subset_iInter₂
    rintro ⟨s, r⟩ hsr
    apply closure_minimal hsr
    exact isClosed_le (continuous_const.inner continuous_id) continuous_const
  · intro x hx
    by_contra hxC
    obtain ⟨f, u, hfC, hfx⟩ :=
      geometric_hahn_banach_closed_point hC₀.closure isClosed_closure hxC
    have hmem : ((InnerProductSpace.toDual ℝ E).symm f, u) ∈ halfspacesContaining C := by
      intro a ha
      show inner ℝ ((InnerProductSpace.toDual ℝ E).symm f) a ≤ u
      rw [InnerProductSpace.toDual_symm_apply]
      exact (hfC a (subset_closure ha)).le
    have hx' := Set.mem_iInter₂.mp hx _ hmem
    change inner ℝ ((InnerProductSpace.toDual ℝ E).symm f) x ≤ u at hx'
    rw [InnerProductSpace.toDual_symm_apply] at hx'
    linarith

end CAMA_chap_3_4_2_4
