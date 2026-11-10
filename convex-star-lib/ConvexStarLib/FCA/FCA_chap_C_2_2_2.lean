import ConvexStarLib.Defs

/-!
# `FCA_chap_C_2_2_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_2_2_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_2_2_2`, so the main result is `FCA_chap_C_2_2_2.FCA_chap_C_2_2_2`.
-/

namespace FCA_chap_C_2_2_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_C_2_2_2
  (S : Set E)
  (s : E)
  (hS : Set.Nonempty S) :
  let sf_S := supportFunction S
  (s ∈ closure (convexHull ℝ S)) ↔
  s ∈ supportSublevelSet sf_S := by
  intro sf_S
  constructor
  · intro hs w
    show ((inner ℝ s w : ℝ) : EReal) ≤ supportFunction S w
    have hSM : S ⊆ {v : E | ((inner ℝ v w : ℝ) : EReal) ≤ supportFunction S w} := by
      intro v hv
      show ((inner ℝ v w : ℝ) : EReal) ≤ sSup ((fun v : E => ((inner ℝ v w : ℝ) : EReal)) '' S)
      exact le_sSup (Set.mem_image_of_mem _ hv)
    have hT_closed : IsClosed {v : E | ((inner ℝ v w : ℝ) : EReal) ≤ supportFunction S w} := by
      apply isClosed_le
      · exact continuous_coe_real_ereal.comp (continuous_id.inner continuous_const)
      · exact continuous_const
    have hT_convex : Convex ℝ {v : E | ((inner ℝ v w : ℝ) : EReal) ≤ supportFunction S w} := by
      intro x hx y hy a b ha hb hab
      simp only [Set.mem_setOf_eq] at hx hy ⊢
      have h1 : inner ℝ (a • x + b • y) w ≤ max (inner ℝ x w) (inner ℝ y w) := by
        rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
        calc a * inner ℝ x w + b * inner ℝ y w
            ≤ a * max (inner ℝ x w) (inner ℝ y w) + b * max (inner ℝ x w) (inner ℝ y w) := by
              gcongr
              · exact le_max_left _ _
              · exact le_max_right _ _
          _ = max (inner ℝ x w) (inner ℝ y w) := by rw [← add_mul, hab, one_mul]
      calc ((inner ℝ (a • x + b • y) w : ℝ) : EReal)
          ≤ ((max (inner ℝ x w) (inner ℝ y w) : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr h1
        _ ≤ supportFunction S w := by
          rcases le_total (inner ℝ x w) (inner ℝ y w) with h | h
          · rw [max_eq_right h]; exact hy
          · rw [max_eq_left h]; exact hx
    exact closure_minimal (convexHull_min hSM hT_convex) hT_closed hs
  · intro hs
    by_contra hns
    haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
    obtain ⟨f, u, hfu, hfs⟩ :=
      geometric_hahn_banach_closed_point (convex_convexHull ℝ S).closure isClosed_closure hns
    have key : ∀ x, inner ℝ x ((InnerProductSpace.toDual ℝ E).symm f) = f x := by
      intro x
      rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    have h1 := hs ((InnerProductSpace.toDual ℝ E).symm f)
    have h2 : supportFunction S ((InnerProductSpace.toDual ℝ E).symm f) ≤ (u : EReal) := by
      apply sSup_le
      rintro _ ⟨v, hv, rfl⟩
      simp only [key]
      exact EReal.coe_le_coe_iff.mpr (le_of_lt (hfu v (subset_closure (subset_convexHull ℝ S hv))))
    have h3 : ((inner ℝ s ((InnerProductSpace.toDual ℝ E).symm f) : ℝ) : EReal) ≤ (u : EReal) :=
      le_trans h1 h2
    rw [key] at h3
    have h4 := EReal.coe_le_coe_iff.mp h3
    linarith

end FCA_chap_C_2_2_2
