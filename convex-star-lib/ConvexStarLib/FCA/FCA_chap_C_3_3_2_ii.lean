import ConvexStarLib.Defs

/-!
# `FCA_chap_C_3_3_2_ii`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_3_3_2_ii` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_3_3_2_ii`, so the main result is `FCA_chap_C_3_3_2_ii.FCA_chap_C_3_3_2_ii`.
-/

namespace FCA_chap_C_3_3_2_ii

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_C_3_3_2_ii {ι : Type*}
  (S : ι → Set E)
  (J : Set ι)
  (hJ_nonempty : Set.Nonempty J)
  (hS_nonempty : ∀ j ∈ J, Set.Nonempty (S j))
  (hS_closed : ∀ j ∈ J, IsClosed (S j))
  (hS_convex : ∀ j ∈ J, Convex ℝ (S j)) :
  let σ := fun j => supportFunction (S j)
  let σ_sup := fun x => sSup (Set.image (fun j => σ j x) J)
  let S' := closure (convexHull ℝ (⋃ j ∈ J, S j))
  ∀ x, σ_sup x = supportFunction S' x := by
  intro σ σ_sup S' x
  simp only [σ_sup, σ, S', supportFunction]
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨j, hj, rfl⟩
    apply sSup_le_sSup
    apply Set.image_mono
    refine subset_trans ?_ subset_closure
    refine subset_trans ?_ (subset_convexHull ℝ _)
    exact Set.subset_biUnion_of_mem (u := S) hj
  · apply sSup_le
    rintro _ ⟨v, hv, rfl⟩
    -- the half-space `{u | ⟪u, x⟫ ≤ c}` (in `EReal`) is closed and convex
    have hHconvex : ∀ c : EReal, Convex ℝ {u : E | ((inner ℝ u x : ℝ) : EReal) ≤ c} := by
      intro c
      induction c using EReal.rec with
      | bot => simpa using convex_empty
      | top => simp [convex_univ]
      | coe c' =>
        simp only [EReal.coe_le_coe_iff]
        exact convex_halfSpace_le
          ⟨fun a b => inner_add_left a b x, fun r a => real_inner_smul_left a x r⟩ c'
    have hHclosed : ∀ c : EReal, IsClosed {u : E | ((inner ℝ u x : ℝ) : EReal) ≤ c} := by
      intro c
      exact isClosed_le (continuous_coe_real_ereal.comp (continuous_id.inner continuous_const))
        continuous_const
    have hU : (⋃ j ∈ J, S j) ⊆ {u : E | ((inner ℝ u x : ℝ) : EReal) ≤
        sSup ((fun j => sSup ((fun v : E => ((inner ℝ v x : ℝ) : EReal)) '' S j)) '' J)} := by
      intro u hu
      simp only [Set.mem_iUnion] at hu
      obtain ⟨j, hj, hu⟩ := hu
      exact le_trans (le_sSup (Set.mem_image_of_mem _ hu))
        (le_sSup (Set.mem_image_of_mem
          (fun j => sSup ((fun v : E => ((inner ℝ v x : ℝ) : EReal)) '' S j)) hj))
    exact closure_minimal (convexHull_min hU (hHconvex _)) (hHclosed _) hv

end FCA_chap_C_3_3_2_ii
