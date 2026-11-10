import ConvexStarLib.Defs

/-!
# `FCA_chap_C_2_2_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_2_2_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_2_2_1`, so the main result is `FCA_chap_C_2_2_1.FCA_chap_C_2_2_1`.
-/

namespace FCA_chap_C_2_2_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_C_2_2_1
  (S : Set E)
  (hS : Set.Nonempty S) :
  let sf_S := supportFunction S
  let sf_clS := supportFunction (closure S)
  let sf_coS := supportFunction (convexHull ℝ S)
  let sf_barcoS := supportFunction (closure (convexHull ℝ S))
  ∀ (x : E),
  (sf_S x = sf_clS x) ∧
  (sf_clS x = sf_coS x) ∧
  (sf_S x = sf_barcoS x) := by
  intro sf_S sf_clS sf_coS sf_barcoS x
  -- every point of `closure (convexHull ℝ S)` lies in the half-space cut out by the support value
  have hsub : closure (convexHull ℝ S) ⊆
      {v : E | ((inner ℝ v x : ℝ) : EReal) ≤ supportFunction S x} := by
    apply closure_minimal
    · apply convexHull_min
      · intro s hs
        show ((inner ℝ s x : ℝ) : EReal) ≤ supportFunction S x
        exact le_sSup (Set.mem_image_of_mem _ hs)
      · intro v hv w hw a b ha hb hab
        simp only [Set.mem_setOf_eq] at hv hw ⊢
        rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
        rcases le_total (inner ℝ v x) (inner ℝ w x) with h | h
        · refine le_trans (EReal.coe_le_coe_iff.mpr ?_) hw
          have h1 := mul_le_mul_of_nonneg_left h ha
          have h2 : a * inner ℝ w x + b * inner ℝ w x = inner ℝ w x := by
            rw [← add_mul, hab, one_mul]
          linarith
        · refine le_trans (EReal.coe_le_coe_iff.mpr ?_) hv
          have h1 := mul_le_mul_of_nonneg_left h hb
          have h2 : a * inner ℝ v x + b * inner ℝ v x = inner ℝ v x := by
            rw [← add_mul, hab, one_mul]
          linarith
    · exact isClosed_le (continuous_coe_real_ereal.comp (continuous_id.inner continuous_const))
        continuous_const
  have key : ∀ T : Set E, S ⊆ T → T ⊆ closure (convexHull ℝ S) →
      supportFunction T x = supportFunction S x := by
    intro T h1 h2
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨v, hv, rfl⟩
      exact hsub (h2 hv)
    · exact sSup_le_sSup (Set.image_mono h1)
  have hS_cl : S ⊆ closure (convexHull ℝ S) := (subset_convexHull ℝ S).trans subset_closure
  have h_cl := key (closure S) subset_closure (closure_mono (subset_convexHull ℝ S))
  have h_co := key (convexHull ℝ S) (subset_convexHull ℝ S) subset_closure
  have h_barco := key (closure (convexHull ℝ S)) hS_cl le_rfl
  exact ⟨h_cl.symm, h_cl.trans h_co.symm, h_barco.symm⟩

end FCA_chap_C_2_2_1
