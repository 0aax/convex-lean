import ConvexStarLib.Defs

/-!
# `FCA_chap_C_3_3_3`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_3_3_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_3_3_3`, so the main result is `FCA_chap_C_3_3_3.FCA_chap_C_3_3_3`.
-/

namespace FCA_chap_C_3_3_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

set_option linter.unusedVariables false in
theorem FCA_chap_C_3_3_3
  (A : E →ₗ[ℝ] F)
  (S : Set E)
  (hS_nonempty : Set.Nonempty S) :
  let A_adj := A.adjoint
  let cl_AS := closure (Set.image A S)
  let σ_clAS := supportFunction cl_AS
  let σ_S_Aadj := fun y => supportFunction S (A_adj y)
  ∀ (y : F), σ_clAS y = σ_S_Aadj y := by
  intro A_adj cl_AS σ_clAS σ_S_Aadj y
  simp only [σ_clAS, σ_S_Aadj, cl_AS, A_adj, supportFunction]
  have h1 : (fun v : E => ((inner ℝ v (LinearMap.adjoint A y) : ℝ) : EReal)) =
      (fun w : F => ((inner ℝ w y : ℝ) : EReal)) ∘ A := by
    funext v
    simp [LinearMap.adjoint_inner_right]
  rw [h1, Set.image_comp]
  set f : F → EReal := fun w => ((inner ℝ w y : ℝ) : EReal) with hf
  have hfc : Continuous f := by
    exact continuous_coe_real_ereal.comp (continuous_id.inner continuous_const)
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨z, hz, rfl⟩
    have hcl : IsClosed {w : F | f w ≤ sSup (f '' (A '' S))} := isClosed_le hfc continuous_const
    have hsub : A '' S ⊆ {w : F | f w ≤ sSup (f '' (A '' S))} := by
      intro w hw
      exact le_sSup (Set.mem_image_of_mem f hw)
    exact (hcl.closure_subset_iff.mpr hsub) hz
  · apply sSup_le_sSup
    exact Set.image_mono subset_closure

end FCA_chap_C_3_3_3
