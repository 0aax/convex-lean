import ConvexStarLib.Defs

/-!
# `FCA_chap_E_1_3_1_iii`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_1_3_1_iii` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_1_3_1_iii`, so the main result is `FCA_chap_E_1_3_1_iii.FCA_chap_E_1_3_1_iii`.
-/

namespace FCA_chap_E_1_3_1_iii

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_E_1_3_1_iii
  (f : E → EReal) (t : ℝ)
  (hf_nondegenerate : IsNondegenerate f) (ht_nonzero : t ≠ 0) :
  let g := fun x => f (t • x)
  let f_conj := fun s => conjugate f s
  let g_conj := fun s => conjugate g s
  ∀ s, g_conj s = f_conj (t⁻¹ • s) := by
  intro g f_conj g_conj s
  simp only [g_conj, f_conj, g, conjugate]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨t • x, ?_⟩
    rw [real_inner_smul_left, real_inner_smul_right, inv_mul_cancel_left₀ ht_nonzero]
  · rintro ⟨y, rfl⟩
    refine ⟨t⁻¹ • y, ?_⟩
    rw [real_inner_smul_left, real_inner_smul_right, smul_inv_smul₀ ht_nonzero]

end FCA_chap_E_1_3_1_iii
