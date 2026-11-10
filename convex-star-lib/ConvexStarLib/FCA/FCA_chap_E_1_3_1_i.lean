import ConvexStarLib.Defs

/-!
# `FCA_chap_E_1_3_1_i`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_1_3_1_i` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_1_3_1_i`, so the main result is `FCA_chap_E_1_3_1_i.FCA_chap_E_1_3_1_i`.
-/

namespace FCA_chap_E_1_3_1_i

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_E_1_3_1_i
  (f : E → EReal) (r : ℝ) (hf_nondegenerate : IsNondegenerate f) :
  let g := fun x => f x + r
  let f_conj := fun s => conjugate f s
  let g_conj := fun s => conjugate g s
  ∀ s, g_conj s = f_conj s - r := by
  intro g f_conj g_conj s
  have key : ∀ x, ((inner ℝ s x : ℝ) : EReal) - g x = (((inner ℝ s x : ℝ) : EReal) - f x) - r := by
    intro x
    simp only [g]
    induction f x using EReal.rec with
    | bot => simp
    | top => simp
    | coe a =>
      rw [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub]
      congr 1
      ring
  show conjugate g s = conjugate f s - r
  unfold conjugate
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨x, -, rfl⟩
    beta_reduce
    rw [key x]
    exact EReal.sub_le_sub (le_sSup ⟨x, Set.mem_univ x, rfl⟩) le_rfl
  · apply EReal.sub_le_of_le_add
    apply sSup_le
    rintro _ ⟨x, -, rfl⟩
    have h1 : ((inner ℝ s x : ℝ) : EReal) - f x = (((inner ℝ s x : ℝ) : EReal) - g x) + r := by
      rw [key x, EReal.sub_add_cancel]
    beta_reduce
    rw [h1]
    gcongr
    exact le_sSup ⟨x, Set.mem_univ x, rfl⟩

end FCA_chap_E_1_3_1_i
