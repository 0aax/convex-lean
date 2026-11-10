import ConvexStarLib.Defs

/-!
# `FCA_chap_E_1_3_1_v`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_1_3_1_v` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_1_3_1_v`, so the main result is `FCA_chap_E_1_3_1_v.FCA_chap_E_1_3_1_v`.
-/

namespace FCA_chap_E_1_3_1_v

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_E_1_3_1_v
  (f : E → EReal) (x₀ : E)
  (hf_nondegenerate : IsNondegenerate f) :
  let g := fun x => f (x - x₀)
  ∀ s, conjugate g s = conjugate f s + inner ℝ s x₀ := by
  intro g s
  have key : ∀ (p q : ℝ) (a : EReal), (p : EReal) - a = ((p - q : ℝ) : EReal) - a + (q : EReal) := by
    intro p q a
    rw [sub_eq_add_neg (p : EReal) a, sub_eq_add_neg ((p - q : ℝ) : EReal) a, add_right_comm,
      ← EReal.coe_add, sub_add_cancel]
  simp only [conjugate, Set.image_univ]
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨x, rfl⟩
    dsimp only
    rw [key (inner ℝ s x) (inner ℝ s x₀) (g x), ← inner_sub_right]
    gcongr
    exact le_sSup ⟨x - x₀, rfl⟩
  · rw [← EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    apply sSup_le
    rintro _ ⟨y, rfl⟩
    dsimp only
    rw [EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    have h2 : f y = g (y + x₀) := by simp only [g, add_sub_cancel_right]
    have h3 : ((inner ℝ s y : ℝ) : EReal) - g (y + x₀) + ((inner ℝ s x₀ : ℝ) : EReal)
        = ((inner ℝ s (y + x₀) : ℝ) : EReal) - g (y + x₀) := by
      rw [key (inner ℝ s (y + x₀)) (inner ℝ s x₀) (g (y + x₀)), inner_add_right,
        add_sub_cancel_right]
    rw [h2, h3]
    exact le_sSup ⟨y + x₀, rfl⟩

end FCA_chap_E_1_3_1_v
