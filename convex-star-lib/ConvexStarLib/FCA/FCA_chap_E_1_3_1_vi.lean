import ConvexStarLib.Defs

/-!
# `FCA_chap_E_1_3_1_vi`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_1_3_1_vi` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_1_3_1_vi`, so the main result is `FCA_chap_E_1_3_1_vi.FCA_chap_E_1_3_1_vi`.
-/

namespace FCA_chap_E_1_3_1_vi

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_E_1_3_1_vi
  (f : E → EReal) (s₀ : E)
  (hf_nondegenerate : IsNondegenerate f) :
  let g := fun x => f x + inner ℝ s₀ x
  ∀ s, conjugate g s = conjugate f (s - s₀) := by
  intro g s
  unfold conjugate
  have h : (fun x => ((inner ℝ s x : ℝ) : EReal) - g x)
      = (fun x => ((inner ℝ (s - s₀) x : ℝ) : EReal) - f x) := by
    funext x
    simp only [g]
    rw [inner_sub_left]
    generalize (inner ℝ s x : ℝ) = r
    generalize (inner ℝ s₀ x : ℝ) = t
    induction f x using EReal.rec with
    | bot =>
      rw [EReal.bot_add, EReal.coe_sub_bot, EReal.coe_sub_bot]
    | top =>
      rw [EReal.top_add_coe, EReal.sub_top, EReal.sub_top]
    | coe a =>
      rw [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub]
      congr 1
      ring
  rw [h]

end FCA_chap_E_1_3_1_vi
