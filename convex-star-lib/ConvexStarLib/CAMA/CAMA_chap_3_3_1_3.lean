import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_3_1_3`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_3_1_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_3_1_3`, so the main result is `CAMA_chap_3_3_1_3.CAMA_chap_3_3_1_3`.
-/

namespace CAMA_chap_3_3_1_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_3_1_3
  (C : Set E)
  (x₁ x₂ : E)
  (hC₀ : IsClosed C)
  (hC₁ : Convex ℝ C)
  (hC₂ : Set.Nonempty C) :
  ‖(pC x₁ C hC₀ hC₁ hC₂) - (pC x₂ C hC₀ hC₁ hC₂)‖ ^ 2
  ≤ inner ℝ ((pC x₁ C hC₀ hC₁ hC₂) - (pC x₂ C hC₀ hC₁ hC₂)) (x₁ - x₂) := by
  have key : ∀ x : E, pC x C hC₀ hC₁ hC₂ ∈ C ∧
      ∀ w ∈ C, inner ℝ (x - pC x C hC₀ hC₁ hC₂) (w - pC x C hC₀ hC₁ hC₂) ≤ 0 := by
    intro x
    have h := Classical.choose_spec
      (exists_norm_eq_iInf_of_complete_convex hC₂ hC₀.isComplete hC₁ x)
    exact ⟨h.1, (norm_eq_iInf_iff_real_inner_le_zero hC₁ h.1).1 h.2⟩
  obtain ⟨hm₁, hi₁⟩ := key x₁
  obtain ⟨hm₂, hi₂⟩ := key x₂
  have a := hi₁ _ hm₂
  have b := hi₂ _ hm₁
  generalize pC x₁ C hC₀ hC₁ hC₂ = p₁ at *
  generalize pC x₂ C hC₀ hC₁ hC₂ = p₂ at *
  rw [← real_inner_self_eq_norm_sq]
  have h : inner ℝ (p₁ - p₂) (x₁ - x₂) - inner ℝ (p₁ - p₂) (p₁ - p₂)
      = -(inner ℝ (x₁ - p₁) (p₂ - p₁)) - inner ℝ (x₂ - p₂) (p₁ - p₂) := by
    simp only [inner_sub_left, inner_sub_right, real_inner_comm]
    ring
  linarith

end CAMA_chap_3_3_1_3
