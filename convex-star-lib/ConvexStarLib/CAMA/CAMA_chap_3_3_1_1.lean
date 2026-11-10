import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_3_1_1`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_3_1_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_3_1_1`, so the main result is `CAMA_chap_3_3_1_1.CAMA_chap_3_3_1_1`.
-/

namespace CAMA_chap_3_3_1_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_3_1_1
  (C : Set E)
  (x y : E)
  (hC₀ : IsClosed C)
  (hC₁ : Convex ℝ C)
  (hC₂ : Set.Nonempty C)
  (hy : y ∈ C) :
  y = pC x C hC₀ hC₁ hC₂ ↔ ∀ z ∈ C, inner ℝ (x - y) (z - y) ≤ 0 := by
  set p := pC x C hC₀ hC₁ hC₂ with hp_def
  have hspec := Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex hC₂ hC₀.isComplete hC₁ x)
  have hpC : p ∈ C := hspec.1
  have hpineq : ∀ w ∈ C, inner ℝ (x - p) (w - p) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hC₁ hpC).1 hspec.2
  constructor
  · rintro rfl
    exact hpineq
  · intro h
    have h1 : inner ℝ (x - y) (p - y) ≤ 0 := h p hpC
    have h2 : inner ℝ (x - p) (y - p) ≤ 0 := hpineq y hy
    have key : inner ℝ (x - y) (p - y) + inner ℝ (x - p) (y - p) = ‖p - y‖ ^ 2 := by
      have e1 : y - p = -(p - y) := by abel
      have e2 : x - y - (x - p) = p - y := by abel
      rw [e1, inner_neg_right, ← sub_eq_add_neg, ← inner_sub_left, e2,
        real_inner_self_eq_norm_sq]
    have h3 : ‖p - y‖ ^ 2 ≤ 0 := by linarith
    have h4 : ‖p - y‖ = 0 := by
      have := norm_nonneg (p - y)
      nlinarith
    have h5 : p - y = 0 := norm_eq_zero.1 h4
    exact (sub_eq_zero.1 h5).symm

end CAMA_chap_3_3_1_1
