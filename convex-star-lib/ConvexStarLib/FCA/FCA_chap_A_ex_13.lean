import ConvexStarLib.Defs

/-!
# `FCA_chap_A_ex_13`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_A_ex_13` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_A_ex_13`, so the main result is `FCA_chap_A_ex_13.FCA_chap_A_ex_13`.
-/

namespace FCA_chap_A_ex_13

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_A_ex_13
  (C : Set E)
  (x yC : E)
  (hC_nonempty : Set.Nonempty C)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C)
  (hyC : yC ∈ C) :
  yC ∈ projectionMapping C x ↔
  (∀ y ∈ C, inner ℝ (x - y) (y - yC) ≤ 0) := by
  constructor
  · -- Forward: compare with `z = y` directly; no convexity needed.
    rintro ⟨-, hmin⟩ y hy
    have h1 : ‖yC - x‖ ^ 2 ≤ ‖y - x‖ ^ 2 := by
      have := hmin y hy
      gcongr
    have e1 : ‖yC - x‖ = ‖(x - y) + (y - yC)‖ := by
      rw [norm_sub_rev]; congr 1; abel
    rw [e1, norm_add_sq_real, norm_sub_rev] at h1
    nlinarith [sq_nonneg ‖y - yC‖]
  · -- Backward: test the hypothesis at the midpoint of `yC` and `z`.
    intro h
    refine ⟨hyC, fun z hz => ?_⟩
    have hm : (1/2 : ℝ) • yC + (1/2 : ℝ) • z ∈ C :=
      hC_convex hyC hz (by norm_num) (by norm_num) (by norm_num)
    have hh := h _ hm
    have e1 : x - ((1/2 : ℝ) • yC + (1/2 : ℝ) • z) = (x - yC) - (1/2 : ℝ) • (z - yC) := by
      module
    have e2 : (1/2 : ℝ) • yC + (1/2 : ℝ) • z - yC = (1/2 : ℝ) • (z - yC) := by
      module
    rw [e1, e2, inner_sub_left, real_inner_smul_left, real_inner_smul_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq] at hh
    have e3 : z - x = (z - yC) - (x - yC) := by abel
    rw [norm_sub_rev yC x, e3, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
      norm_sub_sq_real (z - yC) (x - yC), real_inner_comm]
    linarith

end FCA_chap_A_ex_13
