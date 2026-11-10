import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_5_3_3`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_5_3_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_5_3_3`, so the main result is `CAMA_chap_3_5_3_3.CAMA_chap_3_5_3_3`.
-/

namespace CAMA_chap_3_5_3_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_5_3_3
  (x : E)
  (C : Set E)
  (s : E)
  (hC_nonempty : Set.Nonempty C)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C)
  (hx_in_C : x ∈ C) :
  List.TFAE [
    s ∈ convexNormalCone x C,
    ∀ y ∈ C, inner ℝ s y ≤ inner ℝ s x,
    x = pC (x + s) C hC_closed hC_convex hC_nonempty
  ] := by
  have hp : pC (x + s) C hC_closed hC_convex hC_nonempty ∈ C ∧
      ‖(x + s) - pC (x + s) C hC_closed hC_convex hC_nonempty‖ =
        ⨅ w : C, ‖(x + s) - w‖ :=
    Classical.choose_spec
      (exists_norm_eq_iInf_of_complete_convex hC_nonempty hC_closed.isComplete hC_convex (x + s))
  generalize pC (x + s) C hC_closed hC_convex hC_nonempty = p at hp ⊢
  obtain ⟨hpC, hpmin⟩ := hp
  have hcone : s ∈ convexNormalCone x C ↔ ∀ y ∈ C, inner ℝ s (y - x) ≤ 0 := Iff.rfl
  tfae_have 1 ↔ 2 := by
    rw [hcone]
    constructor
    · intro h y hy
      have := h y hy
      rw [inner_sub_right] at this
      linarith
    · intro h y hy
      rw [inner_sub_right]
      linarith [h y hy]
  tfae_have 3 → 1 := by
    intro hx
    rw [hcone]
    intro y hy
    have h1 : ‖(x + s) - x‖ = ⨅ w : C, ‖(x + s) - w‖ := by
      calc ‖(x + s) - x‖ = ‖(x + s) - p‖ := by rw [← hx]
        _ = ⨅ w : C, ‖(x + s) - w‖ := hpmin
    have h2 := (norm_eq_iInf_iff_real_inner_le_zero hC_convex hx_in_C).1 h1 y hy
    rwa [add_sub_cancel_left] at h2
  tfae_have 1 → 3 := by
    intro h
    rw [hcone] at h
    have h1 : ∀ w ∈ C, inner ℝ ((x + s) - p) (w - p) ≤ 0 :=
      (norm_eq_iInf_iff_real_inner_le_zero hC_convex hpC).1 hpmin
    have h2 := h1 x hx_in_C
    have h3 : inner ℝ s (p - x) ≤ 0 := h p hpC
    have h4 : inner ℝ ((x + s) - p) (x - p) = ‖x - p‖ ^ 2 + inner ℝ s (x - p) := by
      rw [show (x + s) - p = (x - p) + s by abel, inner_add_left, real_inner_self_eq_norm_sq]
    have h5 : inner ℝ s (x - p) = - inner ℝ s (p - x) := by
      rw [← inner_neg_right, neg_sub]
    have h6 : ‖x - p‖ ^ 2 ≤ 0 := by linarith
    have h7 : ‖x - p‖ = 0 := by
      have := sq_nonneg ‖x - p‖
      have h8 : ‖x - p‖ ^ 2 = 0 := le_antisymm h6 this
      exact pow_eq_zero_iff (two_ne_zero) |>.1 h8
    rw [norm_eq_zero, sub_eq_zero] at h7
    exact h7
  tfae_finish

end CAMA_chap_3_5_3_3
