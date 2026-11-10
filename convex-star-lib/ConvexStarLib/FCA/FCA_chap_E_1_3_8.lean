import ConvexStarLib.Defs

/-!
# `FCA_chap_E_1_3_8`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_1_3_8` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_1_3_8`, so the main result is `FCA_chap_E_1_3_8.FCA_chap_E_1_3_8`.
-/

namespace FCA_chap_E_1_3_8

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_E_1_3_8
  (f : E → EReal)
  (hf_nondegenerate : IsNondegenerate f) (hf_coercive : IsOneCoerciveFun f) :
  ∀ s, conjugate f s < ⊤ := by
  intro s
  obtain ⟨_, s₀, b, hb⟩ := hf_nondegenerate
  have h := hf_coercive (‖s‖ + 1)
  rw [Filter.eventually_comap, Filter.eventually_atTop] at h
  obtain ⟨R, hR⟩ := h
  set R' : ℝ := max R 1 with hR'
  have hR'1 : (1 : ℝ) ≤ R' := le_max_right _ _
  set M : ℝ := max 0 ((‖s‖ + ‖s₀‖) * R' + b) with hM
  have hM0 : (0 : ℝ) ≤ M := le_max_left _ _
  have hM2 : (‖s‖ + ‖s₀‖) * R' + b ≤ M := le_max_right _ _
  have key : ∀ x, ((inner ℝ s x : ℝ) : EReal) - f x ≤ (M : EReal) := by
    intro x
    have hsx : inner ℝ s x ≤ ‖s‖ * ‖x‖ := real_inner_le_norm s x
    by_cases hx : R' ≤ ‖x‖
    · have hx1 : (1 : ℝ) ≤ ‖x‖ := le_trans hR'1 hx
      have hxpos : (0 : ℝ) < ‖x‖ := by linarith
      have h1 := hR ‖x‖ (le_trans (le_max_left _ _) hx) x rfl
      generalize f x = y at h1 ⊢
      induction y with
      | bot =>
        exfalso
        rw [EReal.coe_mul_bot_of_pos (inv_pos.mpr hxpos)] at h1
        exact absurd h1 (not_le.mpr (EReal.bot_lt_coe _))
      | coe r =>
        rw [← EReal.coe_mul, EReal.coe_le_coe_iff] at h1
        rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
        have h2 : (‖s‖ + 1) * ‖x‖ ≤ r := by
          have := mul_le_mul_of_nonneg_right h1 hxpos.le
          rwa [mul_comm (‖x‖⁻¹) r, mul_assoc, inv_mul_cancel₀ hxpos.ne', mul_one] at this
        nlinarith
      | top =>
        simp
    · push_neg at hx
      have h1 := hb x
      have hs0x : -(inner ℝ s₀ x) ≤ ‖s₀‖ * ‖x‖ :=
        le_trans (neg_le_abs _) (abs_real_inner_le_norm s₀ x)
      rw [← EReal.coe_sub] at h1
      generalize f x = y at h1 ⊢
      induction y with
      | bot =>
        exfalso
        exact absurd h1 (not_le.mpr (EReal.bot_lt_coe _))
      | coe r =>
        have h1' : inner ℝ s₀ x - b ≤ r := EReal.coe_le_coe_iff.mp h1
        rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
        have : (‖s‖ + ‖s₀‖) * ‖x‖ ≤ (‖s‖ + ‖s₀‖) * R' :=
          mul_le_mul_of_nonneg_left hx.le (by positivity)
        nlinarith
      | top =>
        simp
  calc conjugate f s ≤ (M : EReal) := by
        unfold conjugate
        apply sSup_le
        rintro _ ⟨x, _, rfl⟩
        exact key x
    _ < ⊤ := EReal.coe_lt_top _

end FCA_chap_E_1_3_8
