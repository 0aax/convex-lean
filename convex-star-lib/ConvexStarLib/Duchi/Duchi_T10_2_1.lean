import ConvexStarLib.Defs

/-!
# `Duchi_T10_2_1`

Source: Duchi, EE364m Convex Optimization (exercise sets).

Statement from the `convex-eval-v28-2h/Duchi_T10_2_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Duchi_T10_2_1`, so the main result is `Duchi_T10_2_1.Duchi_T10_2_1`.
-/

namespace Duchi_T10_2_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


set_option linter.unusedVariables false in
theorem Duchi_T10_2_1
  {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EReal)
  (hf_closed : LowerSemicontinuous f)
  (x₀ : EuclideanSpace ℝ (Fin n))
  (ε δ : ℝ)
  (hε : 0 ≤ ε)
  (hx₀_fin : f x₀ < ⊤)
  (hx₀_near : ∀ y, f x₀ ≤ f y + ↑ε)
  (hδ : 0 < δ)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  ∃ (x_hat : EuclideanSpace ℝ (Fin n)),
  (‖x_hat - x₀‖ ≤ ε / δ) ∧
  (f x_hat ≤ f x₀) ∧
  (∀ x, f x_hat ≤ f x + ↑(δ * ‖x - x_hat‖)) ∧
  (∀ x, f x + ↑(δ * ‖x - x_hat‖) = f x_hat → x = x_hat) := by
  -- every value of `f` is either `⊤` or a real number
  have hcases : ∀ x, f x = ⊤ ∨ ∃ r : ℝ, f x = (r : EReal) := by
    intro x
    have h := f_ne_bot x
    generalize f x = y at h ⊢
    induction y using EReal.rec with
    | bot => exact absurd h (lt_irrefl _)
    | coe r => exact Or.inr ⟨r, rfl⟩
    | top => exact Or.inl rfl
  obtain ⟨a, ha⟩ : ∃ a : ℝ, f x₀ = (a : EReal) := by
    rcases hcases x₀ with h | h
    · rw [h] at hx₀_fin; exact absurd hx₀_fin (lt_irrefl _)
    · exact h
  -- the set `S`
  set g : EuclideanSpace ℝ (Fin n) → EReal := fun x => f x + ((δ * ‖x - x₀‖ : ℝ) : EReal)
    with hg_def
  have hg : LowerSemicontinuous g := by
    apply LowerSemicontinuous.add' hf_closed
    · exact (continuous_coe_real_ereal.comp
        (continuous_const.mul (continuous_norm.comp (continuous_id.sub continuous_const)))).lowerSemicontinuous
    · intro x
      apply EReal.continuousAt_add
      · right; exact EReal.coe_ne_bot _
      · left; exact (f_ne_bot x).ne'
  set S : Set (EuclideanSpace ℝ (Fin n)) := g ⁻¹' Set.Iic (f x₀) with hS_def
  have hS_closed : IsClosed S := hg.isClosed_preimage (f x₀)
  have hx₀S : x₀ ∈ S := by
    simp [hS_def, hg_def]
  -- membership in S, in real terms
  have hmemS : ∀ x, x ∈ S → ∃ r : ℝ, f x = (r : EReal) ∧ r + δ * ‖x - x₀‖ ≤ a := by
    intro x hx
    have hx' : f x + ((δ * ‖x - x₀‖ : ℝ) : EReal) ≤ (a : EReal) := by
      simpa [hS_def, hg_def, ha] using hx
    rcases hcases x with h | ⟨r, hr⟩
    · rw [h, EReal.top_add_coe] at hx'
      exact absurd hx' (by simp)
    · refine ⟨r, hr, ?_⟩
      rw [hr, ← EReal.coe_add, EReal.coe_le_coe_iff] at hx'
      exact hx'
  have hnear : ∀ x (r : ℝ), f x = (r : EReal) → a ≤ r + ε := by
    intro x r hr
    have := hx₀_near x
    rw [ha, hr, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
    exact this
  have hS_bdd : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := x₀) (r := ε / δ)).subset ?_
    intro x hx
    obtain ⟨r, hr, hrS⟩ := hmemS x hx
    have h1 := hnear x r hr
    rw [Metric.mem_closedBall, dist_eq_norm, le_div_iff₀ hδ]
    nlinarith
  have hS_compact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hS_closed hS_bdd
  obtain ⟨xh, hxhS, hmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn ⟨x₀, hx₀S⟩ hS_compact (hf_closed.lowerSemicontinuousOn S)
  obtain ⟨b, hb, hbS⟩ := hmemS xh hxhS
  have hnb := hnear xh b hb
  have hnorm_nonneg := norm_nonneg (xh - x₀)
  refine ⟨xh, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hδ]
    nlinarith
  · rw [hb, ha, EReal.coe_le_coe_iff]
    nlinarith
  · intro x
    rcases hcases x with h | ⟨r, hr⟩
    · rw [h, EReal.top_add_coe]; exact le_top
    · rw [hb, hr, ← EReal.coe_add, EReal.coe_le_coe_iff]
      by_cases hxS : x ∈ S
      · have : f xh ≤ f x := hmin hxS
        rw [hb, hr, EReal.coe_le_coe_iff] at this
        have := norm_nonneg (x - xh)
        nlinarith
      · have hlt : (a : EReal) < f x + ((δ * ‖x - x₀‖ : ℝ) : EReal) := by
          simpa [hS_def, hg_def, ha] using hxS
        rw [hr, ← EReal.coe_add, EReal.coe_lt_coe_iff] at hlt
        have htri : ‖x - x₀‖ ≤ ‖x - xh‖ + ‖xh - x₀‖ := norm_sub_le_norm_sub_add_norm_sub x xh x₀
        nlinarith
  · intro x hx
    rcases hcases x with h | ⟨r, hr⟩
    · rw [h, EReal.top_add_coe, hb] at hx
      exact absurd hx.symm (EReal.coe_ne_top b)
    · rw [hb, hr, ← EReal.coe_add, EReal.coe_eq_coe_iff] at hx
      by_cases hxS : x ∈ S
      · have : f xh ≤ f x := hmin hxS
        rw [hb, hr, EReal.coe_le_coe_iff] at this
        have h0 : δ * ‖x - xh‖ ≤ 0 := by linarith
        have h1 : ‖x - xh‖ ≤ 0 := by
          by_contra hcon
          push_neg at hcon
          have := mul_pos hδ hcon
          linarith
        have h2 : ‖x - xh‖ = 0 := le_antisymm h1 (norm_nonneg _)
        rw [norm_eq_zero, sub_eq_zero] at h2
        exact h2
      · have hlt : (a : EReal) < f x + ((δ * ‖x - x₀‖ : ℝ) : EReal) := by
          simpa [hS_def, hg_def, ha] using hxS
        rw [hr, ← EReal.coe_add, EReal.coe_lt_coe_iff] at hlt
        have htri : ‖x - x₀‖ ≤ ‖x - xh‖ + ‖xh - x₀‖ := norm_sub_le_norm_sub_add_norm_sub x xh x₀
        exfalso
        nlinarith

end Duchi_T10_2_1
