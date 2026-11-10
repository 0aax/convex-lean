import ConvexStarLib.Defs

/-!
# `FCA_chap_B_2_2_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_2_2_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_2_2_1`, so the main result is `FCA_chap_B_2_2_1.FCA_chap_B_2_2_1`.
-/

namespace FCA_chap_B_2_2_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_B_2_2_1
  (f : E → EReal)
  (hf_convex : InConvRn f)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  InConvRn (fun (z : WithLp 2 (ℝ × E)) => perspective f z.ofLp.1 z.ofLp.2) := by
  obtain ⟨hbot, ⟨x₀, hx₀⟩, hconv⟩ := hf_convex
  have hmul : ∀ (u : ℝ) (y : EReal) (t : ℝ), 0 < u →
      ((u : EReal) * y ≤ (t : EReal) ↔ y ≤ ((t / u : ℝ) : EReal)) := by
    intro u y t hu
    induction y using EReal.rec with
    | bot => simp [EReal.coe_mul_bot_of_pos hu]
    | coe r =>
      rw [← EReal.coe_mul, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff, le_div_iff₀ hu, mul_comm]
    | top => simp [EReal.coe_mul_top_of_pos hu]
  have key : ∀ (u : ℝ) (x : E) (t : ℝ), perspective f u x ≤ (t : EReal) ↔
      0 < u ∧ f (u⁻¹ • x) ≤ ((t / u : ℝ) : EReal) := by
    intro u x t
    unfold perspective
    split_ifs with hu
    · rw [hmul u _ t hu]
      exact ⟨fun h => ⟨hu, h⟩, fun h => h.2⟩
    · simp only [top_le_iff, EReal.coe_ne_top, false_iff, not_and]
      intro h
      exact absurd h hu
  refine ⟨?_, ?_, ?_⟩
  · intro z
    simp only [perspective]
    split_ifs with hu
    · have hy := hbot (z.ofLp.1⁻¹ • z.ofLp.2)
      generalize f (z.ofLp.1⁻¹ • z.ofLp.2) = y at hy ⊢
      induction y using EReal.rec with
      | bot => exact absurd hy (lt_irrefl _)
      | coe r => rw [← EReal.coe_mul]; exact EReal.bot_lt_coe _
      | top => rw [EReal.coe_mul_top_of_pos hu]; exact bot_lt_top
    · exact bot_lt_top
  · refine ⟨WithLp.toLp 2 (1, x₀), ?_⟩
    simp [perspective, hx₀]
  · intro p hp q hq a b ha hb hab
    obtain ⟨⟨⟨u₁, x₁⟩⟩, t₁⟩ := p
    obtain ⟨⟨⟨u₂, x₂⟩⟩, t₂⟩ := q
    simp only [epigraph, Set.mem_setOf_eq] at hp hq ⊢
    rw [key] at hp hq
    obtain ⟨hu₁, hp⟩ := hp
    obtain ⟨hu₂, hq⟩ := hq
    simp only [Prod.smul_mk, Prod.mk_add_mk, WithLp.ofLp_add, WithLp.ofLp_smul, smul_eq_mul]
    rw [key]
    have hU : 0 < a * u₁ + b * u₂ := by
      rcases eq_or_lt_of_le ha with h | h
      · subst h
        simp only [zero_add] at hab
        subst hab
        simpa using hu₂
      · have h1 := mul_pos h hu₁
        have h2 := mul_nonneg hb hu₂.le
        linarith
    refine ⟨hU, ?_⟩
    have hu₁' : u₁ ≠ 0 := hu₁.ne'
    have hu₂' : u₂ ≠ 0 := hu₂.ne'
    have hU' : a * u₁ + b * u₂ ≠ 0 := hU.ne'
    have hmem := hconv (show (u₁⁻¹ • x₁, t₁ / u₁) ∈ epigraph f from hp)
      (show (u₂⁻¹ • x₂, t₂ / u₂) ∈ epigraph f from hq)
      (a := a * u₁ / (a * u₁ + b * u₂)) (b := b * u₂ / (a * u₁ + b * u₂))
      (div_nonneg (mul_nonneg ha hu₁.le) hU.le) (div_nonneg (mul_nonneg hb hu₂.le) hU.le)
      (by rw [← add_div, div_self hU'])
    simp only [epigraph, Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hmem
    have e1 : (a * u₁ / (a * u₁ + b * u₂)) • u₁⁻¹ • x₁ + (b * u₂ / (a * u₁ + b * u₂)) • u₂⁻¹ • x₂
        = (a * u₁ + b * u₂)⁻¹ • (a • x₁ + b • x₂) := by
      rw [smul_smul, smul_smul, smul_add, smul_smul, smul_smul]
      congr 2 <;> field_simp
    have e2 : a * u₁ / (a * u₁ + b * u₂) * (t₁ / u₁) + b * u₂ / (a * u₁ + b * u₂) * (t₂ / u₂)
        = (a * t₁ + b * t₂) / (a * u₁ + b * u₂) := by
      field_simp
    rw [e1, e2] at hmem
    exact hmem

end FCA_chap_B_2_2_1
