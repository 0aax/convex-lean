import ConvexStarLib.Defs

/-!
# `FCA_chap_C_3_2_5`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_3_2_5` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_3_2_5`, so the main result is `FCA_chap_C_3_2_5.FCA_chap_C_3_2_5`.
-/

namespace FCA_chap_C_3_2_5

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_C_3_2_5
  (C : Set E)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C)
  (hC_origin : 0 ∈ C) :
  let C' := polarBody C
  let σC := supportFunction C
  let γC' := gaugeFun C'
  ∀ (x : E), γC' x = σC x := by
  intro C' σC γC' x
  -- `σC x ≥ 0` since `0 ∈ C`
  have hσ_nonneg : (0 : EReal) ≤ σC x := by
    show (0 : EReal) ≤ sSup _
    apply le_sSup_of_le (b := ((inner ℝ (0 : E) x : ℝ) : EReal))
    · exact ⟨0, hC_origin, rfl⟩
    · simp
  -- for `l' > 0`: `x ∈ l' • C'` iff `σC x ≤ l'`
  have key : ∀ l' : ℝ, 0 < l' → ((∃ y ∈ C', x = l' • y) ↔ σC x ≤ (l' : EReal)) := by
    intro l' hl'
    constructor
    · rintro ⟨y, hy, rfl⟩
      show sSup _ ≤ _
      apply sSup_le
      rintro _ ⟨v, hv, rfl⟩
      have h1 : inner ℝ v y ≤ 1 := hy v hv
      show ((inner ℝ v (l' • y) : ℝ) : EReal) ≤ l'
      rw [inner_smul_right]
      exact_mod_cast (by nlinarith : l' * inner ℝ v y ≤ l')
    · intro h
      refine ⟨l'⁻¹ • x, ?_, ?_⟩
      · intro v hv
        have hmem : ((inner ℝ v x : ℝ) : EReal) ∈
            (fun v : E => ((inner ℝ v x : ℝ) : EReal)) '' C := ⟨v, hv, rfl⟩
        have h1 : ((inner ℝ v x : ℝ) : EReal) ≤ l' := le_trans (le_sSup hmem) h
        have h2 : inner ℝ v x ≤ l' := by exact_mod_cast h1
        rw [inner_smul_right, inv_mul_le_iff₀ hl']
        linarith
      · rw [smul_smul, mul_inv_cancel₀ hl'.ne', one_smul]
  show sInf _ = _
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro c hc
    induction c using EReal.rec with
    | bot => exact absurd hc not_lt_bot
    | top => exact le_top
    | coe c' =>
      have hc'pos : (0 : ℝ) < c' := by
        have := lt_of_le_of_lt hσ_nonneg hc
        exact_mod_cast this
      exact sInf_le ⟨c', rfl, hc'pos, (key c' hc'pos).mpr hc.le⟩
  · apply le_sInf
    rintro _ ⟨l', rfl, hl', hy⟩
    exact (key l' hl').mp hy

end FCA_chap_C_3_2_5
