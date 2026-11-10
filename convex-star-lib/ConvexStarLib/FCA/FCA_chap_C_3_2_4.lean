import ConvexStarLib.Defs

/-!
# `FCA_chap_C_3_2_4`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_3_2_4` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_3_2_4`, so the main result is `FCA_chap_C_3_2_4.FCA_chap_C_3_2_4`.
-/

namespace FCA_chap_C_3_2_4

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_C_3_2_4
  (C : Set E)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C)
  (hC_origin : 0 ∈ C) :
  let γC := gaugeFun C
  let C' := polarBody C
  let σC' := supportFunction C'
  (∀ (x : E), γC x = σC' x) ∧ IsClosed C' ∧ Convex ℝ C' ∧ 0 ∈ C' := by
  intro γC C' σC'
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h0C' : (0 : E) ∈ polarBody C := by
    intro x _
    simp
  have hpolar : polarBody C = ⋂ x ∈ C, {y : E | inner ℝ x y ≤ 1} := by
    ext y; simp [polarBody]
  refine ⟨?_, ?_, ?_, h0C'⟩
  · intro x
    show gaugeFun C x = supportFunction (polarBody C) x
    unfold gaugeFun supportFunction
    apply le_antisymm
    · -- sInf S ≤ sSup T
      apply le_of_forall_gt_imp_ge_of_dense
      intro a ha
      induction a using EReal.rec with
      | bot => exact absurd ha not_lt_bot
      | top => exact le_top
      | coe r =>
        have h0T : (0 : EReal) ≤
            sSup ((fun v : E => ((inner ℝ v x : ℝ) : EReal)) '' polarBody C) := by
          apply le_sSup_of_le (Set.mem_image_of_mem _ h0C')
          simp
        have hr : (0 : ℝ) < r := by
          have := lt_of_le_of_lt h0T ha
          exact_mod_cast this
        have hmem : r⁻¹ • x ∈ C := by
          by_contra hnot
          obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point hC_convex hC_closed hnot
          have hu : 0 < u := by
            have := hfu 0 hC_origin
            simpa using this
          set z := (InnerProductSpace.toDual ℝ E).symm f with hz
          have hzf : ∀ w, inner ℝ z w = f w := fun w => InnerProductSpace.toDual_symm_apply
          have hv : u⁻¹ • z ∈ polarBody C := by
            intro c hc
            rw [real_inner_comm, real_inner_smul_left, hzf]
            rw [inv_mul_le_iff₀ hu]
            linarith [hfu c hc]
          have hlt : (r : EReal) < ((inner ℝ (u⁻¹ • z) x : ℝ) : EReal) := by
            have : r < inner ℝ (u⁻¹ • z) x := by
              rw [real_inner_smul_left, hzf]
              have h1 : f (r⁻¹ • x) = r⁻¹ * f x := by simp
              rw [h1] at hux
              rw [lt_inv_mul_iff₀ hu]
              rw [lt_inv_mul_iff₀ hr] at hux
              nlinarith
            exact_mod_cast this
          have hle : ((inner ℝ (u⁻¹ • z) x : ℝ) : EReal) ≤
              sSup ((fun v : E => ((inner ℝ v x : ℝ) : EReal)) '' polarBody C) := by
            apply le_sSup
            exact ⟨u⁻¹ • z, hv, rfl⟩
          exact absurd (lt_trans (lt_of_lt_of_le hlt hle) ha) (lt_irrefl _)
        apply sInf_le
        refine ⟨r, rfl, hr, r⁻¹ • x, hmem, ?_⟩
        rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    · -- sSup T ≤ sInf S
      apply sSup_le
      rintro b ⟨v, hv, rfl⟩
      apply le_sInf
      rintro l ⟨l', rfl, hl', y, hy, rfl⟩
      have : inner ℝ v (l' • y) ≤ l' := by
        rw [real_inner_smul_right, real_inner_comm]
        have := hv y hy
        nlinarith
      show ((inner ℝ v (l' • y) : ℝ) : EReal) ≤ (l' : EReal)
      exact_mod_cast this
  · -- IsClosed
    show IsClosed (polarBody C)
    rw [hpolar]
    apply isClosed_biInter
    intro x _
    exact isClosed_le (continuous_const.inner continuous_id) continuous_const
  · -- Convex
    show Convex ℝ (polarBody C)
    rw [hpolar]
    apply convex_iInter₂
    intro x _
    exact convex_halfSpace_le (innerₛₗ ℝ x).isLinear 1

end FCA_chap_C_3_2_4
