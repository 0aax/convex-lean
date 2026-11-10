import ConvexStarLib.Defs

/-!
# `FCA_chap_C_2_1_3`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_2_1_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_2_1_3`, so the main result is `FCA_chap_C_2_1_3.FCA_chap_C_2_1_3`.
-/

namespace FCA_chap_C_2_1_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_C_2_1_3
  (S : Set E)
  (hS : Set.Nonempty S) :
  let support_fun := supportFunction S
  (∀ x, support_fun x ≠ ⊤) ↔
  (Bornology.IsBounded S) := by
  intro support_fun
  -- a finite value of the support function gives a real upper bound on `⟪v, w⟫` over `S`
  have key : ∀ w, supportFunction S w ≠ ⊤ → ∃ M : ℝ, ∀ v ∈ S, inner ℝ v w ≤ M := by
    intro w hw
    obtain ⟨M, hM, -⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_top_iff_ne_top.mpr hw)
    refine ⟨M, fun v hv => ?_⟩
    have h1 : ((inner ℝ v w : ℝ) : EReal) ≤ supportFunction S w :=
      le_sSup (Set.mem_image_of_mem _ hv)
    exact EReal.coe_le_coe_iff.mp (h1.trans hM.le)
  constructor
  · intro h
    haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
    -- the functionals `⟪v, ·⟫`, `v ∈ S`, are pointwise bounded; apply Banach–Steinhaus
    have hbd : ∀ w : E, ∃ C, ∀ v : S, ‖innerSL ℝ (v : E) w‖ ≤ C := by
      intro w
      obtain ⟨M₁, hM₁⟩ := key w (h w)
      obtain ⟨M₂, hM₂⟩ := key (-w) (h (-w))
      refine ⟨max M₁ M₂, fun v => ?_⟩
      have h1 := hM₁ v v.2
      have h2 := hM₂ v v.2
      rw [inner_neg_right] at h2
      rw [innerSL_apply_apply, Real.norm_eq_abs, abs_le]
      constructor
      · linarith [le_max_right M₁ M₂]
      · linarith [le_max_left M₁ M₂]
    obtain ⟨C, hC⟩ := banach_steinhaus (g := fun v : S => innerSL ℝ (v : E)) hbd
    refine isBounded_iff_forall_norm_le.mpr ⟨C, fun v hv => ?_⟩
    have := hC ⟨v, hv⟩
    rwa [innerSL_apply_norm] at this
  · intro h x
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp h
    have hle : supportFunction S x ≤ ((R * ‖x‖ : ℝ) : EReal) := by
      apply sSup_le
      rintro _ ⟨v, hv, rfl⟩
      refine EReal.coe_le_coe_iff.mpr ?_
      calc inner ℝ v x ≤ ‖v‖ * ‖x‖ := real_inner_le_norm v x
        _ ≤ R * ‖x‖ := mul_le_mul_of_nonneg_right (hR v hv) (norm_nonneg x)
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hle

end FCA_chap_C_2_1_3
