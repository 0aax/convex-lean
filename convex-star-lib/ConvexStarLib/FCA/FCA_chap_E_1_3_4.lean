import ConvexStarLib.Defs

/-!
# `FCA_chap_E_1_3_4`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_1_3_4` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_1_3_4`, so the main result is `FCA_chap_E_1_3_4.FCA_chap_E_1_3_4`.
-/

namespace FCA_chap_E_1_3_4

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_E_1_3_4
  (f : E → EReal)
  (V : Subspace ℝ E)
  (hf_nondegenerate : IsNondegenerate f)
  (hV_contains_affdom : parallelSubspace (affineSpan ℝ (effDom f)) ⊆
                        (V : Set E)) :
  let U := Vᗮ
  let pV : E → E :=
  fun x => Submodule.orthogonalProjection V x
  let pU : E → E :=
  fun x => Submodule.orthogonalProjection U x
  ∀ z ∈ affineSpan ℝ (effDom f), ∀ s,
  conjugate f s = inner ℝ (pU s) z + conjugate f (pV s) := by
  intro U pV pU z hz s
  -- adding a real constant commutes with suprema in `EReal`
  have key : ∀ (c : ℝ) (g : E → EReal), ⨆ x, ((c : EReal) + g x) = (c : EReal) + ⨆ x, g x := by
    intro c g
    have h1 : ∀ (d : ℝ) (h : E → EReal), ⨆ x, ((d : EReal) + h x) ≤ (d : EReal) + ⨆ x, h x :=
      fun d h => iSup_le fun x => add_le_add le_rfl (le_iSup h x)
    apply le_antisymm (h1 c g)
    calc (c : EReal) + ⨆ x, g x = (c : EReal) + ⨆ x, (((-c : ℝ) : EReal) + ((c : EReal) + g x)) := by
          congr 1
          apply iSup_congr
          intro x
          rw [← add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, zero_add]
      _ ≤ (c : EReal) + (((-c : ℝ) : EReal) + ⨆ x, ((c : EReal) + g x)) :=
          add_le_add le_rfl (h1 _ _)
      _ = ⨆ x, ((c : EReal) + g x) := by
          rw [← add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, zero_add]
  have hpt : ∀ x, ((inner ℝ s x : ℝ) : EReal) - f x =
      ((inner ℝ (pU s) z : ℝ) : EReal) + (((inner ℝ (pV s) x : ℝ) : EReal) - f x) := by
    intro x
    by_cases hx : f x < ⊤
    · have hxV : x - z ∈ V := by
        apply hV_contains_affdom
        exact ⟨x, z, subset_affineSpan ℝ _ hx, hz, rfl⟩
      have hpUs : pU s ∈ Vᗮ := by
        simp [pU, U]
      have h0 : inner ℝ (pU s) (x - z) = 0 := Submodule.inner_left_of_mem_orthogonal hxV hpUs
      have hdecomp : pV s + pU s = s := by
        simp only [pV, pU, U]
        exact V.starProjection_add_starProjection_orthogonal s
      have hreal : inner ℝ s x = inner ℝ (pU s) z + inner ℝ (pV s) x := by
        rw [inner_sub_right] at h0
        conv_lhs => rw [← hdecomp, inner_add_left]
        linarith
      rw [hreal, EReal.coe_add, add_sub_assoc]
    · have hx' : f x = ⊤ := not_lt_top_iff.mp hx
      rw [hx']
      simp
  unfold conjugate
  rw [Set.image_univ, Set.image_univ, sSup_range, sSup_range]
  simp_rw [hpt]
  exact key _ _

end FCA_chap_E_1_3_4
