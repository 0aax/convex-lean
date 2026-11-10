import ConvexStarLib.Defs

/-!
# `FCA_chap_E_1_3_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_1_3_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_1_3_2`, so the main result is `FCA_chap_E_1_3_2.FCA_chap_E_1_3_2`.
-/

namespace FCA_chap_E_1_3_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_E_1_3_2
  (f : E → EReal)
  (H : Subspace ℝ E)
  (hf_nondegenerate : IsNondegenerate f ∧ ∃ (x : E), x ∈ H ∧ f x ≠ ⊤) :
  let pH : E → E :=
  fun x => Submodule.orthogonalProjection H x
  let g := fun x => f x + (setIndicator (H : Set E)) x
  IsNondegenerate g ∧
  ∀ (s : E), conjugate g s = conjugate (f ∘ pH) (pH s) := by
  intro pH g
  obtain ⟨⟨_, ⟨s0, b0, hsb⟩⟩, ⟨x1, hx1H, hx1⟩⟩ := hf_nondegenerate
  have hf_ne_bot : ∀ x, f x ≠ ⊥ := by
    intro x h
    have h1 := hsb x
    rw [h] at h1
    have h2 : ((inner ℝ s0 x : ℝ) : EReal) - (b0 : EReal) = ⊥ := le_bot_iff.mp h1
    rw [← EReal.coe_sub] at h2
    exact EReal.coe_ne_bot _ h2
  have hg_mem : ∀ x ∈ H, g x = f x := by
    intro x hx
    simp [g, setIndicator, hx]
  have hg_nmem : ∀ x ∉ H, g x = ⊤ := by
    intro x hx
    simp only [g, setIndicator, SetLike.mem_coe, hx, if_false]
    exact EReal.add_top_of_ne_bot (hf_ne_bot x)
  have hpH_mem : ∀ x, pH x ∈ H := fun x => Submodule.coe_mem _
  have hpH_self : ∀ x ∈ H, pH x = x := by
    intro x hx
    show ((H.orthogonalProjection x : H) : E) = x
    rw [show x = ((⟨x, hx⟩ : H) : E) from rfl, Submodule.orthogonalProjection_mem_subspace_eq_self]
  have hpH_inner : ∀ u v, inner ℝ (pH u) v = inner ℝ u (pH v) := by
    intro u v
    have := Submodule.inner_starProjection_left_eq_right H u v
    simpa only [Submodule.starProjection_apply] using this
  refine ⟨⟨⟨x1, by rw [hg_mem x1 hx1H]; exact hx1⟩, ⟨s0, b0, fun x => ?_⟩⟩, fun s => ?_⟩
  · by_cases hx : x ∈ H
    · rw [hg_mem x hx]; exact hsb x
    · rw [hg_nmem x hx]; exact le_top
  · unfold conjugate
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨x, -, rfl⟩
      by_cases hx : x ∈ H
      · apply le_sSup
        refine ⟨x, Set.mem_univ _, ?_⟩
        simp only [Function.comp, hpH_inner, hpH_self x hx, hg_mem x hx]
      · simp only [hg_nmem x hx, EReal.sub_top]
        exact bot_le
    · apply sSup_le
      rintro _ ⟨x, -, rfl⟩
      apply le_sSup
      refine ⟨pH x, Set.mem_univ _, ?_⟩
      simp only [Function.comp, hpH_inner, hg_mem _ (hpH_mem x)]

end FCA_chap_E_1_3_2
