import ConvexStarLib.Defs

/-!
# `FCA_chap_A_ex_12`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_A_ex_12` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_A_ex_12`, so the main result is `FCA_chap_A_ex_12.FCA_chap_A_ex_12`.
-/

namespace FCA_chap_A_ex_12

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem FCA_chap_A_ex_12
  (hE : 2 ≤ Module.finrank ℝ E)
  (hF : 1 ≤ Module.finrank ℝ F) :
  (∀  (A : AffineMap ℝ E F)
    (C : Set E) (x : E),
    Convex ℝ C → Function.Injective A →
    x ∈ Set.extremePoints ℝ C →
    A x ∈ Set.extremePoints ℝ (A '' C)) ∧
  (∃  (A : AffineMap ℝ E F)
    (C : Set E) (x : E),
    Convex ℝ C ∧ ¬ Function.Injective A ∧
    x ∈ Set.extremePoints ℝ C ∧
    A x ∉ Set.extremePoints ℝ (A '' C)) := by
  refine ⟨?_, ?_⟩
  · intro A C x _ hA hx
    rw [mem_extremePoints] at hx ⊢
    refine ⟨Set.mem_image_of_mem A hx.1, ?_⟩
    rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩ hseg
    rw [← image_openSegment] at hseg
    obtain ⟨z, hz, hzx⟩ := hseg
    obtain rfl : z = x := hA hzx
    obtain ⟨h1, h2⟩ := hx.2 c₁ hc₁ c₂ hc₂ hz
    exact ⟨by rw [h1], by rw [h2]⟩
  · let b := stdOrthonormalBasis ℝ E
    let i0 : Fin (Module.finrank ℝ E) := ⟨0, by omega⟩
    let i1 : Fin (Module.finrank ℝ E) := ⟨1, by omega⟩
    have hi : i0 ≠ i1 := Fin.ne_of_val_ne (show (0:ℕ) ≠ 1 by norm_num)
    haveI : Nontrivial F := Module.nontrivial_of_finrank_pos (show 0 < Module.finrank ℝ F by omega)
    obtain ⟨f, hf⟩ := exists_ne (0 : F)
    let e₁ := b i0
    let e₂ := b i1
    have he₁ : ‖e₁‖ = 1 := b.orthonormal.1 i0
    have he₂ : ‖e₂‖ = 1 := b.orthonormal.1 i1
    have h12 : inner ℝ e₁ e₂ = 0 := b.orthonormal.2 hi
    have h11 : inner ℝ e₁ e₁ = (1 : ℝ) := by
      rw [real_inner_self_eq_norm_sq, he₁]; norm_num
    let A : E →ᵃ[ℝ] F := ((innerₛₗ ℝ e₁).smulRight f).toAffineMap
    have hA : ∀ z, A z = (inner ℝ e₁ z) • f := fun z => rfl
    refine ⟨A, Metric.closedBall 0 1, e₂, convex_closedBall 0 1, ?_, ?_, ?_⟩
    · intro hinj
      have h1 : A e₂ = A 0 := by
        rw [hA, hA, h12, inner_zero_right]
      have := hinj h1
      rw [this, norm_zero] at he₂
      exact zero_ne_one he₂
    · rw [mem_extremePoints]
      refine ⟨by simp [he₂], ?_⟩
      rintro y₁ hy₁ y₂ hy₂ ⟨a, c, ha, hc, hac, hx⟩
      rw [mem_closedBall_zero_iff] at hy₁ hy₂
      by_cases hne : y₁ = y₂
      · subst hne
        rw [← add_smul, hac, one_smul] at hx
        exact ⟨hx, hx⟩
      · exfalso
        have := norm_combo_lt_of_ne hy₁ hy₂ hne ha hc hac
        rw [hx, he₂] at this
        exact lt_irrefl _ this
    · rw [mem_extremePoints]
      rintro ⟨_, h⟩
      have hm1 : A e₁ ∈ A '' Metric.closedBall 0 1 :=
        Set.mem_image_of_mem A (by simp [he₁])
      have hm2 : A (-e₁) ∈ A '' Metric.closedBall 0 1 :=
        Set.mem_image_of_mem A (by simp [he₁])
      have hseg : A e₂ ∈ openSegment ℝ (A e₁) (A (-e₁)) := by
        refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
        rw [hA, hA, hA, h12, inner_neg_right, h11]
        simp
      have := (h _ hm1 _ hm2 hseg).1
      rw [hA, hA, h12, h11, one_smul, zero_smul] at this
      exact hf this

end FCA_chap_A_ex_12
