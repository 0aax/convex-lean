import ConvexStarLib.Defs

/-!
# `FCA_chap_A_ex_3`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_A_ex_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_A_ex_3`, so the main result is `FCA_chap_A_ex_3.FCA_chap_A_ex_3`.
-/

namespace FCA_chap_A_ex_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_A_ex_3 :
  ∃ (K₁ K₂ : Set (EuclideanSpace ℝ (Fin 3))),
    IsClosed K₁ ∧ IsConvexCone K₁ ∧
    IsClosed K₂ ∧ IsConvexCone K₂ ∧
    ¬ IsClosed (setAdd K₁ K₂) := by
  have h0 : Continuous (fun p : EuclideanSpace ℝ (Fin 3) => p 0) := PiLp.continuous_apply _ _ 0
  have h1 : Continuous (fun p : EuclideanSpace ℝ (Fin 3) => p 1) := PiLp.continuous_apply _ _ 1
  have h2 : Continuous (fun p : EuclideanSpace ℝ (Fin 3) => p 2) := PiLp.continuous_apply _ _ 2
  refine ⟨{p | 0 ≤ p 0 ∧ 0 ≤ p 2 ∧ p 1 ^ 2 ≤ p 0 * p 2},
    {p | p 0 ≤ 0 ∧ p 1 = 0 ∧ p 2 = 0}, ?_, ?_, ?_, ?_, ?_⟩
  · -- K₁ closed
    refine (isClosed_le continuous_const h0).inter ((isClosed_le continuous_const h2).inter ?_)
    exact isClosed_le (h1.pow 2) (h0.mul h2)
  · -- K₁ convex cone
    rintro x ⟨hx0, hx2, hx1⟩ y ⟨hy0, hy2, hy1⟩ α hα β hβ
    simp only [Set.mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have key : 2 * (x 1 * y 1) ≤ x 0 * y 2 + y 0 * x 2 := by
      have hsq : (2 * (x 1 * y 1)) ^ 2 ≤ (x 0 * y 2 + y 0 * x 2) ^ 2 := by
        have : (x 1 * y 1) ^ 2 ≤ (x 0 * x 2) * (y 0 * y 2) := by
          rw [mul_pow]
          exact mul_le_mul hx1 hy1 (sq_nonneg _) (mul_nonneg hx0 hx2)
        nlinarith [sq_nonneg (x 0 * y 2 - y 0 * x 2)]
      exact (abs_le_of_sq_le_sq' hsq (by positivity)).2
    refine ⟨by positivity, by positivity, ?_⟩
    nlinarith [mul_nonneg hα hβ, mul_le_mul_of_nonneg_left key (mul_nonneg hα hβ),
      mul_le_mul_of_nonneg_left hx1 (mul_nonneg hα hα), mul_le_mul_of_nonneg_left hy1 (mul_nonneg hβ hβ)]
  · -- K₂ closed
    exact (isClosed_le h0 continuous_const).inter
      ((isClosed_eq h1 continuous_const).inter (isClosed_eq h2 continuous_const))
  · -- K₂ convex cone
    rintro x ⟨hx0, hx1, hx2⟩ y ⟨hy0, hy1, hy2⟩ α hα β hβ
    simp only [Set.mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hx1, hx2, hy1, hy2]
    refine ⟨?_, by ring, by ring⟩
    nlinarith [mul_nonneg hα (neg_nonneg.mpr hx0), mul_nonneg hβ (neg_nonneg.mpr hy0)]
  · -- sum not closed
    intro hS
    set S := setAdd {p : EuclideanSpace ℝ (Fin 3) | 0 ≤ p 0 ∧ 0 ≤ p 2 ∧ p 1 ^ 2 ≤ p 0 * p 2}
      {p | p 0 ≤ 0 ∧ p 1 = 0 ∧ p 2 = 0} with hSdef
    let g : ℝ → EuclideanSpace ℝ (Fin 3) := fun t => !₂[0, 1, t]
    have hg : Continuous g := by
      refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
      fin_cases i <;> simp <;> fun_prop
    have hpre := hS.preimage hg
    have hsub : Set.Ioi (0:ℝ) ⊆ g ⁻¹' S := by
      intro t ht
      simp only [Set.mem_preimage]
      have ht' : (0:ℝ) < t := ht
      refine ⟨!₂[1/t, 1, t], ⟨?_, ?_, ?_⟩, !₂[-(1/t), 0, 0], ⟨?_, ?_, ?_⟩, ?_⟩
      · simp; positivity
      · simp; positivity
      · simp; field_simp; rfl
      · simp; positivity
      · simp
      · simp
      · ext i
        fin_cases i <;> simp [g]
    have h0 : (0:ℝ) ∈ g ⁻¹' S := by
      have := hpre.closure_subset_iff.mpr hsub
      rw [closure_Ioi] at this
      exact this (Set.self_mem_Ici)
    obtain ⟨c, ⟨hc0, hc2, hc1⟩, k, ⟨hk0, hk1, hk2⟩, hck⟩ := h0
    have e1 : g 0 1 = c 1 + k 1 := by rw [hck]; rfl
    have e2 : g 0 2 = c 2 + k 2 := by rw [hck]; rfl
    simp [g, hk1, hk2] at e1 e2
    rw [← e1, ← e2] at hc1
    norm_num at hc1

end FCA_chap_A_ex_3
