import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_3_2_5`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_3_2_5` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_3_2_5`, so the main result is `CAMA_chap_3_3_2_5.CAMA_chap_3_3_2_5`.
-/

namespace CAMA_chap_3_3_2_5

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_3_2_5
  (K : Set E)
  (x x₁ x₂ : E)
  (hK₀ : IsConvexCone K)
  (hK₁ : IsClosed K)
  (hK₂ : Set.Nonempty K) :
  let K' := (polarCone K)
  x = x₁ + x₂ ∧ x₁ ∈ K ∧ x₂ ∈ K' ∧ inner ℝ x₁ x₂ = 0 ↔
  x₁ = pC x K hK₁ (convexCone_isConvex hK₀) hK₂ ∧
  x₂ = pC x K' polarCone_isClosed polarCone_isConvex polarCone_isNonempty := by
  intro K'
  -- Characterization of the projection via the variational inequality.
  have spec : ∀ (u : E) (C : Set E) (h₁ : IsClosed C) (h₂ : Convex ℝ C) (h₃ : C.Nonempty),
      pC u C h₁ h₂ h₃ ∈ C ∧
        ∀ w ∈ C, inner ℝ (u - pC u C h₁ h₂ h₃) (w - pC u C h₁ h₂ h₃) ≤ 0 := by
    intro u C h₁ h₂ h₃
    obtain ⟨hmem, hnorm⟩ :=
      Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex h₃ h₁.isComplete h₂ u)
    exact ⟨hmem, (norm_eq_iInf_iff_real_inner_le_zero h₂ hmem).1 hnorm⟩
  -- Uniqueness: any point satisfying the variational inequality is the projection.
  have uniq : ∀ (u : E) (C : Set E) (h₁ : IsClosed C) (h₂ : Convex ℝ C) (h₃ : C.Nonempty)
      (v : E), v ∈ C → (∀ w ∈ C, inner ℝ (u - v) (w - v) ≤ 0) → v = pC u C h₁ h₂ h₃ := by
    intro u C h₁ h₂ h₃ v hv hvi
    obtain ⟨hpm, hpi⟩ := spec u C h₁ h₂ h₃
    generalize pC u C h₁ h₂ h₃ = p at hpm hpi ⊢
    have e1 := hpi v hv
    have e2 := hvi p hpm
    have e3 : inner ℝ (v - p) (v - p) ≤ 0 := by
      simp only [inner_sub_left, inner_sub_right] at e1 e2 ⊢
      linarith
    exact sub_eq_zero.mp (real_inner_self_nonpos.mp e3)
  have hKc : Convex ℝ K := convexCone_isConvex hK₀
  have h0K : (0 : E) ∈ K := by
    obtain ⟨y, hy⟩ := hK₂
    have := hK₀ y hy y hy 0 le_rfl 0 le_rfl
    simpa using this
  constructor
  · rintro ⟨hx, hx₁, hx₂, hinner⟩
    constructor
    · apply uniq x K _ _ _ x₁ hx₁
      intro w hw
      have hsub : x - x₁ = x₂ := by rw [hx]; abel
      rw [hsub, inner_sub_right]
      have h := hx₂ w hw
      rw [real_inner_comm] at hinner
      linarith
    · apply uniq x K' _ _ _ x₂ hx₂
      intro w hw
      have hsub : x - x₂ = x₁ := by rw [hx]; abel
      rw [hsub, inner_sub_right]
      have h := hw x₁ hx₁
      rw [real_inner_comm] at h
      linarith
  · rintro ⟨h1, h2⟩
    obtain ⟨hpK, hpi⟩ := spec x K hK₁ hKc hK₂
    generalize hp : pC x K hK₁ hKc hK₂ = p at hpK hpi h1
    have hA : inner ℝ (x - p) p = 0 := by
      have e1 := hpi 0 h0K
      have h2p : (2:ℝ) • p ∈ K := by
        have := hK₀ p hpK p hpK 2 (by norm_num) 0 le_rfl
        simpa using this
      have e2 := hpi ((2:ℝ) • p) h2p
      have h2p' : (2:ℝ) • p - p = p := by rw [two_smul]; abel
      rw [zero_sub, inner_neg_right] at e1
      rw [h2p'] at e2
      linarith
    have hxpK' : x - p ∈ K' := by
      intro w hw
      have := hpi w hw
      rw [inner_sub_right] at this
      linarith
    have hq : x - p = pC x K' polarCone_isClosed polarCone_isConvex polarCone_isNonempty := by
      apply uniq x K' _ _ _ (x - p) hxpK'
      intro w hw
      have hsub : x - (x - p) = p := by abel
      rw [hsub, inner_sub_right]
      have h := hw p hpK
      rw [real_inner_comm] at h hA
      linarith
    rw [← hq] at h2
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h1, h2]; abel
    · rw [h1]; exact hpK
    · rw [h2]; exact hxpK'
    · rw [h1, h2, real_inner_comm]; exact hA

end CAMA_chap_3_3_2_5
