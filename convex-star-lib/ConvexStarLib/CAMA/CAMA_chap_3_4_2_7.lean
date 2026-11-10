import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_4_2_7`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_4_2_7` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_4_2_7`, so the main result is `CAMA_chap_3_4_2_7.CAMA_chap_3_4_2_7`.
-/

namespace CAMA_chap_3_4_2_7

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_4_2_7
  (K : Set E)
  (hK_convex_cone : IsConvexCone K)
  (hK_nonempty : Set.Nonempty K) :
  polarCone (polarCone K) = closure K := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  -- 0 ∈ K
  have h0 : (0 : E) ∈ K := by
    obtain ⟨x, hx⟩ := hK_nonempty
    have := hK_convex_cone x hx x hx 0 le_rfl 0 le_rfl
    simpa using this
  -- K is convex
  have hconv : Convex ℝ K := by
    intro x hx y hy a b ha hb _
    exact hK_convex_cone x hx y hy a ha b hb
  -- K is closed under nonnegative scaling
  have hsmul : ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → t • x ∈ K := by
    intro x hx t ht
    have := hK_convex_cone x hx 0 h0 t ht 0 le_rfl
    simpa using this
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxK
    obtain ⟨f, u, hfu, hux⟩ :=
      geometric_hahn_banach_closed_point hconv.closure isClosed_closure hxK
    have hu0 : 0 < u := by
      have := hfu 0 (subset_closure h0)
      simpa using this
    have hfK : ∀ a ∈ K, f a ≤ 0 := by
      intro a ha
      by_contra hpos
      push_neg at hpos
      have ht : 0 ≤ u / f a := div_nonneg hu0.le hpos.le
      have := hfu ((u / f a) • a) (subset_closure (hsmul a ha _ ht))
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at this
      exact lt_irrefl _ this
    set s : E := (InnerProductSpace.toDual ℝ E).symm f with hs
    have hsf : ∀ y, inner ℝ s y = f y := by
      intro y
      rw [hs, InnerProductSpace.toDual_symm_apply]
    have hsK : s ∈ polarCone K := by
      intro a ha
      rw [hsf]
      exact hfK a ha
    have := hx s hsK
    rw [real_inner_comm, hsf] at this
    linarith
  · have hclosed : IsClosed (polarCone (polarCone K)) := by
      have : polarCone (polarCone K) = ⋂ x ∈ polarCone K, {s : E | inner ℝ s x ≤ 0} := by
        ext s
        simp only [polarCone, Set.mem_iInter, Set.mem_setOf_eq]
      rw [this]
      exact isClosed_biInter fun x _ =>
        isClosed_le (continuous_id.inner continuous_const) continuous_const
    apply closure_minimal _ hclosed
    intro x hx s hs
    rw [real_inner_comm]
    exact hs x hx

end CAMA_chap_3_4_2_7
